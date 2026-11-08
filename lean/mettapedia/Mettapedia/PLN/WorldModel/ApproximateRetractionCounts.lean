import Mettapedia.PLN.WorldModel.ApproximateRetraction
import Mettapedia.PLN.WorldModel.LedgerRetraction

/-!
# Approximate retraction on aggregated counts, and the two contracts

## Aggregates cannot retract exactly

An aggregate count forgets which identities contributed.  The ledgers `{0}` and `{1}` give the same
aggregate to a claim to which both are relevant; withdrawing `0` leaves nothing from the first and
one observation from the second.  No function of the aggregate is exact
(`no_aggregate_retraction`): the obstruction is missing information, not missing computation.

## The cap certificate

If the withdrawn identities are known to contribute at most `cap` to a claim, subtracting the cap
from the aggregate is enclosed with width `cap` in each polarity (`aggregate_encloses`): it never
exceeds the exact recount (`LedgerRetraction.causal_recount`).  A second forgetting subtracts a
second cap; exact subtraction is an isometry, so the widths add (`aggregate_twice`), the shape
`ε₂ + 1 · ε₁` of `ApproximationMap.comp`.

* **The error accumulates, and the sum is attained**: three observations from identity `2`, while
  identities `0` and `1` are each capped at one observation and contributed nothing.  The estimate
  falls from `3` to `2` to `1`; the exact count stays `3` (`Controls.accumulation`).
* **Not idempotent**: forgetting `0` twice subtracts its cap twice, while exact retraction forgets
  once (`Controls.not_idempotent`).  A record of what was forgotten restores idempotence, and that
  record holds the withdrawn identities (`tombstoneForget_idempotent`, `tombstoneForget_records`).
* **It keeps information about the withdrawn identities**: `{0, 1}` and `{1}` agree once `0` is
  withdrawn, and their aggregates after forgetting differ (`Controls.aggregate_leaks`).

## Two contracts

Forgetting that deletes from the ledger and keeps the log of received observations passes belief
retraction: every reading of the ledger agrees with recomputation
(`Contracts.logged_beliefRetraction`).  The log still holds the withdrawn observation
(`Contracts.logged_retains`), and two logged ledgers that agree once it is removed are told apart
after forgetting (`Contracts.logged_not_erased`).  Causal deletion on the ledger keeps no withdrawn
identity (`causalForget_avoids`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetractionCounts

open scoped NNReal
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence (positive)
open Mettapedia.PLN.WorldModel.LedgerRetraction
open Mettapedia.PLN.WorldModel.ApproximateRetraction

/-- Natural-number bounds give an enclosure of their casts. -/
theorem encloses_of_nat {lo w x : ℕ} (h₁ : lo ≤ x) (h₂ : x ≤ lo + w) :
    Encloses (lo : ℝ≥0) (w : ℝ≥0) (x : ℝ≥0) :=
  ⟨Nat.cast_le.mpr h₁, by exact_mod_cast h₂⟩

/-! ## Aggregates cannot retract exactly -/

/-- The claim to which every observation is relevant and positive. -/
def allPositive : IdClaim ℕ := totalClaim fun _ => true

theorem bagEvidence_allPositive_singleton (o : ℕ) : bagEvidence allPositive {o} = positive := by
  simp [bagEvidence, allPositive, totalClaim, sampleEvidence]

/-- **No function of the aggregate retracts exactly.** -/
theorem no_aggregate_retraction :
    ¬ ∃ f : Evidence ℕ → Evidence ℕ, ∀ m : Multiset ℕ,
      f (bagEvidence allPositive m) = bagEvidence allPositive (causalForget {0} m) := by
  rintro ⟨f, hf⟩
  have first := hf {0}
  have second := hf {1}
  have gone : causalForget {0} ({0} : Multiset ℕ) = 0 := by decide
  have kept : causalForget {0} ({1} : Multiset ℕ) = {1} := by decide
  have empty : bagEvidence allPositive (0 : Multiset ℕ) = 0 := by simp [bagEvidence]
  rw [gone, empty, bagEvidence_allPositive_singleton] at first
  rw [kept, bagEvidence_allPositive_singleton] at second
  have same : (0 : Evidence ℕ) = positive := first.symm.trans second
  exact absurd (congrArg Evidence.pos same) (by simp [positive])

/-! ## The cap certificate -/

section Caps

variable {O : Type} [DecidableEq O]

/-- The contribution of the identities `S` to a claim. -/
def contribution (S : Finset O) (m : Multiset O) (q : IdClaim O) : Evidence ℕ :=
  bagEvidence q (m.filter fun o => o ∈ S)

/-- **The cap certificate**: if the withdrawn identities contribute at most `cap`, subtracting the
cap from the aggregate never exceeds the exact recount and misses at most the cap. -/
theorem aggregate_encloses (S : Finset O) (m : Multiset O) (q : IdClaim O) (cap : Evidence ℕ)
    (capped : contribution S m q ≤ cap) :
    Encloses (((bagEvidence q m - cap).pos : ℕ) : ℝ≥0) ((cap.pos : ℕ) : ℝ≥0)
        (((bagEvidence q (causalForget S m)).pos : ℕ) : ℝ≥0) ∧
      Encloses (((bagEvidence q m - cap).neg : ℕ) : ℝ≥0) ((cap.neg : ℕ) : ℝ≥0)
        (((bagEvidence q (causalForget S m)).neg : ℕ) : ℝ≥0) := by
  obtain ⟨hp, hn⟩ := (Evidence.le_def _ _).mp capped
  rw [causal_recount]
  refine ⟨encloses_of_nat ?_ ?_, encloses_of_nat ?_ ?_⟩
  · show (bagEvidence q m).pos - cap.pos ≤ (bagEvidence q m).pos - (contribution S m q).pos
    omega
  · show (bagEvidence q m).pos - (contribution S m q).pos ≤
      (bagEvidence q m).pos - cap.pos + cap.pos
    omega
  · show (bagEvidence q m).neg - cap.neg ≤ (bagEvidence q m).neg - (contribution S m q).neg
    omega
  · show (bagEvidence q m).neg - (contribution S m q).neg ≤
      (bagEvidence q m).neg - cap.neg + cap.neg
    omega

/-- **A second forgetting adds its cap to the width**: exact subtraction is an isometry, so the
earlier width passes through unscaled. -/
theorem aggregate_twice (S T : Finset O) (m : Multiset O) (q : IdClaim O) (capS capT : Evidence ℕ)
    (cappedS : contribution S m q ≤ capS) (cappedT : contribution T m q ≤ capT) :
    Encloses ((((bagEvidence q m - capS) - capT).pos : ℕ) : ℝ≥0) ((capS.pos + capT.pos : ℕ) : ℝ≥0)
        (((bagEvidence q (causalForget T (causalForget S m))).pos : ℕ) : ℝ≥0) ∧
      Encloses ((((bagEvidence q m - capS) - capT).neg : ℕ) : ℝ≥0)
        ((capS.neg + capT.neg : ℕ) : ℝ≥0)
        (((bagEvidence q (causalForget T (causalForget S m))).neg : ℕ) : ℝ≥0) := by
  have later : contribution T (causalForget S m) q ≤ contribution T m q :=
    bagEvidence_mono q (Multiset.filter_le_filter _ (causalForget_le S m))
  obtain ⟨sp, sn⟩ := (Evidence.le_def _ _).mp cappedS
  obtain ⟨tp, tn⟩ := (Evidence.le_def _ _).mp cappedT
  obtain ⟨lp, ln⟩ := (Evidence.le_def _ _).mp later
  rw [causal_recount, causal_recount]
  refine ⟨encloses_of_nat ?_ ?_, encloses_of_nat ?_ ?_⟩
  · show (bagEvidence q m).pos - capS.pos - capT.pos ≤
      (bagEvidence q m).pos - (contribution S m q).pos - (contribution T (causalForget S m) q).pos
    omega
  · show (bagEvidence q m).pos - (contribution S m q).pos -
        (contribution T (causalForget S m) q).pos ≤
      (bagEvidence q m).pos - capS.pos - capT.pos + (capS.pos + capT.pos)
    omega
  · show (bagEvidence q m).neg - capS.neg - capT.neg ≤
      (bagEvidence q m).neg - (contribution S m q).neg - (contribution T (causalForget S m) q).neg
    omega
  · show (bagEvidence q m).neg - (contribution S m q).neg -
        (contribution T (causalForget S m) q).neg ≤
      (bagEvidence q m).neg - capS.neg - capT.neg + (capS.neg + capT.neg)
    omega

/-- Aggregate forgetting with a record of what was forgotten: the caps of identities already
forgotten are not subtracted again. -/
def tombstoneForget (cap : O → Evidence ℕ) (S : Finset O) (s : Evidence ℕ × Finset O) :
    Evidence ℕ × Finset O :=
  (s.1 - ∑ o ∈ S \ s.2, cap o, s.2 ∪ S)

/-- **The record restores idempotence.** -/
theorem tombstoneForget_idempotent (cap : O → Evidence ℕ) (S : Finset O)
    (s : Evidence ℕ × Finset O) :
    tombstoneForget cap S (tombstoneForget cap S s) = tombstoneForget cap S s := by
  have none : S \ (s.2 ∪ S) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_right
  have minusZero : ∀ x : Evidence ℕ, x - 0 = x := fun x =>
    Evidence.ext (Nat.sub_zero x.pos) (Nat.sub_zero x.neg)
  simp only [tombstoneForget]
  rw [none, Finset.sum_empty, minusZero, Finset.union_assoc, Finset.union_self]

/-- **The record holds the withdrawn identities.** -/
theorem tombstoneForget_records (cap : O → Evidence ℕ) (S : Finset O)
    (s : Evidence ℕ × Finset O) : S ⊆ (tombstoneForget cap S s).2 :=
  Finset.subset_union_right

/-- **Causal deletion keeps no withdrawn identity.** -/
theorem causalForget_avoids (S : Finset O) (m : Multiset O) : ∀ o ∈ causalForget S m, o ∉ S :=
  fun _ h => (Multiset.mem_filter.mp h).2

end Caps

namespace Controls

/-- Decidable equality of counts, for checking the controls. -/
local instance : DecidableEq (Evidence ℕ) := fun a b =>
  decidable_of_iff (a.pos = b.pos ∧ a.neg = b.neg) Evidence.ext_iff.symm

/-- Three observations from identity `2`. -/
def three : Multiset ℕ := {2, 2, 2}

/-- **The error accumulates, and the sum is attained.**  Identities `0` and `1`, each capped at one
positive observation, contributed nothing.  After forgetting both, the estimate is `1`, the width
is `1 + 1`, and the exact count is `3`: the estimate plus the width. -/
theorem accumulation :
    contribution {0} three allPositive = 0 ∧ contribution {1} three allPositive = 0 ∧
      (bagEvidence allPositive three - positive).pos = 2 ∧
      ((bagEvidence allPositive three - positive) - positive).pos = 1 ∧
      (bagEvidence allPositive (causalForget {0} three)).pos = 3 ∧
      (bagEvidence allPositive (causalForget {1} (causalForget {0} three))).pos =
        ((bagEvidence allPositive three - positive) - positive).pos +
          ((positive : Evidence ℕ).pos + (positive : Evidence ℕ).pos) := by
  decide

/-- **Not idempotent**: forgetting `0` twice subtracts its cap twice, and exact retraction forgets
once. -/
theorem not_idempotent :
    causalForget {0} (causalForget {0} three) = causalForget {0} three ∧
      ((bagEvidence allPositive three - positive) - positive).pos ≠
        (bagEvidence allPositive three - positive).pos :=
  ⟨causalForget_idempotent {0} three, by decide⟩

/-- **The aggregate keeps information about the withdrawn identity.**  `{0, 1}` and `{1}` agree
once `0` is withdrawn; subtracting a cap of one positive observation leaves them different. -/
theorem aggregate_leaks :
    ¬ ErasesUpToRecomputation
      (fun (_ : Finset ℕ) (m : Multiset ℕ) => bagEvidence allPositive m - positive)
      causalForget := by
  intro erases
  have same := erases {0} {0, 1} {1} (by decide)
  exact absurd (congrArg Evidence.pos same) (by decide)

end Controls

/-! ## Two contracts -/

namespace Contracts

/-- A ledger with the log of every observation it received. -/
abbrev Logged (O : Type) := Multiset O × List O

variable {O : Type} [DecidableEq O]

/-- Forgetting that deletes from the ledger and keeps the log. -/
def forgetKeepingLog (S : Finset O) (s : Logged O) : Logged O := (causalForget S s.1, s.2)

/-- Recomputation without `S`: the ledger and the log of the retained observations. -/
def recompute (S : Finset O) (s : Logged O) : Logged O :=
  (causalForget S s.1, s.2.filter fun o => o ∉ S)

/-- Readings see only the ledger. -/
def readLedger (s : Logged O) (q : IdClaim O) : Evidence ℕ := bagEvidence q s.1

/-- **Belief retraction holds**: every reading agrees with recomputation. -/
theorem logged_beliefRetraction :
    BeliefRetraction (forgetKeepingLog (O := O)) recompute readLedger :=
  fun _ _ _ => rfl

/-- **The log still holds the withdrawn observation.** -/
theorem logged_retains : (4 : ℕ) ∈ (forgetKeepingLog {4} (({4} : Multiset ℕ), [4])).2 := by
  simp [forgetKeepingLog]

/-- **Erasure fails**: two logged ledgers that agree once `4` is removed are told apart after
forgetting it. -/
theorem logged_not_erased : ¬ ErasesUpToRecomputation (forgetKeepingLog (O := ℕ)) recompute := by
  intro erases
  have same := erases {4} (({4} : Multiset ℕ), [4]) (0, []) (by decide)
  exact absurd (congrArg Prod.snd same) (by decide)

end Contracts

end Mettapedia.PLN.WorldModel.ApproximateRetractionCounts

open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms no_aggregate_retraction
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms aggregate_encloses
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms aggregate_twice
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms tombstoneForget_idempotent
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms tombstoneForget_records
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms causalForget_avoids
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Controls.accumulation
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Controls.not_idempotent
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Controls.aggregate_leaks
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Contracts.logged_beliefRetraction
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Contracts.logged_retains
open Mettapedia.PLN.WorldModel.ApproximateRetractionCounts in
#print axioms Contracts.logged_not_erased
