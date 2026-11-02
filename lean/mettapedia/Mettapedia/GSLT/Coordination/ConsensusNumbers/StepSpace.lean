import Mettapedia.GSLT.Coordination.ConsensusNumbers.Spaces
import Mettapedia.GSLT.Coordination.ConsensusNumbers.Race
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps

/-!
# Spaces with the atomic step

A **step** (the draft's `transform`, fired now) is one atomic action on a space, given as a ground
rule (`Rule` of the borrowed-step module): it takes the bag `take`, keeps the bag `keep`, adds the
bag `make`, and requires that nothing else in the space satisfies the test `closed` (absence,
counts, `all`). It fires when all of that holds, and then answers `fired true`; otherwise it
changes nothing and answers `fired false`.
Example: the step taking `(decision undecided)` and making `(decision 1)` fires at the space
`{(decision undecided)}` and leaves `{(decision 1)}`; at `{(decision 0)}` it does nothing.

`ruleSpace allowed` is a space handle that may fire the rules satisfying `allowed` and may query
(`match`). Different `allowed` give handles with fewer rights on the same space:

| handle | rules allowed | consensus number |
|---|---|---|
| `monotoneSpace` | keep and make only | 1 (`monotoneSpace_hasConsensusNumber_one`) |
| `positiveSpace` | take, keep and make, no condition on the whole space | ∞ (`positiveSpace_hasConsensusNumber_top`) |
| `noTakeSpace` | keep, make and conditions on the whole space, no take | ∞ (`noTakeSpace_hasConsensusNumber_top`) |
| `stepSpace` | every rule | ∞ (`stepSpace_hasConsensusNumber_top`) |

Beside `Spaces`: MeTTa's separate operations give 2 with removals that report success and 1 with
silent ones. A step adds and removes too (`make {a}`, `take {a}`), so the step handle has those
rights.

* A monotone step only adds, and its enabling only grows, so any two commute: steps that keep and
  make have consensus number one, like registers.
* A step that takes `(decision undecided)` and makes `(decision v)` is compare-and-swap; so is a
  step that makes `(decision v)` provided no decision is present, with no take at all. Either one
  gives the race of `Race`, and consensus for every number of processes.

## Peek and take-and-re-send

`remake ρ` takes what `ρ` keeps and makes it again. Its firing is the same function of the
space: same enabling, same result, same answer (`remake_apply`). So no measure computed from the
sequential specification of operations, consensus numbers included, tells a peek from a
take-and-re-send. They differ in independence: two keepers of one atom commute, two re-senders of
it clash (`OccurrenceCommits.Basis.keep_not_take_remake`, `not_encodes_keep`).

## Controls

* `Controls.monotone_pair_hidden`: two monotone steps that both fire commute, answers included.
* `Controls.absence_claims_seen`: two absence-guarded claims with different values at the empty
  space are hidden from nobody.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Avoids
  avoids_none)

variable {A : Type} [DecidableEq A]

instance (ρ : Rule A) (M : Multiset A) : Decidable (ρ.Enabled M) :=
  inferInstanceAs (Decidable (ρ.redex ≤ M ∧ Avoids (M - ρ.redex) ρ.closed))

/-- Operations of a space handle: queries, and the rules it may fire. -/
inductive RuleOp (A : Type) (allowed : Rule A → Prop) where
  | query (p : A → Bool)
  | step (ρ : Rule A) (ok : allowed ρ)

variable (A) in
/-- A space handle that may fire the rules satisfying `allowed`, and query. -/
abbrev ruleSpace (allowed : Rule A → Prop) : DetObject where
  State := Multiset A
  Op := RuleOp A allowed
  Res := SpaceReply A
  apply M
    | .query p => (M, .matches (M.filter fun b => p b = true))
    | .step ρ _ => if ρ.Enabled M then (ρ.result M, .fired true) else (M, .fired false)

variable (A) in
/-- Steps that keep and make only. -/
abbrev monotoneSpace : DetObject := ruleSpace A fun ρ => ρ.take = 0 ∧ ρ.Positive

variable (A) in
/-- Steps without conditions on the whole space: take, keep and make (a COMM that does not wait). -/
abbrev positiveSpace : DetObject := ruleSpace A fun ρ => ρ.Positive

variable (A) in
/-- Steps that take nothing, with conditions on the whole space allowed. -/
abbrev noTakeSpace : DetObject := ruleSpace A fun ρ => ρ.take = 0

variable (A) in
/-- Every step: the draft's `transform`. -/
abbrev stepSpace : DetObject := ruleSpace A fun _ => True

/-! ## Monotone steps commute -/

theorem monotone_enabled_iff {ρ : Rule A} (h : ρ.take = 0 ∧ ρ.Positive) (M : Multiset A) :
    ρ.Enabled M ↔ ρ.keep ≤ M := by
  rw [Rule.enabled_iff_of_positive h.2, Rule.redex, h.1, zero_add]

theorem monotone_result {ρ : Rule A} (h : ρ.take = 0) (M : Multiset A) : ρ.result M = M + ρ.make := by
  rw [Rule.result, h, tsub_zero]

/-- **One of the two processes cannot tell the order of two monotone steps.** -/
theorem monotoneSpace_pairCannotOrder : ∀ M a b, PairCannotOrder (monotoneSpace A) M a b := by
  intro M a b
  cases a with
  | query p => exact Or.inl (.noChange rfl)
  | step ρ hρ =>
      cases b with
      | query q => exact Or.inr (.noChange rfl)
      | step σ hσ =>
          by_cases eρ : ρ.Enabled M
          · by_cases eσ : σ.Enabled M
            · have eρ' : ρ.Enabled (M + σ.make) :=
                (monotone_enabled_iff hρ _).mpr
                  (((monotone_enabled_iff hρ M).mp eρ).trans (Multiset.le_add_right _ _))
              have eσ' : σ.Enabled (M + ρ.make) :=
                (monotone_enabled_iff hσ _).mpr
                  (((monotone_enabled_iff hσ M).mp eσ).trans (Multiset.le_add_right _ _))
              refine Or.inl (.commutes ?_ ?_)
              · simp only [if_pos eρ, if_pos eσ, monotone_result hρ.1, monotone_result hσ.1,
                  if_pos eρ', if_pos eσ']
                exact add_right_comm _ _ _
              · simp only [if_pos eσ, monotone_result hσ.1, if_pos eρ', if_pos eρ]
            · exact Or.inr (.noChange (by simp only [if_neg eσ]))
          · exact Or.inl (.noChange (by simp only [if_neg eρ]))

/-- **A space whose steps only keep and make has consensus number one.** -/
theorem monotoneSpace_hasConsensusNumber_one : HasConsensusNumber (monotoneSpace A).toObject 1 :=
  hasConsensusNumber_one (T := monotoneSpace A) 0 monotoneSpace_pairCannotOrder

/-! ## Races from a step -/

section Races

variable {V : Type} (undecided : A) (cell : V → A)

open Classical in
/-- Is the atom a decision cell? -/
noncomputable def isCell (a : A) : Bool := decide (∃ w, cell w = a)

open Classical in
/-- The value of a decision cell found in `m`, or `v`. -/
noncomputable def pickCell (m : Multiset A) (v : V) : V :=
  if h : ∃ w, cell w ∈ m then h.choose else v

/-- Did the step fire? -/
def firedOf : SpaceReply A → Bool
  | .fired b => b
  | _ => false

/-- What a query of the cells found. -/
noncomputable def learnCell : SpaceReply A → V → V
  | .matches m, v => pickCell cell m v
  | _, v => v

/-- Compare-and-swap as a step: take the undecided cell, make the decided one. -/
def casRule (v : V) : Rule A := ⟨{undecided}, 0, {cell v}, fun _ => false⟩

/-- An absence-guarded claim: make the decided cell provided no cell is decided; take nothing. -/
noncomputable def absenceRule (v : V) : Rule A := ⟨0, 0, {cell v}, isCell cell⟩

variable {undecided cell}

omit [DecidableEq A] in
theorem casRule_positive (v : V) : (casRule undecided cell v).Positive := fun _ => rfl

omit [DecidableEq A] in
theorem pickCell_singleton (inj : Function.Injective cell) (v w : V) :
    pickCell cell ((({cell w} : Multiset A)).filter fun b => isCell cell b = true) v = w := by
  have mem : cell w ∈ ((({cell w} : Multiset A)).filter fun b => isCell cell b = true) :=
    Multiset.mem_filter.mpr ⟨Multiset.mem_singleton_self _, by
      simp only [isCell, decide_eq_true_eq]; exact ⟨w, rfl⟩⟩
  unfold pickCell
  rw [dif_pos ⟨w, mem⟩]
  have spec := Exists.choose_spec (p := fun u => cell u ∈ _) ⟨w, mem⟩
  exact inj (Multiset.mem_singleton.mp (Multiset.mem_of_mem_filter spec))

/-- **The compare-and-swap race over positive steps.** -/
noncomputable def casRace (inj : Function.Injective cell) (fresh : ∀ v, cell v ≠ undecided) :
    Race (positiveSpace A) V where
  start := {undecided}
  claim v := .step (casRule undecided cell v) (casRule_positive v)
  read := .query (isCell cell)
  settled v := {cell v}
  won := firedOf
  learn := learnCell cell
  claim_start v := by
    have enabled : (casRule undecided cell v).Enabled {undecided} :=
      ⟨by simp [Rule.redex, casRule], fun _ _ => rfl⟩
    simp only [if_pos enabled]
    simp [Rule.result, casRule]
  claim_settled v w := by
    have disabled : ¬ (casRule undecided cell v).Enabled {cell w} := by
      rintro ⟨le, -⟩
      simp only [Rule.redex, casRule, add_zero, Multiset.singleton_le, Multiset.mem_singleton] at le
      exact fresh w le.symm
    simp only [if_neg disabled]
    simp [firedOf]
  read_settled v w := ⟨rfl, pickCell_singleton inj v w⟩

/-- **The absence-guarded race over steps that take nothing.** -/
noncomputable def absenceRace (inj : Function.Injective cell) : Race (noTakeSpace A) V where
  start := 0
  claim v := .step (absenceRule cell v) rfl
  read := .query (isCell cell)
  settled v := {cell v}
  won := firedOf
  learn := learnCell cell
  claim_start v := by
    have enabled : (absenceRule cell v).Enabled 0 :=
      ⟨by simp [Rule.redex, absenceRule], by simp [Rule.redex, absenceRule]⟩
    simp only [if_pos enabled]
    simp [Rule.result, absenceRule]
  claim_settled v w := by
    have disabled : ¬ (absenceRule cell v).Enabled {cell w} := by
      rintro ⟨-, avoids⟩
      have := avoids (cell w) (by simp [Rule.redex, absenceRule])
      simp [absenceRule, isCell] at this
    simp only [if_neg disabled]
    simp [firedOf]
  read_settled v w := ⟨rfl, pickCell_singleton inj v w⟩

end Races

omit [DecidableEq A] in
/-- Three distinct atoms in an infinite atom type. -/
theorem exists_cells [Infinite A] :
    ∃ (undecided : A) (cell : Bool → A), Function.Injective cell ∧ ∀ v, cell v ≠ undecided := by
  let e : Option Bool → A := fun o => Infinite.natEmbedding A (Encodable.encode o)
  have inj : Function.Injective e :=
    (Infinite.natEmbedding A).injective.comp Encodable.encode_injective
  refine ⟨e none, fun v => e (some v), fun v w h => Option.some.inj (inj h), fun v h => ?_⟩
  exact absurd (inj h) (by simp)

/-- **A space with take-and-make steps and no conditions on the whole space has an infinite
consensus number.** -/
theorem positiveSpace_hasConsensusNumber_top [Infinite A] :
    HasConsensusNumber (positiveSpace A).toObject ⊤ := by
  obtain ⟨undecided, cell, inj, fresh⟩ := exists_cells (A := A)
  exact (casRace (undecided := undecided) inj fresh).hasConsensusNumber_top

/-- **A space whose steps take nothing but may test absence has an infinite consensus number.** -/
theorem noTakeSpace_hasConsensusNumber_top [Infinite A] :
    HasConsensusNumber (noTakeSpace A).toObject ⊤ := by
  obtain ⟨-, cell, inj, -⟩ := exists_cells (A := A)
  exact (absenceRace inj).hasConsensusNumber_top

/-- **The step has an infinite consensus number.** -/
theorem stepSpace_hasConsensusNumber_top [Infinite A] :
    HasConsensusNumber (stepSpace A).toObject ⊤ := by
  obtain ⟨undecided, cell, inj, fresh⟩ := exists_cells (A := A)
  let R := casRace (undecided := undecided) inj fresh
  exact Race.hasConsensusNumber_top
    { start := R.start, claim := fun v => .step (casRule undecided cell v) trivial,
      read := .query (isCell cell), settled := R.settled, won := R.won, learn := R.learn,
      claim_start := R.claim_start, claim_settled := R.claim_settled,
      read_settled := R.read_settled }

/-! ## Peek and take-and-re-send have one sequential specification -/

omit [DecidableEq A] in
/-- Take what `ρ` keeps, and make it again. -/
def remake (ρ : Rule A) : Rule A := ⟨ρ.take + ρ.keep, 0, ρ.make + ρ.keep, ρ.closed⟩

theorem remake_enabled_iff (ρ : Rule A) (M : Multiset A) : (remake ρ).Enabled M ↔ ρ.Enabled M := by
  simp [Rule.Enabled, Rule.redex, remake]

theorem remake_result {ρ : Rule A} {M : Multiset A} (h : ρ.Enabled M) :
    (remake ρ).result M = ρ.result M := by
  have le := Multiset.le_iff_count.mp h.1
  simp only [Rule.result, remake]
  ext x
  have := le x
  simp only [Rule.redex, Multiset.count_add] at this
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

/-- **A take-and-re-send is the same atomic operation as a peek**: same enabling, same result,
same answer, at every space. -/
theorem remake_apply (ρ : Rule A) (M : Multiset A) :
    (stepSpace A).apply M (.step (remake ρ) trivial) = (stepSpace A).apply M (.step ρ trivial) := by
  by_cases h : ρ.Enabled M
  · simp only [if_pos h, if_pos ((remake_enabled_iff ρ M).mpr h), remake_result h]
  · simp only [if_neg h, if_neg (mt (remake_enabled_iff ρ M).mp h)]

/-! ## Controls -/

namespace Controls

/-- **Positive control**: two steps that keep `0` and make `1` and `2` at `{0}` commute, answers
included. -/
theorem monotone_pair_hidden :
    OrderHidden (monotoneSpace ℕ) {0} (.step ⟨0, {0}, {1}, fun _ => false⟩ ⟨rfl, fun _ => rfl⟩)
      (.step ⟨0, {0}, {2}, fun _ => false⟩ ⟨rfl, fun _ => rfl⟩) := by
  refine .commutes ?_ ?_ <;> simp [Rule.Enabled, Rule.redex, Rule.result, Avoids]
  exact Multiset.cons_swap _ _ _

/-- **Negative control**: two absence-guarded claims at the empty space, making `1` and `2`
provided neither is present, are hidden from nobody: the first to fire wins. -/
theorem absence_claims_seen :
    ¬ BystanderCannotOrder (noTakeSpace ℕ) 0
      (.step ⟨0, 0, {1}, fun a => decide (a = 1 ∨ a = 2)⟩ rfl)
      (.step ⟨0, 0, {2}, fun a => decide (a = 1 ∨ a = 2)⟩ rfl) := by
  have one : ∀ a b : ℕ, a ∈ ({1, 2} : Finset ℕ) → b ∈ ({1, 2} : Finset ℕ) → a ≠ b →
      ¬ OrderHidden (noTakeSpace ℕ) 0 (.step ⟨0, 0, {a}, fun c => decide (c = 1 ∨ c = 2)⟩ rfl)
        (.step ⟨0, 0, {b}, fun c => decide (c = 1 ∨ c = 2)⟩ rfl) := by
    intro a b ha hb ne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rintro (h | h | ⟨h, -⟩) <;>
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all [Rule.Enabled, Rule.redex, Rule.result, Avoids]
  rintro ((h | h) | h)
  · exact one 1 2 (by simp) (by simp) (by decide) h
  · exact one 2 1 (by simp) (by simp) (by decide) h
  · simp [Rule.Enabled, Rule.redex, Rule.result, Avoids] at h

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
