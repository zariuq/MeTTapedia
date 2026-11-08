import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates

/-!
# The world-model calculus as firings: revision and deduction over the evidence space

A PLN rule is a firing of the candidate step with three parts: a predicate query of the evidence
space at the firing's cut, guards, and a produced result row. The predicate query is complete: it
holds only when it saw the whole ledger, so the rule reads the world-model state itself.

## Revision

* `revisionFiring φ row seen r` has the predicate query of the evidence space that saw `seen`, no
  guards, and produces at the fresh identity `r` the row of the evidence of `seen`. It is admitted
  exactly when `seen` is the ledger, `r` is fresh and carries that row, and the store has a
  solution (`revisionFiring_valid_iff`). A predicate query that saw anything else is refused
  (`revisionFiring_refused`).
* **Adequacy** (`revision_adequate`): an admitted revision firing produces the row of the
  extraction of the ledger world model at the cut. When the ledger is the union of two ledgers,
  that is the overlap revision of the world model, the sum minus the overlap
  (`revision_adequate_union`).
* A row outside the evidence space leaves the ledger as it was (`revision_keeps_ledger`): results
  are not observations, so a rule cannot count its own output.

## Deduction

* Screening off is decided on the counts of what the query saw (`Screened`). Guard verdicts are
  two terms that no substitution identifies (`GuardBits`); the guard asks the equation of the
  decided verdict with the term for yes (`GuardBits.check`, `GuardBits.holds_iff`).
* `deductionFiring` has the same predicate query, the screening guard, and produces the row of the
  PLN deduction formula on the strengths read from what it saw (`deductionValue`).
* **Adequacy** (`deduction_adequate`): an admitted deduction firing saw the ledger, the ledger
  screens off, and its row is the frequency of the conclusion among the worlds of the antecedent
  in the ledger (`linkValue`): the world-model answer to the conclusion query, by
  `EvidenceContracts.deduction_exact_of_screening`. Without screening off the firing is refused
  (`deduction_refused`).

## Incompleteness is not "no evidence"

* A budgeted scan of the evidence space reports what it found and a status of R27's
  `AnnotatedRunCandidates.Status` (`scanFound`, `scanStatus`). With a scan list covering the cut,
  what it found lies in the ledger (`scanFound_subset`), and is the ledger when it finished
  (`scanFound_eq_of_complete`).
* A count is a whole-table attempt: complete, it counts (`budgetedCount`, `complete_counts`);
  incomplete, it reports a lower bound only (`incomplete_lower_bound`).
* **No evidence** is a complete count of nothing (`NoEvidence`, `noEvidence_iff`), so an exhausted
  scan never reports it (`incomplete_never_noEvidence`). The verdict of the question "is there
  evidence?" is R27's `Verdict.rule`, whose `none` needs a complete search
  (`verdict_none_iff`); as an attempt outcome a count fires or is incomplete and never reports
  `none` (`countOutcome_ne_none`), like a whole-table attempt of `ContextualAttemptOutcomes`.
* A complete scan fires the revision rule on what it found (`complete_scan_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

open MeTTaCalculus.OccurrenceCommits (regionOf PredicateQuery mem_regionOf)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open AnnotatedRunCandidates (Status Verdict)

universe uT uS uO uW
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {W : Type uW}

/-! ## Revision -/

section Revision

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool) (outcome : T → W)

/-- **The revision firing** whose predicate query of the evidence space saw `seen`: no guards,
and the row of the evidence of `seen` made at `r`. -/
def revisionFiring (φ : W → Bool) (row : Evidence ℕ → T) (seen : Finset O) (r : O) :
    Firing T S O :=
  ⟨⟨[], [], [], [], [row (ledgerEvidence (recorded label outcome) φ seen)]⟩,
    [PredicateQueryAdmission.Query.fixed (ledgerQuery space seen)], ⟨[], [], [r]⟩⟩

/-- **Admission of revision**: the predicate query saw the ledger, the row is fresh and carries the
counts, and the store has a solution. -/
theorem revisionFiring_valid_iff (φ : W → Bool) (row : Evidence ℕ → T) (seen : Finset O) (r : O)
    (C : Configuration T O) :
    (revisionFiring label space outcome φ row seen r).Valid A label C ↔
      ledger label space C = seen ∧ r ∉ C.present ∧
        label r = row (ledgerEvidence (recorded label outcome) φ seen) ∧
        A.Consistent C.equations := by
  change PredicateQueryAdmission.Valid A label _ ([ledgerQuery space seen].map PredicateQueryAdmission.Query.fixed)
    C _ ↔ _
  rw [PredicateQueryAdmission.valid_fixed_iff]
  constructor
  · rintro ⟨firing, holds⟩
    refine ⟨holds _ (List.mem_singleton_self _), ?_, ?_, ?_⟩
    · intro present
      exact Finset.disjoint_left.mp firing.occurrences.fresh
        (by simp [Selection.commit, revisionFiring]) present
    · simpa [revisionFiring] using firing.outputs
    · obtain ⟨σ, solved⟩ := firing.consistent
      exact ⟨σ, fun e member => solved e
        (by simp [Selection.problem, Selection.equations, revisionFiring, member])⟩
  · rintro ⟨seenEq, fresh, rowEq, consistent⟩
    refine ⟨⟨by simp [revisionFiring], by simp [revisionFiring], rfl, rfl,
      by simp [revisionFiring, rowEq], ?_, ?_, by simp [revisionFiring]⟩, ?_⟩
    · exact ⟨by simp [Selection.commit, revisionFiring], by simp [Selection.commit, revisionFiring],
        by simp [Selection.commit, revisionFiring],
        by simpa [Selection.commit, revisionFiring] using fresh,
        by simp [Selection.commit, revisionFiring]⟩
    · obtain ⟨σ, solved⟩ := consistent
      exact ⟨σ, fun e member => solved e
        (by simpa [Selection.problem, Selection.equations, revisionFiring] using member)⟩
    · intro query member
      rw [List.mem_singleton.mp member]
      exact seenEq

/-- **A predicate query that saw anything but the ledger is refused.** -/
theorem revisionFiring_refused (φ : W → Bool) (row : Evidence ℕ → T) {seen : Finset O} (r : O)
    {C : Configuration T O} (other : ledger label space C ≠ seen) :
    ¬ (revisionFiring label space outcome φ row seen r).Valid A label C := fun valid =>
  other ((revisionFiring_valid_iff A label space outcome φ row seen r C).mp valid).1

/-- **Adequacy of revision**: an admitted revision firing saw the ledger and produces the row of
the extraction of the ledger world model at the cut. -/
theorem revision_adequate {φ : W → Bool} {row : Evidence ℕ → T} {seen : Finset O} {r : O}
    {C : Configuration T O}
    (valid : (revisionFiring label space outcome φ row seen r).Valid A label C) :
    seen = ledger label space C ∧
      label r =
        row ((ledgerOverlapModel (recorded label outcome)).extract (ledger label space C) φ) := by
  obtain ⟨seenEq, -, rowEq, -⟩ :=
    (revisionFiring_valid_iff A label space outcome φ row seen r C).mp valid
  subst seenEq
  exact ⟨rfl, rowEq⟩

/-- **Revision of two ledgers**: when the ledger is their union, the row is the overlap revision of
the world model. -/
theorem revision_adequate_union {φ : W → Bool} {row : Evidence ℕ → T} {seen : Finset O}
    {r : O} {C : Configuration T O}
    (valid : (revisionFiring label space outcome φ row seen r).Valid A label C)
    {first second : Finset O} (split : ledger label space C = first ∪ second) :
    label r = row (ledgerEvidence (recorded label outcome) φ first +
      ledgerEvidence (recorded label outcome) φ second -
        ledgerEvidence (recorded label outcome) φ (first ∩ second)) := by
  rw [(revision_adequate A label space outcome valid).2, split]
  exact congrArg row ((ledgerOverlapModel (recorded label outcome)).extract_revise first second φ)

/-- **Results are not observations**: a revision firing whose row lies outside the evidence space
leaves the ledger as it was. -/
theorem revision_keeps_ledger (φ : W → Bool) (row : Evidence ℕ → T) (seen : Finset O) (r : O)
    (C : Configuration T O)
    (outside : space (row (ledgerEvidence (recorded label outcome) φ seen)) = false)
    (rowEq : label r = row (ledgerEvidence (recorded label outcome) φ seen)) :
    ledger label space ((revisionFiring (S := S) label space outcome φ row seen r).result label C) =
      ledger label space C := by
  rw [ledger_result]
  have noTake :
      (revisionFiring (S := S) label space outcome φ row seen r).selection.taken.toFinset = ∅ :=
    rfl
  have noObservation :
      madeObservations label space (revisionFiring (S := S) label space outcome φ row seen r) =
        ∅ := by
    ext o
    simp only [madeObservations, revisionFiring, Finset.mem_filter, List.mem_toFinset,
      List.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro rfl
    rw [rowEq, outside]
    simp
  rw [noTake, noObservation, Finset.sdiff_empty, Finset.union_empty]

end Revision

/-! ## Deduction -/

section Deduction

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction (complementConditionalFromMarginal)

variable (label : O → T) (outcome : T → W)

/-- The bag of worlds that a set of observations records. -/
def bagOf (seen : Finset O) : Multiset W := seen.val.map (recorded label outcome)

variable (a b c : W → Bool)

/-- **Screening off in the counts**, with the denominators of the formula nonzero. -/
def Screened (bag : Multiset W) : Prop :=
  count bag (fun w => a w && b w && c w) * count bag b =
      count bag (fun w => a w && b w) * count bag (fun w => b w && c w) ∧
    count bag (fun w => a w && !b w && c w) * count bag (fun w => !b w) =
      count bag (fun w => a w && !b w) * count bag (fun w => !b w && c w) ∧
    count bag a ≠ 0 ∧ count bag b ≠ 0 ∧ count bag (fun w => !b w) ≠ 0

instance (bag : Multiset W) : Decidable (Screened a b c bag) := by
  unfold Screened
  infer_instance

/-- **The PLN deduction formula** on the strengths read from a bag. -/
noncomputable def deductionValue (bag : Multiset W) : ℝ :=
  (count bag (fun w => a w && b w) / count bag a : ℝ) *
      (count bag (fun w => b w && c w) / count bag b) +
    (1 - (count bag (fun w => a w && b w) / count bag a : ℝ)) *
      complementConditionalFromMarginal (count bag b / Multiset.card bag)
        (count bag c / Multiset.card bag) (count bag (fun w => b w && c w) / count bag b)

/-- **The world-model answer to the conclusion**: the frequency of `c` among the `a`-worlds. -/
noncomputable def linkValue (bag : Multiset W) : ℝ :=
  (count bag (fun w => a w && c w) : ℝ) / count bag a

/-- **Under screening off the formula is the world-model answer.** -/
theorem deductionValue_eq_linkValue {bag : Multiset W} (screened : Screened a b c bag) :
    deductionValue a b c bag = linkValue a c bag :=
  (deduction_exact_of_screening bag a b c screened.1 screened.2.1 screened.2.2.1 screened.2.2.2.1
    screened.2.2.2.2).symm

end Deduction

section DeductionFirings

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool) (outcome : T → W)

/-- **Guard verdicts**: two terms that no substitution identifies. -/
structure GuardBits where
  yes : T
  no : T
  apart : ∀ σ : S, ¬ A.E (A.apply σ no) (A.apply σ yes)

/-- The guard that a decided verdict is yes. -/
def GuardBits.check {A : SubstitutionAction T S} (bits : GuardBits A) (verdict : Bool) : Check T :=
  .equal (if verdict then bits.yes else bits.no) bits.yes

omit [DecidableEq O] in
theorem GuardBits.holds_iff {A : SubstitutionAction T S} (bits : GuardBits A) (σ : S)
    (store : Finset O) (verdict : Bool) :
    (bits.check verdict).Holds A σ label store ↔ verdict = true := by
  cases verdict
  · simp only [GuardBits.check, Check.Holds, SubstitutionAction.Solves, Bool.false_eq_true,
      if_false, iff_false]
    exact bits.apart σ
  · simp only [GuardBits.check, Check.Holds, SubstitutionAction.Solves, if_true, iff_true]
    exact A.equivalence.refl _

variable (a b c : W → Bool)

/-- **The deduction firing** whose predicate query of the evidence space saw `seen`: the screening
guard, and the row of the deduction formula made at `r`. -/
noncomputable def deductionFiring (bits : GuardBits A) (row : ℝ → T) (seen : Finset O) (r : O) :
    Firing T S O :=
  ⟨⟨[], [], [], [bits.check (decide (Screened a b c (bagOf label outcome seen)))],
      [row (deductionValue a b c (bagOf label outcome seen))]⟩,
    [PredicateQueryAdmission.Query.fixed (ledgerQuery space seen)], ⟨[], [], [r]⟩⟩

/-- **Adequacy of deduction**: an admitted deduction firing saw the ledger, the ledger screens off,
and its row is the world-model answer to the conclusion. -/
theorem deduction_adequate {bits : GuardBits A} {row : ℝ → T} {seen : Finset O} {r : O}
    {C : Configuration T O}
    (valid : (deductionFiring A label space outcome a b c bits row seen r).Valid A label C) :
    seen = ledger label space C ∧ Screened a b c (bagOf label outcome (ledger label space C)) ∧
      label r = row (linkValue a c (bagOf label outcome (ledger label space C))) := by
  have unfolded : PredicateQueryAdmission.Valid A label _
      ([ledgerQuery space seen].map PredicateQueryAdmission.Query.fixed) C _ := valid
  rw [PredicateQueryAdmission.valid_fixed_iff] at unfolded
  obtain ⟨firing, holds⟩ := unfolded
  have seenEq : ledger label space C = seen := holds _ (List.mem_singleton_self _)
  subst seenEq
  obtain ⟨σ, solved⟩ := firing.consistent
  have guard := (GuardBits.holds_iff label bits σ C.present _).mp
    (firing.checks _ (List.mem_singleton_self _) σ solved)
  have screened : Screened a b c (bagOf label outcome (ledger label space C)) :=
    of_decide_eq_true guard
  have rowEq :
      label r = row (deductionValue a b c (bagOf label outcome (ledger label space C))) := by
    simpa [deductionFiring] using firing.outputs
  exact ⟨rfl, screened, rowEq.trans (congrArg row (deductionValue_eq_linkValue a b c screened))⟩

/-- **Without screening off the deduction firing is refused.** -/
theorem deduction_refused {bits : GuardBits A} {row : ℝ → T} {r : O} {C : Configuration T O}
    (notScreened : ¬ Screened a b c (bagOf label outcome (ledger label space C))) :
    ¬ (deductionFiring A label space outcome a b c bits row (ledger label space C) r).Valid
      A label C :=
  fun valid => notScreened (deduction_adequate A label space outcome a b c valid).2.1

end DeductionFirings

/-! ## Incompleteness is not "no evidence" -/

section Incompleteness

variable (label : O → T) (space : T → Bool) (outcome : T → W)

/-- What a scan with budget `budget` finds: the observations among the first `budget` entries. -/
def scanFound (contents : List O) (budget : ℕ) : Finset O :=
  (contents.take budget).toFinset.filter fun o => space (label o) = true

omit [DecidableEq O] in
/-- Whether the scan finished. -/
def scanStatus (contents : List O) (budget : ℕ) : Status :=
  if contents.length ≤ budget then .complete else .incomplete

omit [DecidableEq O] in
/-- The scan list holds exactly the present occurrences of the cut. -/
def Covers (contents : List O) (C : Configuration T O) : Prop := ∀ o, o ∈ contents ↔ o ∈ C.present

theorem scanFound_subset {contents : List O} {C : Configuration T O} (covers : Covers contents C)
    (budget : ℕ) : scanFound label space contents budget ⊆ ledger label space C := by
  intro o found
  simp only [scanFound, Finset.mem_filter, List.mem_toFinset] at found
  exact (mem_ledger label space).mpr ⟨(covers o).mp (List.mem_of_mem_take found.1), found.2⟩

theorem scanFound_eq_of_complete {contents : List O} {C : Configuration T O}
    (covers : Covers contents C) {budget : ℕ}
    (complete : scanStatus contents budget = .complete) :
    scanFound label space contents budget = ledger label space C := by
  have within : contents.length ≤ budget := by
    by_contra tooLong
    simp [scanStatus, tooLong] at complete
  ext o
  simp only [scanFound, List.take_of_length_le within, Finset.mem_filter, List.mem_toFinset,
    mem_ledger, covers o]

/-- **A count is a whole-table attempt**: it counts when the scan finished, and otherwise reports
what it found as a lower bound. -/
inductive CountOutcome where
  | counted (evidence : Evidence ℕ)
  | incomplete (lower : Evidence ℕ)

/-- The budgeted count of `φ`. -/
def budgetedCount (φ : W → Bool) (contents : List O) (budget : ℕ) : CountOutcome :=
  match scanStatus contents budget with
  | .complete =>
      .counted (ledgerEvidence (recorded label outcome) φ (scanFound label space contents budget))
  | .incomplete =>
      .incomplete
        (ledgerEvidence (recorded label outcome) φ (scanFound label space contents budget))

/-- **A finished count is the readout at the cut.** -/
theorem complete_counts (φ : W → Bool) {contents : List O} {C : Configuration T O}
    (covers : Covers contents C) {budget : ℕ} (complete : scanStatus contents budget = .complete) :
    budgetedCount label space outcome φ contents budget =
      .counted (readout label space outcome φ C) := by
  unfold budgetedCount
  rw [complete, scanFound_eq_of_complete label space covers complete]
  rfl

/-- **An unfinished count is only a lower bound.** -/
theorem incomplete_lower_bound (φ : W → Bool) {contents : List O} {C : Configuration T O}
    (covers : Covers contents C) {budget : ℕ} {lower : Evidence ℕ}
    (reported : budgetedCount label space outcome φ contents budget = .incomplete lower) :
    lower ≤ readout label space outcome φ C := by
  unfold budgetedCount at reported
  cases status : scanStatus contents budget with
  | complete => rw [status] at reported; cases reported
  | incomplete =>
      rw [status] at reported
      cases reported
      exact ledgerEvidence_mono _ φ (scanFound_subset label space covers budget)

/-- **No evidence**: a finished count of nothing. -/
def NoEvidence (counted : CountOutcome) : Prop := counted = .counted 0

/-- **No evidence exactly when the scan finished on an empty ledger.** -/
theorem noEvidence_iff (φ : W → Bool) {contents : List O} {C : Configuration T O}
    (covers : Covers contents C) (budget : ℕ) :
    NoEvidence (budgetedCount label space outcome φ contents budget) ↔
      scanStatus contents budget = .complete ∧ ledger label space C = ∅ := by
  unfold NoEvidence
  cases status : scanStatus contents budget with
  | complete =>
      rw [complete_counts label space outcome φ covers status]
      simp only [CountOutcome.counted.injEq, true_and]
      exact ledgerEvidence_eq_zero_iff _ φ _
  | incomplete =>
      unfold budgetedCount
      rw [status]
      simp

/-- **An exhausted scan never reports no evidence.** -/
theorem incomplete_never_noEvidence (φ : W → Bool) {contents : List O} {budget : ℕ}
    (incomplete : scanStatus contents budget = .incomplete) :
    ¬ NoEvidence (budgetedCount label space outcome φ contents budget) := by
  unfold NoEvidence budgetedCount
  rw [incomplete]
  simp

/-- **The verdict of "is there evidence?" is R27's rule**: `none` needs a finished scan that found
nothing. -/
theorem verdict_none_iff {contents : List O} {C : Configuration T O} (covers : Covers contents C)
    (budget : ℕ) :
    Verdict.rule (scanStatus contents budget)
        (decide (scanFound label space contents budget).Nonempty) = .none ↔
      scanStatus contents budget = .complete ∧ ledger label space C = ∅ := by
  rw [Verdict.rule_none_iff, decide_eq_false_iff_not, Finset.not_nonempty_iff_eq_empty]
  constructor
  · rintro ⟨complete, empty⟩
    exact ⟨complete, (scanFound_eq_of_complete label space covers complete).symm.trans empty⟩
  · rintro ⟨complete, empty⟩
    exact ⟨complete, (scanFound_eq_of_complete label space covers complete).trans empty⟩

omit [DecidableEq O] in
/-- The attempt outcome of a count: it fires when the scan finished, and is incomplete otherwise. -/
def countOutcome (contents : List O) (budget : ℕ) : ContextualAttemptOutcomes.Outcome :=
  match scanStatus contents budget with
  | .complete => .fired
  | .incomplete => .incomplete

omit [DecidableEq O] in
/-- **A count never reports `none`**: like every whole-table attempt, it fires, possibly
vacuously, or is incomplete. -/
theorem countOutcome_ne_none (contents : List O) (budget : ℕ) :
    countOutcome contents budget ≠ .none := by
  unfold countOutcome
  cases scanStatus contents budget <;> simp

variable (A : SubstitutionAction T S)

/-- **A finished scan fires the revision rule on what it found.** -/
theorem complete_scan_fires (φ : W → Bool) (row : Evidence ℕ → T) {contents : List O}
    {C : Configuration T O} (covers : Covers contents C) {budget : ℕ}
    (complete : scanStatus contents budget = .complete) {r : O} (fresh : r ∉ C.present)
    (rowEq : label r = row (readout label space outcome φ C))
    (consistent : A.Consistent C.equations) :
    (revisionFiring label space outcome φ row (scanFound label space contents budget) r).Valid
      A label C := by
  rw [revisionFiring_valid_iff, scanFound_eq_of_complete label space covers complete]
  exact ⟨rfl, fresh, rowEq, consistent⟩

end Incompleteness

end WorldModelRuns

open WorldModelRuns

#print axioms revisionFiring_valid_iff
#print axioms revisionFiring_refused
#print axioms revision_adequate
#print axioms revision_adequate_union
#print axioms revision_keeps_ledger
#print axioms deductionValue_eq_linkValue
#print axioms GuardBits.holds_iff
#print axioms deduction_adequate
#print axioms deduction_refused
#print axioms scanFound_subset
#print axioms scanFound_eq_of_complete
#print axioms complete_counts
#print axioms incomplete_lower_bound
#print axioms noEvidence_iff
#print axioms incomplete_never_noEvidence
#print axioms verdict_none_iff
#print axioms countOutcome_ne_none
#print axioms complete_scan_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
