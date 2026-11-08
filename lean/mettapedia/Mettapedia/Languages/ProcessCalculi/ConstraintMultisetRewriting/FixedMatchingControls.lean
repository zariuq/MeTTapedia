import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Fixed receipts retain shared reads, exact counts and explicit tells

The positive receipt is constructed directly in the matching engine. Its
two reads share one physical occurrence, while the count observes two equal
values at distinct occurrences. The reverse bridge preserves those choices.

Two negative controls delimit the bridge: a currently successful literal
absence test over a shared variable is not a certain ask, and a matching
receipt cannot make an inconsistent tell store admissible.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

abbrev signature := ConstraintMultisetRewriting.Controls.signature
abbrev A := FirstOrder.action signature

def label (occurrence : Nat) : Term signature :=
  if occurrence = 0 then .const 0
  else if occurrence = 1 ∨ occurrence = 4 then .const 2
  else if occurrence = 2 then .const 1
  else .const 3

def before : Configuration (Term signature) Nat := ⟨[], {0, 1, 4}⟩
def rule : RuleInstance (Term signature) :=
  ⟨[.const 0], [.const 2, .const 2], [(.const 9, .const 9)],
    [.count (.const 2) 2, .absent (.const 8)], [.const 1]⟩

def receipt : GuardedMultisetRewriting.FiringReceipt Nat Empty (Term signature) :=
  ⟨ResolvedMatching.assignment, [0], [1, 1], [2], [{1, 4}, ∅]⟩

theorem matching_receipt_is_independently_valid :
    receipt.ValidAt (ResolvedMatching.literalLayer A)
      (ResolvedMatching.resolvedRule A A.identity rule) label before.present := by
  classical
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_, rfl, ?_⟩
  · intro name
    cases name
  · exact .cons ⟨.const 0, rfl, rfl⟩ .nil
  · exact .cons ⟨.const 2, rfl, rfl⟩ (.cons ⟨.const 2, rfl, rfl⟩ .nil)
  · refine .cons ⟨?_, ?_⟩ (.cons ⟨?_, rfl⟩ .nil)
    · change regionOf label before.present (semRegion (ResolvedMatching.literalLayer A)
        ResolvedMatching.assignment (.const 2)) = {1, 4}
      rw [literal_region]
      simp only [Check.matches, A.apply_identity]
      change ({0, 1, 4} : Finset Nat).filter
        (fun occurrence => Term.const (σ := signature) 2 = label occurrence) = {1, 4}
      ext occurrence
      constructor
      · intro member
        obtain ⟨present, equal⟩ := Finset.mem_filter.mp member
        have cases : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 4 := by simpa using present
        rcases cases with rfl | rfl | rfl
        · simp [label] at equal
        · simp
        · simp
      · intro member
        have cases : occurrence = 1 ∨ occurrence = 4 := by simpa using member
        rcases cases with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨by decide, rfl⟩
    · change Multiset.card (labels label {1, 4}) = 2
      simp [labels]
    · change regionOf label before.present (semRegion (ResolvedMatching.literalLayer A)
        ResolvedMatching.assignment (.const 8)) = ∅
      rw [literal_region]
      simp only [Check.matches, A.apply_identity]
      change ({0, 1, 4} : Finset Nat).filter
        (fun occurrence => Term.const (σ := signature) 8 = label occurrence) = ∅
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro occurrence member
      obtain ⟨present, equal⟩ := Finset.mem_filter.mp member
      have cases : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 4 := by simpa using present
      rcases cases with rfl | rfl | rfl <;> simp [label] at equal

theorem fixed_observation : Observation A label before.present rule := by
  constructor
  · intro term member
    simp [rule] at member
    rcases member with rfl | rfl <;> intro assignment <;> rfl
  · intro term member
    have same : term = .const 1 := by simpa [rule] using member
    subst term
    intro assignment
    rfl
  · intro check member term inTerms
    simp [rule] at member
    rcases member with rfl | rfl
    · have same : term = .const 2 := by simpa [Check.terms] using inTerms
      subst term
      intro assignment
      rfl
    · have same : term = .const 8 := by simpa [Check.terms] using inTerms
      subst term
      intro assignment
      rfl
  · intro occurrence _ assignment
    unfold label
    split_ifs <;> rfl

theorem the_explicit_tell_is_compatible : A.Models A.identity (before.equations ++ rule.tell) := by
  simp [before, rule, SubstitutionAction.Models, SubstitutionAction.Solves,
    A, FirstOrder.action, Subst.id, Subst.applyTerm]

theorem the_same_receipt_is_an_actual_constraint_step :
    Step A label rule before ((selection receipt).result label rule before) :=
  step_of_receipt A label receipt matching_receipt_is_independently_valid fixed_observation
    the_explicit_tell_is_compatible

theorem the_read_selection_still_reuses_occurrence_one : (selection receipt).read = [1, 1] := rfl

theorem the_two_equal_valued_occurrences_stay_distinct :
    ((selection receipt).result label rule before).present = {1, 2, 4} := by
  decide +kernel

theorem the_tell_is_not_lost_during_embedding :
    (Term.const (σ := signature) 9, Term.const (σ := signature) 9) ∈
      ((selection receipt).result label rule before).equations := by
  simp [Selection.result, Selection.problem, selection, receipt, rule, before]

def duplicateConsumption : Selection Nat := ⟨[1, 1], [], [2]⟩

theorem duplicate_consumption_is_still_refused : ¬duplicateConsumption.Valid A label rule before := by
  intro valid
  have duplicate := valid.take_distinct
  simp [duplicateConsumption] at duplicate

def openRule : RuleInstance (Term signature) := ⟨[], [], [], [.absent (.const 0)], []⟩
def openBefore : Configuration (Term signature) Nat := ⟨[], {1}⟩
def openReceipt : GuardedMultisetRewriting.FiringReceipt Nat Empty (Term signature) :=
  ⟨ResolvedMatching.assignment, [], [], [], [∅]⟩

theorem a_literal_open_absence_receipt_can_be_valid :
    openReceipt.ValidAt (ResolvedMatching.literalLayer A)
      (ResolvedMatching.resolvedRule A A.identity openRule)
      ConstraintMultisetRewriting.Controls.label openBefore.present := by
  classical
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, .nil, .nil, rfl, .cons ⟨?_, rfl⟩ .nil⟩
  · intro name
    cases name
  · change regionOf ConstraintMultisetRewriting.Controls.label openBefore.present
      (semRegion (ResolvedMatching.literalLayer A) ResolvedMatching.assignment (.const 0)) = ∅
    rw [literal_region]
    simp only [Check.matches, A.apply_identity]
    change ({1} : Finset Nat).filter
      (fun occurrence => Term.const (σ := signature) 0 = ConstraintMultisetRewriting.Controls.label occurrence) = ∅
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro occurrence member
    obtain ⟨present, equal⟩ := Finset.mem_filter.mp member
    have same : occurrence = 1 := by simpa using present
    subst occurrence
    change (Term.const (σ := signature) 0) = .var 0 at equal
    cases equal

theorem that_open_receipt_does_not_justify_a_certain_constraint_ask :
    ¬(selection openReceipt).Valid A ConstraintMultisetRewriting.Controls.label openRule openBefore := by
  intro valid
  have absent := valid.checks (.absent (.const 0)) (by simp [openRule])
    ConstraintMultisetRewriting.Controls.zero (A.models_nil _)
  exact absent 1 (by simp [openBefore]) rfl

theorem its_live_observation_is_not_substitution_fixed :
    ¬Observation A ConstraintMultisetRewriting.Controls.label openBefore.present openRule := by
  intro fixed
  have changed := fixed.values 1 (by simp [openBefore]) ConstraintMultisetRewriting.Controls.zero
  change (Term.const (σ := signature) 0) = .var 0 at changed
  cases changed

def contradictoryRule : RuleInstance (Term signature) :=
  ⟨[], [], [(.const 0, .const 1)], [], []⟩
def emptyBefore : Configuration (Term signature) Nat := ⟨[], ∅⟩
def emptyReceipt : GuardedMultisetRewriting.FiringReceipt Nat Empty (Term signature) :=
  ⟨ResolvedMatching.assignment, [], [], [], []⟩

theorem resolving_away_a_tell_does_not_test_it :
    emptyReceipt.ValidAt (ResolvedMatching.literalLayer A)
      (ResolvedMatching.resolvedRule A A.identity contradictoryRule) label emptyBefore.present := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, .nil, .nil, rfl, .nil⟩
  intro name
  cases name

theorem the_constraint_step_refuses_the_contradictory_tell :
    ¬(selection emptyReceipt).Valid A label contradictoryRule emptyBefore := by
  intro valid
  obtain ⟨assignment, solved⟩ := valid.consistent
  have clash := solved (.const 0, .const 1) (by
    simp [Selection.problem, Selection.equations, selection, emptyReceipt, contradictoryRule, emptyBefore])
  change (Term.const (σ := signature) 0) = .const 1 at clash
  cases clash

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching.Controls
