import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowAssemblyControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission

/-!
# Conditional rows participate in exact entry-world guard regression

A retained schema has a private variable constrained to the caller's shared
reference. At caller 9 it cannot match box(7). One matching input is removed
and a matching output is created. Count stays one; dropping the retained
schema's condition invents a second match and breaks the required frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegressionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards
open ContextualPrefixPublicationControls (base captures none symbol box)
open ContextualRowAssemblyControls.CapturedCondition (declarations row caller forgettingConditions
  the_capture_rejects_an_unrelated_seven dropping_the_condition_invents_an_answer)

abbrev locals := declarations false
def images : Assignment captures none := caller 9
def pattern : Term (signature base captures) [] () := box (symbol 7)
def shared (n : Nat) : Row locals captures [] () := ofStored locals captures (.shared (box (symbol n)))
def entryRows (occurrence : Nat) : Row locals captures [] () := if occurrence = 0 then shared 7 else row
def exitRows (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 2 then shared 7 else if occurrence = 0 then shared 0 else row
def world : Finset Nat := {0, 1}
def removed : Finset Nat := {0}
def created : Finset Nat := {2}

theorem shared_match : Matches locals captures images (box (symbol 7)) (shared 7) := by
  rw [shared, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
  rfl

theorem the_retained_condition_excludes_an_extra_match : ¬ Matches locals captures images (box (symbol 7)) row :=
  the_capture_rejects_an_unrelated_seven

theorem entry_region : region locals images entryRows world pattern = {0} := by
  ext occurrence
  rw [mem_region]
  change (occurrence ∈ world ∧ Matches locals captures images (box (symbol 7)) (entryRows occurrence)) ↔ occurrence ∈ {0}
  by_cases zero : occurrence = 0
  · subst occurrence
    simp [entryRows, world, shared_match]
  · simp [entryRows, zero, the_retained_condition_excludes_an_extra_match]

theorem removed_region : region locals images entryRows removed pattern = {0} := by
  ext occurrence
  rw [mem_region]
  change (occurrence ∈ removed ∧ Matches locals captures images (box (symbol 7)) (entryRows occurrence)) ↔ occurrence ∈ {0}
  by_cases zero : occurrence = 0
  · subst occurrence
    simp [entryRows, removed, shared_match]
  · simp [removed, zero]

theorem created_region : region locals images exitRows created pattern = {2} := by
  ext occurrence
  rw [mem_region]
  change (occurrence ∈ created ∧ Matches locals captures images (box (symbol 7)) (exitRows occurrence)) ↔ occurrence ∈ {2}
  by_cases two : occurrence = 2
  · subst occurrence
    simp [exitRows, created, shared_match]
  · simp [created, two]

theorem retained_frame : ∀ candidatePattern occurrence, occurrence ∈ world → occurrence ∉ removed →
    (Matches locals captures images (instantiate images candidatePattern) (entryRows occurrence) ↔
      Matches locals captures images (instantiate images candidatePattern) (exitRows occurrence)) := by
  intro candidatePattern occurrence member outside
  have one : occurrence = 1 := by
    simp only [world, Finset.mem_insert, Finset.mem_singleton] at member
    simp only [removed, Finset.mem_singleton] at outside
    omega
  subst occurrence
  rfl

theorem actual_count_is_one : Holds locals images exitRows ((world \ removed) ∪ created) (.count pattern 1) := by
  change (region locals images exitRows ((world \ removed) ∪ created) pattern).card = 1
  rw [ContextualGuardRegression.count_after_retained locals locals images entryRows exitRows world removed created pattern
    (by decide +kernel) (by decide +kernel) (retained_frame pattern), entry_region, removed_region, created_region]
  decide +kernel

theorem entry_formula_has_the_same_count :
    ContextualGuardRegression.entryCondition locals locals images entryRows exitRows world removed created (.count pattern 1) :=
  (ContextualGuardRegression.holds_after_iff locals locals images entryRows exitRows world removed created (.count pattern 1)
    (by decide +kernel) (by decide +kernel) retained_frame).mp actual_count_is_one

theorem forgetting_the_removal_gives_the_wrong_count :
    (region locals images entryRows world pattern).card + (region locals images exitRows created pattern).card ≠ 1 := by
  rw [entry_region, created_region]
  decide +kernel

theorem removing_the_only_match_establishes_absence :
    Holds locals images exitRows (world \ removed) (.absent pattern) := by
  intro occurrence member
  have one : occurrence = 1 := by
    simp only [world, removed, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at member
    omega
  subst occurrence
  exact the_retained_condition_excludes_an_extra_match

theorem making_a_matching_row_refutes_absence :
    ¬ Holds locals images exitRows ((world \ removed) ∪ created) (.absent pattern) := by
  intro absent
  exact absent 2 (by decide +kernel) shared_match

def incorrectRows (occurrence : Nat) : Row locals captures [] () :=
  if occurrence = 1 then forgettingConditions else exitRows occurrence

theorem dropping_a_condition_breaks_the_retained_frame :
    ¬ (Matches locals captures images (instantiate images pattern) (entryRows 1) ↔
      Matches locals captures images (instantiate images pattern) (incorrectRows 1)) := by
  intro same
  exact the_retained_condition_excludes_an_extra_match (same.mpr dropping_the_condition_invents_an_answer)

namespace EarlierQuery

open ContextualSourceSchedules ContextualConjunctiveQueries
open ContextualPrefixPublicationControls (initial actor callerX firstSelection firstModel)
open ContextualScheduleControls.EarlierSchema (guardedPlan)

def earlier : Schedule base Nat [] () initial initial := .nil initial
def guard : Check (Term (signature base actor) [] ()) := .equal callerX (symbol 1)

theorem the_original_query_keeps_its_countermodel :
    ¬ ContextualPredicateQueryAdmission.Ask
      (ContextualClauseSourceState.information none none initial guardedPlan firstSelection)
      (ContextualPredicateQueryAdmission.ofOriginalGuardPoint earlier none guard (0 : Nat)) {0} := by
  intro observed
  have verdict := (ContextualPredicateQueryAdmission.ask_condition_iff
    (fun candidate => earlier.ownEntryCondition none guard candidate.declarations candidate.assignment)
    (0 : Nat) {0} (by decide +kernel) _).mp observed Empty none (firstModel none 2)
      (by intro equation member; cases member)
  change symbol (decl := none) 2 = symbol 1 at verdict
  have impossible : (2 : Nat) = 1 := ContextualPrefixPublicationControls.DataOperator.symbol.inj
    (Sum.inl.inj (Term.op.inj verdict).1)
  omega

end EarlierQuery

namespace ComputedQuery

open ContextualSourceSchedules

abbrev sourceSignature := ContextualClausePublication.BinderControls.base
abbrev sourceWorld := ContextualComputedJoinControls.world
abbrev sourceAfter := ContextualClauseSequencingControls.afterFirst

local instance : DecidableEq sourceSignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : sourceSignature.Srt) : DecidableEq (sourceSignature.Op sort) := by
  change DecidableEq (ContextualClausePublication.BinderControls.DataOperator ⊕
    Operator (SchematicReach.spaceDeclaration ContextualClausePublication.BinderControls.dataSignature () (Name := Nat)) sort)
  infer_instance
local instance : DecidableEq sourceWorld.Names := sourceWorld.equality

def earlier : Schedule sourceSignature Nat [] () sourceWorld sourceAfter :=
  .snoc (.nil sourceWorld) ContextualClausePublication.BinderControls.queries
    ContextualComputedJoinControls.plan ContextualComputedJoinControls.picked

/-- The stored-code computation's current port equations and returned-answer guard reach predicate queries. -/
theorem the_computed_clause_has_its_original_guard_queries :
    ∀ check ∈ ContextualClauseSequencingControls.nextPlan.rule.checks,
      ContextualPredicateQueryAdmission.Ask
        (ContextualClauseSourceState.information ContextualClausePublication.BinderControls.captures
          ContextualClauseSequencingControls.rowLocals sourceAfter ContextualClauseSequencingControls.nextPlan
          ContextualClauseSequencingControls.selection)
        (ContextualPredicateQueryAdmission.ofOriginalGuardPoint earlier ContextualClausePublication.BinderControls.captures check (99 : Nat))
        {99} := by
  have admittedPrefix : earlier.Admitted := ContextualScheduleControls.ComputedBody.admitted.1
  have obligations := earlier.admitted_characterization.mp admittedPrefix
  have original : (originalCut sourceAfter ContextualClausePublication.BinderControls.captures
      ContextualClauseSequencingControls.nextPlan ContextualClauseSequencingControls.selection).Holds := by
    simpa only [Cut.Holds, originalCut, List.forall_mem_map, ContextualClauseSourceState.information] using
      ContextualScheduleControls.ComputedBody.admitted.2.checks
  exact (ContextualPredicateQueryAdmission.original_guards_as_point_queries earlier obligations.1 obligations.2.1
    ContextualClausePublication.BinderControls.captures ContextualClauseSequencingControls.nextPlan
    ContextualClauseSequencingControls.selection (99 : Nat) {99} (by decide +kernel)).mp original

end ComputedQuery

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegressionControls
