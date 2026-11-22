import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowAssemblyControls

/-!
# Principal count queries preserve shared conditions and physical multiplicity

Two equal conditional schemas occupy distinct occurrences and both match
their explicit shared capture. An actual native firing publishes a new
value while its complete query records both occurrences. An open caller
counterexample shows that an empty principal table alone is not absence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards ContextualGuardMatching
open ContextualPrincipalCountQueries ContextualPredicateQueryAdmission
open ContextualPrefixPublicationControls (DataOperator base captures none symbol box)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

namespace ConditionalDuplicates

open ContextualRowAssemblyControls.CapturedCondition (declarations row privateValue capturedValue)

abbrev locals := declarations false

theorem matches_its_shared_capture {Next : Type} (next : Next → MetaArity base) (candidate : Assignment captures next) :
    Matches locals captures candidate (box (candidate ())) row := by
  refine ⟨Extension.identity next, (fun _ => candidate ()), ?_, ?_⟩
  · apply (ContextualResidual.models_observed_iff _ privateValue capturedValue).mpr
    erw [privateValue, instantiate_generator, capturedValue, instantiate_generator]
    change candidate () = instantiate (generator next) (candidate ())
    rw [instantiate_identity]
  · change box (instantiate _ privateValue) = instantiate (Extension.identity next).assignment (box (candidate ()))
    erw [privateValue, instantiate_generator]
    change box (candidate ()) = instantiate (generator next) (box (candidate ()))
    rw [instantiate_identity]

abbrev before : ContextualConditionalExecution.State locals Nat [] () :=
  ⟨Unit, inferInstance, captures, ∅, [], {0, 1}, fun _ => row⟩
abbrev nativeFamily := ContextualActivatedStep.target locals captures
def pattern : Term (signature base nativeFamily) [] () :=
  box ((ContextualSelectionViews.capturedTarget locals captures) ())
def code : RuleInstance (Term (signature base (ContextualActivatedStep.source locals captures)) [] ()) :=
  ⟨[], [], [], [], [symbol 7]⟩
def selected : Selection Nat := ⟨[], [], [2]⟩
def outputs (_ : Nat) : Term (signature base nativeFamily) [] () := symbol 7

theorem admitted : ContextualConditionalExecution.Admitted locals before code selected outputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨_, nativeFamily, generator nativeFamily, ?_⟩
    intro equation member
    cases member
  · intro check member
    cases member

def zero : ContextualConditionalExecution.Firing locals before :=
  ⟨code, selected, outputs, (fun _ => false), admitted, 0,
    ContextualFrameWorklist.identity
      (ContextualConditionalExecution.information locals captures ∅ selected code before.rows []), rfl⟩

theorem finished : zero.update.remaining = [] := rfl

theorem both_conditional_rows_match (candidate : Candidate nativeFamily) (occurrence : Nat) :
    Matches locals nativeFamily candidate.assignment (instantiate candidate.assignment pattern)
      (ContextualConditionalExecution.guardRows locals captures before.rows occurrence) := by
  change Matches locals nativeFamily candidate.assignment _
    (row.map locals captures (ContextualSelectionViews.capturedTarget locals captures))
  rw [matches_map_iff]
  with_unfolding_all exact (matches_its_shared_capture candidate.declarations
    (Assignment.compose candidate.assignment (ContextualSelectionViews.capturedTarget locals captures)))

theorem principal_table_has_both_occurrences :
    table locals zero.update (ContextualConditionalExecution.guardRows locals captures before.rows) before.present pattern = {0, 1} := by
  ext occurrence
  rw [table, mem_region]
  change (occurrence ∈ before.present ∧ _) ↔ occurrence ∈ before.present
  exact ⟨And.left, fun present => ⟨present, both_conditional_rows_match
    ⟨zero.update.Variables, zero.update.declaration, zero.update.answer⟩ occurrence⟩⟩

theorem source_count_is_two : ContextualConditionalGuards.Ask locals
    (ContextualConditionalExecution.information locals captures ∅ selected code before.rows [])
    (ContextualConditionalExecution.guardRows locals captures before.rows) before.present (.count pattern 2) := by
  intro Future future candidate _model
  have regionEq : region locals candidate (ContextualConditionalExecution.guardRows locals captures before.rows)
      before.present pattern = before.present := by
    ext occurrence
    rw [mem_region]
    exact ⟨And.left, fun present => ⟨present, both_conditional_rows_match ⟨Future, future, candidate⟩ occurrence⟩⟩
  change (region locals candidate _ _ _).card = 2
  rw [regionEq]
  decide +kernel

/-- Real solver return, complete data query, duplicate physical rows and an actual publication. -/
theorem actual_count_query_publishes_the_new_value :
    ∃ observed : WithQueries locals before,
      observed.firing = zero ∧ observed.firing.target.present = {0, 1, 2} ∧
        observed.queries = [matchingQuery locals pattern {0, 1}] ∧
        ∀ (Future : Type) (future : Future → MetaArity base)
          (candidate : Assignment observed.firing.target.declarations future) (value : Term (signature base future) [] ()),
          Matches (ContextualPublication.privateFamily locals observed.firing.update.declaration)
            observed.firing.target.declarations candidate value (observed.firing.target.rows 2) ↔ value = symbol 7 := by
  have compiled := (native_count_admission_iff locals zero finished pattern 2).mp source_count_is_two
  obtain ⟨observed, same, queries⟩ := compiled.2
  refine ⟨observed, same, ?_, ?_, ?_⟩
  · rw [same, zero.physical_result]
    decide +kernel
  · rw [principal_table_has_both_occurrences] at queries
    exact queries
  · rw [same]
    intro Future future candidate value
    rw [zero.shared_row 2 (by decide +kernel) rfl]
    change Matches _ _ candidate value (ofStored _ _ (.shared (symbol 7))) ↔ _
    rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl

end ConditionalDuplicates

namespace OpenCaller

def pattern : Term (signature base captures) [] () := generator captures ()
def rows (_ : Nat) : Row none captures [] () := ofStored none captures (.shared (symbol 1))
def update : ContextualFrameUpdate.Update ([] : ContextualResidual.Problem captures) := ContextualFrameWorklist.identity []
theorem finished : update.remaining = [] := rfl

theorem principal_table_is_empty : table none update rows {0} pattern = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro occurrence member
  obtain ⟨_present, matched⟩ := (mem_region _ _ _ _ _ _).mp member
  change Matches none captures (generator captures) _ (ofStored none captures (.shared (symbol 1))) at matched
  erw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
  dsimp only [update, pattern] at matched
  simp only [instantiate_identity] at matched
  change generator captures () = symbol 1 at matched
  cases (Term.op.inj matched).1

theorem completed_unification_does_not_complete_the_count_query :
    ¬ AskData ([] : ContextualResidual.Problem captures)
      (matchingQuery none pattern (table none update rows {0} pattern)) (fun occurrence => (occurrence, rows occurrence)) {0} := by
  intro queried
  let candidate : Assignment captures none := fun _ => symbol 1
  have observed := queried Empty none candidate (by intro equation member; cases member)
  have equal := (matching_holds_iff none pattern _ rows {0} ⟨Empty, none, candidate⟩).mp observed
  rw [principal_table_is_empty] at equal
  have member : 0 ∈ region none candidate rows {0} pattern := by
    apply (mem_region _ _ _ _ _ _).mpr
    refine ⟨Finset.mem_singleton_self _, ?_⟩
    dsimp only [rows]
    rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl
  rw [equal] at member
  exact Finset.notMem_empty 0 member

end OpenCaller

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountControls
