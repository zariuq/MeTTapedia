import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ForgetfulControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows

/-!
# A physical schema row has a value at each activation port

The controls use the existing native row representation, allocator and
capture-avoiding opening. One conditional schema is read twice at occurrence
7. Its body instances differ under one common assignment, while a latent
equation at both ports retains the same captured value. A single label for
occurrence 7 cannot record both readings under that assignment. Shared rows
provide the positive fixed-label profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualSelectionViews.Controls
  (base locals captures raw active RawTerm ActiveTerm atom p a b universalRow
    selection occupied first second firstPort secondPort shared sharedValue)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def firstScope : Nat := ContextualActivationScopes.scopeAt occupied firstPort
def secondScope : Nat := ContextualActivationScopes.scopeAt occupied secondPort

def privateCondition : RawTerm := generator raw (.inl 1)
def capturedCondition : RawTerm := generator raw (.inr 0)

def schemaRow : ContextualConditionalRows.Row locals captures [] () :=
  ⟨.schema universalRow, [(observe privateCondition, observe capturedCondition)]⟩

def schemaView (scope : Nat) : ActiveTerm := schemaRow.viewAt locals captures scope

def schemaModel : Assignment active active
  | .inl name => if name.name = 0 ∧ name.scope = secondScope then b else a
  | .inr _ => a

theorem same_physical_read_identity :
    selection.read.get first = 7 ∧ selection.read.get second = 7 :=
  ContextualSelectionViews.Controls.both_read_ports_choose_the_same_physical_occurrence

theorem distinct_activation_scopes : firstScope = 9 ∧ secondScope = 10 :=
  ContextualSelectionViews.Controls.reads_reserve_scopes_nine_and_ten

theorem actual_schema_views :
    instantiate schemaModel (schemaView firstScope) = p a ∧
      instantiate schemaModel (schemaView secondScope) = p b := by
  constructor <;> with_unfolding_all rfl

theorem latent_conditions_are_not_empty : schemaRow.obligations ≠ [] := by
  intro same
  cases same

theorem latent_condition_needs_a_binding :
    ¬ ContextualResidual.Models (generator raw) schemaRow.obligations := by
  intro solved
  have same := solved (observe privateCondition, observe capturedCondition)
    (List.mem_singleton_self _)
  change instantiateObservation (generator raw) (observe privateCondition) =
    instantiateObservation (generator raw) (observe capturedCondition) at same
  rw [instantiateObservation_identity, instantiateObservation_identity] at same
  have terms := observe_injective same
  have names := congrArg (support (S := base) (source := raw)) terms
  change [Sum.inl (1 : Nat)] = [Sum.inr (0 : Nat)] at names
  cases names

theorem both_actual_latent_conditions_hold :
    ContextualResidual.Models schemaModel (schemaRow.obligationsAt locals captures firstScope) ∧
      ContextualResidual.Models schemaModel (schemaRow.obligationsAt locals captures secondScope) := by
  constructor
  · intro equation member
    have only : equation =
        (instantiateObservation (ContextualFreshening.assignment locals captures firstScope)
            (observe privateCondition),
          instantiateObservation (ContextualFreshening.assignment locals captures firstScope)
            (observe capturedCondition)) := by
      simpa only [schemaRow, ContextualConditionalRows.Row.obligationsAt,
        ContextualResidual.mapProblem, List.map_cons, List.map_nil, List.mem_singleton] using member
    subst equation
    with_unfolding_all rfl
  · intro equation member
    have only : equation =
        (instantiateObservation (ContextualFreshening.assignment locals captures secondScope)
            (observe privateCondition),
          instantiateObservation (ContextualFreshening.assignment locals captures secondScope)
            (observe capturedCondition)) := by
      simpa only [schemaRow, ContextualConditionalRows.Row.obligationsAt,
        ContextualResidual.mapProblem, List.map_cons, List.map_nil, List.mem_singleton] using member
    subst equation
    with_unfolding_all rfl

theorem actual_conditional_row_has_both_matches :
    ContextualConditionalRows.Matches locals captures
        (Assignment.compose schemaModel (ContextualSelectionViews.capturedTarget locals captures))
        (p a) schemaRow ∧
      ContextualConditionalRows.Matches locals captures
        (Assignment.compose schemaModel (ContextualSelectionViews.capturedTarget locals captures))
        (p b) schemaRow := by
  constructor
  · exact ContextualConditionalRows.matches_of_open locals captures firstScope schemaModel schemaRow
      (p a) both_actual_latent_conditions_hold.1 actual_schema_views.1
  · exact ContextualConditionalRows.matches_of_open locals captures secondScope schemaModel schemaRow
      (p b) both_actual_latent_conditions_hold.2 actual_schema_views.2

def FixedLabelTracks (label : Nat → ActiveTerm) : Prop :=
  instantiate schemaModel (label (selection.read.get first)) =
      instantiate schemaModel (schemaView firstScope) ∧
    instantiate schemaModel (label (selection.read.get second)) =
      instantiate schemaModel (schemaView secondScope)

theorem no_fixed_label_tracks_both_schema_reads (label : Nat → ActiveTerm) :
    ¬ FixedLabelTracks label := by
  rintro ⟨one, two⟩
  have common : instantiate schemaModel (schemaView firstScope) =
      instantiate schemaModel (schemaView secondScope) := one.symm.trans two
  have different : p a = p b := actual_schema_views.1.symm.trans (common.trans actual_schema_views.2)
  exact ContextualSelectionViews.Controls.distinct_ground_instances_are_unequal different

/-! ## The shared-value profile has one label at both ports -/

def sharedRow : ContextualConditionalRows.Row locals captures [] () :=
  ContextualConditionalRows.ofStored locals captures (.shared (p sharedValue))

def sharedView (scope : Nat) : ActiveTerm := sharedRow.viewAt locals captures scope

theorem shared_views_agree : sharedView firstScope = sharedView secondScope := by
  rfl

def sharedLabel (occurrence : Nat) : ActiveTerm :=
  if occurrence = 7 then sharedView firstScope else a

theorem one_fixed_label_tracks_shared_reads (candidate : Assignment active active) :
    instantiate candidate (sharedLabel (selection.read.get first)) =
        instantiate candidate (sharedView firstScope) ∧
      instantiate candidate (sharedLabel (selection.read.get second)) =
        instantiate candidate (sharedView secondScope) := by
  constructor
  · rfl
  · exact congrArg (instantiate candidate) shared_views_agree

theorem shared_row_cannot_supply_distinct_schema_instances (candidate : Assignment active active) :
    ¬ (instantiate candidate (sharedView firstScope) = p a ∧
      instantiate candidate (sharedView secondScope) = p b) := by
  rintro ⟨one, two⟩
  have common := congrArg (instantiate candidate) shared_views_agree
  exact ContextualSelectionViews.Controls.distinct_ground_instances_are_unequal
    (one.symm.trans (common.trans two))

/-! ## Two indexed events retain actual original worklist executions -/

theorem two_schema_events_have_original_returns :
    ∀ event : Fin 2, ∃ permutation : Equiv.Perm Nat, ∃ fuel update,
      ContextualTransportedActivation.FromRun locals captures fuel
        occupied (ContextualCommonEventControls.selections event)
        (ContextualCommonEventControls.rule event) ContextualCommonEventControls.rows
        ContextualCommonEventControls.before
        (ContextualCommonEventExecution.pullOutputs locals captures permutation
          ContextualCommonEventControls.outputs) update :=
  ContextualCommonEventControls.each_common_event_constructs_an_actual_original_return

theorem actual_common_model_rejects_shared_replacement :
    ContextualFrameUnifier.Models ContextualCommonEventControls.candidate
        (ContextualCommonEventControls.equations 0 ++ ContextualCommonEventControls.equations 1) ∧
      ¬ ContextualFrameUnifier.Models ContextualCommonEventControls.candidate
        (ContextualCommonEventControls.sharedEquations 0 ++
          ContextualCommonEventControls.sharedEquations 1) :=
  ⟨ContextualCommonEventControls.one_model_solves_both_events_and_keeps_callers_fixed.1,
    ContextualCommonEventControls.a_shared_row_cannot_supply_the_two_distinct_instances _⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls.actual_conditional_row_has_both_matches
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls.no_fixed_label_tracks_both_schema_reads
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls.one_fixed_label_tracks_shared_reads
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SchemaControls.actual_common_model_rejects_shared_replacement
