import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveStepProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViewControls

/-!
# Computed occurrence firings across contextual declaration frames

The same stored schema occurrence supplies incompatible private instances
to two read ports, without duplicating the physical row. A retained shared
capture follows the old equation store into the extended frame. Replacing
the schema by a shared shared value refuses that firing. Further controls
retain repeated aliases, reject duplicate consumption and keep guards outside
the declared positive profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm ActiveTerm atom pair p
  a b rawA rawB privateVariable universalRow sharedValue selection occupied first second split)

abbrev CapturedTerm := Term (signature base captures) [] ()
abbrev Stored := ContextualStoredRows.Row locals captures [] ()
abbrev AfterStored := ContextualStoredRows.Row locals active [] ()
abbrev A := ContextualFamilies.action active [] ()

def capturedAtom : CapturedTerm := atom captures

def before : Configuration CapturedTerm Nat := ⟨[(sharedValue, capturedAtom)], {7, 8}⟩

def rows : Nat → Stored
  | 7 => .schema universalRow
  | 8 => .shared (p sharedValue)
  | _ => .shared capturedAtom

def rule : RuleInstance RawTerm :=
  ⟨[], [p rawA, p rawB], [(privateVariable, rawA)], [], [universalRow]⟩

def views := prepared locals captures occupied selection rule rows
def equations := problem locals captures occupied selection rule rows before
def after := result locals captures occupied selection rule rows before
def outputs (_ : Nat) : ActiveTerm := p (generator active (.inl (ScopedVar.at 8 0)))
def afterRows := resultRows locals captures selection outputs rows
def afterOccupied := ContextualActivationScopes.after occupied selection

theorem the_problem_contains_the_old_binding_and_both_independent_read_equations :
    equations =
      [(generator active (.inr 0), a),
       (p a, p (generator active (.inl (ScopedVar.at 9 0)))),
       (p b, p (generator active (.inl (ScopedVar.at 10 0)))),
       (generator active (.inl (ScopedVar.at 8 0)), a)] := by
  with_unfolding_all rfl

theorem the_computed_two_read_problem_has_a_model : A.Models split equations := by
  rw [the_problem_contains_the_old_binding_and_both_independent_read_equations]
  refine (A.models_cons split _ _).mpr ⟨?_, (A.models_cons split _ _).mpr
    ⟨?_, (A.models_cons split _ _).mpr ⟨?_, (A.models_cons split _ _).mpr ⟨?_, A.models_nil split⟩⟩⟩⟩
  all_goals with_unfolding_all rfl

theorem the_shared_physical_schema_read_is_a_valid_firing :
    Valid locals captures occupied selection rule rows before outputs := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ?_⟩
  · with_unfolding_all rfl
  · exact ContextualFrameUnifier.solvable_of_consistent ⟨split, the_computed_two_read_problem_has_a_model⟩

theorem the_schema_uses_an_actual_positive_step :
    Step locals captures occupied rule rows before outputs after afterRows afterOccupied :=
  ⟨selection, the_shared_physical_schema_read_is_a_valid_firing, rfl, rfl, rfl⟩

theorem shared_reads_do_not_manufacture_extra_physical_occurrences :
    after.present = {7, 8, 99} ∧ after.present.card = 3 := by decide

theorem the_chosen_read_occurrence_survives : 7 ∈ after.present :=
  the_shared_physical_schema_read_is_a_valid_firing.kept_survive locals captures (by decide)

theorem the_retained_shared_row_keeps_its_old_capture :
    afterRows 8 = .shared (instantiate (ContextualSelectionViews.capturedTarget locals captures) (p sharedValue)) := by
  have transported :=
    the_shared_physical_schema_read_is_a_valid_firing.retained_row_transports_captures locals captures
      (occurrence := 8) (by decide)
  simpa only [afterRows, rows, ContextualStoredRows.Row.map] using transported

theorem the_binding_reaches_the_unread_retained_row :
    instantiate split (instantiate (ContextualSelectionViews.capturedTarget locals captures) (p sharedValue)) = p a := by
  with_unfolding_all rfl

theorem every_future_model_still_satisfies_the_old_capture_equation
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment active next)
    (solved : ContextualFrameUnifier.Models candidate equations) :
    ContextualFrameUnifier.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) before.equations :=
  models_refine_old_frame locals captures next occupied selection rule rows before candidate solved

def sharedRows : Nat → Stored := fun _ => .shared (p sharedValue)

theorem shared_row_use_views_remain_identical :
    (prepared locals captures occupied selection rule sharedRows).read first =
      (prepared locals captures occupied selection rule sharedRows).read second := by
  exact ContextualSelectionViews.shared_value_does_not_change_between_ports locals captures occupied
    (ContextualActivationScopes.readPort selection first) (ContextualActivationScopes.readPort selection second)
    (p sharedValue)

theorem replacing_the_schema_by_one_shared_row_refuses_the_firing :
    ¬ Valid locals captures occupied selection rule sharedRows before outputs := by
  intro valid
  obtain ⟨Future, future, candidate, solved⟩ := valid.solvable
  have inputs := valid.models_inputs locals captures future candidate solved
  have reads : List.Forall₂
      (fun pattern value => instantiate candidate pattern = instantiate candidate value)
      [p a, p b]
      [instantiate (ContextualSelectionViews.capturedTarget locals captures) (p sharedValue),
       instantiate (ContextualSelectionViews.capturedTarget locals captures) (p sharedValue)] := inputs.2.2.1
  have one := (List.forall₂_cons.mp reads).1
  have two := (List.forall₂_cons.mp (List.forall₂_cons.mp reads).2).1
  have sizes := congrArg termSize (one.trans two.symm)
  change (3 : Nat) = 5 at sizes
  omega

def duplicateSelection : Selection Nat := ⟨[7, 7], [], [99]⟩
def duplicateRule : RuleInstance RawTerm := ⟨[p rawA, p rawB], [], [], [], [universalRow]⟩

def takeSelection : Selection Nat := ⟨[7, 8], [], [99]⟩
def takeRule : RuleInstance RawTerm :=
  ⟨[p rawA, p rawB], [], [(privateVariable, rawA)], [], [universalRow]⟩
def duplicateValuedRows : Nat → Stored := fun _ => .schema universalRow

theorem distinct_occurrences_may_hold_the_same_schema : duplicateValuedRows 7 = duplicateValuedRows 8 := rfl

theorem distinct_takes_build_the_same_value_equations_as_the_two_reads :
    problem locals captures occupied takeSelection takeRule duplicateValuedRows before = equations := by
  with_unfolding_all rfl

theorem two_equal_valued_occurrences_can_be_consumed_distinctly :
    Valid locals captures occupied takeSelection takeRule duplicateValuedRows before outputs := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ?_⟩
  · with_unfolding_all rfl
  · apply ContextualFrameUnifier.solvable_of_consistent
    refine ⟨split, ?_⟩
    rw [distinct_takes_build_the_same_value_equations_as_the_two_reads]
    exact the_computed_two_read_problem_has_a_model

theorem the_two_distinct_consumptions_remove_both_physical_copies :
    (result locals captures occupied takeSelection takeRule duplicateValuedRows before).present = {99} := by decide

theorem distinct_local_views_do_not_license_duplicate_consumption :
    ¬ Valid locals captures occupied duplicateSelection duplicateRule rows before outputs := by
  intro valid
  exact (by decide : ¬ duplicateSelection.taken.Nodup) valid.take_distinct

def guardedRule : RuleInstance RawTerm :=
  ⟨[], [p rawA, p rawB], [], [.equal rawA rawA], [universalRow]⟩

theorem even_a_true_guard_is_outside_the_declared_positive_profile :
    ¬ Valid locals captures occupied selection guardedRule rows before outputs := by
  intro valid
  cases valid.no_checks

def repeatedRows : Nat → Stored := fun _ =>
  .schema (pair privateVariable privateVariable)

theorem repeated_aliases_remain_one_variable_in_the_computed_row_view
    (candidate : Assignment active active) :
    instantiate candidate ((prepared locals captures occupied selection rule repeatedRows).read first) ≠ pair a b :=
  ContextualSelectionViews.Controls.no_assignment_makes_one_repeated_variable_equal_two_distinct_values candidate

abbrev laterSource := ContextualSelectionViews.source locals active
abbrev laterTarget := ContextualSelectionViews.target locals active

theorem the_stored_schema_is_not_specialized_by_its_read_instances :
    afterRows 7 = .schema (p (generator laterSource (.inl 0))) := by
  with_unfolding_all rfl

theorem reading_the_retained_schema_opens_another_private_copy :
    ContextualStoredRows.viewAt locals active 11 (afterRows 7) =
      p (generator laterTarget (.inl (ScopedVar.at 11 0))) := by
  with_unfolding_all rfl

def laterSchema : AfterStored := .schema
  (pair (generator laterSource (.inl 0))
    (generator laterSource (.inr (.inl (ScopedVar.at 8 0)))))

theorem a_later_schema_can_capture_an_earlier_rule_local :
    ContextualStoredRows.viewAt locals active 11 laterSchema =
      pair (generator laterTarget (.inl (ScopedVar.at 11 0)))
        (generator laterTarget (.inr (.inl (ScopedVar.at 8 0)))) := by
  with_unfolding_all rfl

theorem the_scope_ledger_is_advanced_with_the_firing : afterOccupied = {0, 2, 7, 8, 9, 10} := by decide

def sharedLabel (_ : Nat) : CapturedTerm := p sharedValue
def sharedRule : RuleInstance CapturedTerm := ⟨[p sharedValue], [], [], [], [p sharedValue]⟩
def sharedSelection : Selection Nat := ⟨[7], [], [99]⟩
def transportedLabel := ContextualActiveStepProfile.targetLabel locals captures sharedLabel
def transportedRule := ContextualActiveStepProfile.targetRule locals captures sharedRule
def transportedBefore := frame locals captures before
def sharedAfter := sharedSelection.result transportedLabel transportedRule transportedBefore

theorem the_already_active_profile_has_an_ordinary_firing :
    sharedSelection.Valid A transportedLabel transportedRule transportedBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨split, ?_⟩
    change A.Models split [(generator active (.inr 0), a),
      (p (generator active (.inr 0)), p (generator active (.inr 0)))]
    refine (A.models_cons split _ _).mpr ⟨?_, (A.models_cons split _ _).mpr ⟨?_, A.models_nil split⟩⟩
    · with_unfolding_all rfl
    · rfl
  · simp [transportedRule, ContextualActiveStepProfile.targetRule, sharedRule, RuleInstance.map]

theorem the_already_active_step_is_recovered_with_its_ledger :
    ∃ ledger, Step locals captures occupied (ContextualActiveStepProfile.rawRule locals captures sharedRule)
      (ContextualActiveStepProfile.sharedRows locals captures sharedLabel) before transportedLabel sharedAfter
      (ContextualActiveStepProfile.sharedRows locals active transportedLabel) ledger :=
  (ContextualActiveStepProfile.step_iff locals captures occupied (fun () => atom active) sharedRule rfl sharedLabel before sharedAfter).mpr
    ⟨sharedSelection, the_already_active_profile_has_an_ordinary_firing, rfl⟩

theorem the_recovered_consuming_profile_removes_the_taken_occurrence :
    7 ∉ sharedAfter.present ∧ 8 ∈ sharedAfter.present ∧ 99 ∈ sharedAfter.present := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep.Controls
