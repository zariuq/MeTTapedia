import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeRefutationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutationControls

/-!
# Actual structural-pattern completion and guarded refusal controls

A global shape cycle is rejected before the available flexible-pair choice.
A scope failure is rejected despite its shape model. Fresh helpers, binding
fields, retained queue portions and an infinite declaration family remain
within the total structural fragment. General projecting applications keep
their modelled residuals outside that fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTerminationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualFrameWorklist
open ContextualPatternTermination

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

theorem the_actual_combined_driver_refutes_the_global_cycle_in_one_step :
    ∃ proof, run 1 ContextualUnrefutedPatternControls.source ContextualUnrefutedPatternControls.cycle = .refuted proof := by
  have localNone : ContextualEquationRefutation.choose (S := base) (source := ContextualUnrefutedPatternControls.source)
      ContextualUnrefutedPatternControls.cycle = none := ContextualUnrefutedPatternControls.the_cycle_has_no_immediate_equation_refutation
  have present : (ContextualFrameRefutation.choose (S := base) (source := ContextualUnrefutedPatternControls.source)
      ContextualUnrefutedPatternControls.cycle).isSome = true := by
    simp only [ContextualFrameRefutation.choose, localNone, Option.orElse_none]
    exact ContextualShapeRefutationControls.the_pattern_guard_allows_the_certified_cycle_refutation
  cases computed : ContextualFrameRefutation.choose (S := base) (source := ContextualUnrefutedPatternControls.source)
      ContextualUnrefutedPatternControls.cycle with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some refutation => exact refutes_at 0 _ _ ContextualUnrefutedPatternControls.cycle_is_already_normal refutation computed

theorem the_cycle_has_a_finite_finished_run_without_a_supplied_model :
    ∃ fuel, Finished (run fuel ContextualUnrefutedPatternControls.source ContextualUnrefutedPatternControls.cycle) :=
  finishes _ ContextualUnrefutedPatternControls.cycle_is_patterned

def isRefuted {V : Type} {declaration : V → MetaArity base} {problem : Problem declaration} : Result problem → Bool
  | .refuted _ => true
  | .residual _ => false

theorem scope_refusal_precedes_the_shape_phase :
    (ContextualShapeRefutation.solve ContextualUnrefutedPatternControls.missingVariable).isSome = true ∧
      isRefuted (run 1 ContextualUnrefutedPatternControls.source ContextualUnrefutedPatternControls.missingVariable) = true := by
  refine ⟨ContextualShapeRefutationControls.a_scope_inconsistency_can_still_have_a_shape_model.1, ?_⟩
  decide +kernel

theorem the_fresh_binding_field_is_in_the_total_fragment :
    ∃ fuel, Finished (run fuel ContextualFrameImitationControls.declaration ContextualFrameImitationControls.binderProblem) :=
  finishes _ ContextualSolverPatternControls.the_binder_imitation_input_is_structural

theorem the_framed_queue_finishes_without_a_supplied_model :
    ∃ fuel, Finished (run fuel ContextualSolverPatternControls.source ContextualSolverPatternControls.framedProblem) :=
  finishes _ ContextualSolverPatternControls.the_retained_prefix_selected_equation_and_suffix_are_patterns

theorem the_infinite_family_is_in_the_total_fragment :
    ∃ fuel, Finished (run fuel ContextualActiveSupportControls.declaration ContextualActiveSupportControls.problem) :=
  finishes _ ContextualSolverPatternControls.the_infinite_roster_problem_is_structural

theorem ordinary_fresh_helpers_still_finish_in_the_actual_driver :
    ContextualFrameWorklist.Controls.pendingCount
      (run 3 ContextualFrameWorklist.Controls.declaration ContextualFrameWorklist.Controls.constrained) = some 0 :=
  ContextualFrameWorklist.Controls.a_later_ground_equation_binds_the_computed_helper

theorem repeated_and_compound_projection_is_retained_with_its_actual_model :
    run 1 ContextualFrameSaturationControls.generalSource ContextualFrameSaturationControls.generalProblem =
      .residual (identity ContextualFrameSaturationControls.generalProblem) ∧
      Models ContextualFrameSaturationControls.generalModel ContextualFrameSaturationControls.generalProblem ∧
      ¬ ProblemPattern ContextualFrameSaturationControls.generalProblem := by
  refine ⟨ContextualFrameSaturationControls.the_actual_run_retains_both_general_equations,
    ContextualFrameSaturationControls.the_repeated_and_compound_equations_have_a_model, ?_⟩
  rw [← checkProblem_iff]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTerminationControls
