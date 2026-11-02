import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDecompositionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Rigid normalization, contextual binding and ordinary firing

A closed lambda equation is decomposed into an open child, then solved by
the declared unary hole. Both reductions compose, and their actual answer
licenses a consuming occurrence step with a surviving frame. A nullary hole
remains pending after decomposition; a rigid clash is conclusively rejected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBinding.Controls (base declaration extended nullaryId)
open ContextualDecomposition.Controls
  (unaryId unaryBody nullaryBody variableBody lambda unaryProblem nullaryProblem constant)

instance : DecidableEq base.Srt := by
  change DecidableEq Unit
  infer_instance
instance : ∀ sort, DecidableEq (base.Op sort) := fun _ => by
  change DecidableEq ContextualFrame.Controls.Operator
  infer_instance

def child : Problem declaration := [(observe unaryBody, observe variableBody)]

theorem normalization_descends_under_the_lambda : normalize unaryProblem = some child := by
  with_unfolding_all rfl

def answer : Assignment declaration declaration := ContextualBinding.answer unaryId variableBody

theorem the_child_has_a_principal_contextual_answer :
    ContextualFrameUnifier.Principal [(unaryBody, variableBody)] answer := by
  have principal := ContextualUnifierProfiles.binding (S := base) unaryId variableBody
    (by simp [variableBody, support])
  exact principal

theorem child_reduction : Reduction child answer [] := by
  exact of_principal_prefix the_child_has_a_principal_contextual_answer []

theorem the_whole_lambda_problem_has_a_finished_reduction : Reduction unaryProblem answer [] := by
  have composed := (normalization_reduction normalization_descends_under_the_lambda).compose child_reduction
  simpa only [Assignment.compose_identity_right] using composed

theorem the_answer_solves_the_original_equation : Models answer unaryProblem :=
  the_whole_lambda_problem_has_a_finished_reduction.finished_sound

theorem every_solution_factors_through_the_actual_answer
    {Variables : Type} (next : Variables → MetaArity base)
    (candidate : Assignment declaration next) (solved : Models candidate unaryProblem) :
    ∃ residual : Assignment declaration next,
      ∀ identity, candidate identity = instantiate residual (answer identity) := by
  obtain ⟨residual, _, factors⟩ :=
    the_whole_lambda_problem_has_a_finished_reduction.complete next candidate solved
  exact ⟨residual, factors⟩

theorem undeclared_capture_remains_an_explicit_obligation :
    normalize nullaryProblem = some [(observe nullaryBody, observe variableBody)] := by
  with_unfolding_all rfl

theorem returning_a_residual_does_not_assert_its_consistency :
    ¬ (ContextualObservationAction.action declaration).Consistent
      [(observe nullaryBody, observe variableBody)] := by
  rintro ⟨candidate, solved⟩
  have exactModels := models_normalize candidate nullaryProblem
  rw [undeclared_capture_remains_an_explicit_obligation] at exactModels
  have restored := exactModels.mp solved
  exact ContextualDecomposition.Controls.undeclared_binder_capture_is_inconsistent ⟨candidate, restored⟩

def rigidClash : Problem declaration :=
  [(observe (lambda variableBody), observe (lambda constant))]

theorem a_rigid_clash_is_rejected : normalize rigidClash = none := by with_unfolding_all rfl

theorem the_rejection_has_no_solution_in_any_later_frame
    {Variables : Type} (next : Variables → MetaArity base) (candidate : Assignment declaration next) :
    ¬ Models candidate rigidClash := refused_has_no_solution a_rigid_clash_is_rejected candidate

theorem a_context_tag_clash_is_rejected :
    normalize [(observe (constant (Γ := [])), observe (constant (Γ := [()]))) ] = none := by
  with_unfolding_all rfl

def repeated : Term extended [()] () := ContextualBinding.Controls.repeatedCall

theorem repeated_arguments_remain_available_to_other_solver_cases :
    terms repeated constant = some [(observe repeated, observe (constant (Γ := [()])))] := by with_unfolding_all rfl

def compound : Term extended [] () :=
  .op (.inr (.mk unaryId)) (.cons constant .nil)

theorem compound_arguments_are_not_declared_impossible :
    terms compound constant = some [(observe compound, observe (constant (Γ := [])))] := by with_unfolding_all rfl

abbrev A := ContextualObservationAction.action declaration

def label : Nat → Observation base declaration
  | 0 => observe (lambda variableBody)
  | 1 => observe (generator declaration nullaryId)
  | _ => observe (lambda unaryBody)

def initial : Configuration (Observation base declaration) Nat := ⟨[], {0, 1}⟩
def selected : Selection Nat := ⟨[0], [], [2]⟩
def rule : RuleInstance (Observation base declaration) :=
  ⟨[observe (lambda unaryBody)], [], [], [], [observe (lambda unaryBody)]⟩

theorem the_combined_solver_licenses_the_ordinary_step : selected.Valid A label rule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨answer, by
      change Models answer unaryProblem
      exact the_answer_solves_the_original_equation⟩, ?_⟩
  intro check member
  cases member

theorem an_ordinary_occurrence_step_fires :
    Step A label rule initial (selected.result label rule initial) :=
  ⟨selected, the_combined_solver_licenses_the_ordinary_step, rfl⟩

theorem the_frame_occurrence_survives : 1 ∈ (selected.result label rule initial).present := by decide

theorem the_consumed_occurrence_is_gone : 0 ∉ (selected.result label rule initial).present := by decide

theorem the_unrelated_frame_value_is_preserved : instantiateObservation answer (label 1) = label 1 := by
  with_unfolding_all rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver.Controls
