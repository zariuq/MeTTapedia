import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameImitationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameFlexPairControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverBindingProgress

/-!
# The executable frame driver consumes its retained solver choices

An unsupported compound prefix is retained while a later equation is
selected. Both surrounding portions survive the computed update; later
binding solves the complete original queue. Reversed imitation and flexible
pairs still execute, and repetition does not acquire unique recovery.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

abbrev base := ContextualBindingWorklist.Controls.base
abbrev source := ContextualBindingWorklist.Controls.declaration
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def equations : Problem source := ContextualBindingWorklist.Controls.compoundProblem ++
  [(observe (ContextualBindingWorklist.Controls.closed (Γ := [])),
    observe (ContextualBindingWorklist.Controls.constant (Γ := []))),
   (observe (ContextualBindingWorklist.Controls.call (Γ := [(), ()]) (.var .zero) (.var (.succ .zero))),
    observe (ContextualBindingWorklist.Controls.constant (Γ := [(), ()])))]

def candidate : Assignment source source
  | false => ContextualBindingWorklist.Controls.constant
  | true => ContextualBindingWorklist.Controls.constant

theorem all_three_original_equations_have_an_independent_model : Models candidate equations := by
  intro equation member
  simp only [equations, ContextualBindingWorklist.Controls.compoundProblem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem the_actual_choice_retains_one_equation_before_and_after :
    (ContextualSolverSelect.choose equations).map (fun chosen => (chosen.before.length, chosen.after.length)) = some (1, 1) := by
  decide +kernel

theorem performing_that_choice_keeps_both_retained_positions :
    (ContextualFrameWorklist.choose equations).map (fun update => update.remaining.length) = some 2 := by
  decide +kernel

theorem the_recovered_middle_binding_makes_strict_progress_with_both_sides_retained :
    ∃ binding, ContextualBindingCase.tryTerms (ContextualBindingWorklist.Controls.closed (Γ := []))
        (ContextualBindingWorklist.Controls.constant (Γ := [])) = some binding ∧
      Models candidate (ContextualSolverBindingProgress.choice binding
        ContextualBindingWorklist.Controls.compoundProblem (equations.drop 2)).perform.remaining ∧
      ContextualSolverMeasure.Smaller
        (ContextualSolverMeasure.measure candidate (ContextualSolverBindingProgress.choice binding
          ContextualBindingWorklist.Controls.compoundProblem (equations.drop 2)).perform.remaining)
        (ContextualSolverMeasure.measure candidate equations) := by
  have present : (ContextualBindingCase.tryTerms (ContextualBindingWorklist.Controls.closed (Γ := []))
    (ContextualBindingWorklist.Controls.constant (Γ := []))).isSome = true := by decide +kernel
  cases computed : ContextualBindingCase.tryTerms (ContextualBindingWorklist.Controls.closed (Γ := []))
      (ContextualBindingWorklist.Controls.constant (Γ := [])) with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some binding =>
      have progressed := ContextualSolverBindingProgress.model_progress binding
        ContextualBindingWorklist.Controls.compoundProblem (equations.drop 2) candidate
        all_three_original_equations_have_an_independent_model
      exact ⟨binding, rfl, progressed.1, progressed.2.2⟩

theorem the_computed_choice_factors_the_independent_model :
    ∃ chosen, ContextualSolverSelect.choose equations = some chosen ∧
      ∃ remaining : Assignment chosen.perform.declaration source,
        Models remaining chosen.perform.remaining ∧
        ∀ identity, candidate identity = instantiate remaining (chosen.perform.answer identity) := by
  have present : (ContextualSolverSelect.choose equations).isSome = true := by decide +kernel
  cases computed : ContextualSolverSelect.choose equations with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
  | some chosen => exact ⟨chosen, rfl, chosen.perform.factors source candidate all_three_original_equations_have_an_independent_model⟩

def pending {problem : Problem source} : ContextualFrameWorklist.Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem subsequent_actual_steps_solve_the_entire_original_queue :
    pending (ContextualFrameWorklist.run 3 source equations) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 3 equations source candidate
    all_three_original_equations_have_an_independent_model]
  decide +kernel

theorem the_completed_actual_answer_satisfies_all_three_original_equations :
    ∃ update, ContextualFrameWorklist.run 3 source equations = .residual update ∧
      update.remaining = [] ∧ Models update.answer equations := by
  have count := subsequent_actual_steps_solve_the_entire_original_queue
  cases computed : ContextualFrameWorklist.run 3 source equations with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using count
      exact ⟨update, rfl, empty, update.completed empty⟩

theorem repetition_alone_still_has_no_unique_binding_choice :
    (ContextualSolverSelect.choose ContextualBindingWorklist.Controls.repeatedProblem).isSome = false := by
  decide +kernel

theorem the_undeclared_ambient_capture_does_not_get_a_solver_choice :
    (ContextualSolverSelect.choose ContextualBindingWorklist.Controls.captureProblem).isSome = false := by
  decide +kernel

theorem reversed_imitation_still_uses_the_actual_driver :
    ContextualFrameImitationControls.pendingCount
      (ContextualFrameWorklist.run 4 ContextualFrameImitationControls.declaration ContextualFrameImitationControls.reversed) = some 0 := by
  exact ContextualFrameImitationControls.the_reverse_orientation_uses_the_same_solver

theorem the_disjoint_flexible_pair_still_uses_a_fresh_interface :
    ContextualFrameFlexPairControls.originalArity
      (ContextualFrameWorklist.run 1 ContextualFrameFlexPairControls.declaration ContextualFrameFlexPairControls.disjoint) false = some 0 := by
  exact ContextualFrameFlexPairControls.both_original_images_use_a_closed_helper.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceControls
