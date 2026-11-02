import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeight
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls

/-!
# Constructor decomposition increases queue length but decreases term work

One binary equation becomes two flexible field equations: queue length
grows from one to two while structural weight drops from ten to eight.
A lambda field retains its extended object context. These controls use
ordinary compound applications, without assuming the pattern fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeightControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualEquationWeight

abbrev base := ContextualBindingWorklist.Controls.base
abbrev source := ContextualBindingWorklist.Controls.declaration
abbrev extended := signature base source
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def pair : Term extended [] () := .op (.inl .pair)
  (.cons (ContextualBindingWorklist.Controls.call ContextualBindingWorklist.Controls.constant
      ContextualBindingWorklist.Controls.constant)
    (.cons ContextualBindingWorklist.Controls.closed .nil))
def problem : Problem source := [(observe pair, observe pair)]

theorem the_original_single_equation_weighs_ten : problem.length = 1 ∧ weight problem = 10 := by
  constructor <;> decide +kernel

theorem actual_decomposition_yields_two_equations :
    (ContextualRigidSolver.normalize problem).map List.length = some 2 := by
  decide +kernel

theorem actual_decomposition_weighs_eight :
    (ContextualRigidSolver.normalize problem).map weight = some 8 := by
  decide +kernel

theorem queue_length_is_not_a_monotone_normalization_measure :
    ∃ remaining, ContextualRigidSolver.normalize problem = some remaining ∧
      problem.length < remaining.length ∧ weight remaining < weight problem := by
  have count := actual_decomposition_yields_two_equations
  have size := actual_decomposition_weighs_eight
  cases computed : ContextualRigidSolver.normalize problem with
  | none => simp only [computed, Option.map_none, reduceCtorEq] at count
  | some remaining =>
      have length : remaining.length = 2 := by simpa only [computed, Option.map_some, Option.some.injEq] using count
      have measured : weight remaining = 8 := by simpa only [computed, Option.map_some, Option.some.injEq] using size
      refine ⟨remaining, rfl, ?_, ?_⟩
      · rw [length, the_original_single_equation_weighs_ten.1]
        decide
      · rw [measured, the_original_single_equation_weighs_ten.2]
        decide

def lambda : Term extended [] () := .op (.inl .lam)
  (.cons (ContextualBindingWorklist.Controls.call (.var .zero) (.var .zero)) .nil)
def boundProblem : Problem source := [(observe lambda, observe lambda)]

theorem the_decomposed_lambda_field_has_its_own_object_context :
    ((ContextualRigidSolver.normalize boundProblem).bind fun remaining => remaining[0]?).map
      (fun equation => equation.1.1.length) = some 1 := by
  decide +kernel

theorem a_closed_constructor_equality_has_no_remaining_work :
    (ContextualRigidSolver.normalize
      [(observe (ContextualBindingWorklist.Controls.constant (Γ := [])),
        observe (ContextualBindingWorklist.Controls.constant (Γ := [])))]).map weight = some 0 := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeightControls
