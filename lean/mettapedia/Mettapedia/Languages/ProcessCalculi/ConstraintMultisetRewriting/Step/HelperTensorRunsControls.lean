import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunRebaseControls

/-!
# Two complete local runs with equal-shaped final declaration scopes

The left run creates helpers valued seven and eight. The right context starts
with its own helper valued forty-two and creates a function-valued helper
valued thirteen. The two final local frames have identical shapes; the native
joint execution retains their separate assignments and all three events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.TensorRunsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny constant)

abbrev first := RunRebaseControls.localRun
abbrev placed := ContextResultControls.placed

def rightFiring : Firing ContextResultControls.context :=
  ⟨3, ([()], ()), constant 13, [ContextResultControls.pinned]⟩

theorem right_allowed : helperStep.Admits rightFiring := by
  apply (admits_iff rightFiring).mpr
  exact ⟨ContextResultControls.context_solvable, by decide, fun _ _ solved => solved⟩

def second : helperStep.Run ContextResultControls.context := .cons rightFiring right_allowed (.nil _)

abbrev leftPlan := RunRebaseControls.plan
abbrev leftResult := RebasePlan.realize placed first leftPlan

theorem right_joint_solvable :
    (Frames.contextual tiny).Solvable leftResult.target.swap.state.knowledge :=
  leftResult.target.swapIso.solvable_iff.mpr
    ((RebasePlan.target_solvable_iff placed first leftPlan).mpr ContextResultControls.placed_solvable)

theorem right_native_allowed : helperStep.Admits (s := leftResult.target.swap.state)
    (leftResult.target.swap.leftFiring rightFiring) :=
  (leftResult.target.swap.admitted_left_iff rightFiring right_allowed).mpr
    ⟨right_joint_solvable, by decide +kernel⟩

def rightPlan : RebasePlan tiny Nat leftResult.target.swap second :=
  .cons (by simp [Firing.selection]) right_native_allowed (.nil _)

def plan : TensorPlan placed first second := ⟨leftPlan, rightPlan⟩

def realization : TensorRealization placed first second := TensorPlan.realize plan

theorem actual_joint_run_has_three_events : realization.execution.word.length = 3 := realization.length_preserved

theorem end_frame_shapes_equal : first.last.frame = second.last.frame := rfl

theorem occurrence_ids_retained : realization.resultIso.rename = Equiv.refl Nat := rfl

theorem joint_resource_outputs : realization.execution.last.present = {1, 2, 3} := by
  have preserved := realization.resultIso.present
  rw [occurrence_ids_retained] at preserved
  simp only [Equiv.refl_toEmbedding, Finset.map_refl] at preserved
  have expected : realization.target.state.present = {1, 2, 3} := by
    change first.last.present ∪ second.last.present = {1, 2, 3}
    decide +kernel
  exact preserved.trans expected

theorem tensor_domain_holds : TensorDomain placed first second := (tensor_plan_iff_domain placed first second).mp ⟨plan⟩

theorem final_joint_knowledge_solvable : (Frames.contextual tiny).Solvable realization.target.state.knowledge :=
  (RebasePlan.realize leftResult.target.swap second plan.rightPlan).target.swapIso.solvable_iff.mpr
    ((RebasePlan.target_solvable_iff leftResult.target.swap second plan.rightPlan).mpr right_joint_solvable)

theorem final_scoped_realization : helperStep.toStep.effectCore.configuration realization.target.state =
    EffectCore.Systems.realize scopedHelperEffect [(false, first.last), (true, second.last)]
      realization.target.placement := realization.target.native_realization

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.TensorRunsControls
