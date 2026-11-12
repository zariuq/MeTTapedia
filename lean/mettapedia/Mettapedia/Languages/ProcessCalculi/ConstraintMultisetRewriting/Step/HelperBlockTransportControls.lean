import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementBlocks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorRunsControls

/-!
# Native continuations after swapping complete declaration blocks

The prior blocks create helpers seven/eight and a function-valued helper
thirteen beside an existing forty-two. New rules refer to the earlier seven
and forty-two through their original source scopes. Both complete future
plans transport across the block permutation and retain two native events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.BlockTransportControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny)
open TensorRunsControls (first second placed)

abbrev leftPlace := (placed.advanceLeft first).advanceRight second
abbrev rightPlace := (placed.advanceRight second).advanceLeft first
def permutation : PlacementIso leftPlace rightPlace := placed.blockSwap first second

def futureLeft : Firing first.last :=
  ⟨4, ([], ()), generator first.last.frame.arity (.inl (.inr ())), []⟩
def futureRight : Firing second.last :=
  ⟨5, ([], ()), generator second.last.frame.arity (.inl (.inr ())), []⟩

theorem stored_left_reference :
    (observe futureLeft.value, observe (Helpers.Consumer.constant (declaration := first.last.frame.arity) (Γ := []) 7)) ∈
      first.last.knowledge := List.mem_cons_self

theorem stored_right_reference :
    (observe futureRight.value, observe (Helpers.Consumer.constant (declaration := second.last.frame.arity) (Γ := []) 42)) ∈
      second.last.knowledge := List.mem_cons_self

theorem future_left_meaning {target : Frames.Frame tiny} (σ : Assignment first.last.frame.arity target.arity)
    (solved : (Frames.contextual tiny).Models σ first.last.knowledge) :
    instantiate σ futureLeft.value = Helpers.Consumer.constant (declaration := target.arity) (Γ := []) 7 :=
  observe_injective (solved _ stored_left_reference)

theorem future_right_meaning {target : Frames.Frame tiny} (σ : Assignment second.last.frame.arity target.arity)
    (solved : (Frames.contextual tiny).Models σ second.last.knowledge) :
    instantiate σ futureRight.value = Helpers.Consumer.constant (declaration := target.arity) (Γ := []) 42 :=
  observe_injective (solved _ stored_right_reference)

theorem future_left_allowed : helperStep.Admits futureLeft :=
  (admits_iff futureLeft).mpr
    ⟨(run_solvable_iff first).mpr Helpers.Consumer.start_solvable, by decide, asks_nil⟩

theorem future_right_allowed : helperStep.Admits futureRight :=
  (admits_iff futureRight).mpr
    ⟨(run_solvable_iff second).mpr ContextResultControls.context_solvable, by decide, asks_nil⟩

def leftRun : helperStep.Run first.last := .cons futureLeft future_left_allowed (.nil _)
def rightRun : helperStep.Run second.last := .cons futureRight future_right_allowed (.nil _)

theorem left_place_solvable : (Frames.contextual tiny).Solvable leftPlace.state.knowledge :=
  Eq.mp (congrArg (fun p : ContextPlacement first.last second.last => (Frames.contextual tiny).Solvable p.state.knowledge)
    (ContextPlacement.tensor_target placed first second TensorRunsControls.plan)) TensorRunsControls.final_joint_knowledge_solvable

theorem native_left_allowed : helperStep.Admits (s := leftPlace.state) (leftPlace.leftFiring futureLeft) :=
  (leftPlace.admitted_left_iff futureLeft future_left_allowed).mpr ⟨left_place_solvable, by decide⟩

def leftPlan : RebasePlan tiny Nat leftPlace leftRun :=
  .cons (by simp [Firing.selection]) native_left_allowed (.nil _)

abbrev leftResult := RebasePlan.realize leftPlace leftRun leftPlan

theorem right_place_solvable : (Frames.contextual tiny).Solvable leftResult.target.swap.state.knowledge :=
  leftResult.target.swapIso.solvable_iff.mpr
    ((RebasePlan.target_solvable_iff leftPlace leftRun leftPlan).mpr left_place_solvable)

theorem native_right_allowed : helperStep.Admits (s := leftResult.target.swap.state)
    (leftResult.target.swap.leftFiring futureRight) :=
  (leftResult.target.swap.admitted_left_iff futureRight future_right_allowed).mpr ⟨right_place_solvable, by decide⟩

def rightPlan : RebasePlan tiny Nat leftResult.target.swap rightRun :=
  .cons (by simp [Firing.selection]) native_right_allowed (.nil _)

def futureTensor : TensorPlan leftPlace leftRun rightRun := ⟨leftPlan, rightPlan⟩

def mapped := placementTransport.mapTensorPlan contextualFlip placementFlipCompatible permutation futureTensor

theorem both_native_futures_similar : helperTransport.Similar
    (TensorPlan.realize futureTensor).execution (TensorPlan.realize mapped.1).execution :=
  placementTransport.tensors_similar contextualFlip placementFlipCompatible permutation futureTensor mapped.1

theorem both_native_futures_have_two_events :
    (TensorPlan.realize futureTensor).execution.word.length = 2 ∧
      (TensorPlan.realize mapped.1).execution.word.length = 2 :=
  ⟨(TensorPlan.realize futureTensor).length_preserved, (TensorPlan.realize mapped.1).length_preserved⟩

def final_source_embeddings : PlacementIso (TensorPlan.realize futureTensor).target (TensorPlan.realize mapped.1).target := mapped.2

theorem physical_ids_fixed : permutation.toStateIso.rename = Equiv.refl Nat := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.BlockTransportControls
