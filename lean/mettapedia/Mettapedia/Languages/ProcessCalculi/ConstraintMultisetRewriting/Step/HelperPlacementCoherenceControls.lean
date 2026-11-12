import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementCoherence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResultControls

/-!
# Equal frame shapes still require the declaration permutation

Two fresh nullary helpers are placed beside an existing helper. The two
orders have literally equal frame shapes and different source assignments.
The canonical swap makes the square commute; an identity map would confuse
the helpers valued seven and thirteen. Both actual event orders are admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.PlacementCoherenceControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny empty first constant)
open ContextResultControls (context placed pinned placed_solvable)

def other : Firing context := ⟨3, ([], ()), constant 13, [pinned]⟩

theorem other_allowed : helperStep.Admits other := by
  apply (admits_iff other).mpr
  exact ⟨ContextResultControls.context_solvable, by decide, fun _ _ solved => solved⟩

theorem joint_independent : helperTransport.Independent placed.state
    (placed.leftFiring first) (placed.rightFiring other) :=
  (placed.independent_pair_iff first other ResidualRunExchangeControls.first_admitted other_allowed).mpr
    ⟨placed_solvable, by decide, by decide, by decide⟩

abbrev leftRight := placed.afterLeftRight first other
abbrev rightLeft := placed.afterRightLeft first other
def square : helperStep.StateIso leftRight.state rightLeft.state := placed.afterBothSwap first other

theorem frame_shapes_equal : leftRight.frame = rightLeft.frame := rfl
theorem physical_ids_preserved : square.rename = Equiv.refl Nat := rfl

def distinguish : Assignment leftRight.frame.arity empty.arity
  | .inl (.inl (.inl impossible)) => impossible.elim
  | .inl (.inl (.inr ())) => constant 42
  | .inl (.inr ()) => constant 7
  | .inr () => constant 13

theorem source_maps_differ : leftRight.leftMap ≠ rightLeft.leftMap := by
  intro same
  have separated := congrArg (fun assignment => instantiate distinguish (assignment (.inr ()))) same
  change (constant (declaration := empty.arity) (Γ := []) 7) = constant 13 at separated
  cases separated

theorem identity_frame_map_fails : square.frame.hom ≠ (Frames.contextual tiny).id leftRight.frame := by
  intro same
  have commutes := placed.after_both_left_map first other
  change Assignment.compose square.frame.hom leftRight.leftMap = rightLeft.leftMap at commutes
  rw [same] at commutes
  have identity : Assignment.compose ((Frames.contextual tiny).id leftRight.frame) leftRight.leftMap = leftRight.leftMap := by
    funext name
    exact instantiate_identity _
  exact source_maps_differ (identity.symm.trans commutes)

theorem actual_native_orders :
    ∃ leftRun rightRun : helperStep.Run placed.state,
      leftRun.word.length = 2 ∧ rightRun.word.length = 2 ∧ helperTransport.TraceEquiv placed.state leftRun rightRun := by
  obtain ⟨af, ag, afterFirst, afterSecond, close, exchange⟩ := joint_independent.swap
  let leftRun : helperStep.Run placed.state :=
    .cons (placed.leftFiring first) af
      (.cons (helperTransport.residual (placed.leftFiring first) af (placed.rightFiring other)) afterFirst (.nil _))
  let rightRun : helperStep.Run placed.state :=
    .cons (placed.rightFiring other) ag
      (.cons (helperTransport.residual (placed.rightFiring other) ag (placed.leftFiring first)) afterSecond
        (helperTransport.moveRun close (.nil _)))
  exact ⟨leftRun, rightRun, rfl, rfl, .rel _ _ (.inl (exchange (.nil _)))⟩

theorem left_right_solvable : (Frames.contextual tiny).Solvable leftRight.state.knowledge :=
  ((placed.afterLeft first).swap.afterLeft other).swapIso.solvable_iff.mpr
    (((placed.afterLeft first).swap.after_left_solvable_iff other).mpr
      ((placed.afterLeft first).swapIso.solvable_iff.mpr
        ((placed.after_left_solvable_iff first).mpr placed_solvable)))

theorem right_left_solvable : (Frames.contextual tiny).Solvable rightLeft.state.knowledge :=
  square.solvable_iff.mp left_right_solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.PlacementCoherenceControls
