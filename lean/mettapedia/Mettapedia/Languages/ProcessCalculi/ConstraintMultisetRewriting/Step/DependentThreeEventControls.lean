import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentThreeEventCell
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunControls

/-!
# Three actual dependent publication events

The first block publishes a path helper, the second and third publish
independent point helpers under different occurrence identities. The pair
exchange retains the third event and all three published occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open DependentFull.Controls TelescopeControls

def thirdData : Natural setting.levels Nat pointHelpers.frame :=
  ⟨[], [], [], [], [(3, Make.ofRow pointRow)], [], [], []⟩

def third : HelperFiring setting.levels Nat baseState := ⟨pointHelpers, thirdData⟩

theorem third_shapes : (diamond.thirdForward third).toFiring.Shapes := by
  refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, ?_⟩
  intro made member
  obtain rfl := List.mem_singleton.mp member
  exact ((Make.ofRow_wellTyped pointRow).reindex _).reindex _

theorem third_after_pair : (helperStep setting.levels Nat).Admits (diamond.thirdForward third) := by
  refine ⟨third_shapes, (enabled_iff _).mpr ?_, ?_, ?_⟩
  · refine ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, ?_⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    decide
  · exact ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩
  · exact fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩

theorem three_steps_really_run :
    (diamond.forwardThree third third_after_pair).word.length = 3 ∧
      (diamond.backwardThree third third_after_pair).word.length = 3 :=
  diamond.three_event_count third third_after_pair

theorem all_three_occurrences :
    (diamond.forwardThree third third_after_pair).last.present = {1, 2, 3} ∧
      (diamond.backwardThree third third_after_pair).last.present = {1, 2, 3} := by decide

theorem third_position_kept :
    (Transport.RunRearrangement.events (helperTransport setting.levels Nat)
      (diamond.cellThree third third_after_pair) ⟨2, by decide⟩).val = 2 :=
  (diamond.three_event_positions third third_after_pair ⟨2, by decide⟩).trans rfl

theorem three_typed_rows_kept (occurrence : Nat) :
    (diamond.backwardThree third third_after_pair).last.label occurrence =
      ((diamond.forwardThree third third_after_pair).last.label occurrence).reindex
        (diamond.thirdResultIso third third_after_pair).frame.hom :=
  diamond.three_typed_rows third third_after_pair occurrence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls.third_after_pair
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Controls.third_position_kept
