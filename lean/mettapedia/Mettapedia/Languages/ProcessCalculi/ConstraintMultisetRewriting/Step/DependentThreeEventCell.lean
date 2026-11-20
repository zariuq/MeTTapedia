import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentResidualCube
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStateGroupoid

/-!
# A witnessed pair exchange inside actual three-event dependent executions

The third event need only be admitted after the first two. Moving it across
their canonical comparison preserves that admission. The resulting cell
exchanges the first two event positions and keeps the third, while retaining
the complete dependent endpoint comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}
  (diamond : Diamond first second accepted accepted')
  (third : HelperFiring levels O state)
  (admitted : (helperStep levels O).Admits (diamond.thirdForward third))

def restForward : (helperStep levels O).toStep.Run diamond.forward.last :=
  .cons (diamond.thirdForward third) admitted (.nil _)

def restBackward : (helperStep levels O).toStep.Run diamond.backward.last :=
  .cons (diamond.thirdBackward third) ((diamond.third_admits_iff third).mp admitted) (.nil _)

def forwardThree : (helperStep levels O).toStep.Run state :=
  diamond.forward.append (diamond.restForward third admitted)

def backwardThree : (helperStep levels O).toStep.Run state :=
  diamond.backward.append (diamond.restBackward third admitted)

noncomputable def afterPairSwap : (helperStep levels O).toStep.Run state :=
  diamond.backward.append
    ((helperTransport levels O).moveRun diamond.close (diamond.restForward third admitted))

noncomputable def pairWithThird :
    (helperTransport levels O).InterchangeWitness (diamond.forwardThree third admitted)
      (diamond.afterPairSwap third admitted) :=
  Transport.InterchangeWitness.here (T := helperTransport levels O) accepted accepted'
    diamond.afterFirst diamond.afterSecond diamond.close (diamond.restForward third admitted)

noncomputable def thirdSimilarity :
    (helperTransport levels O).SimilarityWitness
      ((helperTransport levels O).moveRun diamond.close (diamond.restForward third admitted))
      (diamond.restBackward third admitted) :=
  Transport.SimilarityWitness.cons (T := helperTransport levels O) (PlainIso.refl _)
    ((helperAlike_equivalence _).trans
      (helper_move_refl ((diamond.thirdForward third).move diamond.close)) (diamond.third_alike third))
    (.nil ((diamond.thirdComparisonData third).resultComparison
      ((helper_admits_move diamond.close (diamond.thirdForward third)).mpr admitted)
      ((diamond.third_admits_iff third).mp admitted)))

noncomputable def cellThree :
    Transport.RunRearrangement.Cell (helperTransport levels O)
      (diamond.forwardThree third admitted) (diamond.backwardThree third admitted) :=
  Transport.RunRearrangement.generator (helperTransport levels O) (.inr (diamond.pairWithThird third admitted)) ≫
    Transport.RunRearrangement.generator (helperTransport levels O)
      (.inl ((Transport.SimilarityWitness.refl (T := helperTransport levels O) diamond.backward).append
        (diamond.thirdSimilarity third admitted)))

theorem three_event_count :
    (diamond.forwardThree third admitted).word.length = 3 ∧
      (diamond.backwardThree third admitted).word.length = 3 := ⟨rfl, rfl⟩

theorem three_event_positions (event : Fin (diamond.forwardThree third admitted).word.length) :
    (Transport.RunRearrangement.events (helperTransport levels O)
      (diamond.cellThree third admitted) event).val = ProofRelevantRuns.swapAt 0 event.val := by
  unfold cellThree
  rw [Transport.RunRearrangement.events_comp, Transport.RunRearrangement.events_generator,
    Transport.RunRearrangement.events_generator]
  rfl

theorem three_endpoint_map :
    RunStateGroupoid.endpointMap levels O (diamond.cellThree third admitted) =
      diamond.thirdResultIso third admitted := by
  unfold cellThree
  rw [RunStateGroupoid.endpointMap_comp, RunStateGroupoid.endpointMap_generator,
    RunStateGroupoid.endpointMap_generator]
  rfl

theorem three_typed_rows (occurrence : O) :
    (diamond.backwardThree third admitted).last.label occurrence =
      ((diamond.forwardThree third admitted).last.label occurrence).reindex
        (diamond.thirdResultIso third admitted).frame.hom :=
  (diamond.thirdResultIso third admitted).label occurrence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.three_event_positions
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.three_endpoint_map
