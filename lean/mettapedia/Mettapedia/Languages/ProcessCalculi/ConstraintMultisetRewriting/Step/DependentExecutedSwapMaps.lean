import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentIteratedBlockBraid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentThreeEventCell

/-!
# Adjacent exchange maps of complete native triple executions

The first exchange carries the third event through a canonical pair diamond;
its retained pullback legs determine the iterated-block exchange. The last
exchange is a pair diamond beneath an actual first firing. Both statements
refer to the endpoint interpreter of the witnessed execution cells.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open BlockTriple

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}

theorem Diamond.thirdResultIso_is_swap (diamond : Diamond first second accepted accepted')
    (third : HelperFiring levels O state)
    (admitted : (helperStep levels O).Admits (diamond.thirdForward third)) :
    (diamond.thirdResultIso third admitted).frame.hom = iteratedSwapFirst second.helpers first.helpers third.helpers := by
  apply (iterated_isLift first.helpers second.helpers third.helpers).unique
  · exact (diamond.thirdResultIso_pair third admitted).trans
      (iteratedSwapFirst_pair second.helpers first.helpers third.helpers).symm
  · exact (diamond.thirdResultIso_original third admitted).trans
      (iteratedSwapFirst_third second.helpers first.helpers third.helpers).symm

theorem Diamond.cellThree_frame (diamond : Diamond first second accepted accepted')
    (third : HelperFiring levels O state)
    (admitted : (helperStep levels O).Admits (diamond.thirdForward third)) :
    (RunStateGroupoid.endpointMap levels O (diamond.cellThree third admitted)).frame.hom =
      iteratedSwapFirst second.helpers first.helpers third.helpers := by
  rw [diamond.three_endpoint_map third admitted]
  exact diamond.thirdResultIso_is_swap third admitted

variable (first second third : HelperFiring levels O state) (accepted : (helperStep levels O).Admits first)
  {secondAccepted : (helperStep levels O).Admits (helperResidual first accepted second)}
  {thirdAccepted : (helperStep levels O).Admits (helperResidual first accepted third)}
  (inner : Diamond (helperResidual first accepted second) (helperResidual first accepted third)
    secondAccepted thirdAccepted)

def lastForward : (helperStep levels O).toStep.Run state := .cons first accepted inner.forward
def lastBackward : (helperStep levels O).toStep.Run state := .cons first accepted inner.backward

noncomputable def lastWitness :
    (helperTransport levels O).InterchangeWitness (lastForward first second third accepted inner)
      (lastBackward first second third accepted inner) :=
  .later first accepted inner.witness

noncomputable def lastCell :
    Transport.RunRearrangement.Cell (helperTransport levels O) (lastForward first second third accepted inner)
      (lastBackward first second third accepted inner) :=
  Transport.RunRearrangement.generator (helperTransport levels O)
    (.inr (lastWitness first second third accepted inner))

theorem lastCell_frame :
    (RunStateGroupoid.endpointMap levels O (lastCell first second third accepted inner)).frame.hom =
      iteratedSwapLast first.helpers third.helpers second.helpers := by
  unfold lastCell
  rw [RunStateGroupoid.endpointMap_generator]
  rfl

theorem lastCell_events (event : Fin (lastForward first second third accepted inner).word.length) :
    (Transport.RunRearrangement.events (helperTransport levels O)
      (lastCell first second third accepted inner) event).val = ProofRelevantRuns.swapAt 1 event.val := by
  unfold lastCell
  rw [Transport.RunRearrangement.events_generator]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.cellThree_frame
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.lastCell_frame
