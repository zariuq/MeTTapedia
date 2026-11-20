import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextResidual

/-!
# Placing actual interchange witnesses

Licenses on both complete runs suffice. The placed residuals are identified
with the new native residuals, and the retained continuation comparison is
placed explicitly. The resulting witness factors through the existing
canonical generators and exchanges exactly the original two event positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

noncomputable section

def retargetSwap {state : State rules O}
    {first first' second second' : (helperStep levels O).toStep.Run state}
    (left : first = first') (right : second = second')
    (witness : (helperTransport levels O).SwapWitness first second) :
    (helperTransport levels O).SwapWitness first' second' := by
  cases left
  cases right
  exact witness

theorem retargetSwap_depth {state : State rules O}
    {first first' second second' : (helperStep levels O).toStep.Run state}
    (left : first = first') (right : second = second')
    (witness : (helperTransport levels O).SwapWitness first second) :
    (retargetSwap left right witness).depth = witness.depth := by
  cases left
  cases right
  rfl

set_option maxHeartbeats 800000 in
def placeInterchange (extra : Finset O) {state : State rules O}
    {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).InterchangeWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    {placed : (helperTransport levels O).SwapWitness
      (placeRun extra first firstSafe) (placeRun extra second secondSafe) // placed.depth = witness.depth} := by
  induction witness with
  | @here state first second accepted accepted' afterFirst afterSecond close rest =>
      let admittedFirst := admits extra first accepted firstSafe.1.fresh firstSafe.1.queries
      let admittedSecond := admits extra second accepted' secondSafe.1.fresh secondSafe.1.queries
      let leftBoundary := (result extra first accepted firstSafe.1).symm
      let rightBoundary := (result extra second accepted' secondSafe.1).symm
      let leftResidual := firing extra (helperResidual first accepted second)
      let rightResidual := firing extra (helperResidual second accepted' first)
      let admittedLeft := admits extra _ afterFirst firstSafe.2.1.fresh firstSafe.2.1.queries
      let admittedRight := admits extra _ afterSecond secondSafe.2.1.fresh secondSafe.2.1.queries
      let placedTail := placeSimilarity extra (Transport.SimilarityWitness.moveRun close rest)
        firstSafe.2.2 secondSafe.2.2
      let resultTail := castSimilarity
        (result extra _ afterFirst firstSafe.2.1).symm
        (result extra _ afterSecond secondSafe.2.1).symm placedTail
      let castTail := castSimilarity
        ((helperStep levels O).toStep.castResult leftBoundary leftResidual admittedLeft).symm
        ((helperStep levels O).toStep.castResult rightBoundary rightResidual admittedRight).symm resultTail
      have alikeLeft : (helperTransport levels O).Alike
          (helperResidual (firing extra first) admittedFirst (firing extra second))
          (leftBoundary ▸ leftResidual) := by
        rw [residual_placed extra first second accepted firstSafe.1]
        exact Transport.Alike.refl _
      have alikeRight : (helperTransport levels O).Alike
          (helperResidual (firing extra second) admittedSecond (firing extra first))
          (rightBoundary ▸ rightResidual) := by
        rw [residual_placed extra second first accepted' secondSafe.1]
        exact Transport.Alike.refl _
      let actual := Transport.SwapWitness.here (T := helperTransport levels O)
        admittedFirst admittedSecond alikeLeft
        ((helperStep levels O).toStep.castAdmits leftBoundary leftResidual admittedLeft)
        alikeRight ((helperStep levels O).toStep.castAdmits rightBoundary rightResidual admittedRight) castTail
      have leftRun :
          (Step.Run.cons (firing extra first) admittedFirst
            (.cons (leftBoundary ▸ leftResidual)
              ((helperStep levels O).toStep.castAdmits leftBoundary leftResidual admittedLeft)
              (((helperStep levels O).toStep.castResult leftBoundary leftResidual admittedLeft).symm ▸
                ((result extra _ afterFirst firstSafe.2.1).symm ▸ placeRun extra rest firstSafe.2.2)))) =
            placeRun extra (.cons first accepted (.cons (helperResidual first accepted second) afterFirst rest)) firstSafe := by
        simp only [placeRun, Step.castRun_cons]
        rfl
      have rightRun :
          (Step.Run.cons (firing extra second) admittedSecond
            (.cons (rightBoundary ▸ rightResidual)
              ((helperStep levels O).toStep.castAdmits rightBoundary rightResidual admittedRight)
              (((helperStep levels O).toStep.castResult rightBoundary rightResidual admittedRight).symm ▸
                ((result extra _ afterSecond secondSafe.2.1).symm ▸
                  placeRun extra ((helperTransport levels O).moveRun close rest) secondSafe.2.2)))) =
            placeRun extra (.cons second accepted'
              (.cons (helperResidual second accepted' first) afterSecond ((helperTransport levels O).moveRun close rest))) secondSafe := by
        simp only [placeRun, Step.castRun_cons]
        rfl
      exact ⟨retargetSwap leftRun rightRun actual, retargetSwap_depth leftRun rightRun actual⟩
  | later candidate accepted tail ih =>
      let placed := ih firstSafe.2 secondSafe.2
      let casted := castSwap (result extra candidate accepted firstSafe.1).symm placed.val
      refine ⟨.later (firing extra candidate)
        (admits extra candidate accepted firstSafe.1.fresh firstSafe.1.queries) casted, ?_⟩
      change casted.depth + 1 = tail.depth + 1
      exact congrArg (· + 1) ((castSwap_depth _ placed.val).trans placed.property)

def interchangeCell (extra : Finset O) {state : State rules O}
    {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).InterchangeWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    Transport.RunRearrangement.Cell (helperTransport levels O)
      (placeRun extra first firstSafe) (placeRun extra second secondSafe) :=
  (placeInterchange extra witness firstSafe secondSafe).val.cell

theorem interchange_event (extra : Finset O) {state : State rules O}
    {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).InterchangeWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second)
    (event : Fin (placeRun extra first firstSafe).word.length) :
    (Transport.RunRearrangement.events (helperTransport levels O)
      (interchangeCell extra witness firstSafe secondSafe) event).val = witness.position event.val := by
  exact (Transport.SwapWitness.cell_events (placeInterchange extra witness firstSafe secondSafe).val event).trans
    (congrArg (fun depth => ProofRelevantRuns.swapAt depth event.val)
      (placeInterchange extra witness firstSafe secondSafe).property)

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.interchange_event
