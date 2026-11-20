import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextFunctor
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunWitnessBoundaries

/-!
# Actual helper boundary maps under contextual placement

Packed contextual maps retain their source and target frames. This permits
comparison through the equalities of complete placed result states without
silently identifying those states definitionally. Placing a witnessed
similarity or interchange preserves its original contextual map.
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
  {levels : LevelModel rules L} {O : Type}

def frameMap {source target : State rules O} (comparison : PlainIso levels source target) :
    Σ targetFrame : Context rules, Σ sourceFrame : Context rules, targetFrame ≅ sourceFrame :=
  ⟨target.frame, source.frame, comparison.frame⟩

theorem iso_hext {source source' target target' : State rules O}
    (left : source = source') (right : target = target')
    {first : PlainIso levels source target} {second : PlainIso levels source' target'}
    (framesAgree : frameMap first = frameMap second) : HEq first second := by
  cases left
  cases right
  apply heq_of_eq
  apply RunStateGroupoid.iso_ext
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj framesAgree).2)).2

variable [DecidableEq O]

theorem castSimilarity_frame {source source' target target' : State rules O}
    (left : source = source') (right : target = target')
    {first : (helperStep levels O).toStep.Run source} {second : (helperStep levels O).toStep.Run target}
    (witness : (helperTransport levels O).SimilarityWitness first second) :
    frameMap (castSimilarity left right witness).lastIso = frameMap witness.lastIso := by
  cases left
  cases right
  rfl

theorem placeSimilarity_frame (extra : Finset O) {source target : State rules O}
    {first : (helperStep levels O).toStep.Run source} {second : (helperStep levels O).toStep.Run target}
    (witness : (helperTransport levels O).SimilarityWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    frameMap (placeSimilarity extra witness firstSafe secondSafe).lastIso = frameMap witness.lastIso := by
  induction witness with
  | nil comparison => rfl
  | cons comparison alike tail ih =>
      exact (castSimilarity_frame _ _ _).trans (ih firstSafe.2 secondSafe.2)

theorem castSwap_frame {source target : State rules O} (same : source = target)
    {first second : (helperStep levels O).toStep.Run source}
    (witness : (helperTransport levels O).SwapWitness first second) :
    frameMap (castSwap same witness).lastIso = frameMap witness.lastIso := by
  cases same
  rfl

theorem retargetSwap_frame {state : State rules O}
    {first first' second second' : (helperStep levels O).toStep.Run state}
    (left : first = first') (right : second = second')
    (witness : (helperTransport levels O).SwapWitness first second) :
    frameMap (retargetSwap left right witness).lastIso = frameMap witness.lastIso := by
  cases left
  cases right
  rfl

set_option maxHeartbeats 800000 in
theorem placeInterchange_frame (extra : Finset O) {state : State rules O}
    {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).InterchangeWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    frameMap (placeInterchange extra witness firstSafe secondSafe).val.lastIso = frameMap witness.lastIso := by
  induction witness with
  | here accepted accepted' afterFirst afterSecond close rest =>
      simp only [placeInterchange, retargetSwap_frame, Transport.SwapWitness.lastIso,
        castSimilarity_frame, placeSimilarity_frame, Transport.InterchangeWitness.lastIso]
  | later candidate accepted tail ih =>
      exact (castSwap_frame _ _).trans (ih firstSafe.2 secondSafe.2)

theorem interchangeCell_frame (extra : Finset O) {state : State rules O}
    {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).InterchangeWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    frameMap (RunStateGroupoid.endpointMap levels O (interchangeCell extra witness firstSafe secondSafe)) =
      frameMap witness.lastIso := by
  unfold interchangeCell
  rw [RunStateGroupoid.swap_cell_boundary]
  exact placeInterchange_frame extra witness firstSafe secondSafe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.interchangeCell_frame
