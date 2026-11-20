import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextRuns

/-!
# Placing witnessed similarities of actual dependent runs

The context license is checked on both executions. Every retained stage
comparison is then placed using the same contextual isomorphism and helper
comparison. The construction includes the result-state equalities required
by the complete placed continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

theorem alike (extra : Finset O) {state : State rules O}
    {first second : HelperFiring levels O state} (same : HelperAlike levels O first second) :
    HelperAlike levels O (firing extra first) (firing extra second) := by
  obtain ⟨witness⟩ := same
  exact ⟨⟨witness.frame, witness.commutes, witness.data⟩⟩

theorem move_firing (extra : Finset O) {source target : State rules O}
    (comparison : PlainIso levels source target) (candidate : HelperFiring levels O source) :
    (firing extra candidate).move (placeIso extra comparison) = firing extra (candidate.move comparison) := rfl

noncomputable section

def castSimilarity {source source' target target' : State rules O}
    (left : source = source') (right : target = target')
    {first : (helperStep levels O).toStep.Run source}
    {second : (helperStep levels O).toStep.Run target}
    (witness : (helperTransport levels O).SimilarityWitness first second) :
    (helperTransport levels O).SimilarityWitness (left ▸ first) (right ▸ second) := by
  cases left
  cases right
  exact witness

def placeSimilarity (extra : Finset O) {source target : State rules O}
    {first : (helperStep levels O).toStep.Run source}
    {second : (helperStep levels O).toStep.Run target}
    (witness : (helperTransport levels O).SimilarityWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    (helperTransport levels O).SimilarityWitness
      (placeRun extra first firstSafe) (placeRun extra second secondSafe) := by
  induction witness with
  | nil comparison => exact .nil (placeIso extra comparison)
  | @cons s t one two accepted accepted' rest rest' comparison same tail ih =>
      refine .cons (placeIso extra comparison) (alike extra same) ?_
      exact castSimilarity (result extra one accepted firstSafe.1).symm
        (result extra two accepted' secondSafe.1).symm (ih firstSafe.2 secondSafe.2)

theorem placed_similar (extra : Finset O) {source target : State rules O}
    {first : (helperStep levels O).toStep.Run source}
    {second : (helperStep levels O).toStep.Run target}
    (same : (helperTransport levels O).Similar first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second) :
    (helperTransport levels O).Similar
      (placeRun extra first firstSafe) (placeRun extra second secondSafe) := by
  obtain ⟨witness⟩ := (Transport.SimilarityWitness.nonempty_iff first second).mpr same
  exact (placeSimilarity extra witness firstSafe secondSafe).similar

theorem placeSimilarity_event (extra : Finset O) {source target : State rules O}
    {first : (helperStep levels O).toStep.Run source}
    {second : (helperStep levels O).toStep.Run target}
    (witness : (helperTransport levels O).SimilarityWitness first second)
    (firstSafe : RunSafe extra first) (secondSafe : RunSafe extra second)
    (event : Fin (placeRun extra first firstSafe).word.length) :
    ((placeSimilarity extra witness firstSafe secondSafe).events event).val = event.val := rfl

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.placed_similar
