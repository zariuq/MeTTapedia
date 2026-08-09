import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Transporting carried bisimulations through locally covered embeddings

A map that merely preserves source steps cannot transport bisimulation: the
target may add an unmatched transition at an image state.  `StepCover` names
the exact additional obligation.  Every target step beginning at an image
must lift to a source step whose image is its target.

This condition is local to the image; it does not require a carrier
equivalence or forbid unrelated target states.  It composes, and it transports
the proof-relevant `BisimulationWitness` without erasing the source terms or
the selected matching transitions.
-/

namespace Mettapedia.GSLT.Ultrainfinite

open Mettapedia.GSLT

universe uSource uTarget uCell

/-- A step-preserving map with local reflection of every transition leaving
an image state.  The lifted source target and its equality with the observed
target remain data. -/
structure StepCover (source target : GSLT)
    (mapTerm : source.Term → target.Term) where
  mapStep : ∀ {sourceTerm sourceTarget},
    source.Step sourceTerm sourceTarget →
      target.Step (mapTerm sourceTerm) (mapTerm sourceTarget)
  liftStep : ∀ {sourceTerm targetTerm},
    target.Step (mapTerm sourceTerm) targetTerm →
      ∃ sourceTarget,
        source.Step sourceTerm sourceTarget ∧
          mapTerm sourceTarget = targetTerm

namespace StepCover

/-- Identity covers every one-step transition exactly. -/
def id (system : GSLT) : StepCover system system id where
  mapStep := fun step => step
  liftStep := fun {_sourceTerm targetTerm} step =>
    ⟨targetTerm, step, rfl⟩

/-- Locally covered embeddings compose while retaining both lifted stages. -/
def comp {first middle last : GSLT}
    {earlierMap : first.Term → middle.Term}
    {laterMap : middle.Term → last.Term}
    (earlier : StepCover first middle earlierMap)
    (later : StepCover middle last laterMap) :
    StepCover first last (laterMap ∘ earlierMap) where
  mapStep := fun step => later.mapStep (earlier.mapStep step)
  liftStep := by
    intro sourceTerm targetTerm step
    obtain ⟨middleTarget, middleStep, middleTargetEq⟩ :=
      later.liftStep step
    obtain ⟨sourceTarget, sourceStep, sourceTargetEq⟩ :=
      earlier.liftStep middleStep
    exact ⟨sourceTarget, sourceStep,
      (congrArg laterMap sourceTargetEq).trans middleTargetEq⟩

end StepCover

/-- The transported relation keeps the two source preimages, their image
equalities, and the original relation witness.  Target states without such
preimages are intentionally absent. -/
structure MappedBisimulationRelation
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (mapTerm : source.Term → target.Term)
    (witness : BisimulationWitness.{uCell} source)
    (targetLeft targetRight : target.Term) where
  sourceLeft : source.Term
  sourceRight : source.Term
  left_eq : mapTerm sourceLeft = targetLeft
  right_eq : mapTerm sourceRight = targetRight
  related : witness.Related sourceLeft sourceRight

namespace BisimulationWitness

/-- Transport a carried bisimulation through a locally covered embedding.
The output still carries the source relation witness and all selected
matching successors. -/
noncomputable def map {source target : GSLT}
    {mapTerm : source.Term → target.Term}
    (cover : StepCover source target mapTerm)
    (witness : BisimulationWitness.{uCell} source) :
    BisimulationWitness target where
  Related := MappedBisimulationRelation mapTerm witness
  forward := by
    intro left right related leftTarget step
    rcases related with
      ⟨sourceLeft, sourceRight, leftEq, rightEq, sourceRelated⟩
    have imageStep : target.Step (mapTerm sourceLeft) leftTarget := by
      rw [leftEq]
      exact step
    let sourceTarget := Classical.choose (cover.liftStep imageStep)
    have lifted := Classical.choose_spec (cover.liftStep imageStep)
    have sourceStep := lifted.1
    have targetEq := lifted.2
    let matched := witness.forward sourceRelated sourceStep
    have targetMatched :
        target.Step right (mapTerm matched.otherTarget) := by
      exact rightEq ▸ cover.mapStep matched.step
    exact ⟨mapTerm matched.otherTarget, targetMatched,
      { sourceLeft := sourceTarget
        sourceRight := matched.otherTarget
        left_eq := targetEq
        right_eq := rfl
        related := matched.related }⟩
  backward := by
    intro left right related rightTarget step
    rcases related with
      ⟨sourceLeft, sourceRight, leftEq, rightEq, sourceRelated⟩
    have imageStep : target.Step (mapTerm sourceRight) rightTarget := by
      rw [rightEq]
      exact step
    let sourceTarget := Classical.choose (cover.liftStep imageStep)
    have lifted := Classical.choose_spec (cover.liftStep imageStep)
    have sourceStep := lifted.1
    have targetEq := lifted.2
    let matched := witness.backward sourceRelated sourceStep
    have targetMatched :
        target.Step left (mapTerm matched.otherTarget) := by
      exact leftEq ▸ cover.mapStep matched.step
    exact ⟨mapTerm matched.otherTarget, targetMatched,
      { sourceLeft := matched.otherTarget
        sourceRight := sourceTarget
        left_eq := rfl
        right_eq := targetEq
        related := matched.related }⟩

/-- Related source terms remain bisimilar after a covered translation. -/
theorem map_toBisimilar {source target : GSLT}
    {mapTerm : source.Term → target.Term}
    (cover : StepCover source target mapTerm)
    (witness : BisimulationWitness.{uCell} source)
    {left right : source.Term} (related : witness.Related left right) :
    target.Bisimilar (mapTerm left) (mapTerm right) :=
  (witness.map cover).toBisimilar
    { sourceLeft := left
      sourceRight := right
      left_eq := rfl
      right_eq := rfl
      related := related }

/-- The target bisimulation quotient is the propositional shadow of the
transported carried witness. -/
theorem map_toBisimClass_eq {source target : GSLT}
    {mapTerm : source.Term → target.Term}
    (cover : StepCover source target mapTerm)
    (witness : BisimulationWitness.{uCell} source)
    {left right : source.Term} (related : witness.Related left right) :
    Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass target
        (mapTerm left) =
      Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass target
        (mapTerm right) :=
  (witness.map cover).toBisimClass_eq
    { sourceLeft := left
      sourceRight := right
      left_eq := rfl
      right_eq := rfl
      related := related }

end BisimulationWitness

end Mettapedia.GSLT.Ultrainfinite
