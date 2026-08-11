import Mathlib.CategoryTheory.Functor.OfSequence
import Mettapedia.GSLT.Dynamics.IndexedQueryRevision

/-!
# Canaries for indexed theory growth and world revision

The source stage permits one increment event.  The target stage preserves it
and adds a distinct jump event.  Thus ordinary source revision commutes with
stage transport, while the extension is intentionally forward-only: it
cannot be presented as an exact translation with the same revision map.
-/

namespace Mettapedia.GSLT.Dynamics.IndexedQueryRevision.Canary

open CategoryTheory
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.IndexedQueryRevision
open Mettapedia.GSLT.IndexedOperational

private def sourceTheory : Theory where
  World := Nat
  Revision := Unit
  Query := Unit
  Observation := Nat
  Step := fun _ source target => target = source + 1
  query := fun world _ => world

private def targetTheory : Theory where
  World := Nat
  Revision := Bool
  Query := Unit
  Observation := Nat
  Step := fun revision source target =>
    if revision then target = source + 2 else target = source + 1
  query := fun world _ => world

private def targetAddTwo (world : targetTheory.World) : targetTheory.World := by
  change Nat at world ⊢
  exact world + 2

/-- The old increment meaning is preserved by the richer target stage. -/
private def sourceTargetTranslation : Translation sourceTheory targetTheory where
  mapWorld := id
  mapRevision := fun _ => false
  mapQuery := id
  mapObservation := id
  step_map := by
    intro revision source target step
    simpa [sourceTheory, targetTheory] using step
  query_natural := fun _ _ => rfl

private def stageTheory : Nat → QueryableTheory
  | 0 => ⟨sourceTheory⟩
  | _ + 1 => ⟨targetTheory⟩

private def stageArrow : ∀ stage : Nat,
    stageTheory stage ⟶ stageTheory (stage + 1)
  | 0 => sourceTargetTranslation
  | _ + 1 => Translation.id targetTheory

private def diagram : Diagram Nat :=
  CategoryTheory.Functor.ofSequence stageArrow

private def firstGrowth : (0 : Nat) ⟶ 1 :=
  CategoryTheory.homOfLE (by omega)

private theorem firstGrowth_map :
    diagram.map firstGrowth = sourceTargetTranslation := by
  exact CategoryTheory.Functor.ofSequence_map_homOfLE_succ stageArrow 0

private def sourceWorld7 : (diagram.obj 0).theory.World := by
  change Nat
  exact 7

private def sourceWorld8 : (diagram.obj 0).theory.World := by
  change Nat
  exact 8

private def sourceQuery : (diagram.obj 0).theory.Query := by
  change Unit
  exact ()

/-- Positive: the complete query result is unchanged when transported to the
new theory stage. -/
theorem query_survives_theory_growth :
    (diagram.obj 1).theory.query
        (transportWorld diagram firstGrowth sourceWorld7)
        ((diagram.map firstGrowth).mapQuery sourceQuery) =
      (diagram.map firstGrowth).mapObservation
        ((diagram.obj 0).theory.query sourceWorld7 sourceQuery) := by
  exact query_transport diagram firstGrowth sourceWorld7 sourceQuery

private theorem incrementStep :
    (diagram.obj 0).theory.Step () sourceWorld7 sourceWorld8 := by
  change (8 : Nat) = 7 + 1
  rfl

private def incrementSemanticStep :=
  revisionSemanticStep diagram 0 incrementStep

/-- Positive: revise-then-extend and extend-then-revise are the two sides of
the generated proof-relevant naturality diamond. -/
def incrementGrowthDiamond :=
  revisionNaturalityDiamond diagram firstGrowth incrementStep

/-- Both paths contain one world revision and one theory-stage crossing, in
opposite orders. -/
theorem increment_and_growth_paths_have_equal_length :
    (Command.reduceBeforeRoute diagram.toOperational firstGrowth
        incrementSemanticStep).length =
      (Command.transportBeforeRoute diagram.toOperational firstGrowth
        incrementSemanticStep).length := by
  rfl

/-- Negative: the target's new jump event prevents the forward extension from
being reclassified as an exact translation with the same revision map. -/
theorem added_revision_prevents_exactness :
    ¬ ∃ exact : ExactTranslation sourceTheory targetTheory,
      exact.toTranslation.mapRevision =
        sourceTargetTranslation.mapRevision := by
  rintro ⟨exact, sameRevisionMap⟩
  let sourceZero : sourceTheory.World := by
    change Nat
    exact 0
  let jumpTarget : targetTheory.World :=
    targetAddTwo (exact.toTranslation.mapWorld sourceZero)
  have jump : targetTheory.Step true
      (exact.toTranslation.mapWorld sourceZero) jumpTarget := by
    simp [targetTheory, jumpTarget, targetAddTwo]
  obtain ⟨sourceRevision, sourceTarget, sourceStep, revisionEq, targetEq⟩ :=
    exact.liftStep jump
  have mappedFalse : exact.toTranslation.mapRevision sourceRevision = false := by
    cases sourceRevision
    simpa [sourceTargetTranslation] using congrFun sameRevisionMap ()
  have falseEqualsTrue : false = true := mappedFalse.symm.trans revisionEq
  exact Bool.false_ne_true falseEqualsTrue

#print axioms query_survives_theory_growth
#print axioms increment_and_growth_paths_have_equal_length
#print axioms added_revision_prevents_exactness

end Mettapedia.GSLT.Dynamics.IndexedQueryRevision.Canary
