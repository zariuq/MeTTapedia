import Mettapedia.Computability.CantorSpace
import Mettapedia.Logic.WorldModel.Generative

/-!
# Open-ended world-model observations

An open-ended world is primary; finite stages are observations of it.  This
file does not identify an infinite world with an arbitrary family of finite
snapshots.  Instead, one observation system supplies the restriction laws that
every snapshot of a real world must satisfy.

Finite cylinder properties are useful and decidable at a declared stage.  The
negative control proves that even the elementary property "some future bit is
true" is not determined by any fixed finite prefix of Cantor space.
-/

namespace Mettapedia.Logic.WorldModel.OpenEnded

open Mettapedia.Logic.WorldModel.Generative

universe uWorld uSnapshot

/-- A coherent family of finite observations of one primary world type. -/
structure PrefixObservation (World : Type uWorld) where
  Snapshot : Nat → Type uSnapshot
  observe : (stage : Nat) → World → Snapshot stage
  restrict : ∀ {small large : Nat}, small ≤ large → Snapshot large → Snapshot small
  observe_restrict : ∀ {small large : Nat} (h : small ≤ large) (world : World),
    restrict h (observe large world) = observe small world

/-- A property determined by one finite stage of an open-ended world. -/
def CylinderProperty {World : Type uWorld}
    (observation : PrefixObservation World)
    (stage : Nat) (localProperty : observation.Snapshot stage → Prop) :
    World → Prop :=
  fun world => localProperty (observation.observe stage world)

/-- Some finite observation completely determines the property. -/
def FinitelyDetermined {World : Type uWorld}
    (observation : PrefixObservation World) (property : World → Prop) : Prop :=
  ∃ stage, ∃ localProperty : observation.Snapshot stage → Prop,
    ∀ world, property world ↔
      localProperty (observation.observe stage world)

/-- At every finite stage, two primary worlds remain observationally equal but
disagree on the property. -/
def HasUnresolvedTail {World : Type uWorld}
    (observation : PrefixObservation World) (property : World → Prop) : Prop :=
  ∀ stage, ∃ positiveWorld negativeWorld,
    observation.observe stage positiveWorld =
      observation.observe stage negativeWorld ∧
    property positiveWorld ∧ ¬ property negativeWorld

theorem cylinderProperty_finitelyDetermined
    {World : Type uWorld} (observation : PrefixObservation World)
    (stage : Nat) (localProperty : observation.Snapshot stage → Prop) :
    FinitelyDetermined observation
      (CylinderProperty observation stage localProperty) := by
  exact ⟨stage, localProperty, fun _ => Iff.rfl⟩

/-- A permanently unresolved tail obstructs every proposed finite-stage
factorization. -/
theorem hasUnresolvedTail_not_finitelyDetermined
    {World : Type uWorld} {observation : PrefixObservation World}
    {property : World → Prop}
    (unresolved : HasUnresolvedTail observation property) :
    ¬ FinitelyDetermined observation property := by
  rintro ⟨stage, localProperty, determines⟩
  obtain ⟨positiveWorld, negativeWorld, samePrefix,
    positive, negative⟩ := unresolved stage
  have localPositive :
      localProperty (observation.observe stage positiveWorld) :=
    (determines positiveWorld).mp positive
  have localNegative :
      localProperty (observation.observe stage negativeWorld) := by
    rw [← samePrefix]
    exact localPositive
  exact negative ((determines negativeWorld).mpr localNegative)

/-! ## Consequence at a declared finite observation -/

/-- Entailment of a cylinder property is still ordinary relational entailment;
the stage only states how an auditor may observe the property. -/
def EntailsAt
    {Model : Type*} {Residual : Type*} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (observation : PrefixObservation World)
    (model : Model) (stage : Nat)
    (localProperty : observation.Snapshot stage → Prop) : Prop :=
  Entails semantics model
    (CylinderProperty observation stage localProperty)

theorem entailsAt_iff
    {Model : Type*} {Residual : Type*} {World : Type uWorld}
    (semantics : Semantics Model Residual World)
    (observation : PrefixObservation World)
    (model : Model) (stage : Nat)
    (localProperty : observation.Snapshot stage → Prop) :
    EntailsAt semantics observation model stage localProperty ↔
      ∀ residual world, semantics.realizes model residual world →
        localProperty (observation.observe stage world) :=
  Iff.rfl

/-! ## Cantor-space positive and negative controls -/

open Mettapedia.Computability

/-- Standard finite-prefix observations of a primary Cantor-space world. -/
def cantorPrefixObservation : PrefixObservation CantorSpace where
  Snapshot := fun stage => Fin stage → Bool
  observe := prefixProj
  restrict := fun h => finPrefixProj h
  observe_restrict := by
    intro small large h world
    rfl

/-- The first bit is a genuine cylinder property at stage one. -/
def firstBitTrue (world : CantorSpace) : Prop := world 0 = true

theorem firstBitTrue_finitelyDetermined :
    FinitelyDetermined cantorPrefixObservation firstBitTrue := by
  refine ⟨1, fun snapshot => snapshot ⟨0, by omega⟩ = true, ?_⟩
  intro world
  rfl

/-- An open-tail property: some coordinate, with no fixed horizon, is true. -/
def someBitTrue (world : CantorSpace) : Prop :=
  ∃ coordinate, world coordinate = true

theorem someBitTrue_hasUnresolvedTail :
    HasUnresolvedTail cantorPrefixObservation someBitTrue := by
  intro stage
  let positiveWorld : CantorSpace := fun coordinate => decide (coordinate = stage)
  let negativeWorld : CantorSpace := fun _ => false
  refine ⟨positiveWorld, negativeWorld, ?_, ?_, ?_⟩
  · funext coordinate
    simp [cantorPrefixObservation, prefixProj, positiveWorld, negativeWorld,
      Nat.ne_of_lt coordinate.isLt]
  · exact ⟨stage, by simp [positiveWorld]⟩
  · simp [someBitTrue, negativeWorld]

/-- No fixed finite prefix decides whether a true bit will ever occur. -/
theorem someBitTrue_not_finitelyDetermined :
    ¬ FinitelyDetermined cantorPrefixObservation someBitTrue :=
  hasUnresolvedTail_not_finitelyDetermined someBitTrue_hasUnresolvedTail

#print axioms hasUnresolvedTail_not_finitelyDetermined
#print axioms firstBitTrue_finitelyDetermined
#print axioms someBitTrue_not_finitelyDetermined

end Mettapedia.Logic.WorldModel.OpenEnded
