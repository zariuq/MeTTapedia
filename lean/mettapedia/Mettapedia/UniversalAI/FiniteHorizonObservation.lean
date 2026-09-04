import Mettapedia.Logic.WorldModel.FiniteHorizonLanguage
import Mettapedia.UniversalAI.InfiniteHistory

/-!
# Finite-horizon observations of infinite interaction histories

An infinite trajectory is the primary object.  Its finite prefixes form a
coherent `PrefixObservation`, so the generic finite-horizon language can ask
bounded questions without replacing the trajectory by a fixed cutoff.

A predicate on one coordinate is an exact finite-horizon formula and remains
exact after extending the horizon.  In contrast, the property that some
future Boolean coordinate is true is not represented by any one such formula.
This gives a positive and a negative control for finite acceleration over an
open-ended interaction semantics.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.FiniteHorizonObservation

open Mettapedia.Logic.WorldModel.OpenEnded
open Mettapedia.Logic.WorldModel.FiniteHorizonLanguage
open Mettapedia.UniversalAI.InfiniteHistory

universe uX

/-- Restrict an infinite dependent trajectory to coordinates at most the
declared stage. -/
def trajectoryPrefixObservation (X : Nat → Type uX) :
    PrefixObservation (TrajectoryOf X) where
  Snapshot := PrefixOf X
  observe := fun _stage trajectory coordinate => trajectory coordinate.1
  restrict := fun {small large} horizon snapshot coordinate =>
    snapshot ⟨coordinate.1, by
      exact Finset.mem_Iic.mpr
        ((Finset.mem_Iic.mp coordinate.2).trans horizon)⟩
  observe_restrict := by
    intro small large horizon trajectory
    rfl

/-- A property of one selected trajectory coordinate, represented at exactly
that observation horizon. -/
def coordinateFormula (X : Nat → Type uX) (coordinate : Nat)
    (predicate : X coordinate → Prop) :
    Formula (trajectoryPrefixObservation X) where
  stage := coordinate
  predicate := fun snapshot =>
    predicate (snapshot
      ⟨coordinate, Finset.mem_Iic.mpr (le_refl coordinate)⟩)

/-- The coordinate formula denotes precisely its declared coordinate
predicate on the primary infinite trajectory. -/
theorem coordinateFormula_meaning_iff (X : Nat → Type uX)
    (coordinate : Nat) (predicate : X coordinate → Prop)
    (trajectory : TrajectoryOf X) :
    (coordinateFormula X coordinate predicate).meaning trajectory ↔
      predicate (trajectory coordinate) :=
  Iff.rfl

/-- Extending the observation horizon preserves the coordinate formula's
meaning. -/
theorem coordinateFormula_lift_meaning_iff (X : Nat → Type uX)
    (coordinate later : Nat) (horizon : coordinate ≤ later)
    (predicate : X coordinate → Prop) (trajectory : TrajectoryOf X) :
    ((coordinateFormula X coordinate predicate).lift horizon).meaning trajectory ↔
      predicate (trajectory coordinate) :=
  ((coordinateFormula X coordinate predicate).lift_meaning_iff
    horizon trajectory).trans
      (coordinateFormula_meaning_iff X coordinate predicate trajectory)

/-! ## Open-tail control -/

abbrev BooleanTrajectory : Type := TrajectoryOf (fun _ => Bool)

/-- A property whose witnessing coordinate may lie beyond every proposed
finite observation horizon. -/
def eventuallyTrue (trajectory : BooleanTrajectory) : Prop :=
  ∃ coordinate, trajectory coordinate = true

/-- At every finite horizon there are two trajectories with the same visible
prefix but opposite `eventuallyTrue` verdicts. -/
theorem eventuallyTrue_hasUnresolvedTail :
    HasUnresolvedTail
      (trajectoryPrefixObservation (fun _ => Bool)) eventuallyTrue := by
  intro stage
  let positive : BooleanTrajectory := fun coordinate =>
    decide (coordinate = stage + 1)
  let negative : BooleanTrajectory := fun _coordinate => false
  refine ⟨positive, negative, ?_, ?_, ?_⟩
  · funext coordinate
    have coordinateLe : coordinate.1 ≤ stage :=
      Finset.mem_Iic.mp coordinate.2
    have coordinateNe : coordinate.1 ≠ stage + 1 :=
      Nat.ne_of_lt (Nat.lt_succ_of_le coordinateLe)
    simp [trajectoryPrefixObservation, positive, negative, coordinateNe]
  · exact ⟨stage + 1, by simp [positive]⟩
  · simp [eventuallyTrue, negative]

/-- No single finite-horizon formula represents the open-tail property on all
infinite Boolean trajectories. -/
theorem eventuallyTrue_not_representable :
    ¬ ∃ formula : Formula
        (trajectoryPrefixObservation (fun _ => Bool)),
      ∀ trajectory, formula.meaning trajectory ↔ eventuallyTrue trajectory := by
  rintro ⟨formula, represents⟩
  apply hasUnresolvedTail_not_finitelyDetermined
      eventuallyTrue_hasUnresolvedTail
  refine ⟨formula.stage, formula.predicate, ?_⟩
  intro trajectory
  exact (represents trajectory).symm

#print axioms coordinateFormula_meaning_iff
#print axioms coordinateFormula_lift_meaning_iff
#print axioms eventuallyTrue_hasUnresolvedTail
#print axioms eventuallyTrue_not_representable

end Mettapedia.UniversalAI.FiniteHorizonObservation
