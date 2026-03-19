import Mathlib.MeasureTheory.Constructions.Cylinders
import Mettapedia.Logic.PLNMarkovLogicInfiniteProjective

/-!
# Infinite MLN Local Queries as Cylinder Events

This module bridges the bespoke local-query events used in the infinite MLN
development to Mathlib's standard cylinder-event language.

This matters because the literature's existence theorem is formulated via
cluster points of the finite-volume specifications on cylinder events.  To line
up with that route, we show:

- local query events are cylinders,
- hence they lie in `measurableCylinders`,
- and the stage marginals compute exactly their finite-dimensional masses.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders

open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteProjective
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive

/-- The base set of local assignments satisfying a local finite constraint
query. -/
def localConstraintSet
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Set (LocalAssignment Atom Λ) :=
  {x | satisfiesConstraints x q}

theorem measurableSet_localConstraintSet
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    MeasurableSet (localConstraintSet Λ q) := by
  unfold localConstraintSet
  exact (Set.to_countable {x : LocalAssignment Atom Λ | satisfiesConstraints x q}).measurableSet

theorem localQueryEvent_eq_cylinder
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    localQueryEvent (Atom := Atom) Λ q =
      MeasureTheory.cylinder Λ (localConstraintSet Λ q) := by
  ext ω
  have hrestrict : worldRestriction Λ ω = Finset.restrict Λ ω := by
    funext i
    rfl
  simp [localQueryEvent, localConstraintSet, MeasureTheory.cylinder, hrestrict]

theorem localQueryEvent_mem_measurableCylinders
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    localQueryEvent (Atom := Atom) Λ q ∈
      MeasureTheory.measurableCylinders (fun _ : Atom => Bool) := by
  rw [localQueryEvent_eq_cylinder Λ q]
  exact MeasureTheory.cylinder_mem_measurableCylinders _ _ (measurableSet_localConstraintSet Λ q)

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

theorem stageMarginal_apply_localConstraintSet
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (q : LocalConstraintQuery Atom (E.region n)) :
    Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n (E.region n) (localConstraintSet (E.region n) q) =
      E.finiteVolumeKernelSequence M ξ n
        (localQueryEvent (Atom := Atom) (E.region n) q) := by
  rw [Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal]
  rw [localQueryEvent_eq_cylinder (E.region n) q]
  rw [MeasureTheory.cylinder]
  rw [Measure.map_apply (Finset.measurable_restrict (E.region n))
    (measurableSet_localConstraintSet (E.region n) q)]

end RegionExhaustion

end Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders
