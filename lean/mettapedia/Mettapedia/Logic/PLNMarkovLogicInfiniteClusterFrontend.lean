import Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders

/-!
# Infinite MLN Cluster-Point Frontend

This module adds the first honest frontend for the global existence step in the
infinite-MLN development.

The Singla--Domingos / Georgii route does **not** use literal eventual
stabilization of finite-volume kernels. Instead it reasons about cluster points
of the finite-volume specifications on cylinder events. Here we package the
corresponding Lean-level notions:

- convergence on cylinder events,
- convergence of finite-dimensional marginals,
- equivalence between the two in our Boolean product setting,
- local-query convergence as a corollary via the cylinder bridge.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend

open Filter
open MeasureTheory
open scoped Topology
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteProjective
open Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

abbrev BoolCoord (Atom : Type*) (i : Atom) :=
  Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i

/-- A candidate global measure is a cluster point of the finite-volume kernel
sequence on cylinder events if cylinder probabilities converge to its cylinder
probabilities. -/
def CylinderClusterPoint
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom)) : Prop :=
  ∀ (I : Finset Atom) (S : Set (∀ i : I, BoolCoord Atom i)),
    MeasurableSet S →
      Tendsto
        (fun n => E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S))
        atTop
        (nhds (μ (MeasureTheory.cylinder I S)))

/-- Equivalent finite-dimensional formulation: the stage marginals converge
pointwise on measurable sets to the marginals of `μ`. -/
def MarginalClusterPoint
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom)) : Prop :=
  ∀ (I : Finset Atom) (S : Set (∀ i : I, BoolCoord Atom i)),
    MeasurableSet S →
      Tendsto
        (fun n =>
          Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
            E M ξ n I S)
        atTop
        (nhds ((μ.map I.restrict) S))

theorem cylinderClusterPoint_iff_marginalClusterPoint
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom)) :
    CylinderClusterPoint E M ξ μ ↔ MarginalClusterPoint E M ξ μ := by
  constructor
  · intro h
    show MarginalClusterPoint E M ξ μ
    intro I S hS
    have h' := h I S hS
    simpa [MarginalClusterPoint,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal,
      MeasureTheory.cylinder, Measure.map_apply (Finset.measurable_restrict I) hS]
      using h'
  · intro h
    show CylinderClusterPoint E M ξ μ
    intro I S hS
    have h' := h I S hS
    simpa [CylinderClusterPoint,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal,
      MeasureTheory.cylinder, Measure.map_apply (Finset.measurable_restrict I) hS]
      using h'

theorem CylinderClusterPoint.tendsto_localQueryEvent
    {E : RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : CylinderClusterPoint E M ξ μ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Tendsto
      (fun n => E.finiteVolumeKernelSequence M ξ n
        (localQueryEvent Λ q))
      atTop
      (nhds (μ (localQueryEvent Λ q))) := by
  simpa [localQueryEvent_eq_cylinder Λ q] using
    h Λ (localConstraintSet Λ q) (measurableSet_localConstraintSet Λ q)

theorem MarginalClusterPoint.tendsto_localConstraintSet
    {E : RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : MarginalClusterPoint E M ξ μ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Tendsto
      (fun n =>
        Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          E M ξ n Λ (localConstraintSet Λ q))
      atTop
      (nhds ((μ.map Λ.restrict) (localConstraintSet Λ q))) :=
  h Λ (localConstraintSet Λ q) (measurableSet_localConstraintSet Λ q)

end RegionExhaustion

end Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend
