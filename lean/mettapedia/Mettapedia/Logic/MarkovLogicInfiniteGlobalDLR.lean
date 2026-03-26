import Mettapedia.Logic.MarkovLogicInfiniteLimitFamily

/-!
# Infinite MLN Global Candidate Measures and Local-Query DLR Consistency

This module states the first honest global-consistency notion supported by the
current infinite-MLN development.

We do **not** yet formalize full regular-conditional-probability DLR semantics.
Instead, we isolate the local-query consequence that the current machinery can
already support:

- finite-volume kernels along an exhaustion,
- a global probability measure on `Atom → Bool`,
- convergence of the finite-volume local query laws to the global local query law.

This is the precise bridge between the newly constructed global candidate
measure and the DLR-facing finite-volume specification layer.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR

open Filter
open MeasureTheory
open scoped Topology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A global probability measure is locally DLR-consistent along an exhaustion
if every finite local query probability along the finite-volume kernel sequence
converges to the corresponding local query probability of the global measure. -/
def LocalQueryDLRConsistent
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ),
    Tendsto
      (fun n => E.finiteVolumeKernelSequence M ξ n (localQueryEvent Λ q))
      atTop
      (nhds ((globalMeasureMassSemantics (Atom := Atom) μ Λ).queryProb q))

/-- Stage marginals compute local query events on any finite region, not just on
the distinguished exhaustion stage itself. -/
theorem stageMarginal_apply_localConstraintSet
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n Λ (localConstraintSet Λ q) =
        E.finiteVolumeKernelSequence M ξ n
          (localQueryEvent (Atom := Atom) Λ q) := by
  rw [Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal]
  rw [localQueryEvent_eq_cylinder Λ q]
  rw [MeasureTheory.cylinder]
  rw [Measure.map_apply (Finset.measurable_restrict Λ)
    (measurableSet_localConstraintSet Λ q)]

/-- A cylinder cluster point of the finite-volume kernels is locally
DLR-consistent. -/
theorem CylinderClusterPoint.localQueryDLRConsistent
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (h : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.CylinderClusterPoint E M ξ μ) :
    LocalQueryDLRConsistent E M ξ μ := by
  intro Λ q
  simpa [LocalQueryDLRConsistent,
    globalMeasureMassSemantics_queryProb (Atom := Atom) (μ := μ) Λ q] using
    h.tendsto_localQueryEvent (Λ := Λ) q

/-- A marginal cluster point is likewise locally DLR-consistent. -/
theorem MarginalClusterPoint.localQueryDLRConsistent
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (h : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.MarginalClusterPoint E M ξ μ) :
    LocalQueryDLRConsistent E M ξ μ := by
  intro Λ q
  have h' := h Λ (localConstraintSet Λ q) (measurableSet_localConstraintSet Λ q)
  have htarget :
      (Measure.map (Finset.restrict Λ) μ) (localConstraintSet Λ q) =
        μ (localQueryEvent Λ q) := by
    simpa [limitMarginal] using
      (limitMarginal_apply_localConstraintSet (Atom := Atom) (μ := μ) Λ q)
  simpa [LocalQueryDLRConsistent,
    stageMarginal_apply_localConstraintSet (Atom := Atom) (ClauseId := ClauseId) E M ξ,
    globalMeasureMassSemantics_queryProb (Atom := Atom) (μ := μ) Λ q,
    htarget] using h'

/-- If a projective family `P` agrees with the finite-dimensional marginals of a
cluster-point measure `μ`, then the canonical projective-limit measure built
from `P` is locally DLR-consistent as well. -/
theorem projectiveLimitMeasure_localQueryDLRConsistent_of_eq
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hEq : projectiveLimitMeasure (Atom := Atom) e P hP = μ) :
    LocalQueryDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  simpa [hEq] using
    (CylinderClusterPoint.localQueryDLRConsistent
      (E := E) (M := M) (ξ := ξ) (μ := μ) hμ)

/-- If a projective family `P` agrees with the finite-dimensional marginals of a
cluster-point measure `μ`, then the canonical projective-limit measure built
from `P` is locally DLR-consistent as well. -/
theorem projectiveLimitMeasure_localQueryDLRConsistent_of_limitMarginal_eq
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    LocalQueryDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hEq := projectiveLimitMeasure_eq_of_limitMarginal_eq
    (Atom := Atom) (μ := μ) e P hP hPμ
  exact projectiveLimitMeasure_localQueryDLRConsistent_of_eq
    (E := E) (M := M) (ξ := ξ) (μ := μ) hμ e P hP hEq

/-- The same inheritance theorem using the marginal-cluster-point frontend. -/
theorem projectiveLimitMeasure_localQueryDLRConsistent_of_marginalClusterPoint
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.MarginalClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    LocalQueryDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hcyl : CylinderClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).2 hμ
  exact projectiveLimitMeasure_localQueryDLRConsistent_of_limitMarginal_eq
    hcyl e P hP hPμ

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR
