import Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend
import Mettapedia.Logic.MarkovLogicCountableProjectiveLimit
import Mettapedia.Logic.MarkovLogicAbstract

/-!
# Infinite MLN Limiting Projective Families

This module packages the finite-dimensional marginals of a candidate global
measure as a projective family, and identifies those marginals on the local
constraint events used throughout the infinite-MLN development.

It does not yet prove existence of a global Gibbs measure.  Instead it provides
the exact "limit family" object that a later cluster-point/existence theorem
should target.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteLimitFamily

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
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicCountableProjectiveLimit
open Mettapedia.Logic.MarkovLogicAbstract

namespace RegionExhaustion

variable {Atom : Type*}

abbrev BoolCoord (Atom : Type*) (i : Atom) :=
  Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i

/-- The finite-dimensional marginals of a candidate global measure. -/
noncomputable def limitMarginal
    (μ : Measure (InfiniteWorld Atom))
    (I : Finset Atom) : Measure (∀ i : I, BoolCoord Atom i) :=
  μ.map I.restrict

instance limitMarginal_isProbability
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    (I : Finset Atom) :
    IsProbabilityMeasure (limitMarginal (Atom := Atom) μ I) := by
  dsimp [limitMarginal]
  exact Measure.isProbabilityMeasure_map (Finset.measurable_restrict I).aemeasurable

/-- For a countable atom type, a projective family of finite-dimensional
marginals induces a canonical candidate global measure via the generic
countable projective-limit theorem. -/
noncomputable def projectiveLimitMeasure
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (_hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    Measure (InfiniteWorld Atom) :=
  countableProjectiveLimit e P

instance projectiveLimitMeasure_isProbability
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    IsProbabilityMeasure (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  letI : ∀ n, IsProbabilityMeasure
      (Mettapedia.Logic.MarkovLogicCountableProjectiveExtension.prefixFamily e P n) :=
    fun n =>
      Mettapedia.Logic.MarkovLogicCountableProjectiveExtension.prefixFamily_isProbability
        e P n
  letI : IsProbabilityMeasure
      (natProjectiveLimit
        (μ := Mettapedia.Logic.MarkovLogicCountableProjectiveExtension.prefixFamily e P)) := by
    delta natProjectiveLimit
    infer_instance
  unfold projectiveLimitMeasure countableProjectiveLimit
  unfold Mettapedia.Logic.MarkovLogicCountableProjectiveExtension.transportMeasure
  exact Measure.isProbabilityMeasure_map
    ((MeasurableEquiv.piCongrLeft (fun _ : Atom => Bool) e).measurable.aemeasurable)

/-- The candidate global measure constructed from a countable projective family
is its projective limit. -/
theorem isProjectiveLimit_projectiveLimitMeasure
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    MeasureTheory.IsProjectiveLimit
      (projectiveLimitMeasure (Atom := Atom) e P hP) P :=
  countableProjectiveLimit_isProjectiveLimit e P hP

/-- Therefore the `limitMarginal` of the candidate global measure recovers the
original projective family. -/
theorem limitMarginal_projectiveLimitMeasure
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (I : Finset Atom) :
    limitMarginal (Atom := Atom)
      (projectiveLimitMeasure (Atom := Atom) e P hP) I = P I := by
  simpa [limitMarginal] using
    isProjectiveLimit_projectiveLimitMeasure (Atom := Atom) e P hP I

/-- The finite-dimensional marginals of any global measure form a projective
family. -/
theorem isProjectiveMeasureFamily_limitMarginal
    (μ : Measure (InfiniteWorld Atom)) :
    MeasureTheory.IsProjectiveMeasureFamily
      (ι := Atom) (α := BoolCoord Atom) (limitMarginal (Atom := Atom) μ) := by
  intro I J hJI
  unfold limitMarginal
  rw [Measure.map_map
    (Finset.measurable_restrict₂ (X := BoolCoord Atom) hJI)
    (Finset.measurable_restrict I)]
  congr 1

/-- Any global measure is the projective limit of its own finite-dimensional
marginals. -/
theorem isProjectiveLimit_limitMarginal
    (μ : Measure (InfiniteWorld Atom)) :
    MeasureTheory.IsProjectiveLimit
      (ι := Atom) (α := BoolCoord Atom) μ (limitMarginal (Atom := Atom) μ) := by
  intro I
  rfl

/-- If a probability measure `μ` has finite-dimensional marginals exactly equal
to a projective family `P`, then the canonical countable projective-limit
measure built from `P` is literally equal to `μ`. -/
theorem projectiveLimitMeasure_eq_of_limitMarginal_eq
    (μ : Measure (InfiniteWorld Atom))
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal (Atom := Atom) μ I) :
    projectiveLimitMeasure (Atom := Atom) e P hP = μ := by
  have hμP : MeasureTheory.IsProjectiveLimit
      (ι := Atom) (α := BoolCoord Atom) μ P := by
    intro I
    rw [hPμ I]
    exact isProjectiveLimit_limitMarginal (Atom := Atom) μ I
  exact MeasureTheory.IsProjectiveLimit.unique
    (P := P)
    (μ := projectiveLimitMeasure (Atom := Atom) e P hP)
    (ν := μ)
    (isProjectiveLimit_projectiveLimitMeasure (Atom := Atom) e P hP)
    hμP

/-- The limiting marginal on a local constraint set is exactly the probability
of the corresponding local query event. -/
theorem limitMarginal_apply_localConstraintSet
    [DecidableEq Atom]
    (μ : Measure (InfiniteWorld Atom))
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    limitMarginal (Atom := Atom) μ Λ (localConstraintSet Λ q) =
      μ (localQueryEvent Λ q) := by
  unfold limitMarginal
  rw [localQueryEvent_eq_cylinder Λ q]
  rw [MeasureTheory.cylinder]
  rw [Measure.map_apply (Finset.measurable_restrict Λ)
    (measurableSet_localConstraintSet Λ q)]

/-- The countable projective-limit construction therefore agrees with the
projective family on local query events. -/
theorem projectiveLimitMeasure_localQueryEvent
    [DecidableEq Atom]
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    projectiveLimitMeasure (Atom := Atom) e P hP (localQueryEvent Λ q) =
      P Λ (localConstraintSet Λ q) := by
  rw [← limitMarginal_apply_localConstraintSet
    (Atom := Atom)
    (μ := projectiveLimitMeasure (Atom := Atom) e P hP) Λ q]
  exact congrArg (fun ν => ν (localConstraintSet Λ q))
    (limitMarginal_projectiveLimitMeasure (Atom := Atom) e P hP Λ)

/-- Any probability measure on infinite Boolean worlds induces the same
local-query `MassSemantics` interface used by the finite-volume DLR layer. -/
noncomputable def globalMeasureMassSemantics
    [DecidableEq Atom]
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    (Λ : Region Atom) :
    MassSemantics (LocalConstraintQuery Atom Λ) where
  queryMass := fun q => μ (localQueryEvent Λ q)
  totalMass := 1
  queryMass_le_total := by
    intro q
    letI := ‹IsProbabilityMeasure μ›
    have hmono :
        μ (localQueryEvent (Atom := Atom) Λ q) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ (localQueryEvent (Atom := Atom) Λ q))
    simpa using hmono
  totalMass_ne_top := ENNReal.one_ne_top

/-- For a probability measure on infinite worlds, the induced local-query
semantics computes query probabilities by direct evaluation of the local
query event. -/
theorem globalMeasureMassSemantics_queryProb
    [DecidableEq Atom]
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (globalMeasureMassSemantics (Atom := Atom) μ Λ).queryProb q =
      μ (localQueryEvent Λ q) := by
  simp [globalMeasureMassSemantics, MassSemantics.queryProb]

/-- The candidate global measure obtained from a countable projective family
therefore has the expected local-query probabilities. -/
theorem projectiveLimitMeasure_queryProb_eq_family
    [DecidableEq Atom]
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (globalMeasureMassSemantics (Atom := Atom)
      (projectiveLimitMeasure (Atom := Atom) e P hP) Λ).queryProb q =
        P Λ (localConstraintSet Λ q) := by
  rw [globalMeasureMassSemantics_queryProb]
  exact projectiveLimitMeasure_localQueryEvent (Atom := Atom) e P hP Λ q

/-- Through the abstract WM bridge, the singleton state built from the global
candidate measure has query strength equal to the corresponding finite-dimensional
marginal on each local query. -/
theorem projectiveLimitMeasure_queryStrength_eq_family
    [DecidableEq Atom]
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
      ({globalMeasureMassSemantics (Atom := Atom)
        (projectiveLimitMeasure (Atom := Atom) e P hP) Λ} :
          MassState (LocalConstraintQuery Atom Λ)) q =
        P Λ (localConstraintSet Λ q) := by
  rw [MassState.queryStrength_singleton_eq_queryProb]
  exact projectiveLimitMeasure_queryProb_eq_family (Atom := Atom) e P hP Λ q

/-- A marginal cluster point converges on local constraint sets to the limiting
projective family induced by the candidate global measure. -/
theorem MarginalClusterPoint.tendsto_limitMarginal_localConstraintSet
    {ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.MarginalClusterPoint E M ξ μ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Tendsto
      (fun n =>
        Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
          E M ξ n Λ (localConstraintSet Λ q))
      atTop
      (nhds (limitMarginal (Atom := Atom) μ Λ (localConstraintSet Λ q))) := by
  simpa [limitMarginal] using
    h.tendsto_localConstraintSet (Λ := Λ) q

/-- Cylinder cluster points therefore converge to the limiting projective
family on local query events. -/
theorem CylinderClusterPoint.tendsto_limitMarginal_localQueryEvent
    {ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : Mettapedia.Logic.MarkovLogicInfinitePositive.StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion.CylinderClusterPoint E M ξ μ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Tendsto
      (fun n => E.finiteVolumeKernelSequence M ξ n (localQueryEvent Λ q))
      atTop
      (nhds (limitMarginal (Atom := Atom) μ Λ (localConstraintSet Λ q))) := by
  have h' := h.tendsto_localQueryEvent (Λ := Λ) q
  simpa [limitMarginal_apply_localConstraintSet (μ := μ) Λ q] using h'

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteLimitFamily
