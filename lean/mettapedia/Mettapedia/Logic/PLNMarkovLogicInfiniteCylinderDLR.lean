import Mettapedia.Logic.PLNMarkovLogicInfiniteContent
import Mettapedia.Logic.PLNMarkovLogicInfiniteGlobalDLR
import Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders

/-!
# Infinite MLN Cylinder-Level DLR Consistency

This module strengthens the local-query DLR layer to the full measurable-cylinder
language already present in the infinite-MLN development.

The key point is that both the finite-volume stages and the candidate global
measures induce additive contents on measurable cylinders.  We package the
corresponding convergence notion and connect it to:

- the existing cluster-point frontends,
- the projective-limit candidate measure,
- and the previously established local-query DLR consistency.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteCylinderDLR

open Filter
open MeasureTheory
open scoped Topology
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteProjective
open Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders
open Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend
open Mettapedia.Logic.PLNMarkovLogicInfiniteContent
open Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily
open Mettapedia.Logic.PLNMarkovLogicInfiniteGlobalDLR
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive
open Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteContent.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteGlobalDLR.RegionExhaustion

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Stage marginals compute arbitrary measurable cylinders. -/
theorem stageMarginal_apply_cylinder
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i))
    (hS : MeasurableSet S) :
    Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n I S =
        E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S) := by
  rw [Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal]
  rw [MeasureTheory.cylinder]
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]

/-- The content induced by a finite-volume stage agrees with the stage kernel on
every measurable cylinder. -/
theorem stageContent_cylinder
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i))
    (hS : MeasurableSet S) :
    stageContent E M ξ n (MeasureTheory.cylinder I S) =
      E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S) := by
  calc
    stageContent E M ξ n (MeasureTheory.cylinder I S)
        = stageMarginal E M ξ n I S := by
          simpa [stageContent] using
            (MeasureTheory.projectiveFamilyContent_cylinder
              (P := stageMarginal E M ξ n)
              (I := I) (S := S)
              (hP := isProjectiveMeasureFamily_stageMarginal E M ξ n)
              hS)
    _ = E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S) := by
          exact stageMarginal_apply_cylinder E M ξ n I S hS

omit [DecidableEq Atom] in
/-- The limiting marginal of a global measure computes measurable cylinders. -/
theorem limitMarginal_apply_cylinder
    (μ : Measure (InfiniteWorld Atom))
    (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i))
    (hS : MeasurableSet S) :
    limitMarginal μ I S = μ (MeasureTheory.cylinder I S) := by
  rw [limitMarginal]
  rw [MeasureTheory.cylinder]
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]

omit [DecidableEq Atom] in
/-- The content induced by a global measure via its finite-dimensional marginals
agrees with the original measure on every measurable cylinder. -/
theorem limitContent_cylinder
    (μ : Measure (InfiniteWorld Atom))
    (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i))
    (hS : MeasurableSet S) :
    limitContent μ (MeasureTheory.cylinder I S) =
      μ (MeasureTheory.cylinder I S) := by
  calc
    limitContent μ (MeasureTheory.cylinder I S)
        = limitMarginal μ I S := by
            simpa [limitContent, familyContent] using
              (MeasureTheory.projectiveFamilyContent_cylinder
                (P := limitMarginal μ) (I := I) (S := S)
                (hP := isProjectiveMeasureFamily_limitMarginal μ) hS)
    _ = μ (MeasureTheory.cylinder I S) := by
          exact limitMarginal_apply_cylinder μ I S hS

/-- Cylinder-level DLR consistency: finite-volume stage contents converge to the
content induced by a global measure on every measurable cylinder. -/
def CylinderContentDLRConsistent
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom)) : Prop :=
  ∀ (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i)),
    MeasurableSet S →
      Tendsto
        (fun n => stageContent E M ξ n (MeasureTheory.cylinder I S))
        atTop
        (nhds (limitContent μ (MeasureTheory.cylinder I S)))

/-- The exhaustion-stage kernel sequence is exactly the strictly positive
finite-volume Gibbsian specification evaluated on the corresponding stage. -/
theorem finiteVolumeKernelSequence_apply
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (A : Set (InfiniteWorld Atom)) :
    E.finiteVolumeKernelSequence M ξ n A =
      ((StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeSpecification M).kernel
        (E.region n) ξ
        (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M (E.region n) ξ)) A := by
  rfl

/-- Cylinder-level DLR consistency phrased directly in terms of the finite-volume
Gibbsian specification kernels. -/
def SpecificationCylinderDLRConsistent
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom)) : Prop :=
  ∀ (I : Finset Atom)
    (S : Set (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i)),
    MeasurableSet S →
      Tendsto
        (fun n =>
          ((StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeSpecification M).kernel
            (E.region n) ξ
            (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M (E.region n) ξ))
            (MeasureTheory.cylinder I S))
        atTop
        (nhds (μ (MeasureTheory.cylinder I S)))

/-- Cylinder cluster points yield cylinder-level DLR consistency. -/
theorem CylinderClusterPoint.cylinderContentDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : CylinderClusterPoint E M ξ μ) :
    CylinderContentDLRConsistent E M ξ μ := by
  intro I S hS
  have h' := h I S hS
  have hstage :
      (fun n => stageContent E M ξ n (MeasureTheory.cylinder I S)) =
        (fun n => E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S)) := by
    funext n
    exact stageContent_cylinder (Atom := Atom) (ClauseId := ClauseId) E M ξ n I S hS
  have htarget :
      limitContent μ (MeasureTheory.cylinder I S) = μ (MeasureTheory.cylinder I S) := by
    exact limitContent_cylinder (Atom := Atom) (μ := μ) I S hS
  simpa [hstage, htarget] using h'

/-- Marginal cluster points yield cylinder-level DLR consistency. -/
theorem MarginalClusterPoint.cylinderContentDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : MarginalClusterPoint E M ξ μ) :
    CylinderContentDLRConsistent E M ξ μ := by
  have hcyl : CylinderClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).2 h
  exact CylinderClusterPoint.cylinderContentDLRConsistent hcyl

/-- Cylinder-level DLR consistency implies the previously defined local-query
DLR consistency. -/
theorem CylinderContentDLRConsistent.localQueryDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (h : CylinderContentDLRConsistent E M ξ μ) :
    LocalQueryDLRConsistent E M ξ μ := by
  intro Λ q
  let S := localConstraintSet Λ q
  have hS : MeasurableSet S := by
    simpa [S] using measurableSet_localConstraintSet Λ q
  have h' := h Λ S hS
  have hstage :
      (fun n => stageContent E M ξ n (MeasureTheory.cylinder Λ S)) =
        (fun n =>
          E.finiteVolumeKernelSequence M ξ n
            (Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures.localQueryEvent Λ q)) := by
    funext n
    rw [localQueryEvent_eq_cylinder Λ q]
    exact stageContent_cylinder (Atom := Atom) (ClauseId := ClauseId) E M ξ n Λ S hS
  have htarget :
      limitContent μ (MeasureTheory.cylinder Λ S) =
        (globalMeasureMassSemantics (Atom := Atom) μ Λ).queryProb q := by
    rw [globalMeasureMassSemantics_queryProb (Atom := Atom) (μ := μ) Λ q]
    rw [localQueryEvent_eq_cylinder Λ q]
    exact limitContent_cylinder (Atom := Atom) (μ := μ) Λ S hS
  simpa [LocalQueryDLRConsistent, hstage, htarget] using h'

/-- Cylinder-content DLR consistency immediately yields the same convergence
statement phrased via the finite-volume Gibbsian specification kernels. -/
theorem CylinderContentDLRConsistent.specificationCylinderDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : CylinderContentDLRConsistent E M ξ μ) :
    SpecificationCylinderDLRConsistent E M ξ μ := by
  intro I S hS
  have h' := h I S hS
  have hstage :
      (fun n => stageContent E M ξ n (MeasureTheory.cylinder I S)) =
        (fun n =>
          ((StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeSpecification M).kernel
            (E.region n) ξ
            (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M (E.region n) ξ))
            (MeasureTheory.cylinder I S)) := by
    funext n
    rw [stageContent_cylinder (Atom := Atom) (ClauseId := ClauseId) E M ξ n I S hS]
    exact finiteVolumeKernelSequence_apply E M ξ n (MeasureTheory.cylinder I S)
  have htarget :
      limitContent μ (MeasureTheory.cylinder I S) = μ (MeasureTheory.cylinder I S) := by
    exact limitContent_cylinder (Atom := Atom) (μ := μ) I S hS
  simpa [SpecificationCylinderDLRConsistent, hstage, htarget] using h'

/-- Cylinder cluster points therefore satisfy the cylinder-level DLR law stated
through the finite-volume Gibbsian specification kernels. -/
theorem CylinderClusterPoint.specificationCylinderDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : CylinderClusterPoint E M ξ μ) :
    SpecificationCylinderDLRConsistent E M ξ μ := by
  exact
    (CylinderContentDLRConsistent.specificationCylinderDLRConsistent
      (h := CylinderClusterPoint.cylinderContentDLRConsistent h))

/-- Marginal cluster points satisfy the same specification-kernel version. -/
theorem MarginalClusterPoint.specificationCylinderDLRConsistent
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : MarginalClusterPoint E M ξ μ) :
    SpecificationCylinderDLRConsistent E M ξ μ := by
  exact
    (CylinderContentDLRConsistent.specificationCylinderDLRConsistent
      (h := MarginalClusterPoint.cylinderContentDLRConsistent h))

/-- If a projective family agrees with the finite-dimensional marginals of a
cluster-point measure, then the projective-limit candidate measure is
cylinder-level DLR-consistent. -/
theorem projectiveLimitMeasure_cylinderContentDLRConsistent_of_eq
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hEq : projectiveLimitMeasure (Atom := Atom) e P hP = μ) :
    CylinderContentDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  simpa [hEq] using
    (CylinderClusterPoint.cylinderContentDLRConsistent
      (E := E) (M := M) (ξ := ξ) (μ := μ) hμ)

/-- If a projective family agrees with the finite-dimensional marginals of a
cluster-point measure, then the projective-limit candidate measure is
cylinder-level DLR-consistent. -/
theorem projectiveLimitMeasure_cylinderContentDLRConsistent_of_limitMarginal_eq
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    CylinderContentDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hEq := projectiveLimitMeasure_eq_of_limitMarginal_eq
    (Atom := Atom) (μ := μ) e P hP hPμ
  exact projectiveLimitMeasure_cylinderContentDLRConsistent_of_eq
    (E := E) (M := M) (ξ := ξ) (μ := μ) hμ e P hP hEq

/-- The same inheritance theorem via the marginal-cluster-point frontend. -/
theorem projectiveLimitMeasure_cylinderContentDLRConsistent_of_marginalClusterPoint
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : MarginalClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    CylinderContentDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hcyl : CylinderClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).2 hμ
  exact projectiveLimitMeasure_cylinderContentDLRConsistent_of_limitMarginal_eq
    hcyl e P hP hPμ

/-- Hence the canonical projective-limit candidate measure satisfies the
specification-kernel cylinder DLR law whenever it matches a cylinder cluster
point on finite-dimensional marginals. -/
theorem projectiveLimitMeasure_specificationCylinderDLRConsistent_of_eq
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hEq : projectiveLimitMeasure (Atom := Atom) e P hP = μ) :
    SpecificationCylinderDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  simpa [hEq] using
    (CylinderClusterPoint.specificationCylinderDLRConsistent
      (E := E) (M := M) (ξ := ξ) (μ := μ) hμ)

/-- Hence the canonical projective-limit candidate measure satisfies the
specification-kernel cylinder DLR law whenever it matches a cylinder cluster
point on finite-dimensional marginals. -/
theorem projectiveLimitMeasure_specificationCylinderDLRConsistent_of_limitMarginal_eq
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    SpecificationCylinderDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hEq := projectiveLimitMeasure_eq_of_limitMarginal_eq
    (Atom := Atom) (μ := μ) e P hP hPμ
  exact projectiveLimitMeasure_specificationCylinderDLRConsistent_of_eq
    (E := E) (M := M) (ξ := ξ) (μ := μ) hμ e P hP hEq

/-- The same inheritance theorem via the marginal-cluster-point frontend. -/
theorem projectiveLimitMeasure_specificationCylinderDLRConsistent_of_marginalClusterPoint
    {E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (hμ : MarginalClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    SpecificationCylinderDLRConsistent E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  exact
    (CylinderContentDLRConsistent.specificationCylinderDLRConsistent
      (h :=
        projectiveLimitMeasure_cylinderContentDLRConsistent_of_marginalClusterPoint
          hμ e P hP hPμ))

end RegionExhaustion

end Mettapedia.Logic.PLNMarkovLogicInfiniteCylinderDLR
