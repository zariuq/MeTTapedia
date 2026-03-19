import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume

/-!
# Infinite MLN Finite-Volume World Measures

This module lifts the finite-volume local assignment semantics to honest
probability measures on the full infinite world space `Atom → Bool`.

For a finite region `Λ` and boundary condition `ξ`, we:

1. normalize the finite-volume weights on local assignments `Λ → Bool`,
2. push that finite distribution forward along `patch Λ · ξ`,
3. obtain a probability measure on full infinite worlds,
4. prove its probabilities on local constraint events agree with the already
   constructed `finiteVolumeMassSemantics`.

This is the measure-theoretic doorway needed before defining global Gibbs/DLR
consistency.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.PLNMarkovLogicAbstract

/-- Restrict a full infinite world to a local assignment on a finite region. -/
def worldRestriction {Atom : Type*}
    (Λ : Region Atom) (ω : InfiniteWorld Atom) : LocalAssignment Atom Λ :=
  fun a => ω a.1

theorem measurable_worldRestriction {Atom : Type*} (Λ : Region Atom) :
    Measurable (worldRestriction (Atom := Atom) Λ) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro a
  simpa [worldRestriction] using (measurable_pi_apply a.1)

/-- The event that a full world satisfies a local finite constraint query. -/
def localQueryEvent {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Set (InfiniteWorld Atom) :=
  {ω | satisfiesConstraints (worldRestriction Λ ω) q}

theorem measurableSet_localQueryEvent
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    MeasurableSet (localQueryEvent (Atom := Atom) Λ q) := by
  unfold localQueryEvent
  convert measurableSet_preimage (measurable_worldRestriction (Atom := Atom) Λ)
    ((Set.to_countable
      {x : LocalAssignment Atom Λ | satisfiesConstraints x q}).measurableSet)

/-- The unnormalized local weight function as a function on assignments. -/
noncomputable def finiteVolumeWeightFn
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    LocalAssignment Atom Λ → ENNReal :=
  fun x => M.finiteVolumeWeight Λ x ξ

theorem tsum_finiteVolumeWeightFn_eq_partition
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    ∑' x : LocalAssignment Atom Λ, finiteVolumeWeightFn M Λ ξ x =
      M.finiteVolumePartition Λ ξ := by
  classical
  unfold finiteVolumeWeightFn InfiniteGroundMLNSpec.finiteVolumePartition
  rw [tsum_eq_sum (s := (Finset.univ : Finset (LocalAssignment Atom Λ)))
    (fun x hx => (hx (Finset.mem_univ x)).elim)]

/-- The normalized finite-volume distribution on local assignments. -/
noncomputable def finiteVolumeAssignmentPMF
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    PMF (LocalAssignment Atom Λ) :=
  PMF.normalize (finiteVolumeWeightFn M Λ ξ)
    (by
      rw [tsum_finiteVolumeWeightFn_eq_partition]
      exact hZ)
    (by
      rw [tsum_finiteVolumeWeightFn_eq_partition]
      exact finiteVolumePartition_ne_top M Λ ξ)

@[simp] theorem finiteVolumeAssignmentPMF_apply
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (x : LocalAssignment Atom Λ) :
    finiteVolumeAssignmentPMF M Λ ξ hZ x =
      M.finiteVolumeWeight Λ x ξ * (M.finiteVolumePartition Λ ξ)⁻¹ := by
  rw [finiteVolumeAssignmentPMF, PMF.normalize_apply, tsum_finiteVolumeWeightFn_eq_partition]
  simp [finiteVolumeWeightFn]

/-- The finite-volume PMF on full worlds, obtained by patching local assignments
into the boundary condition. -/
noncomputable def finiteVolumeWorldPMF
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    PMF (InfiniteWorld Atom) :=
  (finiteVolumeAssignmentPMF M Λ ξ hZ).map (patch Λ · ξ)

/-- The finite-volume probability measure on the full infinite world space. -/
noncomputable def finiteVolumeWorldMeasure
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    Measure (InfiniteWorld Atom) :=
  (finiteVolumeWorldPMF M Λ ξ hZ).toMeasure

instance finiteVolumeWorldMeasure_isProbability
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    IsProbabilityMeasure (finiteVolumeWorldMeasure M Λ ξ hZ) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem measurable_patch
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    Measurable (fun x : LocalAssignment Atom Λ => patch Λ x ξ) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro a
  by_cases h : a ∈ Λ
  · have hregion : Measurable (fun x : LocalAssignment Atom Λ => x (⟨a, h⟩ : RegionAtom Atom Λ)) := by
      simpa using (measurable_pi_apply (a := (⟨a, h⟩ : RegionAtom Atom Λ)))
    simpa [patch, h] using hregion
  · simp [patch, h]

theorem preimage_localQueryEvent_patch
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) :
    (fun x : LocalAssignment Atom Λ => patch Λ x ξ) ⁻¹'
      localQueryEvent (Atom := Atom) Λ q =
      {x | satisfiesConstraints x q} := by
  ext x
  simp [localQueryEvent, worldRestriction, satisfiesConstraints, patch]

theorem finiteVolumeWorldMeasure_localQueryEvent
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (q : LocalConstraintQuery Atom Λ) :
    finiteVolumeWorldMeasure M Λ ξ hZ (localQueryEvent (Atom := Atom) Λ q) =
      (finiteVolumeMassSemantics M Λ ξ).queryProb q := by
  classical
  unfold finiteVolumeWorldMeasure finiteVolumeWorldPMF
  rw [PMF.toMeasure_map_apply (p := finiteVolumeAssignmentPMF M Λ ξ hZ)
    (f := fun x : LocalAssignment Atom Λ => patch Λ x ξ)
    (s := localQueryEvent Λ q) (hf := measurable_patch Λ ξ)
    (hs := measurableSet_localQueryEvent Λ q)]
  rw [preimage_localQueryEvent_patch Λ ξ q]
  rw [PMF.toMeasure_apply_fintype]
  simp_rw [Set.indicator_apply, finiteVolumeAssignmentPMF_apply]
  simp_rw [Set.mem_setOf_eq]
  have hsum :
      ∑ x : LocalAssignment Atom Λ,
        (if satisfiesConstraints x q then
          M.finiteVolumeWeight Λ x ξ * (M.finiteVolumePartition Λ ξ)⁻¹
        else 0) =
      finiteVolumeQueryMass M Λ ξ q * (M.finiteVolumePartition Λ ξ)⁻¹ := by
    unfold finiteVolumeQueryMass
    calc
      (∑ x : LocalAssignment Atom Λ,
          if satisfiesConstraints x q then
            M.finiteVolumeWeight Λ x ξ * (M.finiteVolumePartition Λ ξ)⁻¹
          else 0)
          =
        ∑ x : LocalAssignment Atom Λ,
          (if satisfiesConstraints x q then M.finiteVolumeWeight Λ x ξ else 0) *
            (M.finiteVolumePartition Λ ξ)⁻¹ := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hsat : satisfiesConstraints x q <;> simp [hsat]
      _ = finiteVolumeQueryMass M Λ ξ q * (M.finiteVolumePartition Λ ξ)⁻¹ := by
        rw [← Finset.sum_mul]
        simp [finiteVolumeQueryMass]
  rw [hsum]
  simp [finiteVolumeMassSemantics, MassSemantics.queryProb, hZ, div_eq_mul_inv]

end Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures
