import Mettapedia.Logic.MarkovLogicInfiniteDLR

/-!
# Positive-Potential Infinite MLNs

This module isolates the standard Gibbs/MLN regime where every local clause
potential is strictly positive. In this regime:

- every finite-volume weight is nonzero,
- every finite-volume partition function is nonzero,
- the boundary-conditioned world measures no longer need an external
  nonzero-partition hypothesis.

This is the natural literature-facing doorstep for building finite-volume kernel
sequences along exhaustions.
-/

namespace Mettapedia.Logic.MarkovLogicInfinitePositive

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteDLR

/-- An infinite MLN specification with strictly positive local clause potentials. -/
structure StrictlyPositiveInfiniteGroundMLNSpec
    (Atom ClauseId : Type*) [DecidableEq Atom] [DecidableEq ClauseId]
    extends InfiniteGroundMLNSpec Atom ClauseId where
  satisfiedPotential_ne_zero : ∀ j, (clauseData j).satisfiedPotential ≠ 0
  unsatisfiedPotential_ne_zero : ∀ j, (clauseData j).unsatisfiedPotential ≠ 0

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

omit [DecidableEq Atom] in
theorem WeightedGroundClause.eval_ne_zero_of_potentials_ne_zero
    (wc : WeightedGroundClause Atom)
    (hsat : wc.satisfiedPotential ≠ 0)
    (hunsat : wc.unsatisfiedPotential ≠ 0)
    (W : AtomValuation Atom) :
    wc.eval W ≠ 0 := by
  classical
  unfold WeightedGroundClause.eval
  split_ifs
  · exact hsat
  · exact hunsat

omit [DecidableEq Atom] in
theorem classicalWeightedClause_satisfiedPotential_ne_zero
    (clause : GroundClause Atom) (logWeight : ℝ) :
    (classicalWeightedClause clause logWeight).satisfiedPotential ≠ 0 := by
  simp [classicalWeightedClause, Real.exp_pos]

omit [DecidableEq Atom] in
theorem classicalWeightedClause_unsatisfiedPotential_ne_zero
    (clause : GroundClause Atom) (logWeight : ℝ) :
    (classicalWeightedClause clause logWeight).unsatisfiedPotential ≠ 0 := by
  simp [classicalWeightedClause]

namespace StrictlyPositiveInfiniteGroundMLNSpec

theorem finiteVolumeWeight_ne_zero
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (x : LocalAssignment Atom Λ) (ξ : BoundaryCondition Atom) :
    M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ x ξ ≠ 0 := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumeWeight
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact WeightedGroundClause.eval_ne_zero_of_potentials_ne_zero
    (wc := M.clauseData j)
    (hsat := M.satisfiedPotential_ne_zero j)
    (hunsat := M.unsatisfiedPotential_ne_zero j)
    (W := patch Λ x ξ)

theorem finiteVolumePartition_ne_zero
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    M.toInfiniteGroundMLNSpec.finiteVolumePartition Λ ξ ≠ 0 := by
  classical
  let x₀ : LocalAssignment Atom Λ := fun _ => false
  have hx₀ : M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ x₀ ξ ≠ 0 :=
    finiteVolumeWeight_ne_zero M Λ x₀ ξ
  have hle :
      M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ x₀ ξ ≤
        M.toInfiniteGroundMLNSpec.finiteVolumePartition Λ ξ := by
    unfold InfiniteGroundMLNSpec.finiteVolumePartition
    exact Finset.single_le_sum
      (fun y hy => show 0 ≤ M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ y ξ by exact zero_le _)
      (Finset.mem_univ x₀)
  intro hpart
  have hx₀_le_zero :
      M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ x₀ ξ ≤ 0 := by
    simpa [hpart] using hle
  exact hx₀ (le_antisymm hx₀_le_zero bot_le)

/-- In the strictly positive regime, the normalized finite-volume world measure
is available without an explicit nonzero-partition witness. -/
noncomputable def finiteVolumeWorldMeasure
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    Measure (InfiniteWorld Atom) :=
  MarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
    (M := M.toInfiniteGroundMLNSpec) Λ ξ (finiteVolumePartition_ne_zero M Λ ξ)

instance finiteVolumeWorldMeasure_isProbability
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    IsProbabilityMeasure (finiteVolumeWorldMeasure M Λ ξ) := by
  unfold finiteVolumeWorldMeasure
  infer_instance

/-- The canonical Gibbsian specification in the strictly positive regime. -/
noncomputable def finiteVolumeSpecification
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId) :
    GibbsianSpecification Atom ClauseId M.toInfiniteGroundMLNSpec :=
  MarkovLogicInfiniteDLR.finiteVolumeSpecification M.toInfiniteGroundMLNSpec

theorem finiteVolumeSpecification_queryProb_eq_finiteVolume
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) :
    ((finiteVolumeSpecification M).kernelMassSemantics Λ ξ
      (finiteVolumePartition_ne_zero M Λ ξ)).queryProb q =
      (finiteVolumeMassSemantics M.toInfiniteGroundMLNSpec Λ ξ).queryProb q := by
  exact MarkovLogicInfiniteDLR.finiteVolumeSpecification_queryProb_eq_finiteVolume
    M.toInfiniteGroundMLNSpec Λ ξ (finiteVolumePartition_ne_zero M Λ ξ) q

end StrictlyPositiveInfiniteGroundMLNSpec

end Mettapedia.Logic.MarkovLogicInfinitePositive
