import Mettapedia.MachineLearning.ContinualLearning.QuadraticTwoTask
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.OverlapCalibration

/-!
# Multiplicity and metric-mismatch dictionary for forgetting

This file connects two already sealed finite-dimensional models.  Declared
evidence overlap becomes an effective multiplicity, while sequential
quadratic learning decomposes relative to an arbitrary joint reference into
an additive metric mismatch and the exact second-order reuse remainder.

The statements are scalar Gaussian and finite-dimensional linear-quadratic.
They do not identify an unknown dependence structure from data.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Effective multiplicity -/

/-- A packet with declared scalar overlap `overlap` is counted with effective
multiplicity one plus that overlap in the normalized unit-packet chart. -/
noncomputable def effectiveMultiplicity (overlap : ℝ) : ℝ :=
  1 + overlap

/-- Exact dictionary: precision overstatement by `multiplicity - 1` is
equivalent to the effective-multiplicity assignment. -/
theorem precisionOverstatement_eq_multiplicity_sub_one_iff
    (priorPrecision firstPrecision secondPrecision overlap multiplicity : ℝ) :
    naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision -
          overlapCalibratedPrecision priorPrecision firstPrecision
            secondPrecision overlap =
        multiplicity - 1 ↔
      multiplicity = effectiveMultiplicity overlap := by
  rw [naivePrecision_sub_calibrated_eq_overlap]
  unfold effectiveMultiplicity
  constructor <;> intro h <;> linarith

/-- Positive fixture: fresh evidence has multiplicity one and causes no
precision overstatement. -/
theorem freshEvidence_unitMultiplicity_positiveExample :
    effectiveMultiplicity 0 = 1 ∧
      naiveOverlappingPrecision 1 1 1 -
          overlapCalibratedPrecision 1 1 1 0 = 0 := by
  norm_num [effectiveMultiplicity, naiveOverlappingPrecision,
    overlapCalibratedPrecision]

/-- Negative fixture: duplicating one normalized observation has effective
multiplicity two and overstates precision by one. -/
theorem duplicateEvidence_doubleMultiplicity_negativeExample :
    effectiveMultiplicity 1 = 2 ∧
      naiveOverlappingPrecision 1 1 1 -
          overlapCalibratedPrecision 1 1 1 1 = 1 := by
  norm_num [effectiveMultiplicity, naiveOverlappingPrecision,
    overlapCalibratedPrecision]

/-! ## Metric mismatch plus connection remainder -/

section Quadratic

variable {Index : Type*} [Fintype Index]

/-- Forgetting measured against a declared joint reference state. -/
noncomputable def quadraticForgettingAgainstReference
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter reference : Index → ℝ) : Index → ℝ :=
  sequentialTwoTaskUpdate first second stepSize parameter - reference

/-- The mismatch between the additive joint-gradient step and the declared
joint reference. -/
noncomputable def quadraticMetricMismatchAgainstReference
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter reference : Index → ℝ) : Index → ℝ :=
  additiveTwoTaskUpdate first second stepSize parameter - reference

/-- The exact second-order remainder introduced by sequential reuse. -/
noncomputable def quadraticConnectionRemainder
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter : Index → ℝ) : Index → ℝ :=
  stepSize ^ 2 • second.curvature.mulVec (first.gradient parameter)

/-- Metric-forgetting decomposition in the sealed quadratic model: total
deviation from a joint reference is additive metric mismatch plus the exact
sequential-connection remainder. -/
theorem quadraticForgetting_eq_metricMismatch_add_connectionRemainder
    (first second : QuadraticTask Index) (stepSize : ℝ)
    (parameter reference : Index → ℝ) :
    quadraticForgettingAgainstReference first second stepSize parameter reference =
      quadraticMetricMismatchAgainstReference first second stepSize parameter reference +
        quadraticConnectionRemainder first second stepSize parameter := by
  rw [quadraticForgettingAgainstReference,
    quadraticMetricMismatchAgainstReference, quadraticConnectionRemainder]
  have h := sequentialTwoTaskUpdate_sub_additive_exact
    first second stepSize parameter
  calc
    sequentialTwoTaskUpdate first second stepSize parameter - reference =
        (additiveTwoTaskUpdate first second stepSize parameter - reference) +
          (sequentialTwoTaskUpdate first second stepSize parameter -
            additiveTwoTaskUpdate first second stepSize parameter) := by
      abel
    _ = (additiveTwoTaskUpdate first second stepSize parameter - reference) +
        stepSize ^ 2 • second.curvature.mulVec (first.gradient parameter) := by
      rw [h]

end Quadratic

/-- Positive fixture: disjoint coordinate tasks have zero connection
remainder. -/
theorem orthogonalTasks_connectionRemainder_zero_positiveExample
    (stepSize : ℝ) (parameter : Fin 2 → ℝ) :
    quadraticConnectionRemainder orthogonalFirstTask orthogonalSecondTask
      stepSize parameter = 0 := by
  funext i
  fin_cases i <;>
    simp [quadraticConnectionRemainder, orthogonalFirstTask,
      orthogonalSecondTask, QuadraticTask.gradient,
      dotProduct, Fin.sum_univ_two]

/-- Negative fixture: same-cause reuse has a nonzero connection remainder
despite its zero curvature commutator. -/
theorem sameCause_connectionRemainder_nonzero_negativeExample :
    quadraticConnectionRemainder scalarUnitTask scalarUnitTask (1 / 2)
        scalarUnitParameter ≠ 0 := by
  intro hzero
  have hdifference := sequentialTwoTaskUpdate_sub_additive_exact
    scalarUnitTask scalarUnitTask (1 / 2) scalarUnitParameter
  rw [quadraticConnectionRemainder] at hzero
  rw [hzero] at hdifference
  have heq :
      sequentialTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter =
        additiveTwoTaskUpdate scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter := sub_eq_zero.mp hdifference
  exact sameCause_reuse_zero_commutator_nonadditive_fixture.2.2.2 heq

#print axioms precisionOverstatement_eq_multiplicity_sub_one_iff
#print axioms quadraticForgetting_eq_metricMismatch_add_connectionRemainder
#print axioms orthogonalTasks_connectionRemainder_zero_positiveExample
#print axioms sameCause_connectionRemainder_nonzero_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
