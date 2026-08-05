import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.GammaImportanceSampling

/-!
# Pointwise replay for weighted coordinate proposals

An asymptotic coordinate-descent theorem requires uniform directional
smoothness and weighted strong convexity on every reachable state.  A finite
checkpoint replay cannot establish those regional premises, but it can still
answer a smaller exact question: for this state and this enumerated family of
coordinate proposals, what is the one-step expected objective?

This module proves the finite replay algebra.  The expected post-step value is
the pre-step value minus the weighted average of the observed benefits.
Consequently, strict expected descent is equivalent to positive expected
benefit, and one sampling law beats another exactly when it assigns greater
weighted benefit to the same proposal table.

These are pointwise statements.  They do not imply a future geometric rate,
regional curvature, or wall-time improvement.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PointwiseCoordinateReplay

open ImportanceSampledCoordinateDescent

universe u

variable {Coordinate : Type u}
  [Fintype Coordinate] [Nonempty Coordinate]

/-- Objective benefit of one enumerated coordinate proposal. -/
noncomputable def replayBenefit
    (before : ℝ) (after : Coordinate → ℝ) : Coordinate → ℝ :=
  fun coordinate => before - after coordinate

/-- A normalized weighted average preserves constants. -/
theorem weightedAverage_const
    (weight : Coordinate → ℝ)
    (positiveWeight :
      ∀ coordinate, 0 < weight coordinate)
    (value : ℝ) :
    weightedAverage weight (fun _coordinate => value) = value := by
  have totalNe : totalWeight weight ≠ 0 :=
    ne_of_gt (totalWeight_pos weight positiveWeight)
  unfold weightedAverage
  rw [show (∑ coordinate, weight coordinate * value) =
      totalWeight weight * value by
    simp [totalWeight, Finset.sum_mul]]
  field_simp [totalNe]

/-- Weighted averaging commutes with subtracting an enumerated benefit from
one common pre-step value. -/
theorem weightedAverage_const_sub
    (weight benefit : Coordinate → ℝ)
    (positiveWeight :
      ∀ coordinate, 0 < weight coordinate)
    (before : ℝ) :
    weightedAverage weight
        (fun coordinate => before - benefit coordinate) =
      before - weightedAverage weight benefit := by
  have totalNe : totalWeight weight ≠ 0 :=
    ne_of_gt (totalWeight_pos weight positiveWeight)
  unfold weightedAverage
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ coordinate, weight coordinate * before) =
      totalWeight weight * before by
    simp [totalWeight, Finset.sum_mul]]
  field_simp [totalNe]

/-- Exact one-state replay identity. -/
theorem weightedAverage_after_eq_before_sub_benefit
    (weight after : Coordinate → ℝ)
    (positiveWeight :
      ∀ coordinate, 0 < weight coordinate)
    (before : ℝ) :
    weightedAverage weight after =
      before -
        weightedAverage weight (replayBenefit before after) := by
  have pointwise :
      after =
        fun coordinate =>
          before - replayBenefit before after coordinate := by
    funext coordinate
    simp [replayBenefit]
  calc
    weightedAverage weight after =
        weightedAverage weight
          (fun coordinate =>
            before - replayBenefit before after coordinate) :=
      congrArg (weightedAverage weight) pointwise
    _ = before -
        weightedAverage weight (replayBenefit before after) :=
      weightedAverage_const_sub
        weight (replayBenefit before after) positiveWeight before

/-- At one enumerated state, strict expected descent is exactly positive
weighted benefit. -/
theorem pointwiseExpectedDescent_iff_positiveBenefit
    (weight after : Coordinate → ℝ)
    (positiveWeight :
      ∀ coordinate, 0 < weight coordinate)
    (before : ℝ) :
    weightedAverage weight after < before ↔
      0 < weightedAverage weight (replayBenefit before after) := by
  rw [weightedAverage_after_eq_before_sub_benefit
    weight after positiveWeight before]
  constructor <;> intro inequality <;> linarith

/-- A per-coordinate benefit floor becomes the same floor on the exact
weighted expectation. -/
theorem benefitFloor_le_weightedAverage
    (weight benefit : Coordinate → ℝ)
    (positiveWeight :
      ∀ coordinate, 0 < weight coordinate)
    (floor : ℝ)
    (pointwise : ∀ coordinate, floor ≤ benefit coordinate) :
    floor ≤ weightedAverage weight benefit := by
  have positiveTotal := totalWeight_pos weight positiveWeight
  have monotone :
      weightedAverage weight (fun _coordinate => floor) ≤
        weightedAverage weight benefit :=
    weightedAverage_mono weight
      (fun coordinate => (positiveWeight coordinate).le)
      positiveTotal pointwise
  rw [weightedAverage_const weight positiveWeight floor] at monotone
  exact monotone

/-- For the same proposal table, sampling law `leftWeight` has a lower
expected post-step objective exactly when it has a greater weighted benefit. -/
theorem weightedLaw_better_iff_greaterBenefit
    (leftWeight rightWeight after : Coordinate → ℝ)
    (positiveLeft :
      ∀ coordinate, 0 < leftWeight coordinate)
    (positiveRight :
      ∀ coordinate, 0 < rightWeight coordinate)
    (before : ℝ) :
    weightedAverage leftWeight after <
        weightedAverage rightWeight after ↔
      weightedAverage rightWeight (replayBenefit before after) <
        weightedAverage leftWeight (replayBenefit before after) := by
  have leftIdentity :=
    weightedAverage_after_eq_before_sub_benefit
      leftWeight after positiveLeft before
  have rightIdentity :=
    weightedAverage_after_eq_before_sub_benefit
      rightWeight after positiveRight before
  rw [leftIdentity, rightIdentity]
  constructor <;> intro inequality <;> linarith

/-! ## Exact mixed-benefit fixture -/

def uniformWeight (_coordinate : Bool) : ℝ := 1

def helpfulBiasedWeight : Bool → ℝ
  | false => 3
  | true => 1

/-- The `false` proposal lowers objective `1` to `0`; the `true` proposal
raises it to `3`. -/
def mixedAfter : Bool → ℝ
  | false => 0
  | true => 3

theorem uniformWeight_pos :
    ∀ coordinate, 0 < uniformWeight coordinate := by
  intro coordinate
  cases coordinate <;> norm_num [uniformWeight]

theorem helpfulBiasedWeight_pos :
    ∀ coordinate, 0 < helpfulBiasedWeight coordinate := by
  intro coordinate
  cases coordinate <;> norm_num [helpfulBiasedWeight]

/-- Positive uniform weights do not prevent expected ascent when one
coordinate proposal is sufficiently harmful. -/
theorem uniformMixedReplay_increases :
    1 < weightedAverage uniformWeight mixedAfter := by
  norm_num [weightedAverage, totalWeight, uniformWeight, mixedAfter]

/-- Reweighting the same proposal table toward the helpful coordinate yields
strict expected descent. -/
theorem biasedMixedReplay_decreases :
    weightedAverage helpfulBiasedWeight mixedAfter < 1 := by
  norm_num [
    weightedAverage, totalWeight, helpfulBiasedWeight, mixedAfter]

/-- The helpful-biased law strictly beats uniform sampling on the exact same
pointwise replay table. -/
theorem biasedMixedReplay_better_than_uniform :
    weightedAverage helpfulBiasedWeight mixedAfter <
      weightedAverage uniformWeight mixedAfter := by
  norm_num [
    weightedAverage, totalWeight, helpfulBiasedWeight,
    uniformWeight, mixedAfter]

#print axioms weightedAverage_const
#print axioms weightedAverage_const_sub
#print axioms weightedAverage_after_eq_before_sub_benefit
#print axioms pointwiseExpectedDescent_iff_positiveBenefit
#print axioms benefitFloor_le_weightedAverage
#print axioms weightedLaw_better_iff_greaterBenefit
#print axioms uniformMixedReplay_increases
#print axioms biasedMixedReplay_decreases
#print axioms biasedMixedReplay_better_than_uniform

end PointwiseCoordinateReplay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
