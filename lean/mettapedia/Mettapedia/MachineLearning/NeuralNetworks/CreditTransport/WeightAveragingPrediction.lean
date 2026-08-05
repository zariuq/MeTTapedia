import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AffineFixedPointAcceleration

/-!
# Weight averaging versus prediction averaging

Izmailov et al., *Averaging Weights Leads to Wider Optima and Better
Generalization* (arXiv:1803.05407), Section 3.5, compare the prediction at the
average weight with the average of predictions.  Their Taylor argument uses
centered weight displacements: the linear terms cancel, leaving a
second-order error.

This file isolates that finite argument for arbitrary affine weights and real
normed parameter and output spaces.  A declared pointwise Taylor-remainder
bound yields an explicit weighted prediction error.  Affine predictors recover
prediction averaging exactly.  Scalar fixtures show both sharp boundaries:
quadratic prediction has a nonzero second-order gap even for perfectly centered
weights, while an affine predictor fails to cancel when the displacements are
not centered.

These results do not claim that stochastic weight averaging improves
generalization, finds a wide optimum, or is safe on an arbitrary nonconvex
loss.  They identify the local structural premise behind the source's
weight-average versus ensemble approximation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace WeightAveragingPrediction

noncomputable section

section General

variable {ι Parameter Output : Type*} [Fintype ι]
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
variable [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- The weighted displacements cancel at the declared center. -/
def IsCenteredWeights
    (coefficients : ι → ℝ) (deviations : ι → Parameter) : Prop :=
  weightedCombination coefficients deviations = 0

/-- Average predictions at weights represented as a center plus displacement. -/
def weightedPrediction
    (coefficients : ι → ℝ) (predict : Parameter → Output)
    (center : Parameter) (deviations : ι → Parameter) : Output :=
  weightedCombination coefficients
    (fun i => predict (center + deviations i))

/-- The error left after subtracting the first-order model at one center. -/
def predictionRemainder
    (predict : Parameter → Output)
    (derivative : Parameter →L[ℝ] Output)
    (center deviation : Parameter) : Output :=
  predict (center + deviation) - predict center - derivative deviation

/-- Continuous linear maps commute with finite weighted combinations. -/
theorem weightedCombination_map
    (derivative : Parameter →L[ℝ] Output)
    (coefficients : ι → ℝ) (states : ι → Parameter) :
    weightedCombination coefficients (fun i => derivative (states i)) =
      derivative (weightedCombination coefficients states) := by
  simp [weightedCombination, map_sum]

/-- Exact source algebra: affine normalization removes the constant term and
centered displacements remove the complete first-order term. -/
theorem weightedPrediction_sub_center_eq_remainder
    (coefficients : ι → ℝ) (predict : Parameter → Output)
    (derivative : Parameter →L[ℝ] Output)
    (center : Parameter) (deviations : ι → Parameter)
    (affine : IsAffineWeights coefficients)
    (centered : IsCenteredWeights coefficients deviations) :
    weightedPrediction coefficients predict center deviations -
        predict center =
      weightedCombination coefficients
        (fun i => predictionRemainder predict derivative center
          (deviations i)) := by
  rw [weightedPrediction,
    weightedCombination_sub_reference coefficients _ (predict center) affine]
  calc
    weightedCombination coefficients
          (fun i => predict (center + deviations i) - predict center) =
        weightedCombination coefficients
          (fun i =>
            derivative (deviations i) +
              predictionRemainder predict derivative center
                (deviations i)) := by
          apply congrArg (weightedCombination coefficients)
          funext i
          dsimp only [predictionRemainder]
          abel
    _ =
        weightedCombination coefficients
            (fun i => derivative (deviations i)) +
          weightedCombination coefficients
            (fun i => predictionRemainder predict derivative center
              (deviations i)) :=
      weightedCombination_add _ _ _
    _ =
        derivative (weightedCombination coefficients deviations) +
          weightedCombination coefficients
            (fun i => predictionRemainder predict derivative center
              (deviations i)) := by
      rw [weightedCombination_map]
    _ =
        weightedCombination coefficients
          (fun i => predictionRemainder predict derivative center
            (deviations i)) := by
      rw [centered]
      simp

/-- A pointwise second-order remainder budget yields the finite weighted
prediction-average error bound. -/
theorem norm_weightedPrediction_sub_center_le
    (coefficients : ι → ℝ) (predict : Parameter → Output)
    (derivative : Parameter →L[ℝ] Output)
    (center : Parameter) (deviations : ι → Parameter)
    (curvatureBudget : ℝ)
    (affine : IsAffineWeights coefficients)
    (nonnegative : ∀ i, 0 ≤ coefficients i)
    (centered : IsCenteredWeights coefficients deviations)
    (remainderBound : ∀ i,
      ‖predictionRemainder predict derivative center (deviations i)‖ ≤
        curvatureBudget * ‖deviations i‖ ^ 2) :
    ‖weightedPrediction coefficients predict center deviations -
        predict center‖ ≤
      ∑ i, coefficients i *
        (curvatureBudget * ‖deviations i‖ ^ 2) := by
  rw [weightedPrediction_sub_center_eq_remainder
    coefficients predict derivative center deviations affine centered]
  rw [weightedCombination]
  calc
    ‖∑ i, coefficients i •
        predictionRemainder predict derivative center (deviations i)‖ ≤
        ∑ i, ‖coefficients i •
          predictionRemainder predict derivative center (deviations i)‖ :=
      norm_sum_le _ _
    _ = ∑ i, coefficients i *
          ‖predictionRemainder predict derivative center (deviations i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (nonnegative i)]
    _ ≤ ∑ i, coefficients i *
          (curvatureBudget * ‖deviations i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (remainderBound i) (nonnegative i)

/-- If every first-order remainder vanishes, weight averaging and prediction
averaging coincide exactly. -/
theorem weightedPrediction_eq_center_of_zeroRemainder
    (coefficients : ι → ℝ) (predict : Parameter → Output)
    (derivative : Parameter →L[ℝ] Output)
    (center : Parameter) (deviations : ι → Parameter)
    (affine : IsAffineWeights coefficients)
    (centered : IsCenteredWeights coefficients deviations)
    (zeroRemainder : ∀ i,
      predictionRemainder predict derivative center (deviations i) = 0) :
    weightedPrediction coefficients predict center deviations =
      predict center := by
  apply sub_eq_zero.mp
  rw [weightedPrediction_sub_center_eq_remainder
    coefficients predict derivative center deviations affine centered]
  simp [weightedCombination, zeroRemainder]

/-- An affine predictor. -/
def affinePrediction
    (base : Output) (linear : Parameter →L[ℝ] Output) :
    Parameter → Output :=
  fun parameter => base + linear parameter

/-- Affine predictors exactly identify averaging weights with averaging
predictions for every centered affine weighting. -/
theorem weightedPrediction_affine_eq_center
    (coefficients : ι → ℝ)
    (base : Output) (linear : Parameter →L[ℝ] Output)
    (center : Parameter) (deviations : ι → Parameter)
    (affine : IsAffineWeights coefficients)
    (centered : IsCenteredWeights coefficients deviations) :
    weightedPrediction coefficients (affinePrediction base linear)
        center deviations =
      affinePrediction base linear center := by
  apply weightedPrediction_eq_center_of_zeroRemainder
    coefficients (affinePrediction base linear) linear center deviations
    affine centered
  intro i
  simp only [predictionRemainder, affinePrediction, map_add]
  abel

end General

/-! ## Exact scalar boundaries -/

def halfWeights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

def oppositeDeviations : Fin 2 → ℝ := ![-1, 1]

def sameDeviations : Fin 2 → ℝ := ![1, 1]

def squarePrediction (parameter : ℝ) : ℝ :=
  parameter ^ 2

theorem halfWeights_are_affine :
    IsAffineWeights halfWeights := by
  norm_num [IsAffineWeights, halfWeights]

theorem halfWeights_nonnegative (i : Fin 2) :
    0 ≤ halfWeights i := by
  fin_cases i <;> norm_num [halfWeights]

theorem oppositeDeviations_are_centered :
    IsCenteredWeights halfWeights oppositeDeviations := by
  norm_num [IsCenteredWeights, weightedCombination, halfWeights,
    oppositeDeviations]

/-- The source's second-order remainder is real: centered weights do not make a
nonlinear predictor commute exactly with averaging. -/
theorem centered_square_prediction_has_unit_gap :
    weightedPrediction halfWeights squarePrediction 0 oppositeDeviations = 1 ∧
      squarePrediction 0 = 0 := by
  norm_num [weightedPrediction, weightedCombination, halfWeights,
    oppositeDeviations, squarePrediction]

/-- For the scalar square at zero with zero derivative, the unit-curvature
remainder budget is exact. -/
theorem squarePrediction_remainder_exact (deviation : ℝ) :
    predictionRemainder squarePrediction (0 : ℝ →L[ℝ] ℝ)
      0 deviation =
      deviation ^ 2 := by
  simp [predictionRemainder, squarePrediction]

/-- The aggregate second-order bound is attained by the centered square
fixture. -/
theorem centered_square_prediction_bound_attained :
    ‖weightedPrediction halfWeights squarePrediction 0 oppositeDeviations -
        squarePrediction 0‖ =
      ∑ i, halfWeights i * (1 * ‖oppositeDeviations i‖ ^ 2) := by
  norm_num [weightedPrediction, weightedCombination, halfWeights,
    oppositeDeviations, squarePrediction, Real.norm_eq_abs]

/-- Affine normalization without centered displacements does not cancel the
linear term. -/
theorem sameDeviations_are_not_centered :
    ¬ IsCenteredWeights halfWeights sameDeviations := by
  norm_num [IsCenteredWeights, weightedCombination, halfWeights,
    sameDeviations]

/-- The failed-centering boundary is visible even for the identity predictor. -/
theorem noncentered_affine_prediction_mismatch :
    weightedPrediction halfWeights (fun state : ℝ => state)
        0 sameDeviations = 1 ∧
      weightedPrediction halfWeights (fun state : ℝ => state)
        0 sameDeviations ≠ 0 := by
  norm_num [weightedPrediction, weightedCombination, halfWeights,
    sameDeviations]

#print axioms weightedCombination_map
#print axioms weightedPrediction_sub_center_eq_remainder
#print axioms norm_weightedPrediction_sub_center_le
#print axioms weightedPrediction_eq_center_of_zeroRemainder
#print axioms weightedPrediction_affine_eq_center
#print axioms halfWeights_are_affine
#print axioms oppositeDeviations_are_centered
#print axioms centered_square_prediction_has_unit_gap
#print axioms squarePrediction_remainder_exact
#print axioms centered_square_prediction_bound_attained
#print axioms sameDeviations_are_not_centered
#print axioms noncentered_affine_prediction_mismatch

end

end WeightAveragingPrediction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
