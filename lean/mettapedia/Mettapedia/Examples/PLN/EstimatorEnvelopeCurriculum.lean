import Mathlib.Tactic
import Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope

/-!
# Estimator-envelope curriculum example

This wrapper centralizes the certified selector story: selected deduction
strength stays inside the credal envelope, and calibrated fixed-feature weights
minimize finite squared loss.
-/

namespace Mettapedia.Examples.PLN.EstimatorEnvelopeCurriculum

open Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope

noncomputable section

/-! ## Positive case: the selector remains inside the deduction envelope -/

/-- The positive toy selector is concrete and remains inside its ITV envelope. -/
theorem positive_selector_inside_envelope :
    toyPositiveITV.lower ≤ toyPositiveSelected ∧
      toyPositiveSelected ≤ toyPositiveITV.upper :=
  toyPositiveSelected_mem_ITV

/-- Concrete selected value for the positive toy. -/
theorem positive_selector_value :
    toyPositiveSelected = 103 / 125 :=
  toyPositiveSelected_eq

/-! ## Negative case: a point estimate can sit far from a legal endpoint -/

/-- The negative fixture still stays inside its envelope after selection. -/
theorem negative_selector_inside_envelope :
    toyNegativeITV.lower ≤ toyNegativeSelected ∧
      toyNegativeSelected ≤ toyNegativeITV.upper :=
  toyNegativeSelected_mem_ITV

/-- Negative example: the naive point can be far from the lower endpoint that
the certified interval still permits. -/
theorem negative_point_far_from_lower_endpoint :
    toyNegativePoint - (2 / 5 : ℝ) = 41 / 100 :=
  toyNegativePoint_minus_lowerEndpoint_eq

/-! ## Calibration: the fixed-feature weight is a squared-loss minimizer -/

/-- A one-row calibration sample whose independence branch is true. -/
def onePositiveCalibrationSample : Fin 1 → SelectorSample :=
  fun _ =>
    { x := 1
      y := 0
      latentAssumption := true
      x_mem_unit := by norm_num
      y_mem_unit := by norm_num }

/-- The weight `1` is calibrated for the one-row positive sample. -/
theorem one_positive_sample_q_one_calibrated :
    empiricalCalibrationCondition onePositiveCalibrationSample (1 : ℝ) := by
  norm_num [empiricalCalibrationCondition, onePositiveCalibrationSample,
    SelectorSample.gapWeight, SelectorSample.assumptionIndicator]

/-- Positive calibration theorem, restated in curriculum form. -/
theorem calibrated_weight_minimizes_mean_loss
    {n : ℕ} (sample : Fin n → SelectorSample) (hn : n ≠ 0)
    (q r : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hcal : empiricalCalibrationCondition sample q) :
    meanSquaredLossFixed sample q ≤ meanSquaredLossFixed sample r :=
  empiricalCalibrationCondition_meanSquaredLoss_le_any_fixedWeight
    sample hn q r hq hr hcal

/-- Negative calibration example: using the wrong fixed weight is strictly
worse on the one-row calibrated sample. -/
theorem one_positive_sample_q_zero_worse :
    meanSquaredLossFixed onePositiveCalibrationSample (1 : ℝ) <
      meanSquaredLossFixed onePositiveCalibrationSample (0 : ℝ) := by
  norm_num [meanSquaredLossFixed, sumSquaredLossFixed,
    onePositiveCalibrationSample, SelectorSample.loss,
    SelectorSample.prediction, SelectorSample.target,
    SelectorSample.assumptionIndicator]

end

end Mettapedia.Examples.PLN.EstimatorEnvelopeCurriculum
