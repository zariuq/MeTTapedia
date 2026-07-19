import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Selectivity

/-!
# Linear measurement distortion belongs in the measurement map

For the centered scalar model `y = d*x + ε`, with latent error variance `P`
and noise variance `R`, a raw-measurement correction coefficient `a` has risk
`(1-a*d)² P + a² R`.  The optimal learned coefficient is
`P*d/(P*d²+R)`.  A fusion rule calibrated for the false unit model instead uses
`P/(P+R)`; its risk is strictly higher exactly away from two equality
boundaries.

The same optimum is obtained without learning the fusion law: recalibrate the
measurement to `y/d`, transform its noise variance to `R/d²`, and apply the
ordinary hardwired unit-observation Kalman fusion.  Thus, for a fixed nonzero
linear distortion, correction can be pushed entirely into the measurement map.
This is a scalar linear-Gaussian factorization, not a nonlinear universality
claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Distorted-model risk -/

/-- Mean-squared risk of a raw-measurement correction coefficient under
`y = distortion * x + noise`. -/
noncomputable def distortedMeasurementRisk
    (priorVariance noiseVariance distortion coefficient : ℝ) : ℝ :=
  (1 - coefficient * distortion) ^ 2 * priorVariance +
    coefficient ^ 2 * noiseVariance

/-- Risk-optimal coefficient for the fixed linear distortion. -/
noncomputable def distortedOptimalMix
    (priorVariance noiseVariance distortion : ℝ) : ℝ :=
  priorVariance * distortion /
    (priorVariance * distortion ^ 2 + noiseVariance)

/-- The variance-coordinate risk is exactly the existing precision-coordinate
`scalarGainRisk` after reciprocating variances. -/
theorem distortedMeasurementRisk_eq_scalarGainRisk
    (priorVariance noiseVariance distortion coefficient : ℝ) :
    distortedMeasurementRisk priorVariance noiseVariance distortion coefficient =
      scalarGainRisk distortion priorVariance⁻¹ noiseVariance⁻¹ coefficient := by
  unfold distortedMeasurementRisk scalarGainRisk
  field_simp

/-- Exact excess-risk square around the distorted-model optimum. -/
theorem distortedMeasurementRisk_sub_optimal_eq_square
    (priorVariance noiseVariance distortion coefficient : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    distortedMeasurementRisk priorVariance noiseVariance distortion coefficient -
        distortedMeasurementRisk priorVariance noiseVariance distortion
          (distortedOptimalMix priorVariance noiseVariance distortion) =
      (priorVariance * distortion ^ 2 + noiseVariance) *
        (coefficient -
          distortedOptimalMix priorVariance noiseVariance distortion) ^ 2 := by
  have hden : 0 < priorVariance * distortion ^ 2 + noiseVariance := by
    positivity
  unfold distortedMeasurementRisk distortedOptimalMix
  field_simp [hden.ne']
  ring

/-- The distorted-model coefficient is the unique global scalar risk
minimizer. -/
theorem distortedOptimalMix_uniqueMinimizer
    (priorVariance noiseVariance distortion : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    (∀ coefficient,
      distortedMeasurementRisk priorVariance noiseVariance distortion
          (distortedOptimalMix priorVariance noiseVariance distortion) ≤
        distortedMeasurementRisk priorVariance noiseVariance distortion
          coefficient) ∧
      (∀ coefficient,
        distortedMeasurementRisk priorVariance noiseVariance distortion
            coefficient =
          distortedMeasurementRisk priorVariance noiseVariance distortion
            (distortedOptimalMix priorVariance noiseVariance distortion) ↔
        coefficient =
          distortedOptimalMix priorVariance noiseVariance distortion) := by
  have hden : 0 < priorVariance * distortion ^ 2 + noiseVariance := by
    positivity
  constructor
  · intro coefficient
    have hexcess := distortedMeasurementRisk_sub_optimal_eq_square
      priorVariance noiseVariance distortion coefficient hprior hnoise
    nlinarith [mul_nonneg hden.le (sq_nonneg
      (coefficient - distortedOptimalMix
        priorVariance noiseVariance distortion))]
  · intro coefficient
    constructor
    · intro heq
      have hexcess := distortedMeasurementRisk_sub_optimal_eq_square
        priorVariance noiseVariance distortion coefficient hprior hnoise
      rw [heq, sub_self] at hexcess
      have hsquare :
          (coefficient - distortedOptimalMix
            priorVariance noiseVariance distortion) ^ 2 = 0 :=
        (mul_eq_zero.mp hexcess.symm).resolve_left hden.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    · rintro rfl
      rfl

/-! ## When learned mixing strictly repairs a false unit model -/

/-- Coefficient used by hardwired fusion when it incorrectly assumes a unit
measurement map. -/
noncomputable def unitModelHardwiredMix
    (priorVariance noiseVariance : ℝ) : ℝ :=
  varianceKalmanGain priorVariance noiseVariance

/-- Exact equality boundary: the false-unit coefficient happens to equal the
distortion-aware optimum iff `(d-1)(P*d-R)=0`.  Distortion alone therefore does
not imply a strict risk gap. -/
theorem unitModelHardwiredMix_eq_distortedOptimalMix_iff
    (priorVariance noiseVariance distortion : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    unitModelHardwiredMix priorVariance noiseVariance =
        distortedOptimalMix priorVariance noiseVariance distortion ↔
      (distortion - 1) *
        (priorVariance * distortion - noiseVariance) = 0 := by
  have hunitDen : 0 < priorVariance + noiseVariance := add_pos hprior hnoise
  have hdistortedDen : 0 <
      priorVariance * distortion ^ 2 + noiseVariance := by
    positivity
  unfold unitModelHardwiredMix varianceKalmanGain distortedOptimalMix
  rw [div_eq_div_iff hunitDen.ne' hdistortedDen.ne']
  constructor
  · intro hcross
    have hcancel : priorVariance * distortion ^ 2 + noiseVariance =
        distortion * (priorVariance + noiseVariance) := by
      apply (mul_left_cancel₀ hprior.ne')
      calc
        priorVariance *
            (priorVariance * distortion ^ 2 + noiseVariance) =
          priorVariance * distortion *
            (priorVariance + noiseVariance) := hcross
        _ = priorVariance *
            (distortion * (priorVariance + noiseVariance)) := by ring
    calc
      (distortion - 1) *
          (priorVariance * distortion - noiseVariance) =
        (priorVariance * distortion ^ 2 + noiseVariance) -
          distortion * (priorVariance + noiseVariance) := by ring
      _ = 0 := sub_eq_zero.mpr hcancel
  · intro hfactor
    have hcalibration : priorVariance * distortion ^ 2 + noiseVariance =
        distortion * (priorVariance + noiseVariance) := by
      apply sub_eq_zero.mp
      calc
        (priorVariance * distortion ^ 2 + noiseVariance) -
            distortion * (priorVariance + noiseVariance) =
          (distortion - 1) *
            (priorVariance * distortion - noiseVariance) := by ring
        _ = 0 := hfactor
    rw [hcalibration]
    ring

/-- Learned mixing has strictly lower risk than uncorrected hardwired fusion
exactly when the false-unit coefficient is off the equality boundary. -/
theorem learnedMix_strictlyOutperforms_uncorrectedHardwiredFusion
    (priorVariance noiseVariance distortion : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance)
    (hoffBoundary :
      (distortion - 1) *
        (priorVariance * distortion - noiseVariance) ≠ 0) :
    distortedMeasurementRisk priorVariance noiseVariance distortion
        (distortedOptimalMix priorVariance noiseVariance distortion) <
      distortedMeasurementRisk priorVariance noiseVariance distortion
        (unitModelHardwiredMix priorVariance noiseVariance) := by
  have hden : 0 < priorVariance * distortion ^ 2 + noiseVariance := by
    positivity
  have hcoefficientNe : unitModelHardwiredMix priorVariance noiseVariance ≠
      distortedOptimalMix priorVariance noiseVariance distortion := by
    intro heq
    exact hoffBoundary
      ((unitModelHardwiredMix_eq_distortedOptimalMix_iff
        priorVariance noiseVariance distortion hprior hnoise).mp heq)
  have hexcess := distortedMeasurementRisk_sub_optimal_eq_square
    priorVariance noiseVariance distortion
    (unitModelHardwiredMix priorVariance noiseVariance) hprior hnoise
  have hsquare : 0 <
      (unitModelHardwiredMix priorVariance noiseVariance -
        distortedOptimalMix priorVariance noiseVariance distortion) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hcoefficientNe)
  nlinarith [mul_pos hden hsquare]

/-! ## Push the repair into the measurement map -/

/-- Noise variance after recalibrating `y` to `y / distortion`. -/
noncomputable def recalibratedNoiseVariance
    (noiseVariance distortion : ℝ) : ℝ :=
  noiseVariance / distortion ^ 2

/-- The effective raw-measurement coefficient of unit-model hardwired fusion
after measurement recalibration. -/
noncomputable def recalibratedHardwiredRawCoefficient
    (priorVariance noiseVariance distortion : ℝ) : ℝ :=
  varianceKalmanGain priorVariance
      (recalibratedNoiseVariance noiseVariance distortion) /
    distortion

/-- Linear factorization crown: recalibrating the observation and its noise
pushes the complete correction into the measurement map while fusion remains
the ordinary hardwired unit-observation rule. -/
theorem recalibratedHardwiredRawCoefficient_eq_distortedOptimalMix
    (priorVariance noiseVariance distortion : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance)
    (hdistortion : distortion ≠ 0) :
    recalibratedHardwiredRawCoefficient
        priorVariance noiseVariance distortion =
      distortedOptimalMix priorVariance noiseVariance distortion := by
  have hdistortionSq : 0 < distortion ^ 2 := sq_pos_of_ne_zero hdistortion
  have hrecalibratedNoise : 0 <
      recalibratedNoiseVariance noiseVariance distortion := by
    unfold recalibratedNoiseVariance
    positivity
  have hunitDen : 0 < priorVariance +
      recalibratedNoiseVariance noiseVariance distortion :=
    add_pos hprior hrecalibratedNoise
  have hdistortedDen : 0 <
      priorVariance * distortion ^ 2 + noiseVariance := by
    positivity
  unfold recalibratedHardwiredRawCoefficient recalibratedNoiseVariance
  unfold varianceKalmanGain distortedOptimalMix
  field_simp [hdistortion, hdistortionSq.ne', hunitDen.ne', hdistortedDen.ne']

/-- At the update level, learned raw mixing and recalibrated hardwired fusion
produce exactly the same posterior mean for every prior and measurement. -/
theorem recalibratedHardwiredUpdate_eq_distortedOptimalUpdate
    (priorVariance noiseVariance distortion priorMean measurement : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance)
    (hdistortion : distortion ≠ 0) :
    priorMean + varianceKalmanGain priorVariance
          (recalibratedNoiseVariance noiseVariance distortion) *
        (measurement / distortion - priorMean) =
      priorMean + distortedOptimalMix priorVariance noiseVariance distortion *
        (measurement - distortion * priorMean) := by
  have hcoefficient :=
    recalibratedHardwiredRawCoefficient_eq_distortedOptimalMix
      priorVariance noiseVariance distortion hprior hnoise hdistortion
  unfold recalibratedHardwiredRawCoefficient at hcoefficient
  field_simp [hdistortion] at hcoefficient ⊢
  rw [hcoefficient]
  ring

/-! ## Positive and negative fixtures -/

/-- Positive repair fixture: at `P=R=1, d=2`, learned/recalibrated fusion uses
coefficient `2/5` and strictly beats the false-unit half-gate. -/
theorem distortionRepair_positiveExample :
    distortedOptimalMix 1 1 2 = (2 / 5 : ℝ) ∧
      recalibratedHardwiredRawCoefficient 1 1 2 = (2 / 5 : ℝ) ∧
      distortedMeasurementRisk 1 1 2 (2 / 5) <
        distortedMeasurementRisk 1 1 2 (1 / 2) := by
  norm_num [distortedOptimalMix, recalibratedHardwiredRawCoefficient,
    recalibratedNoiseVariance, varianceKalmanGain, distortedMeasurementRisk]

/-- Negative strictness boundary: distortion `d=2` does not help learned
mixing when `P*d=R`; both coefficients are exactly `1/3`. -/
theorem distortionAlone_not_strict_negativeExample :
    unitModelHardwiredMix 1 2 = (1 / 3 : ℝ) ∧
      distortedOptimalMix 1 2 2 = (1 / 3 : ℝ) ∧
      distortedMeasurementRisk 1 2 2 (1 / 3) =
        distortedMeasurementRisk 1 2 2
          (distortedOptimalMix 1 2 2) := by
  norm_num [unitModelHardwiredMix, varianceKalmanGain, distortedOptimalMix,
    distortedMeasurementRisk]

#print axioms distortedMeasurementRisk_eq_scalarGainRisk
#print axioms distortedMeasurementRisk_sub_optimal_eq_square
#print axioms distortedOptimalMix_uniqueMinimizer
#print axioms unitModelHardwiredMix_eq_distortedOptimalMix_iff
#print axioms learnedMix_strictlyOutperforms_uncorrectedHardwiredFusion
#print axioms recalibratedHardwiredRawCoefficient_eq_distortedOptimalMix
#print axioms recalibratedHardwiredUpdate_eq_distortedOptimalUpdate
#print axioms distortionRepair_positiveExample
#print axioms distortionAlone_not_strict_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
