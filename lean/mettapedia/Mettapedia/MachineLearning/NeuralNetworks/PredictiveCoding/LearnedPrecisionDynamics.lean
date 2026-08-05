import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherGeometry

/-!
# Learned scalar precision dynamics

Ofner, Stober, and Wermter (2021), *Learning and Cognitive Systems with
Predictive Coding and Natural Gradients*, estimate prediction-error precision
and use precision-weighted local updates.  This file isolates the scalar
Gaussian learning problem behind Equations 4, 8, and 12--13.

For a positive prediction-error second moment, the Gaussian precision energy
has the unique positive optimum `precision = 1 / secondMoment`.  Direct
additive descent in precision coordinates can nevertheless leave the positive
domain.  Log-precision coordinates preserve positivity; their optimum is a
fixed point and the linearized update is stable exactly for rates in `(0, 4)`.

This is a scalar statistical calibration result.  It does not identify scalar
precision with the full neural-network Fisher matrix; the imported Fisher
geometry gives the exact Kronecker factorization and a correlated-activation
counterexample to that stronger claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Positive scalar Gaussian precision -/

/-- Expected scalar Gaussian negative log likelihood, up to constants that do
not depend on precision.  `secondMoment` is the expected squared residual. -/
noncomputable def scalarGaussianPrecisionEnergy
    (secondMoment precision : ℝ) : ℝ :=
  (precision * secondMoment - Real.log precision) / 2

/-- Gradient of the scalar Gaussian precision energy on the positive domain. -/
noncomputable def scalarGaussianPrecisionGradient
    (secondMoment precision : ℝ) : ℝ :=
  (secondMoment - 1 / precision) / 2

theorem scalarGaussianPrecisionEnergy_hasDerivAt
    (secondMoment precision : ℝ) (hprecision : precision ≠ 0) :
    HasDerivAt (scalarGaussianPrecisionEnergy secondMoment)
      (scalarGaussianPrecisionGradient secondMoment precision) precision := by
  have hlinear :
      HasDerivAt (fun p : ℝ => p * secondMoment) secondMoment precision := by
    simpa using (hasDerivAt_id precision).mul_const secondMoment
  have hlog : HasDerivAt Real.log (1 / precision) precision := by
    simpa [one_div] using Real.hasDerivAt_log hprecision
  exact (hlinear.sub hlog).div_const 2

/-- The inverse second moment is the only positive stationary precision. -/
theorem scalarGaussianPrecisionGradient_eq_zero_iff
    (secondMoment precision : ℝ)
    (hsecondMoment : 0 < secondMoment) (hprecision : 0 < precision) :
    scalarGaussianPrecisionGradient secondMoment precision = 0 ↔
      precision = 1 / secondMoment := by
  unfold scalarGaussianPrecisionGradient
  constructor
  · intro h
    have hsecondMomentNe : secondMoment ≠ 0 := ne_of_gt hsecondMoment
    have hprecisionNe : precision ≠ 0 := ne_of_gt hprecision
    field_simp [hprecisionNe] at h
    apply (eq_div_iff hsecondMomentNe).2
    nlinarith
  · rintro rfl
    simp

/-- The inverse-second-moment precision is a global positive minimizer. -/
theorem scalarGaussianPrecisionEnergy_minimized_at_inverseSecondMoment
    (secondMoment precision : ℝ)
    (hsecondMoment : 0 < secondMoment) (hprecision : 0 < precision) :
    scalarGaussianPrecisionEnergy secondMoment (1 / secondMoment) ≤
      scalarGaussianPrecisionEnergy secondMoment precision := by
  have hlog :=
    Real.log_le_sub_one_of_pos (mul_pos hprecision hsecondMoment)
  rw [Real.log_mul (ne_of_gt hprecision) (ne_of_gt hsecondMoment)] at hlog
  simp only [scalarGaussianPrecisionEnergy]
  rw [show Real.log (1 / secondMoment) = -Real.log secondMoment by
    simp [Real.log_inv]]
  have hsecondMomentNe : secondMoment ≠ 0 := ne_of_gt hsecondMoment
  field_simp [hsecondMomentNe]
  nlinarith

/-- Every other positive precision has strictly greater energy. -/
theorem scalarGaussianPrecisionEnergy_strict_of_ne_inverseSecondMoment
    (secondMoment precision : ℝ)
    (hsecondMoment : 0 < secondMoment) (hprecision : 0 < precision)
    (hne : precision ≠ 1 / secondMoment) :
    scalarGaussianPrecisionEnergy secondMoment (1 / secondMoment) <
      scalarGaussianPrecisionEnergy secondMoment precision := by
  have hsecondMomentNe : secondMoment ≠ 0 := ne_of_gt hsecondMoment
  have hproduct : precision * secondMoment ≠ 1 := by
    intro h
    apply hne
    apply (eq_div_iff hsecondMomentNe).2
    nlinarith
  have hlog := Real.log_lt_sub_one_of_pos
    (mul_pos hprecision hsecondMoment) hproduct
  rw [Real.log_mul (ne_of_gt hprecision) (ne_of_gt hsecondMoment)] at hlog
  simp only [scalarGaussianPrecisionEnergy]
  rw [show Real.log (1 / secondMoment) = -Real.log secondMoment by
    simp [Real.log_inv]]
  field_simp [hsecondMomentNe]
  nlinarith

/-- The source's scalar precision weighting is exactly inverse-variance
rescaling at the calibrated optimum. -/
theorem optimalPrecision_weightedError
    (secondMoment error : ℝ) :
    (1 / secondMoment) * error = error / secondMoment := by
  ring

/-! ## Additive-coordinate failure -/

/-- One additive gradient step in raw precision coordinates. -/
noncomputable def additivePrecisionStep
    (secondMoment rate precision : ℝ) : ℝ :=
  precision -
    rate * scalarGaussianPrecisionGradient secondMoment precision

/-- A valid positive starting precision can cross zero in one additive step. -/
theorem additivePrecisionStep_can_leave_positiveDomain :
    additivePrecisionStep 4 1 1 = -(1 / 2 : ℝ) := by
  norm_num [additivePrecisionStep, scalarGaussianPrecisionGradient]

/-- With zero residual second moment, every positive finite precision still
has a negative energy gradient; there is no finite stationary calibration. -/
theorem zeroSecondMoment_gradient_negative
    (precision : ℝ) (hprecision : 0 < precision) :
    scalarGaussianPrecisionGradient 0 precision < 0 := by
  unfold scalarGaussianPrecisionGradient
  have hinverse : 0 < 1 / precision := by positivity
  linarith

/-! ## Positivity-preserving log-precision coordinates -/

/-- Chain-rule gradient with respect to log precision. -/
noncomputable def logPrecisionGradient
    (secondMoment logPrecision : ℝ) : ℝ :=
  (Real.exp logPrecision * secondMoment - 1) / 2

/-- One gradient step in log-precision coordinates. -/
noncomputable def logPrecisionStep
    (secondMoment rate logPrecision : ℝ) : ℝ :=
  logPrecision - rate * logPrecisionGradient secondMoment logPrecision

/-- Decode a log-precision coordinate after one step. -/
noncomputable def decodedLogPrecisionStep
    (secondMoment rate logPrecision : ℝ) : ℝ :=
  Real.exp (logPrecisionStep secondMoment rate logPrecision)

theorem decodedLogPrecisionStep_pos
    (secondMoment rate logPrecision : ℝ) :
    0 < decodedLogPrecisionStep secondMoment rate logPrecision := by
  exact Real.exp_pos _

theorem exp_neg_log_eq_inverse
    (secondMoment : ℝ) (hsecondMoment : 0 < secondMoment) :
    Real.exp (-Real.log secondMoment) = 1 / secondMoment := by
  simp [Real.exp_neg, Real.exp_log hsecondMoment]

/-- The calibrated log precision has zero gradient. -/
theorem logPrecisionGradient_at_optimum
    (secondMoment : ℝ) (hsecondMoment : 0 < secondMoment) :
    logPrecisionGradient secondMoment (-Real.log secondMoment) = 0 := by
  unfold logPrecisionGradient
  rw [exp_neg_log_eq_inverse secondMoment hsecondMoment]
  field_simp [ne_of_gt hsecondMoment]
  norm_num

/-- The calibrated log precision is fixed for every update rate. -/
theorem logPrecisionStep_at_optimum
    (secondMoment rate : ℝ) (hsecondMoment : 0 < secondMoment) :
    logPrecisionStep secondMoment rate (-Real.log secondMoment) =
      -Real.log secondMoment := by
  simp [logPrecisionStep,
    logPrecisionGradient_at_optimum secondMoment hsecondMoment]

/-- Exact derivative of one log-precision update. -/
theorem logPrecisionStep_hasDerivAt
    (secondMoment rate logPrecision : ℝ) :
    HasDerivAt (logPrecisionStep secondMoment rate)
      (1 - rate * (Real.exp logPrecision * secondMoment / 2))
      logPrecision := by
  have hexp :
      HasDerivAt (fun p : ℝ => Real.exp p * secondMoment)
        (Real.exp logPrecision * secondMoment) logPrecision := by
    simpa using Real.hasDerivAt_exp logPrecision |>.mul_const secondMoment
  have hgradient :
      HasDerivAt (logPrecisionGradient secondMoment)
        (Real.exp logPrecision * secondMoment / 2) logPrecision :=
    (hexp.sub_const 1).div_const 2
  exact (hasDerivAt_id logPrecision).sub (hgradient.const_mul rate)

/-- At the calibrated precision, the update's linear multiplier is
`1 - rate / 2`. -/
theorem logPrecisionStep_hasDerivAt_optimum
    (secondMoment rate : ℝ) (hsecondMoment : 0 < secondMoment) :
    HasDerivAt (logPrecisionStep secondMoment rate)
      (1 - rate / 2) (-Real.log secondMoment) := by
  have hderivative :=
    logPrecisionStep_hasDerivAt
      secondMoment rate (-Real.log secondMoment)
  convert hderivative using 1
  rw [exp_neg_log_eq_inverse secondMoment hsecondMoment]
  field_simp [ne_of_gt hsecondMoment]

/-- The exact local stability interval of the scalar log-precision update. -/
theorem abs_logPrecisionMultiplier_lt_one_iff (rate : ℝ) :
    |1 - rate / 2| < 1 ↔ 0 < rate ∧ rate < 4 := by
  rw [abs_lt]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor <;> linarith
  · rintro ⟨hpositive, hfour⟩
    constructor <;> linarith

#print axioms scalarGaussianPrecisionEnergy_minimized_at_inverseSecondMoment
#print axioms scalarGaussianPrecisionEnergy_strict_of_ne_inverseSecondMoment
#print axioms additivePrecisionStep_can_leave_positiveDomain
#print axioms zeroSecondMoment_gradient_negative
#print axioms decodedLogPrecisionStep_pos
#print axioms logPrecisionStep_at_optimum
#print axioms logPrecisionStep_hasDerivAt_optimum
#print axioms abs_logPrecisionMultiplier_lt_one_iff

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
