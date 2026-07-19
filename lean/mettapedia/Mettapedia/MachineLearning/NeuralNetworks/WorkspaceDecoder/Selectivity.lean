import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.KalmanCorrespondence

/-!
# Selective-gate separation under changing observation noise

For a scalar unit-observation model, the posterior mean-squared error of gate
`g` is `(1-g)² P + g² R`, where `P` is prior variance and `R` is observation
noise variance.  Completing the square shows that the unique optimal gate is
the Kalman gain `P/(P+R)`.

For two one-step regimes that share a prior variance but have different
positive noise variances, their optimal gates differ.  Consequently every
single constant gate has strictly greater total risk than selecting the two
Kalman gains separately.  This reset/steady-prior comparison does not model
sequential posterior-covariance propagation.  It is a linear-Gaussian reason
input-dependent gating can matter, not a claim about a trained nonlinear
selective SSM.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Variance-coordinate Kalman risk -/

/-- Unit-observation scalar Kalman gain in variance coordinates. -/
noncomputable def varianceKalmanGain
    (priorVariance noiseVariance : ℝ) : ℝ :=
  priorVariance / (priorVariance + noiseVariance)

/-- Posterior mean-squared error for a scalar correction gate. -/
noncomputable def varianceGateRisk
    (priorVariance noiseVariance gate : ℝ) : ℝ :=
  (1 - gate) ^ 2 * priorVariance + gate ^ 2 * noiseVariance

/-- Variance- and precision-coordinate Kalman gains agree. -/
theorem varianceKalmanGain_eq_scalarKalmanGain_reciprocalPrecision
    (priorVariance noiseVariance : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    varianceKalmanGain priorVariance noiseVariance =
      scalarKalmanGain 1 priorVariance⁻¹ noiseVariance⁻¹ := by
  have hprior_ne : priorVariance ≠ 0 := ne_of_gt hprior
  have hnoise_ne : noiseVariance ≠ 0 := ne_of_gt hnoise
  have hsum : priorVariance + noiseVariance ≠ 0 :=
    ne_of_gt (add_pos hprior hnoise)
  unfold varianceKalmanGain scalarKalmanGain
  field_simp [hprior_ne, hnoise_ne, hsum]
  ring

/-- Exact excess-risk square around the variance-coordinate Kalman gain. -/
theorem varianceGateRisk_sub_kalman_eq_square
    (priorVariance noiseVariance gate : ℝ)
    (hsum : priorVariance + noiseVariance ≠ 0) :
    varianceGateRisk priorVariance noiseVariance gate -
        varianceGateRisk priorVariance noiseVariance
          (varianceKalmanGain priorVariance noiseVariance) =
      (priorVariance + noiseVariance) *
        (gate - varianceKalmanGain priorVariance noiseVariance) ^ 2 := by
  unfold varianceGateRisk varianceKalmanGain
  field_simp [hsum]
  ring

/-- Positive variances make the Kalman gate the unique scalar risk minimizer. -/
theorem varianceKalmanGain_uniqueMinimizer
    (priorVariance noiseVariance : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    (∀ gate,
      varianceGateRisk priorVariance noiseVariance
          (varianceKalmanGain priorVariance noiseVariance) ≤
        varianceGateRisk priorVariance noiseVariance gate) ∧
    (∀ gate,
      varianceGateRisk priorVariance noiseVariance gate =
          varianceGateRisk priorVariance noiseVariance
            (varianceKalmanGain priorVariance noiseVariance) ↔
        gate = varianceKalmanGain priorVariance noiseVariance) := by
  have hsum : 0 < priorVariance + noiseVariance := add_pos hprior hnoise
  constructor
  · intro gate
    have hexcess := varianceGateRisk_sub_kalman_eq_square
      priorVariance noiseVariance gate hsum.ne'
    rw [sub_eq_iff_eq_add] at hexcess
    rw [hexcess]
    exact le_add_of_nonneg_left (mul_nonneg hsum.le (sq_nonneg _))
  · intro gate
    constructor
    · intro heq
      have hexcess := varianceGateRisk_sub_kalman_eq_square
        priorVariance noiseVariance gate hsum.ne'
      rw [heq, sub_self] at hexcess
      have hsquare :
          (gate - varianceKalmanGain priorVariance noiseVariance) ^ 2 = 0 :=
        (mul_eq_zero.mp hexcess.symm).resolve_left hsum.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    · rintro rfl
      rfl

/-! ## Two-regime selectivity separation -/

/-- Total risk of one constant gate across two noise regimes. -/
noncomputable def twoRegimeConstantGateRisk
    (priorVariance firstNoise secondNoise gate : ℝ) : ℝ :=
  varianceGateRisk priorVariance firstNoise gate +
    varianceGateRisk priorVariance secondNoise gate

/-- Total risk when each regime selects its own Kalman gate. -/
noncomputable def twoRegimeSelectiveRisk
    (priorVariance firstNoise secondNoise : ℝ) : ℝ :=
  varianceGateRisk priorVariance firstNoise
      (varianceKalmanGain priorVariance firstNoise) +
    varianceGateRisk priorVariance secondNoise
      (varianceKalmanGain priorVariance secondNoise)

/-- Exact two-regime excess-risk decomposition. -/
theorem twoRegime_constant_sub_selective_eq_squares
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hfirst : priorVariance + firstNoise ≠ 0)
    (hsecond : priorVariance + secondNoise ≠ 0) :
    twoRegimeConstantGateRisk priorVariance firstNoise secondNoise gate -
        twoRegimeSelectiveRisk priorVariance firstNoise secondNoise =
      (priorVariance + firstNoise) *
          (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 +
        (priorVariance + secondNoise) *
          (gate - varianceKalmanGain priorVariance secondNoise) ^ 2 := by
  have h₁ := varianceGateRisk_sub_kalman_eq_square
    priorVariance firstNoise gate hfirst
  have h₂ := varianceGateRisk_sub_kalman_eq_square
    priorVariance secondNoise gate hsecond
  unfold twoRegimeConstantGateRisk twoRegimeSelectiveRisk
  linarith

/-- Distinct positive noise variances induce distinct Kalman gates. -/
theorem varianceKalmanGain_ne_of_noise_ne
    (priorVariance firstNoise secondNoise : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hnoise : firstNoise ≠ secondNoise) :
    varianceKalmanGain priorVariance firstNoise ≠
      varianceKalmanGain priorVariance secondNoise := by
  have hsum₁ : priorVariance + firstNoise ≠ 0 :=
    ne_of_gt (add_pos hprior hfirst)
  have hsum₂ : priorVariance + secondNoise ≠ 0 :=
    ne_of_gt (add_pos hprior hsecond)
  intro heq
  unfold varianceKalmanGain at heq
  field_simp [hsum₁, hsum₂] at heq
  exact hnoise (by nlinarith)

/-- Selectivity crown: with nonconstant positive observation noise, every
constant gate is strictly suboptimal to the two time-varying Kalman gates. -/
theorem everyConstantGate_strictlySuboptimal
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hnoise : firstNoise ≠ secondNoise) :
    twoRegimeSelectiveRisk priorVariance firstNoise secondNoise <
      twoRegimeConstantGateRisk priorVariance firstNoise secondNoise gate := by
  have hsum₁ : 0 < priorVariance + firstNoise := add_pos hprior hfirst
  have hsum₂ : 0 < priorVariance + secondNoise := add_pos hprior hsecond
  have hgates := varianceKalmanGain_ne_of_noise_ne
    priorVariance firstNoise secondNoise hprior hfirst hsecond hnoise
  have hexcess := twoRegime_constant_sub_selective_eq_squares
    priorVariance firstNoise secondNoise gate hsum₁.ne' hsum₂.ne'
  have hpositive : 0 <
      (priorVariance + firstNoise) *
          (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 +
        (priorVariance + secondNoise) *
          (gate - varianceKalmanGain priorVariance secondNoise) ^ 2 := by
    by_cases hgate : gate = varianceKalmanGain priorVariance firstNoise
    · have hsecondGate : gate ≠ varianceKalmanGain priorVariance secondNoise := by
        intro heq
        exact hgates (hgate.symm.trans heq)
      have hsecondSquare : 0 <
          (gate - varianceKalmanGain priorVariance secondNoise) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hsecondGate)
      positivity
    · have hfirstSquare : 0 <
          (gate - varianceKalmanGain priorVariance firstNoise) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hgate)
      positivity
  linarith

/-! ## Positive and negative fixtures -/

/-- Concrete two-regime separation: prior variance one and noise variances one
and three select gates `1/2` and `1/4`; constant gate `1/2` pays excess `1/4`. -/
theorem concrete_twoNoise_selectivity_separation :
    twoRegimeSelectiveRisk 1 1 3 = 5 / 4 ∧
      twoRegimeConstantGateRisk 1 1 3 (1 / 2) = 3 / 2 ∧
      twoRegimeSelectiveRisk 1 1 3 <
        twoRegimeConstantGateRisk 1 1 3 (1 / 2) := by
  norm_num [twoRegimeSelectiveRisk, twoRegimeConstantGateRisk,
    varianceGateRisk, varianceKalmanGain]

/-- Negative boundary: when noise is constant, selecting the same Kalman gate
twice has exactly the constant-gate risk, so strict separation is impossible. -/
theorem constantNoise_no_selectivitySeparation
    (priorVariance noiseVariance : ℝ) :
    twoRegimeConstantGateRisk priorVariance noiseVariance noiseVariance
        (varianceKalmanGain priorVariance noiseVariance) =
      twoRegimeSelectiveRisk priorVariance noiseVariance noiseVariance := by
  rfl

#print axioms varianceKalmanGain_eq_scalarKalmanGain_reciprocalPrecision
#print axioms varianceKalmanGain_uniqueMinimizer
#print axioms everyConstantGate_strictlySuboptimal
#print axioms concrete_twoNoise_selectivity_separation
#print axioms constantNoise_no_selectivitySeparation

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
