import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Selectivity

/-!
# Nonstationary boundary of monotone evidence accumulation

This file studies one scalar linear-Gaussian parameter-jump step.  An old
posterior error variance `P` is inflated to predictive variance `P + Q` by an
independent zero-mean jump of variance `Q`; the next observation has noise
variance `R`.  The optimal correction gain is therefore `(P+Q)/(P+Q+R)`.

A monotone evidence accumulator can only preserve or reduce its stored
variance, so its effective variance `A` satisfies `0 ≤ A ≤ P`.  When `Q > 0`,
every such accumulator selects a strictly smaller gain and incurs strictly
larger one-step risk.  The derived repair decays old information by
`P/(P+Q)`.  Its moment update retains old state by `R/(P+Q+R)`, yielding exact
exponential fading under repeated fixed-regime updates.

The scope is the declared scalar jump model.  No claim is made that a single
constant decay is optimal for arbitrary nonlinear or unknown drift.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Jump-aware gain and the monotone-accumulator boundary -/

/-- Predictive variance after an independent parameter jump. -/
noncomputable def jumpPredictiveVariance
    (oldVariance jumpVariance : ℝ) : ℝ :=
  oldVariance + jumpVariance

/-- Risk-optimal observation gain after the parameter jump. -/
noncomputable def jumpOptimalGain
    (oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  varianceKalmanGain
    (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance

/-- Variance signature of a confidence-monotone evidence accumulator. -/
def MonotoneAccumulatorVariance
    (oldVariance retainedVariance : ℝ) : Prop :=
  0 ≤ retainedVariance ∧ retainedVariance ≤ oldVariance

/-- Any confidence-monotone accumulator uses a strictly smaller correction
gain than the jump-aware filter when process variance is positive. -/
theorem monotoneAccumulatorGain_lt_jumpOptimalGain
    (oldVariance jumpVariance noiseVariance retainedVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 < jumpVariance)
    (hnoise : 0 < noiseVariance)
    (hretained : MonotoneAccumulatorVariance oldVariance retainedVariance) :
    varianceKalmanGain retainedVariance noiseVariance <
      jumpOptimalGain oldVariance jumpVariance noiseVariance := by
  have hretainedDen : 0 < retainedVariance + noiseVariance :=
    add_pos_of_nonneg_of_pos hretained.1 hnoise
  have hpredictive : 0 < jumpPredictiveVariance oldVariance jumpVariance := by
    unfold jumpPredictiveVariance
    positivity
  have hpredictiveDen : 0 <
      jumpPredictiveVariance oldVariance jumpVariance + noiseVariance :=
    add_pos hpredictive hnoise
  unfold jumpOptimalGain varianceKalmanGain
  rw [div_lt_div_iff₀ hretainedDen hpredictiveDen]
  unfold jumpPredictiveVariance
  have hvarianceLt : retainedVariance < oldVariance + jumpVariance := by
    nlinarith [hretained.2]
  have hweightedLt : retainedVariance * noiseVariance <
      (oldVariance + jumpVariance) * noiseVariance :=
    mul_lt_mul_of_pos_right hvarianceLt hnoise
  nlinarith

/-- Nonstationarity crown: after any positive-variance jump, every monotone
evidence accumulator is strictly suboptimal for the actual jump-regime risk. -/
theorem monotoneEvidenceAccumulator_strictlySuboptimalAfterJump
    (oldVariance jumpVariance noiseVariance retainedVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 < jumpVariance)
    (hnoise : 0 < noiseVariance)
    (hretained : MonotoneAccumulatorVariance oldVariance retainedVariance) :
    varianceGateRisk (jumpPredictiveVariance oldVariance jumpVariance)
        noiseVariance
        (jumpOptimalGain oldVariance jumpVariance noiseVariance) <
      varianceGateRisk (jumpPredictiveVariance oldVariance jumpVariance)
        noiseVariance
        (varianceKalmanGain retainedVariance noiseVariance) := by
  have hpredictive : 0 < jumpPredictiveVariance oldVariance jumpVariance := by
    unfold jumpPredictiveVariance
    positivity
  have hsum : jumpPredictiveVariance oldVariance jumpVariance +
      noiseVariance ≠ 0 := ne_of_gt (add_pos hpredictive hnoise)
  have hgateLt := monotoneAccumulatorGain_lt_jumpOptimalGain
    oldVariance jumpVariance noiseVariance retainedVariance
    hold hjump hnoise hretained
  unfold jumpOptimalGain at hgateLt
  have hexcess := varianceGateRisk_sub_kalman_eq_square
    (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance
    (varianceKalmanGain retainedVariance noiseVariance) hsum
  have hsquare : 0 <
      (varianceKalmanGain retainedVariance noiseVariance -
        varianceKalmanGain
          (jumpPredictiveVariance oldVariance jumpVariance)
          noiseVariance) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hgateLt.ne)
  have hcoefficient : 0 <
      jumpPredictiveVariance oldVariance jumpVariance + noiseVariance :=
    add_pos hpredictive hnoise
  unfold jumpOptimalGain
  nlinarith [mul_pos hcoefficient hsquare]

/-! ## The decay dictated by jump statistics -/

/-- Fraction of old information retained after adding process variance. -/
noncomputable def jumpInformationRetention
    (oldVariance jumpVariance : ℝ) : ℝ :=
  oldVariance / (oldVariance + jumpVariance)

/-- Inflating covariance by the jump is exactly multiplicative decay of the
old natural precision. -/
theorem jumpPredictivePrecision_eq_decayedOldPrecision
    (oldVariance jumpVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance) :
    (jumpPredictiveVariance oldVariance jumpVariance)⁻¹ =
      jumpInformationRetention oldVariance jumpVariance * oldVariance⁻¹ := by
  have hsum : 0 < oldVariance + jumpVariance :=
    add_pos_of_pos_of_nonneg hold hjump
  unfold jumpPredictiveVariance jumpInformationRetention
  field_simp [hold.ne', hsum.ne']

/-- A positive jump forces strict old-information decay. -/
theorem jumpInformationRetention_mem_Ioo
    (oldVariance jumpVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 < jumpVariance) :
    jumpInformationRetention oldVariance jumpVariance ∈ Set.Ioo (0 : ℝ) 1 := by
  have hsum : 0 < oldVariance + jumpVariance := add_pos hold hjump
  constructor
  · unfold jumpInformationRetention
    positivity
  · unfold jumpInformationRetention
    rw [div_lt_one hsum]
    linarith

/-- Fraction of the old moment retained by the jump-optimal correction step. -/
noncomputable def jumpMomentRetention
    (oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  1 - jumpOptimalGain oldVariance jumpVariance noiseVariance

/-- The moment-retention rate is determined by process and observation
statistics: `R/(P+Q+R)`. -/
theorem jumpMomentRetention_eq_noise_div_total
    (oldVariance jumpVariance noiseVariance : ℝ)
    (hsum : oldVariance + jumpVariance + noiseVariance ≠ 0) :
    jumpMomentRetention oldVariance jumpVariance noiseVariance =
      noiseVariance /
        (oldVariance + jumpVariance + noiseVariance) := by
  unfold jumpMomentRetention jumpOptimalGain jumpPredictiveVariance
  unfold varianceKalmanGain
  field_simp [hsum]
  ring

/-- One fixed-regime fading update written in the moment chart. -/
noncomputable def affineFadingStep
    (retention measurement state : ℝ) : ℝ :=
  retention * state + (1 - retention) * measurement

/-- Repeated fixed-regime fading has an exact exponential memory trace. -/
theorem affineFadingStep_iterate_closedForm
    (retention measurement initial : ℝ) (steps : ℕ) :
    (affineFadingStep retention measurement)^[steps] initial =
      measurement + retention ^ steps * (initial - measurement) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold affineFadingStep
      rw [pow_succ]
      ring

/-- The jump-aware Kalman update is the fading step with the statistically
derived moment-retention rate. -/
theorem jumpOptimalUpdate_eq_affineFadingStep
    (oldVariance jumpVariance noiseVariance oldValue measurement : ℝ) :
    oldValue + jumpOptimalGain oldVariance jumpVariance noiseVariance *
        (measurement - oldValue) =
      affineFadingStep
        (jumpMomentRetention oldVariance jumpVariance noiseVariance)
        measurement oldValue := by
  unfold affineFadingStep jumpMomentRetention
  ring

/-! ## Positive and negative fixtures -/

/-- Positive stationary boundary: with zero process variance, no precision
decay is required and the jump gain is the ordinary stationary gain. -/
theorem zeroJump_recovers_stationaryFusion_positiveExample :
    jumpInformationRetention 2 0 = 1 ∧
      jumpOptimalGain 2 0 3 = varianceKalmanGain 2 3 := by
  norm_num [jumpInformationRetention, jumpOptimalGain, jumpPredictiveVariance]

/-- Negative open-world fixture: a unit process jump makes a monotone unit
variance accumulator use gain `1/2` instead of the optimal `2/3`. -/
theorem positiveJump_monotoneAccumulator_negativeExample :
    varianceKalmanGain 1 1 = (1 / 2 : ℝ) ∧
      jumpOptimalGain 1 1 1 = (2 / 3 : ℝ) ∧
      varianceGateRisk 2 1 (2 / 3) < varianceGateRisk 2 1 (1 / 2) := by
  norm_num [varianceKalmanGain, jumpOptimalGain, jumpPredictiveVariance,
    varianceGateRisk]

#print axioms monotoneAccumulatorGain_lt_jumpOptimalGain
#print axioms monotoneEvidenceAccumulator_strictlySuboptimalAfterJump
#print axioms jumpPredictivePrecision_eq_decayedOldPrecision
#print axioms jumpInformationRetention_mem_Ioo
#print axioms jumpMomentRetention_eq_noise_div_total
#print axioms affineFadingStep_iterate_closedForm
#print axioms jumpOptimalUpdate_eq_affineFadingStep
#print axioms zeroJump_recovers_stationaryFusion_positiveExample
#print axioms positiveJump_monotoneAccumulator_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
