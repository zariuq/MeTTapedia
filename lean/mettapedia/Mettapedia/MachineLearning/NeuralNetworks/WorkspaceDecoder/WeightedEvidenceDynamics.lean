import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NaturalEvidenceCoordinates
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NonstationaryFusion
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState
import Mettapedia.PLN.Evidence.WeightedEvidence

/-!
# Drift-calibrated weighted evidence for workspace belief registers

This file transports the scalar jump-model results into the weighted evidence
layer.  The derived retention is the already-proved `P/(P+Q)`: it acts on PLN
weighted counts for temporal forgetting and on Gaussian prior precision for
the calibrated estimator.  The Gaussian optimality theorem is reused rather
than re-proved.

Confidence is no longer monotone in wall-clock time when evidence fades.  Its
replacement law is explicit: confidence is monotone in current effective
evidence, and online fade-then-fuse updates that quantity by
`retention * oldEffective + freshEffective`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

/-! ## Exact-count chart preservation -/

/-- Lifting exact natural counts into weighted registers preserves the
existing derived strength/confidence chart exactly. -/
theorem weightedDerivedChart_preserves_exactCounts
    (κ : ℝ≥0∞) (evidence : BinEvNat) :
    WeightedEvidence.derivedSTV κ (WeightedEvidence.ofBinEvNat evidence) =
      binEvNatDerivedSTV κ evidence :=
  rfl

/-! ## The retention registered from jump statistics -/

/-- Weighted-evidence retention obtained from the jump-model information
retention proved in `NonstationaryFusion`. -/
noncomputable def derivedJumpEvidenceRetention
    (oldVariance jumpVariance : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (jumpInformationRetention oldVariance jumpVariance)

/-- The stationary boundary `Q=0` registers unit retention. -/
theorem derivedJumpEvidenceRetention_zeroJump
    (oldVariance : ℝ) (hold : 0 < oldVariance) :
    derivedJumpEvidenceRetention oldVariance 0 = 1 := by
  simp [derivedJumpEvidenceRetention, jumpInformationRetention, hold.ne']

/-- Under the jump model's variance conditions, the derived retention is an
honest forgetting factor rather than an evidence amplifier. -/
theorem derivedJumpEvidenceRetention_le_one
    (oldVariance jumpVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance) :
    derivedJumpEvidenceRetention oldVariance jumpVariance ≤ 1 := by
  have hsum : 0 < oldVariance + jumpVariance :=
    add_pos_of_pos_of_nonneg hold hjump
  have hreal : jumpInformationRetention oldVariance jumpVariance ≤ 1 := by
    unfold jumpInformationRetention
    rw [div_le_one hsum]
    exact le_add_of_nonneg_right hjump
  simpa [derivedJumpEvidenceRetention] using ENNReal.ofReal_le_ofReal hreal

/-- Therefore zero process noise recovers exact weighted addition. -/
theorem derivedZeroJump_fadeThenFuse_eq_add
    (oldVariance : ℝ) (hold : 0 < oldVariance)
    (old fresh : WeightedEvidence) :
    WeightedEvidence.fadeThenFuse
        (derivedJumpEvidenceRetention oldVariance 0) old fresh =
      old + fresh := by
  rw [derivedJumpEvidenceRetention_zeroJump oldVariance hold]
  exact WeightedEvidence.fadeThenFuse_one old fresh

/-- Repeated drift-calibrated fading has the exact exponential retention
trajectory inherited from the scalar action. -/
theorem derivedJumpFade_iterate
    (oldVariance jumpVariance : ℝ)
    (evidence : WeightedEvidence) (steps : ℕ) :
    (fun current =>
      derivedJumpEvidenceRetention oldVariance jumpVariance • current)^[steps]
        evidence =
      derivedJumpEvidenceRetention oldVariance jumpVariance ^ steps • evidence :=
  WeightedEvidence.fade_iterate
    (derivedJumpEvidenceRetention oldVariance jumpVariance) evidence steps

/-! ## Transport of jump-optimal calibration -/

/-- Gaussian prior precision after applying the T3-derived information
retention to the old precision. -/
noncomputable def fadedPriorPrecision
    (oldVariance jumpVariance : ℝ) : ℝ :=
  jumpInformationRetention oldVariance jumpVariance * oldVariance⁻¹

/-- The faded precision is exactly the jump-predictive precision.  This is a
direct transport of the existing nonstationarity theorem. -/
theorem fadedPriorPrecision_eq_jumpPredictivePrecision
    (oldVariance jumpVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance) :
    fadedPriorPrecision oldVariance jumpVariance =
      (jumpPredictiveVariance oldVariance jumpVariance)⁻¹ := by
  exact (jumpPredictivePrecision_eq_decayedOldPrecision
    oldVariance jumpVariance hold hjump).symm

/-- Fading old precision and then fusing the observation produces exactly the
jump-optimal gain. -/
theorem fadedPrecisionGain_eq_jumpOptimalGain
    (oldVariance jumpVariance noiseVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance)
    (hnoise : 0 < noiseVariance) :
    precisionGain (fadedPriorPrecision oldVariance jumpVariance)
        noiseVariance⁻¹ =
      jumpOptimalGain oldVariance jumpVariance noiseVariance := by
  rw [fadedPriorPrecision_eq_jumpPredictivePrecision
    oldVariance jumpVariance hold hjump]
  unfold jumpOptimalGain
  simpa [precisionGain, scalarKalmanGain] using
    (varianceKalmanGain_eq_scalarKalmanGain_reciprocalPrecision
      (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance
      (by unfold jumpPredictiveVariance; positivity) hnoise).symm

/-- Estimator using faded prior precision and ordinary hardwired fusion. -/
noncomputable def fadedPrecisionEstimator
    (oldValue measurement oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  precisionInterpolate oldValue measurement
    (fadedPriorPrecision oldVariance jumpVariance) noiseVariance⁻¹

/-- Calibration crown: the faded hardwired estimator is exactly the already
proved jump-optimal affine update. -/
theorem fadedPrecisionEstimator_eq_jumpOptimalUpdate
    (oldValue measurement oldVariance jumpVariance noiseVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance)
    (hnoise : 0 < noiseVariance) :
    fadedPrecisionEstimator oldValue measurement oldVariance
        jumpVariance noiseVariance =
      oldValue + jumpOptimalGain oldVariance jumpVariance noiseVariance *
        (measurement - oldValue) := by
  unfold fadedPrecisionEstimator precisionInterpolate
  rw [fadedPrecisionGain_eq_jumpOptimalGain
    oldVariance jumpVariance noiseVariance hold hjump hnoise]

/-- Risk-optimality is transported from the sealed Kalman minimizer after the
gain-identification theorem; no new optimality proof is introduced. -/
theorem fadedPrecisionGain_minimizesJumpRisk
    (oldVariance jumpVariance noiseVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance)
    (hnoise : 0 < noiseVariance) :
    ∀ gate,
      varianceGateRisk
          (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance
          (precisionGain (fadedPriorPrecision oldVariance jumpVariance)
            noiseVariance⁻¹) ≤
        varianceGateRisk
          (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance gate := by
  intro gate
  rw [fadedPrecisionGain_eq_jumpOptimalGain
    oldVariance jumpVariance noiseVariance hold hjump hnoise]
  exact (varianceKalmanGain_uniqueMinimizer
    (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance
    (by unfold jumpPredictiveVariance; positivity) hnoise).1 gate

/-! ## Confidence tracks current effective evidence -/

/-- Online fading and fusion update effective evidence by the registered
retention-weighted old total plus the full fresh total. -/
theorem effectiveEvidence_fadeThenFuse
    (retention : ℝ≥0∞) (old fresh : WeightedEvidence) :
    WeightedEvidence.effectiveEvidence
        (WeightedEvidence.fadeThenFuse retention old fresh) =
      retention * WeightedEvidence.effectiveEvidence old +
        WeightedEvidence.effectiveEvidence fresh := by
  unfold WeightedEvidence.fadeThenFuse
  rw [WeightedEvidence.effectiveEvidence_add,
    WeightedEvidence.effectiveEvidence_smul]

/-- Replacement for wall-clock monotonicity: confidence is monotone whenever
the current effective evidence is monotone. -/
theorem weightedConfidence_mono_of_effectiveEvidence
    (κ : ℝ≥0∞) (hκ_pos : κ ≠ 0) (hκ_top : κ ≠ ⊤)
    (first second : WeightedEvidence)
    (hsecondTop : WeightedEvidence.effectiveEvidence second ≠ ⊤)
    (heffective : WeightedEvidence.effectiveEvidence first ≤
      WeightedEvidence.effectiveEvidence second) :
    BinaryEvidence.toConfidence κ first ≤
      BinaryEvidence.toConfidence κ second := by
  exact BinaryEvidence.confidence_monotone_in_total κ first second
    hκ_pos hκ_top hsecondTop heffective

/-! ## Positive and negative fixtures -/

/-- Positive fixture: half retention halves effective evidence. -/
theorem halfRetention_halvesEffectiveEvidence :
    WeightedEvidence.effectiveEvidence
        ((1 / 2 : ℝ≥0∞) • (⟨2, 2⟩ : WeightedEvidence)) = 2 := by
  unfold WeightedEvidence.effectiveEvidence BinaryEvidence.total
  simp only [HSMul.hSMul, SMul.smul]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- Negative boundary: confidence can strictly fall after honest fractional
forgetting, so the exact-count wall-clock monotonicity theorem cannot survive. -/
theorem fractionalFade_lowersConfidence_negativeExample :
    BinaryEvidence.toConfidence 1
        ((1 / 2 : ℝ≥0∞) • (⟨2, 0⟩ : WeightedEvidence)) <
      BinaryEvidence.toConfidence 1 (⟨2, 0⟩ : WeightedEvidence) := by
  unfold BinaryEvidence.toConfidence BinaryEvidence.total
  simp only [HSMul.hSMul, SMul.smul]
  simp only [mul_zero, add_zero]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num

/-- Positive-jump boundary: the statistically derived retention itself can
strictly lower confidence, not merely an arbitrary hand-chosen fade. -/
theorem positiveJumpDerivedRetention_lowersConfidence_negativeExample :
    BinaryEvidence.toConfidence 1
        (derivedJumpEvidenceRetention 1 1 •
          (⟨2, 0⟩ : WeightedEvidence)) <
      BinaryEvidence.toConfidence 1 (⟨2, 0⟩ : WeightedEvidence) := by
  have hretention :
      derivedJumpEvidenceRetention 1 1 = (1 / 2 : ℝ≥0∞) := by
    change ENNReal.ofReal ((1 : ℝ) / (1 + 1)) = (1 / 2 : ℝ≥0∞)
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 + 1)]
    norm_num
  rw [hretention]
  exact fractionalFade_lowersConfidence_negativeExample

#print axioms weightedDerivedChart_preserves_exactCounts
#print axioms derivedJumpEvidenceRetention_zeroJump
#print axioms derivedJumpEvidenceRetention_le_one
#print axioms derivedZeroJump_fadeThenFuse_eq_add
#print axioms derivedJumpFade_iterate
#print axioms fadedPriorPrecision_eq_jumpPredictivePrecision
#print axioms fadedPrecisionGain_eq_jumpOptimalGain
#print axioms fadedPrecisionEstimator_eq_jumpOptimalUpdate
#print axioms fadedPrecisionGain_minimizesJumpRisk
#print axioms effectiveEvidence_fadeThenFuse
#print axioms weightedConfidence_mono_of_effectiveEvidence
#print axioms halfRetention_halvesEffectiveEvidence
#print axioms fractionalFade_lowersConfidence_negativeExample
#print axioms positiveJumpDerivedRetention_lowersConfidence_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
