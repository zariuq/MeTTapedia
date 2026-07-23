import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.NonstationaryFusion

/-!
# Retention economics for a persistent evidence plane

This module prices persistence in the scalar linear-Gaussian jump model used
by the workspace belief theory.  A fresh-only carrier discards its old state
and uses the new measurement directly.  A persistent carrier first inflates
the old posterior variance by the declared process variance and then uses the
jump-optimal gain.

The per-revision risk reduction is exactly

`noiseVariance² / (oldVariance + jumpVariance + noiseVariance)`.

Persistence is not declared free.  `RetentionCost` records one activation
cost and one per-revision metadata cost, measured in the same declared scalar
utility units as squared-error risk.  The main theorem gives the exact
revision-count crossover when the statistical benefit exceeds the
per-revision cost.  High drift can erase that margin, and explicit negative
fixtures record that boundary.

The result is a scoped habitat criterion, not a claim about trained-network
loss or wall-clock time.  Those quantities must be supplied by a later
experiment or a separately justified surrogate map.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-- Declared cost of enabling and maintaining persistent evidence. -/
structure RetentionCost where
  activation : ℝ
  perRevision : ℝ

/-- Risk of discarding the old estimate and using the new measurement
directly after a parameter jump. -/
noncomputable def freshOnlyRisk
    (oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  varianceGateRisk
    (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance 1

/-- Risk of the jump-calibrated persistent estimator. -/
noncomputable def calibratedPersistentRisk
    (oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  varianceGateRisk
    (jumpPredictiveVariance oldVariance jumpVariance) noiseVariance
    (jumpOptimalGain oldVariance jumpVariance noiseVariance)

/-- Per-revision squared-error reduction from calibrated persistence relative
to discarding the old estimate. -/
noncomputable def retentionRiskReduction
    (oldVariance jumpVariance noiseVariance : ℝ) : ℝ :=
  freshOnlyRisk oldVariance jumpVariance noiseVariance -
    calibratedPersistentRisk oldVariance jumpVariance noiseVariance

/-- The measurement-only estimator has risk equal to the observation-noise
variance, independently of the old and jump variances. -/
theorem freshOnlyRisk_eq_noiseVariance
    (oldVariance jumpVariance noiseVariance : ℝ) :
    freshOnlyRisk oldVariance jumpVariance noiseVariance = noiseVariance := by
  simp [freshOnlyRisk, varianceGateRisk]

/-- Exact statistical value of retaining the jump-calibrated old state for
one revision. -/
theorem retentionRiskReduction_eq
    (oldVariance jumpVariance noiseVariance : ℝ)
    (hsum : oldVariance + jumpVariance + noiseVariance ≠ 0) :
    retentionRiskReduction oldVariance jumpVariance noiseVariance =
      noiseVariance ^ 2 /
        (oldVariance + jumpVariance + noiseVariance) := by
  unfold retentionRiskReduction calibratedPersistentRisk
  rw [freshOnlyRisk_eq_noiseVariance]
  unfold jumpOptimalGain jumpPredictiveVariance varianceKalmanGain
  unfold varianceGateRisk
  field_simp [hsum]
  ring

/-- Positive variances make persistence strictly statistically valuable
before implementation cost is charged. -/
theorem retentionRiskReduction_pos
    (oldVariance jumpVariance noiseVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance)
    (hnoise : 0 < noiseVariance) :
    0 < retentionRiskReduction oldVariance jumpVariance noiseVariance := by
  have hsum : 0 < oldVariance + jumpVariance + noiseVariance := by
    positivity
  rw [retentionRiskReduction_eq _ _ _ hsum.ne']
  positivity

/-- More process drift strictly lowers the value of carrying a fixed old
estimate when the other variances remain positive. -/
theorem retentionRiskReduction_strictAnti_jumpVariance
    (oldVariance firstJump secondJump noiseVariance : ℝ)
    (hold : 0 < oldVariance) (hfirst : 0 ≤ firstJump)
    (hjumps : firstJump < secondJump) (hnoise : 0 < noiseVariance) :
    retentionRiskReduction oldVariance secondJump noiseVariance <
      retentionRiskReduction oldVariance firstJump noiseVariance := by
  have hsecond : 0 ≤ secondJump := le_trans hfirst hjumps.le
  have hdenFirst : 0 < oldVariance + firstJump + noiseVariance := by
    positivity
  have hdenSecond : 0 < oldVariance + secondJump + noiseVariance := by
    positivity
  rw [retentionRiskReduction_eq _ _ _ hdenSecond.ne',
    retentionRiskReduction_eq _ _ _ hdenFirst.ne']
  rw [div_lt_div_iff₀ hdenSecond hdenFirst]
  have hnoiseSq : 0 < noiseVariance ^ 2 := sq_pos_of_pos hnoise
  nlinarith

/-- Net declared advantage after a finite number of revisions: accumulated
risk reduction minus one activation cost and the recurring metadata cost. -/
noncomputable def retentionNetAdvantage
    (revisions : ℕ) (oldVariance jumpVariance noiseVariance : ℝ)
    (cost : RetentionCost) : ℝ :=
  (revisions : ℝ) *
      (retentionRiskReduction oldVariance jumpVariance noiseVariance -
        cost.perRevision) -
    cost.activation

/-- Exact habitat crossover.  Once the per-revision statistical reduction
strictly exceeds its recurring cost, persistence pays exactly when the
revision count exceeds activation cost divided by that margin. -/
theorem retentionNetAdvantage_pos_iff_revisionThreshold
    (revisions : ℕ) (oldVariance jumpVariance noiseVariance : ℝ)
    (cost : RetentionCost)
    (hmargin : cost.perRevision <
      retentionRiskReduction oldVariance jumpVariance noiseVariance) :
    0 < retentionNetAdvantage revisions oldVariance jumpVariance
        noiseVariance cost ↔
      cost.activation /
          (retentionRiskReduction oldVariance jumpVariance noiseVariance -
            cost.perRevision) <
        (revisions : ℝ) := by
  have hpositive :
      0 < retentionRiskReduction oldVariance jumpVariance noiseVariance -
        cost.perRevision := sub_pos.mpr hmargin
  rw [div_lt_iff₀ hpositive]
  unfold retentionNetAdvantage
  constructor <;> intro h <;> nlinarith

/-- If recurring cost meets or exceeds the statistical reduction and
activation cost is nonnegative, no finite revision count yields positive net
advantage. -/
theorem retention_never_pays_of_reduction_le_recurringCost
    (revisions : ℕ) (oldVariance jumpVariance noiseVariance : ℝ)
    (cost : RetentionCost)
    (hactivation : 0 ≤ cost.activation)
    (hcost : retentionRiskReduction oldVariance jumpVariance noiseVariance ≤
      cost.perRevision) :
    retentionNetAdvantage revisions oldVariance jumpVariance
      noiseVariance cost ≤ 0 := by
  unfold retentionNetAdvantage
  have hrevisions : 0 ≤ (revisions : ℝ) := Nat.cast_nonneg revisions
  nlinarith

/-! ## Executable positive and negative boundaries -/

/-- With unit old/noise variance, no drift, activation cost one, and recurring
cost one tenth, three revisions pay while two do not. -/
theorem three_revisions_cross_lowDrift_threshold :
    0 < retentionNetAdvantage 3 1 0 1
        { activation := 1, perRevision := 1 / 10 } ∧
      retentionNetAdvantage 2 1 0 1
        { activation := 1, perRevision := 1 / 10 } < 0 := by
  norm_num [retentionNetAdvantage, retentionRiskReduction,
    freshOnlyRisk, calibratedPersistentRisk, jumpOptimalGain,
    jumpPredictiveVariance, varianceKalmanGain, varianceGateRisk]

/-- With the same observation model but jump variance eight, the statistical
benefit falls to the recurring cost, so even zero activation cost never
produces a strict advantage. -/
theorem highDrift_erases_retention_margin :
    ∀ revisions,
      retentionNetAdvantage revisions 1 8 1
        { activation := 0, perRevision := 1 / 10 } = 0 := by
  intro revisions
  have hReduction : retentionRiskReduction 1 8 1 = (1 / 10 : ℝ) := by
    rw [retentionRiskReduction_eq]
    · norm_num
    · norm_num
  rw [retentionNetAdvantage, hReduction]
  ring

/-- A positive activation cost rules out persistence at zero revisions even
when the future per-revision margin is favorable. -/
theorem zero_revisions_cannot_repay_activation :
    retentionNetAdvantage 0 1 0 1
      { activation := 1, perRevision := 0 } = -1 := by
  norm_num [retentionNetAdvantage]

#print axioms freshOnlyRisk_eq_noiseVariance
#print axioms retentionRiskReduction_eq
#print axioms retentionRiskReduction_pos
#print axioms retentionRiskReduction_strictAnti_jumpVariance
#print axioms retentionNetAdvantage_pos_iff_revisionThreshold
#print axioms retention_never_pays_of_reduction_le_recurringCost
#print axioms three_revisions_cross_lowDrift_threshold
#print axioms highDrift_erases_retention_margin
#print axioms zero_revisions_cannot_repay_activation

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
