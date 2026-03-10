/-
# Kalman Filter Demo: Wake/Sleep Temporal Filtering

The flagship applied example for the wake/sleep narrative in PLN.

## The Model

1D position tracking with known noise parameters:
- Process model: x_{t+1} = x_t + w_t, w_t ~ N(0, σ_w²)
- Measurement: z_t = x_t + v_t, v_t ~ N(0, σ_v²)
- Predict: σ²_pred = σ² + σ_w² (variance inflation)
- Update: K = σ²_pred/(σ²_pred + σ_v²), μ_new = μ + K(z-μ), σ²_new = (1-K)σ²

All arithmetic is scalar — no matrices needed for the 1D case.

## Key Results

1. Kalman gain properties: 0 < K < 1
2. Variance reduction: each measurement strictly reduces uncertainty
3. Sleep = Wake equivalence: batch replay of deferred observations yields
   the same posterior as sequential online filtering
4. Exceedance threshold ordering for collision/boundary queries

## Wake/Sleep Narrative

- **Wake = filtering**: process measurements one-by-one as they arrive
- **Sleep = batch replay**: process all deferred measurements from the prior
- The central theorem: filtering sequentially = batch processing (foldl associativity)

0 sorry.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Mettapedia.Logic.PLNKalmanSleepDemo

/-! ## §1: Core Structures -/

/-- A 1D Gaussian belief: posterior mean and variance. -/
structure GaussianBelief where
  /-- Posterior mean estimate -/
  mean : ℝ
  /-- Posterior variance (uncertainty) -/
  variance : ℝ
  /-- Variance is strictly positive -/
  variance_pos : 0 < variance

namespace GaussianBelief

theorem variance_ne_zero (b : GaussianBelief) : b.variance ≠ 0 :=
  ne_of_gt b.variance_pos

theorem variance_nonneg (b : GaussianBelief) : 0 ≤ b.variance :=
  le_of_lt b.variance_pos

@[ext]
theorem ext {b₁ b₂ : GaussianBelief}
    (hm : b₁.mean = b₂.mean) (hv : b₁.variance = b₂.variance) :
    b₁ = b₂ := by
  cases b₁; cases b₂; simp only [mk.injEq]; exact ⟨hm, hv⟩

end GaussianBelief

/-- Parameters for the 1D Kalman filter: known noise variances. -/
structure KalmanParams where
  /-- Process noise variance σ_w² -/
  processNoise : ℝ
  /-- Measurement noise variance σ_v² -/
  measurementNoise : ℝ
  /-- Process noise is positive -/
  processNoise_pos : 0 < processNoise
  /-- Measurement noise is positive -/
  measurementNoise_pos : 0 < measurementNoise

/-! ## §2: Core Operations -/

/-- Predict step: propagate belief through the process model.
    Mean is unchanged (random walk), variance inflates by process noise. -/
def predict (p : KalmanParams) (b : GaussianBelief) : GaussianBelief where
  mean := b.mean
  variance := b.variance + p.processNoise
  variance_pos := by linarith [b.variance_pos, p.processNoise_pos]

/-- Kalman gain: K = σ²/(σ² + σ_v²).
    Weights the measurement innovation relative to prior uncertainty. -/
noncomputable def kalmanGain (p : KalmanParams) (b : GaussianBelief) : ℝ :=
  b.variance / (b.variance + p.measurementNoise)

/-- Update step: incorporate a measurement z into the belief.
    Mean shifts toward z, variance shrinks. -/
noncomputable def update (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    GaussianBelief where
  mean := b.mean + kalmanGain p b * (z - b.mean)
  variance := (1 - kalmanGain p b) * b.variance
  variance_pos := by
    unfold kalmanGain
    have hv := b.variance_pos
    have hm := p.measurementNoise_pos
    have hden : 0 < b.variance + p.measurementNoise := by linarith
    have hK_lt : b.variance / (b.variance + p.measurementNoise) < 1 := by
      rw [div_lt_one hden]; linarith
    exact mul_pos (by linarith) hv

/-- Single predict-update cycle. -/
noncomputable def step (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    GaussianBelief :=
  update p (predict p b) z

/-! ## §3: Kalman Gain Properties -/

theorem kalmanGain_pos (p : KalmanParams) (b : GaussianBelief) :
    0 < kalmanGain p b := by
  unfold kalmanGain
  exact div_pos b.variance_pos (by linarith [b.variance_pos, p.measurementNoise_pos])

theorem kalmanGain_lt_one (p : KalmanParams) (b : GaussianBelief) :
    kalmanGain p b < 1 := by
  unfold kalmanGain
  rw [div_lt_one (by linarith [b.variance_pos, p.measurementNoise_pos])]
  linarith [p.measurementNoise_pos]

theorem kalmanGain_le_one (p : KalmanParams) (b : GaussianBelief) :
    kalmanGain p b ≤ 1 :=
  le_of_lt (kalmanGain_lt_one p b)

theorem one_sub_kalmanGain_pos (p : KalmanParams) (b : GaussianBelief) :
    0 < 1 - kalmanGain p b := by
  linarith [kalmanGain_lt_one p b]

theorem kalmanGain_nonneg (p : KalmanParams) (b : GaussianBelief) :
    0 ≤ kalmanGain p b :=
  le_of_lt (kalmanGain_pos p b)

/-- The complement 1 - K equals σ_v²/(σ² + σ_v²). -/
theorem one_sub_kalmanGain_eq (p : KalmanParams) (b : GaussianBelief) :
    1 - kalmanGain p b = p.measurementNoise / (b.variance + p.measurementNoise) := by
  unfold kalmanGain
  have hden : b.variance + p.measurementNoise ≠ 0 :=
    ne_of_gt (by linarith [b.variance_pos, p.measurementNoise_pos])
  field_simp [hden]
  ring

/-! ## §4: Variance Reduction -/

/-- Each update strictly reduces variance: (1-K)σ² < σ². -/
theorem update_variance_lt (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (update p b z).variance < b.variance := by
  show (1 - kalmanGain p b) * b.variance < b.variance
  have hK_pos := kalmanGain_pos p b
  have h1mK := one_sub_kalmanGain_pos p b
  have h1mK_lt : 1 - kalmanGain p b < 1 := by linarith [kalmanGain_pos p b]
  calc (1 - kalmanGain p b) * b.variance
      < 1 * b.variance := by
        apply mul_lt_mul_of_pos_right h1mK_lt b.variance_pos
    _ = b.variance := one_mul _

/-- Closed form for updated variance: σ²·σ_v²/(σ² + σ_v²). -/
theorem update_variance_eq (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (update p b z).variance =
      b.variance * p.measurementNoise / (b.variance + p.measurementNoise) := by
  show (1 - kalmanGain p b) * b.variance = _
  rw [one_sub_kalmanGain_eq]
  have hden : b.variance + p.measurementNoise ≠ 0 :=
    ne_of_gt (by linarith [b.variance_pos, p.measurementNoise_pos])
  field_simp [hden]

/-- A full step (predict + update) reduces variance relative to the predicted state. -/
theorem step_variance_lt_predict (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (step p b z).variance < (predict p b).variance :=
  update_variance_lt p (predict p b) z

/-- Information gain: after a step, variance is less than prior variance + process noise. -/
theorem step_variance_lt_inflated (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (step p b z).variance < b.variance + p.processNoise :=
  step_variance_lt_predict p b z

/-! ## §5: Filter Orbit -/

/-- Sequential Kalman filtering: fold predict-update steps over a list of measurements. -/
noncomputable def filterOrbit (p : KalmanParams) (b₀ : GaussianBelief)
    (measurements : List ℝ) : GaussianBelief :=
  measurements.foldl (step p) b₀

@[simp]
theorem filterOrbit_nil (p : KalmanParams) (b₀ : GaussianBelief) :
    filterOrbit p b₀ [] = b₀ := rfl

@[simp]
theorem filterOrbit_cons (p : KalmanParams) (b₀ : GaussianBelief) (z : ℝ) (zs : List ℝ) :
    filterOrbit p b₀ (z :: zs) = filterOrbit p (step p b₀ z) zs := rfl

/-- Orbit composition: processing two batches sequentially = processing the concatenation. -/
theorem filterOrbit_append (p : KalmanParams) (b₀ : GaussianBelief)
    (zs₁ zs₂ : List ℝ) :
    filterOrbit p b₀ (zs₁ ++ zs₂) = filterOrbit p (filterOrbit p b₀ zs₁) zs₂ :=
  List.foldl_append ..

/-! ## §6: Sleep = Wake Equivalence

The central theorem: deferred observations can be replayed in a batch
and yield the same posterior as sequential online filtering. -/

/-- **Sleep = Wake**: batch replay of morning + night observations yields the
    same state as processing morning first, then night.

    This is the Kalman analog of sleep consolidation: the system can accumulate
    measurements during the day and assimilate them in a single batch at night,
    getting the same posterior as real-time filtering. -/
theorem sleep_eq_wake (p : KalmanParams) (b₀ : GaussianBelief)
    (morningObs nightObs : List ℝ) :
    filterOrbit p b₀ (morningObs ++ nightObs) =
    filterOrbit p (filterOrbit p b₀ morningObs) nightObs :=
  filterOrbit_append p b₀ morningObs nightObs

/-- Three-shift generalization: morning + afternoon + night. -/
theorem sleep_eq_wake_three (p : KalmanParams) (b₀ : GaussianBelief)
    (obs₁ obs₂ obs₃ : List ℝ) :
    filterOrbit p b₀ (obs₁ ++ obs₂ ++ obs₃) =
    filterOrbit p (filterOrbit p (filterOrbit p b₀ obs₁) obs₂) obs₃ := by
  rw [filterOrbit_append, filterOrbit_append]

/-! ## §7: Exceedance Specification

Abstract specification for P(position > boundary) given a Gaussian belief.
Parametric in any function satisfying monotonicity and variance sensitivity. -/

/-- Specification for Gaussian exceedance P(position > boundary).
    Like BrokenSensorDemo's ExceedanceSpec but for GaussianBelief. -/
structure KalmanExceedanceSpec where
  /-- P(position > c) given a Gaussian belief -/
  exceedance : GaussianBelief → ℝ → ℝ
  /-- Result is non-negative -/
  exceedance_nonneg : ∀ b c, 0 ≤ exceedance b c
  /-- Result is at most 1 -/
  exceedance_le_one : ∀ b c, exceedance b c ≤ 1
  /-- Monotone decreasing in threshold -/
  exceedance_anti_threshold : ∀ b c₁ c₂, c₁ ≤ c₂ →
    exceedance b c₂ ≤ exceedance b c₁
  /-- Monotone increasing in mean (same variance) -/
  exceedance_mono_mean : ∀ b₁ b₂ c,
    b₁.variance = b₂.variance → b₁.mean ≤ b₂.mean →
    exceedance b₁ c ≤ exceedance b₂ c

/-- Exceedance decreases as threshold increases (threshold ordering). -/
theorem exceedance_warning_ge_critical (spec : KalmanExceedanceSpec)
    (b : GaussianBelief) (cw cc : ℝ) (h : cw ≤ cc) :
    spec.exceedance b cc ≤ spec.exceedance b cw :=
  spec.exceedance_anti_threshold b cw cc h

/-! ## §8: Concrete Scenario -/

/-- Tracking parameters: moderate process noise, noisy sensor. -/
noncomputable def trackingParams : KalmanParams where
  processNoise := 0.5
  measurementNoise := 1
  processNoise_pos := by norm_num
  measurementNoise_pos := by norm_num

/-- Initial belief: start at origin with high uncertainty. -/
noncomputable def initialBelief : GaussianBelief where
  mean := 0
  variance := 10
  variance_pos := by norm_num

/-- Warning boundary: position above 5.0 is concerning. -/
def warningBoundary : ℝ := 5

/-- Critical boundary: position above 10.0 is dangerous. -/
def criticalBoundary : ℝ := 10

/-- Morning measurements: 5 observations suggesting position near 2.0. -/
def morningMeasurements : List ℝ := [1.8, 2.3, 1.5, 2.1, 2.0]

/-- Night measurements: 5 observations suggesting drift toward 3.0. -/
def nightMeasurements : List ℝ := [2.8, 3.2, 2.9, 3.5, 3.1]

/-- Full day of measurements. -/
def fullDayMeasurements : List ℝ := morningMeasurements ++ nightMeasurements

/-! ## §8b: Bridge Theorems — Concrete Kalman Parameters

Pin the Kalman gain and first-step update to closed-form expressions,
bridging the Lean formalization to the Python numerical layer. -/

/-- Kalman gain for the initial belief: K = σ²/(σ² + σ_v²) = 10/(10+1). -/
theorem kalmanGain_initial :
    kalmanGain trackingParams initialBelief =
      initialBelief.variance / (initialBelief.variance + trackingParams.measurementNoise) := rfl

/-- Update mean after first measurement z: mean + K*(z - mean). -/
theorem update_mean_first (z : ℝ) :
    (update trackingParams initialBelief z).mean =
      initialBelief.mean + kalmanGain trackingParams initialBelief * (z - initialBelief.mean) := rfl

/-- Update variance after first measurement: (1 - K) * σ².
    Variance strictly decreases with each measurement (proved generically above). -/
theorem update_variance_first (z : ℝ) :
    (update trackingParams initialBelief z).variance =
      (1 - kalmanGain trackingParams initialBelief) * initialBelief.variance := rfl

/-! ## §9: Main Theorems -/

/-- **Concrete sleep consolidation**: full day = morning then night. -/
theorem sleep_consolidation :
    filterOrbit trackingParams initialBelief fullDayMeasurements =
    filterOrbit trackingParams
      (filterOrbit trackingParams initialBelief morningMeasurements)
      nightMeasurements := by
  unfold fullDayMeasurements
  exact filterOrbit_append trackingParams initialBelief morningMeasurements nightMeasurements

/-- Each measurement reduces uncertainty relative to the predicted state. -/
theorem each_measurement_reduces_uncertainty (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (step p b z).variance < (predict p b).variance :=
  step_variance_lt_predict p b z

/-- The predict step is the only source of variance increase. -/
theorem predict_increases_variance (p : KalmanParams) (b : GaussianBelief) :
    b.variance < (predict p b).variance := by
  show b.variance < b.variance + p.processNoise
  linarith [p.processNoise_pos]

/-! ## §10: Canary Tests -/

/-- Canary: predict preserves mean. -/
theorem canary_predict_mean (p : KalmanParams) (b : GaussianBelief) :
    (predict p b).mean = b.mean := rfl

/-- Canary: predict adds process noise to variance. -/
theorem canary_predict_variance (p : KalmanParams) (b : GaussianBelief) :
    (predict p b).variance = b.variance + p.processNoise := rfl

/-- Canary: empty measurement list returns initial belief. -/
theorem canary_filterOrbit_nil :
    filterOrbit trackingParams initialBelief [] = initialBelief := rfl

/-- Canary: morning has 5 measurements. -/
theorem canary_morning_length : morningMeasurements.length = 5 := by decide

/-- Canary: night has 5 measurements. -/
theorem canary_night_length : nightMeasurements.length = 5 := by decide

/-- Canary: full day has 10 measurements. -/
theorem canary_fullDay_length : fullDayMeasurements.length = 10 := by
  simp [fullDayMeasurements, morningMeasurements, nightMeasurements]

/-- Canary: Kalman gain is positive for concrete parameters. -/
theorem canary_kalmanGain_pos :
    0 < kalmanGain trackingParams initialBelief :=
  kalmanGain_pos trackingParams initialBelief

/-- Canary: Kalman gain is less than 1 for concrete parameters. -/
theorem canary_kalmanGain_lt_one :
    kalmanGain trackingParams initialBelief < 1 :=
  kalmanGain_lt_one trackingParams initialBelief

/-- Canary: warning boundary ≤ critical boundary. -/
theorem canary_warning_le_critical : warningBoundary ≤ criticalBoundary := by
  unfold warningBoundary criticalBoundary; norm_num

/-- Canary: sleep = wake for the concrete scenario. -/
theorem canary_sleep_eq_wake :
    filterOrbit trackingParams initialBelief (morningMeasurements ++ nightMeasurements) =
    filterOrbit trackingParams
      (filterOrbit trackingParams initialBelief morningMeasurements)
      nightMeasurements :=
  filterOrbit_append _ _ _ _

end Mettapedia.Logic.PLNKalmanSleepDemo
