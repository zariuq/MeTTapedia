/-
# NAB Machine Temperature Demo: Anomaly Detection with Wake/Sleep

The sixth applied example exercising continuous (Gaussian) world models in PLN.
Based on real data from the Numenta Anomaly Benchmark (NAB, MIT License).
File: realKnownCause/machine_temperature_system_failure.csv

## The Model

A machine temperature monitoring system.  The sensor produces 5-minute
readings that track an underlying temperature state via a 1D Kalman filter.
Normal operation is ~85°F; anomaly = system failure dropping to ~25°F.

## What's New vs Previous Demos

- **Real anomaly benchmark data** (NAB, 22,695 readings, 4 anomaly windows)
- **Three operating regimes** (calm/hot/anomaly) from a single sensor
- **Anomaly detection narrative**: exceedance queries detect regime shifts
- **Wake/sleep with anomaly context**: batch replay of calm vs anomalous periods

## Key Results

1. Sleep = Wake on real data: batch replay = sequential for each regime
2. Multi-regime composition: calm ++ hot ++ anomaly = full sequence
3. Exceedance threshold ordering for anomaly thresholds
4. Kalman gain properties (inherited from KalmanSleepDemo)
5. Variance reduction per measurement

## Fixture Provenance

Machine temperature (°F), 5 readings per regime:
- Calm (idx 100-104): stable ~85°F
- Hot (idx 2398-2402): elevated ~101°F
- Anomaly (idx 3967-3971): failure ~30°F

Extraction script: scripts/extract_nab_fixture.py

0 sorry.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Mettapedia.Logic.WMNABSleepDemo

/-! ## §1: Core Structures (restate for self-containment) -/

/-- A 1D Gaussian belief: posterior mean and variance. -/
structure GaussianBelief where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

namespace GaussianBelief

theorem variance_ne_zero (b : GaussianBelief) : b.variance ≠ 0 :=
  ne_of_gt b.variance_pos

@[ext]
theorem ext {b₁ b₂ : GaussianBelief}
    (hm : b₁.mean = b₂.mean) (hv : b₁.variance = b₂.variance) :
    b₁ = b₂ := by
  cases b₁; cases b₂; simp only [mk.injEq]; exact ⟨hm, hv⟩

end GaussianBelief

/-- Kalman filter parameters: known noise variances. -/
structure KalmanParams where
  processNoise : ℝ
  measurementNoise : ℝ
  processNoise_pos : 0 < processNoise
  measurementNoise_pos : 0 < measurementNoise

/-! ## §2: Core Operations -/

/-- Predict: variance inflates, mean unchanged. -/
def predict (p : KalmanParams) (b : GaussianBelief) : GaussianBelief where
  mean := b.mean
  variance := b.variance + p.processNoise
  variance_pos := by linarith [b.variance_pos, p.processNoise_pos]

/-- Kalman gain. -/
noncomputable def kalmanGain (p : KalmanParams) (b : GaussianBelief) : ℝ :=
  b.variance / (b.variance + p.measurementNoise)

/-- Update: incorporate measurement. -/
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

/-- Sequential filtering. -/
noncomputable def filterOrbit (p : KalmanParams) (b₀ : GaussianBelief)
    (measurements : List ℝ) : GaussianBelief :=
  measurements.foldl (step p) b₀

@[simp]
theorem filterOrbit_nil (p : KalmanParams) (b₀ : GaussianBelief) :
    filterOrbit p b₀ [] = b₀ := rfl

@[simp]
theorem filterOrbit_cons (p : KalmanParams) (b₀ : GaussianBelief) (z : ℝ) (zs : List ℝ) :
    filterOrbit p b₀ (z :: zs) = filterOrbit p (step p b₀ z) zs := rfl

/-- Orbit composition: two batches sequentially = concatenation. -/
theorem filterOrbit_append (p : KalmanParams) (b₀ : GaussianBelief)
    (zs₁ zs₂ : List ℝ) :
    filterOrbit p b₀ (zs₁ ++ zs₂) = filterOrbit p (filterOrbit p b₀ zs₁) zs₂ :=
  List.foldl_append ..

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

theorem one_sub_kalmanGain_pos (p : KalmanParams) (b : GaussianBelief) :
    0 < 1 - kalmanGain p b := by
  linarith [kalmanGain_lt_one p b]

/-! ## §4: Variance Reduction -/

/-- Each update strictly reduces variance. -/
theorem update_variance_lt (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (update p b z).variance < b.variance := by
  show (1 - kalmanGain p b) * b.variance < b.variance
  have h1mK_lt : 1 - kalmanGain p b < 1 := by linarith [kalmanGain_pos p b]
  calc (1 - kalmanGain p b) * b.variance
      < 1 * b.variance := mul_lt_mul_of_pos_right h1mK_lt b.variance_pos
    _ = b.variance := one_mul _

/-- A full step reduces variance relative to the predicted state. -/
theorem step_variance_lt_predict (p : KalmanParams) (b : GaussianBelief) (z : ℝ) :
    (step p b z).variance < (predict p b).variance :=
  update_variance_lt p (predict p b) z

/-! ## §5: Exceedance Specification -/

/-- Abstract exceedance specification for anomaly detection. -/
structure AnomalyExceedanceSpec where
  /-- P(temp > c) given a Gaussian belief -/
  exceedance : GaussianBelief → ℝ → ℝ
  exceedance_nonneg : ∀ b c, 0 ≤ exceedance b c
  exceedance_le_one : ∀ b c, exceedance b c ≤ 1
  exceedance_anti_threshold : ∀ b c₁ c₂, c₁ ≤ c₂ →
    exceedance b c₂ ≤ exceedance b c₁
  exceedance_mono_mean : ∀ b₁ b₂ c,
    b₁.variance = b₂.variance → b₁.mean ≤ b₂.mean →
    exceedance b₁ c ≤ exceedance b₂ c

/-! ## §6: Real NAB Fixture Data

Machine temperature (°F) from a real industrial sensor with known failure modes.
Source: NAB, realKnownCause/machine_temperature_system_failure.csv, MIT License. -/

/-- Monitoring parameters for machine temperature.
    Process noise = 0.5°F²/step, measurement noise = 2°F². -/
noncomputable def machineParams : KalmanParams where
  processNoise := 0.5
  measurementNoise := 2
  processNoise_pos := by norm_num
  measurementNoise_pos := by norm_num

/-- Initial belief: room temperature estimate with high uncertainty. -/
noncomputable def initialBelief : GaussianBelief where
  mean := 80
  variance := 100
  variance_pos := by norm_num

/-- Calm regime: 5 readings during stable operation (~85°F).
    NAB idx 100-104. -/
def calmReadings : List ℝ := [87.6, 86.4, 86.7, 84.7, 84.1]

/-- Hot regime: 5 readings during elevated pre-anomaly period (~101°F).
    NAB idx 2398-2402. -/
def hotReadings : List ℝ := [101.2, 101.0, 100.9, 99.9, 101.3]

/-- Anomaly regime: 5 readings during system failure (~30°F).
    NAB idx 3967-3971. -/
def anomalyReadings : List ℝ := [35.1, 32.5, 30.7, 30.5, 27.2]

/-- Full monitoring sequence: calm → hot → anomaly. -/
def fullSequence : List ℝ := calmReadings ++ hotReadings ++ anomalyReadings

/-- Warning threshold: temperature below 60°F. -/
def lowTempWarning : ℝ := 60

/-- Critical threshold: temperature below 40°F. -/
def lowTempCritical : ℝ := 40

/-! ## §6b: Bridge Theorems — Concrete Kalman Parameters -/

/-- Kalman gain for initial machine belief: K = σ²/(σ² + σ_v²) = 100/(100+2). -/
theorem kalmanGain_initial :
    kalmanGain machineParams initialBelief =
      initialBelief.variance / (initialBelief.variance + machineParams.measurementNoise) := rfl

/-- Update mean after first measurement z: mean + K*(z - mean). -/
theorem update_mean_first (z : ℝ) :
    (update machineParams initialBelief z).mean =
      initialBelief.mean + kalmanGain machineParams initialBelief * (z - initialBelief.mean) := rfl

/-- Update variance after first measurement: (1 - K) * σ². -/
theorem update_variance_first (z : ℝ) :
    (update machineParams initialBelief z).variance =
      (1 - kalmanGain machineParams initialBelief) * initialBelief.variance := rfl

/-! ## §7: Sleep = Wake Theorems -/

/-- **Sleep = Wake** on real calm data: batch replay = sequential filtering. -/
theorem sleep_eq_wake_calm_hot :
    filterOrbit machineParams initialBelief (calmReadings ++ hotReadings) =
    filterOrbit machineParams
      (filterOrbit machineParams initialBelief calmReadings)
      hotReadings :=
  filterOrbit_append machineParams initialBelief calmReadings hotReadings

/-- **Sleep = Wake** across all three regimes. -/
theorem sleep_eq_wake_three_regimes :
    filterOrbit machineParams initialBelief
      (calmReadings ++ hotReadings ++ anomalyReadings) =
    filterOrbit machineParams
      (filterOrbit machineParams
        (filterOrbit machineParams initialBelief calmReadings)
        hotReadings)
      anomalyReadings := by
  rw [filterOrbit_append, filterOrbit_append]

/-- Full sequence = three-phase sequential processing. -/
theorem full_sequence_decomposition :
    filterOrbit machineParams initialBelief fullSequence =
    filterOrbit machineParams
      (filterOrbit machineParams
        (filterOrbit machineParams initialBelief calmReadings)
        hotReadings)
      anomalyReadings := by
  unfold fullSequence
  rw [filterOrbit_append, filterOrbit_append]

/-- Batch replay of calm alone then hot-anomaly combined gives same result
    as processing all three separately. -/
theorem two_phase_eq_three_phase :
    filterOrbit machineParams
      (filterOrbit machineParams initialBelief calmReadings)
      (hotReadings ++ anomalyReadings) =
    filterOrbit machineParams
      (filterOrbit machineParams
        (filterOrbit machineParams initialBelief calmReadings)
        hotReadings)
      anomalyReadings :=
  filterOrbit_append machineParams _ hotReadings anomalyReadings

/-! ## §8: Anomaly Detection Theorems -/

/-- Exceedance threshold ordering: P(temp > 60) ≥ P(temp > 40) is FALSE
    because exceedance is decreasing.  Instead:
    P(temp > 40) ≥ P(temp > 60) — lower threshold has higher exceedance. -/
theorem anomaly_threshold_ordering (spec : AnomalyExceedanceSpec)
    (b : GaussianBelief) :
    spec.exceedance b lowTempWarning ≤ spec.exceedance b lowTempCritical :=
  spec.exceedance_anti_threshold b lowTempCritical lowTempWarning (by
    unfold lowTempCritical lowTempWarning; norm_num)

/-- Predict step increases variance (uncertainty grows between readings). -/
theorem predict_increases_variance (b : GaussianBelief) :
    b.variance < (predict machineParams b).variance := by
  show b.variance < b.variance + machineParams.processNoise
  linarith [machineParams.processNoise_pos]

/-- Each measurement reduces uncertainty relative to predicted state. -/
theorem measurement_reduces_uncertainty (b : GaussianBelief) (z : ℝ) :
    (step machineParams b z).variance < (predict machineParams b).variance :=
  step_variance_lt_predict machineParams b z

/-! ## §9: Canary Tests -/

/-- Canary: calm readings have 5 measurements. -/
theorem canary_calm_length : calmReadings.length = 5 := by decide

/-- Canary: hot readings have 5 measurements. -/
theorem canary_hot_length : hotReadings.length = 5 := by decide

/-- Canary: anomaly readings have 5 measurements. -/
theorem canary_anomaly_length : anomalyReadings.length = 5 := by decide

/-- Canary: full sequence has 15 measurements. -/
theorem canary_full_length : fullSequence.length = 15 := by
  simp [fullSequence, calmReadings, hotReadings, anomalyReadings]

/-- Canary: predict preserves mean. -/
theorem canary_predict_mean (b : GaussianBelief) :
    (predict machineParams b).mean = b.mean := rfl

/-- Canary: empty measurement list returns initial belief. -/
theorem canary_filterOrbit_nil :
    filterOrbit machineParams initialBelief [] = initialBelief := rfl

/-- Canary: Kalman gain is positive for our parameters. -/
theorem canary_kalmanGain_pos :
    0 < kalmanGain machineParams initialBelief :=
  kalmanGain_pos machineParams initialBelief

/-- Canary: Kalman gain is less than 1 for our parameters. -/
theorem canary_kalmanGain_lt_one :
    kalmanGain machineParams initialBelief < 1 :=
  kalmanGain_lt_one machineParams initialBelief

/-- Canary: warning threshold < critical threshold (note: low-temp anomaly). -/
theorem canary_critical_lt_warning : lowTempCritical < lowTempWarning := by
  unfold lowTempCritical lowTempWarning; norm_num

/-- Canary: sleep = wake concrete instance. -/
theorem canary_concrete_sleep_eq_wake :
    filterOrbit machineParams initialBelief (calmReadings ++ hotReadings) =
    filterOrbit machineParams
      (filterOrbit machineParams initialBelief calmReadings)
      hotReadings :=
  filterOrbit_append _ _ _ _

end Mettapedia.Logic.WMNABSleepDemo
