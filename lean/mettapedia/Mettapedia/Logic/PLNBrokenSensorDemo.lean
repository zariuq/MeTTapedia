/-
# Broken Sensor Demo: Hybrid Discrete/Continuous World Model

The first applied example exercising continuous (Gaussian) world models in PLN.

## The Model

A sensor monitoring system where:
- Temperature readings come from N(μ, 1/τ) with unknown μ, τ
- A Normal-Gamma prior on (μ, τ) is updated by streaming observations
- A cooling system may fail (Boolean, with observed evidence)
- The device is "broken" when temperature exceeds a threshold

## Key Results

1. Sleep consolidation: batch replay = sequential Bayesian update
2. Hybrid evidence compositionality for the product state
3. Exceedance monotonicity (parametric in any valid exceedance spec)
4. Confidence monotonicity with observation count
5. Wake/sleep equivalence: deferred assimilation preserves the posterior

## Design: ExceedanceSpec

Mathlib has no Normal CDF, so P(X > c) is handled abstractly via a
specification class: a function satisfying mathematical properties
(monotone decreasing in threshold, monotone increasing in posterior mean).
All theorems are parametric in any valid exceedance function.

0 sorry.
-/

import Mettapedia.Logic.EvidenceNormalGamma
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel

namespace Mettapedia.Logic.PLNBrokenSensorDemo

open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel

/-! ## §1: Hybrid State Type

The sensor state is a product of continuous temperature evidence
and Boolean cooling-failure evidence. -/

/-- Hybrid state: continuous temperature + Boolean cooling failure. -/
structure SensorState where
  /-- Sufficient statistics for temperature observations -/
  tempEvidence : NormalGammaEvidence
  /-- Binary evidence for cooling system failure -/
  coolFailEvidence : Evidence

namespace SensorState

/-- Zero state: no observations of either kind. -/
def zero : SensorState where
  tempEvidence := NormalGammaEvidence.zero
  coolFailEvidence := Evidence.zero

/-- Componentwise addition (revision). -/
noncomputable def add (s₁ s₂ : SensorState) : SensorState where
  tempEvidence := s₁.tempEvidence + s₂.tempEvidence
  coolFailEvidence := s₁.coolFailEvidence + s₂.coolFailEvidence

noncomputable instance : Add SensorState where add := add
instance : Zero SensorState where zero := zero

@[simp] theorem add_tempEvidence (s₁ s₂ : SensorState) :
    (s₁ + s₂).tempEvidence = s₁.tempEvidence + s₂.tempEvidence := rfl

@[simp] theorem add_coolFailEvidence (s₁ s₂ : SensorState) :
    (s₁ + s₂).coolFailEvidence = s₁.coolFailEvidence + s₂.coolFailEvidence := rfl

@[simp] theorem zero_tempEvidence : (zero : SensorState).tempEvidence = NormalGammaEvidence.zero := rfl

@[simp] theorem zero_coolFailEvidence : (zero : SensorState).coolFailEvidence = Evidence.zero := rfl

@[ext]
theorem ext {s₁ s₂ : SensorState}
    (ht : s₁.tempEvidence = s₂.tempEvidence)
    (hc : s₁.coolFailEvidence = s₂.coolFailEvidence) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact ⟨ht, hc⟩

theorem add_comm (s₁ s₂ : SensorState) : s₁ + s₂ = s₂ + s₁ := by
  apply ext
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact Evidence.hplus_comm _ _

theorem add_assoc (s₁ s₂ s₃ : SensorState) : s₁ + s₂ + s₃ = s₁ + (s₂ + s₃) := by
  apply ext
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact Evidence.hplus_assoc _ _ _

theorem zero_add (s : SensorState) : zero + s = s := by
  apply ext
  · exact NormalGammaEvidence.zero_hplus _
  · exact Evidence.zero_hplus _

theorem add_zero (s : SensorState) : s + zero = s := by
  apply ext
  · exact NormalGammaEvidence.hplus_zero _
  · exact Evidence.hplus_zero _

noncomputable instance instAddCommMonoid : AddCommMonoid SensorState where
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

noncomputable instance instEvidenceType : EvidenceType SensorState where

end SensorState

/-! ## §2: Exceedance Specification

Abstract specification for P(X > c) given a Normal-Gamma posterior.
Parametric in any function satisfying basic probability and monotonicity laws. -/

/-- Specification for Gaussian exceedance probability P(X > c).
    Any function satisfying these properties gives valid theorems. -/
structure ExceedanceSpec where
  /-- P(X > c) given posterior parameters -/
  exceedance : NormalGammaPrior → ℝ → ℝ
  /-- Result is non-negative -/
  exceedance_nonneg : ∀ p c, 0 ≤ exceedance p c
  /-- Result is at most 1 -/
  exceedance_le_one : ∀ p c, exceedance p c ≤ 1
  /-- Monotone decreasing in threshold: higher c → lower P(X > c) -/
  exceedance_anti_threshold : ∀ p c₁ c₂, c₁ ≤ c₂ →
    exceedance p c₂ ≤ exceedance p c₁
  /-- Monotone increasing in posterior mean (other params fixed) -/
  exceedance_mono_mean : ∀ p₁ p₂ c,
    p₁.κ₀ = p₂.κ₀ → p₁.α₀ = p₂.α₀ → p₁.β₀ = p₂.β₀ →
    p₁.μ₀ ≤ p₂.μ₀ → exceedance p₁ c ≤ exceedance p₂ c

/-! ## §3: Query Type -/

/-- Queries against the hybrid sensor state. -/
inductive SensorQuery where
  /-- Is the cooling system failing? (Boolean) -/
  | coolFail
  /-- Temperature exceeds threshold c? (Gaussian) -/
  | exceedance (c : ℝ)

/-! ## §4: Evidence Extraction

Given a prior and exceedance spec, extract binary Evidence for each query. -/

/-- Extract binary evidence for cooling failure: directly from the Boolean component. -/
def coolFailEvidence (s : SensorState) : Evidence :=
  s.coolFailEvidence

/-- Effective sample size for converting exceedance probability to binary evidence.
    Uses the temperature observation count as the effective sample size. -/
def exceedanceEffectiveSampleSize (s : SensorState) : ℕ :=
  s.tempEvidence.n

/-- Extract binary evidence for a threshold exceedance query.

    Given a prior π and exceedance spec φ:
    1. Compute posterior: π' = posterior(π, tempEvidence)
    2. Compute P(X > c) = φ.exceedance(π', c)
    3. Convert to binary Evidence with effective sample size n

    The strength of the resulting evidence is the exceedance probability.
    The effective sample size is the number of temperature observations. -/
noncomputable def exceedanceEvidence
    (spec : ExceedanceSpec) (prior : NormalGammaPrior) (s : SensorState) (c : ℝ) :
    Evidence :=
  let post := posterior prior s.tempEvidence
  let p := spec.exceedance post c
  let n := s.tempEvidence.n
  -- Convert probability p with n observations to binary evidence
  -- n⁺ = p · n, n⁻ = (1-p) · n
  ⟨ENNReal.ofReal (p * n), ENNReal.ofReal ((1 - p) * n)⟩

/-- Full evidence extraction for any sensor query. -/
noncomputable def sensorEvidence
    (spec : ExceedanceSpec) (prior : NormalGammaPrior) (s : SensorState) :
    SensorQuery → Evidence
  | .coolFail => coolFailEvidence s
  | .exceedance c => exceedanceEvidence spec prior s c

/-! ## §5: Concrete Sensor Data -/

/-- A sensor prior: temperature expected around 15°C, moderate confidence. -/
noncomputable def sensorPrior : NormalGammaPrior where
  μ₀ := 15
  κ₀ := 1
  α₀ := 2
  β₀ := 10
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Warning threshold: 20°C -/
def warningThreshold : ℝ := 20

/-- Critical threshold: 30°C -/
def criticalThreshold : ℝ := 30

/-- A single temperature observation. -/
noncomputable def tempObs (x : ℝ) : SensorState where
  tempEvidence := NormalGammaEvidence.single x
  coolFailEvidence := Evidence.zero

/-- A single cooling-failure observation (positive = failure seen). -/
def coolFailObs (failed : Bool) : SensorState where
  tempEvidence := NormalGammaEvidence.zero
  coolFailEvidence := if failed then ⟨1, 0⟩ else ⟨0, 1⟩

/-- Morning shift: 5 normal temperature readings. -/
noncomputable def morningShift : SensorState :=
  tempObs 16.2 + tempObs 15.8 + tempObs 16.5 + tempObs 15.1 + tempObs 16.0

/-- Night shift: 5 elevated temperature readings (something wrong?). -/
noncomputable def nightShift : SensorState :=
  tempObs 22.5 + tempObs 23.1 + tempObs 21.8 + tempObs 24.0 + tempObs 22.2

/-- Cooling system observations: 2 failures in 100 checks. -/
def coolFailHistory : SensorState where
  tempEvidence := NormalGammaEvidence.zero
  coolFailEvidence := ⟨2, 98⟩

/-- Full day of observations: morning + night + cooling checks. -/
noncomputable def fullDay : SensorState :=
  morningShift + nightShift + coolFailHistory

/-! ## §6: Realizability Side Conditions -/

theorem single_realizable (x : ℝ) :
    (NormalGammaEvidence.single x).Realizable := by
  intro h; simp [NormalGammaEvidence.single] at h

theorem morningShift_temp_realizable : morningShift.tempEvidence.Realizable := by
  simp only [morningShift, tempObs, SensorState.add_tempEvidence]
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _

theorem nightShift_temp_realizable : nightShift.tempEvidence.Realizable := by
  simp only [nightShift, tempObs, SensorState.add_tempEvidence]
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _

/-! ## §7: Bridge Theorems — Closed-Form Posterior Parameters

These theorems pin the posterior parameters to closed-form symbolic expressions,
bridging the Lean formalization to the Python numerical layer.  The Python script
`scripts/wm_pln_posterior.py` computes credible intervals, predictive densities,
and exceedance probabilities from (μₙ, κₙ, αₙ, βₙ); these theorems guarantee
the formulas are the same. -/

/-- Posterior mean after morning shift: affine combination of prior and data. -/
theorem morningShift_posterior_mu :
    (posterior sensorPrior morningShift.tempEvidence).μ₀ =
      (sensorPrior.κ₀ * sensorPrior.μ₀ + morningShift.tempEvidence.sum) /
      (sensorPrior.κ₀ + morningShift.tempEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ morningShift_temp_realizable

/-- Posterior κ after morning shift. -/
theorem morningShift_posterior_kappa :
    (posterior sensorPrior morningShift.tempEvidence).κ₀ =
      sensorPrior.κ₀ + morningShift.tempEvidence.n := rfl

/-- Posterior α after morning shift. -/
theorem morningShift_posterior_alpha :
    (posterior sensorPrior morningShift.tempEvidence).α₀ =
      sensorPrior.α₀ + (morningShift.tempEvidence.n : ℝ) / 2 := rfl

/-- Posterior β after morning shift: closed form under realizability. -/
theorem morningShift_posterior_beta :
    (posterior sensorPrior morningShift.tempEvidence).β₀ =
      sensorPrior.β₀ +
        (morningShift.tempEvidence.sumSq + sensorPrior.κ₀ * sensorPrior.μ₀ ^ 2
          - (sensorPrior.κ₀ * sensorPrior.μ₀ + morningShift.tempEvidence.sum) ^ 2 /
            (sensorPrior.κ₀ + morningShift.tempEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ morningShift_temp_realizable

/-- Posterior mean after night shift. -/
theorem nightShift_posterior_mu :
    (posterior sensorPrior nightShift.tempEvidence).μ₀ =
      (sensorPrior.κ₀ * sensorPrior.μ₀ + nightShift.tempEvidence.sum) /
      (sensorPrior.κ₀ + nightShift.tempEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ nightShift_temp_realizable

/-- Posterior κ after night shift. -/
theorem nightShift_posterior_kappa :
    (posterior sensorPrior nightShift.tempEvidence).κ₀ =
      sensorPrior.κ₀ + nightShift.tempEvidence.n := rfl

/-- Posterior α after night shift. -/
theorem nightShift_posterior_alpha :
    (posterior sensorPrior nightShift.tempEvidence).α₀ =
      sensorPrior.α₀ + (nightShift.tempEvidence.n : ℝ) / 2 := rfl

/-- Posterior β after night shift: closed form under realizability. -/
theorem nightShift_posterior_beta :
    (posterior sensorPrior nightShift.tempEvidence).β₀ =
      sensorPrior.β₀ +
        (nightShift.tempEvidence.sumSq + sensorPrior.κ₀ * sensorPrior.μ₀ ^ 2
          - (sensorPrior.κ₀ * sensorPrior.μ₀ + nightShift.tempEvidence.sum) ^ 2 /
            (sensorPrior.κ₀ + nightShift.tempEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ nightShift_temp_realizable

/-! ## §8: Main Theorems -/

/-- **Sleep consolidation**: replaying deferred observations into sufficient statistics
    preserves the posterior. Batch replay = sequential Bayesian update.

    This is the mathematical foundation for "sleep as evidence consolidation":
    the system can accumulate observations during the day and assimilate them
    in a single batch at night, getting the same posterior as sequential updates. -/
theorem sleep_consolidation :
    posterior sensorPrior (morningShift.tempEvidence + nightShift.tempEvidence) =
    posterior (posterior sensorPrior morningShift.tempEvidence) nightShift.tempEvidence :=
  posterior_hplus_of_realizable
    sensorPrior _ _ morningShift_temp_realizable nightShift_temp_realizable

/-- Confidence increases with more observations. -/
theorem confidence_monotone_add (e₁ e₂ : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e₁.toConfidence κ ≤ (e₁ + e₂).toConfidence κ :=
  EvidenceNormalGamma.confidence_monotone _ _ _ hκ (Nat.le_add_right _ _)

/-- Exceedance probability decreases as threshold increases
    (for any valid ExceedanceSpec). -/
theorem exceedance_warning_ge_critical (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (s : SensorState) :
    spec.exceedance (posterior prior s.tempEvidence) criticalThreshold ≤
    spec.exceedance (posterior prior s.tempEvidence) warningThreshold := by
  apply spec.exceedance_anti_threshold
  unfold warningThreshold criticalThreshold
  norm_num

/-- The cooling-failure evidence extraction is purely Boolean:
    it only depends on the coolFailEvidence component of the state. -/
theorem coolFail_independent_of_temp (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (s : SensorState) :
    sensorEvidence spec prior s .coolFail = s.coolFailEvidence := rfl

/-- Temperature exceedance evidence is independent of cooling-failure observations. -/
theorem exceedance_independent_of_coolFail (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (s₁ s₂ : SensorState) (c : ℝ)
    (ht : s₁.tempEvidence = s₂.tempEvidence) :
    sensorEvidence spec prior s₁ (.exceedance c) =
    sensorEvidence spec prior s₂ (.exceedance c) := by
  simp [sensorEvidence, exceedanceEvidence, ht]

/-! ## §8: Hybrid State Properties -/

/-- Observation count for temperature increases with revision. -/
theorem temp_obs_count_add (s₁ s₂ : SensorState) :
    (s₁ + s₂).tempEvidence.n = s₁.tempEvidence.n + s₂.tempEvidence.n := rfl

/-- Cool-fail evidence adds componentwise. -/
theorem coolFail_evidence_add (s₁ s₂ : SensorState) :
    (s₁ + s₂).coolFailEvidence = s₁.coolFailEvidence + s₂.coolFailEvidence := rfl

/-- A pure temperature observation does not affect cooling evidence. -/
theorem tempObs_coolFail_zero (x : ℝ) : (tempObs x).coolFailEvidence = Evidence.zero := rfl

/-- A cooling observation does not affect temperature evidence. -/
theorem coolFailObs_temp_zero (b : Bool) :
    (coolFailObs b).tempEvidence = NormalGammaEvidence.zero := rfl

/-! ## §9: Canary Tests -/

/-- Canary: sensor state addition is commutative. -/
theorem canary_add_comm : morningShift + nightShift = nightShift + morningShift :=
  SensorState.add_comm _ _

/-- Canary: morning shift has 5 temperature observations. -/
theorem canary_morning_count : morningShift.tempEvidence.n = 5 := by
  simp only [morningShift, tempObs, SensorState.add_tempEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: night shift has 5 temperature observations. -/
theorem canary_night_count : nightShift.tempEvidence.n = 5 := by
  simp only [nightShift, tempObs, SensorState.add_tempEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: full day has 10 temperature observations. -/
theorem canary_fullDay_temp_count : fullDay.tempEvidence.n = 10 := by
  simp only [fullDay, coolFailHistory, morningShift, nightShift, tempObs,
    SensorState.add_tempEvidence, hplus_n,
    NormalGammaEvidence.single, NormalGammaEvidence.zero]

/-- Canary: full day has 100 cooling checks. -/
theorem canary_fullDay_coolFail_total :
    fullDay.coolFailEvidence.pos + fullDay.coolFailEvidence.neg = 100 := by
  simp only [fullDay, coolFailHistory, morningShift, nightShift, tempObs,
    SensorState.add_coolFailEvidence, Evidence.hplus_def, Evidence.zero]
  norm_num

/-- Canary: pure temperature observations don't pollute cooling evidence. -/
theorem canary_temp_only_no_coolFail :
    (morningShift + nightShift).coolFailEvidence = Evidence.zero := by
  simp only [morningShift, nightShift, tempObs,
    SensorState.add_coolFailEvidence, Evidence.hplus_def, Evidence.zero]
  ext <;> simp

end Mettapedia.Logic.PLNBrokenSensorDemo
