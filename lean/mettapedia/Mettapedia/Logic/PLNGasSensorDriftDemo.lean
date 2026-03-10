/-
# Gas Sensor Array Drift Demo: Multi-Source Classification with Temporal Drift

The fourth applied example exercising continuous (Gaussian) world models in PLN.
Based on real data from the UCI Gas Sensor Array Drift Dataset
(DOI 10.24432/C5RP6W, Vergara et al., CC BY 4.0).

## The Model

A chemical sensor array monitoring 3 gas types (Ethanol, Ammonia, Toluene).
Each gas produces a characteristic sensor-1 steady-state resistance response
drawn from N(μᵢ, 1/τᵢ) with unknown per-gas parameters.  Normal-Gamma
priors per gas type are updated by streaming observations.

## What's New vs Previous Demos

- **3 source classes** instead of 2 (extends widget factory to ternary)
- **Real UCI data** as fixture values (not hand-crafted toy numbers)
- **Temporal drift**: batch 1 (2007) vs batch 10 (2011) exhibit
  sensor drift, demonstrating that posteriors from different epochs
  capture genuine distributional shift
- **Multi-batch sleep consolidation**: batch1 ++ batch10 = sequential

## Key Results

1. Per-gas sleep consolidation: batch replay = sequential Bayesian update
2. Cross-gas independence: ethanol observations don't affect ammonia's posterior
3. Multi-batch composition: early + late batches compose associatively
4. Confidence monotonicity per gas type
5. Gas-type attribution evidence (ternary source tracking)
6. Exceedance anti-threshold for classification queries

## Fixture Provenance

Sensor 1 steady-state resistance (feature index 1), 5 samples per gas
from batch 1 and batch 10.  Extraction script:
  scripts/extract_gas_sensor_fixture.py

0 sorry.
-/

import Mettapedia.Logic.EvidenceNormalGamma
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNBrokenSensorDemo

namespace Mettapedia.Logic.PLNGasSensorDriftDemo

open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNBrokenSensorDemo (ExceedanceSpec)

/-! ## §1: Gas Type -/

/-- The three target gas types from the UCI dataset. -/
inductive GasType where
  | ethanol | ammonia | toluene
  deriving DecidableEq, Inhabited

/-! ## §2: Sensor Array State

The state tracks per-gas Normal-Gamma evidence for sensor responses
and ternary source-attribution counts. -/

/-- Sensor array state: per-gas Gaussian evidence + source attribution. -/
structure SensorArrayState where
  /-- Sufficient statistics for ethanol sensor responses -/
  ethanolEvidence : NormalGammaEvidence
  /-- Sufficient statistics for ammonia sensor responses -/
  ammoniaEvidence : NormalGammaEvidence
  /-- Sufficient statistics for toluene sensor responses -/
  tolueneEvidence : NormalGammaEvidence
  /-- Ternary source attribution: (ethanol_count, ammonia_count, toluene_count) -/
  sourceEthanol : ℕ
  sourceAmmonia : ℕ
  sourceToluene : ℕ

namespace SensorArrayState

/-- Zero state: no observations from any gas. -/
def zero : SensorArrayState where
  ethanolEvidence := NormalGammaEvidence.zero
  ammoniaEvidence := NormalGammaEvidence.zero
  tolueneEvidence := NormalGammaEvidence.zero
  sourceEthanol := 0
  sourceAmmonia := 0
  sourceToluene := 0

/-- Componentwise addition (revision). -/
noncomputable def add (s₁ s₂ : SensorArrayState) : SensorArrayState where
  ethanolEvidence := s₁.ethanolEvidence + s₂.ethanolEvidence
  ammoniaEvidence := s₁.ammoniaEvidence + s₂.ammoniaEvidence
  tolueneEvidence := s₁.tolueneEvidence + s₂.tolueneEvidence
  sourceEthanol := s₁.sourceEthanol + s₂.sourceEthanol
  sourceAmmonia := s₁.sourceAmmonia + s₂.sourceAmmonia
  sourceToluene := s₁.sourceToluene + s₂.sourceToluene

noncomputable instance : Add SensorArrayState where add := add
instance : Zero SensorArrayState where zero := zero

@[simp] theorem add_ethanolEvidence (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).ethanolEvidence = s₁.ethanolEvidence + s₂.ethanolEvidence := rfl
@[simp] theorem add_ammoniaEvidence (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).ammoniaEvidence = s₁.ammoniaEvidence + s₂.ammoniaEvidence := rfl
@[simp] theorem add_tolueneEvidence (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).tolueneEvidence = s₁.tolueneEvidence + s₂.tolueneEvidence := rfl
@[simp] theorem add_sourceEthanol (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).sourceEthanol = s₁.sourceEthanol + s₂.sourceEthanol := rfl
@[simp] theorem add_sourceAmmonia (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).sourceAmmonia = s₁.sourceAmmonia + s₂.sourceAmmonia := rfl
@[simp] theorem add_sourceToluene (s₁ s₂ : SensorArrayState) :
    (s₁ + s₂).sourceToluene = s₁.sourceToluene + s₂.sourceToluene := rfl

@[simp] theorem zero_ethanolEvidence :
    (zero : SensorArrayState).ethanolEvidence = NormalGammaEvidence.zero := rfl
@[simp] theorem zero_ammoniaEvidence :
    (zero : SensorArrayState).ammoniaEvidence = NormalGammaEvidence.zero := rfl
@[simp] theorem zero_tolueneEvidence :
    (zero : SensorArrayState).tolueneEvidence = NormalGammaEvidence.zero := rfl

@[ext]
theorem ext {s₁ s₂ : SensorArrayState}
    (hE : s₁.ethanolEvidence = s₂.ethanolEvidence)
    (hA : s₁.ammoniaEvidence = s₂.ammoniaEvidence)
    (hT : s₁.tolueneEvidence = s₂.tolueneEvidence)
    (hSE : s₁.sourceEthanol = s₂.sourceEthanol)
    (hSA : s₁.sourceAmmonia = s₂.sourceAmmonia)
    (hST : s₁.sourceToluene = s₂.sourceToluene) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact ⟨hE, hA, hT, hSE, hSA, hST⟩

theorem add_comm (s₁ s₂ : SensorArrayState) : s₁ + s₂ = s₂ + s₁ := by
  apply ext
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _

theorem add_assoc (s₁ s₂ s₃ : SensorArrayState) : s₁ + s₂ + s₃ = s₁ + (s₂ + s₃) := by
  apply ext
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact Nat.add_assoc _ _ _
  · exact Nat.add_assoc _ _ _
  · exact Nat.add_assoc _ _ _

theorem zero_add (s : SensorArrayState) : zero + s = s := by
  apply ext
  · exact NormalGammaEvidence.zero_hplus _
  · exact NormalGammaEvidence.zero_hplus _
  · exact NormalGammaEvidence.zero_hplus _
  · exact Nat.zero_add _
  · exact Nat.zero_add _
  · exact Nat.zero_add _

theorem add_zero (s : SensorArrayState) : s + zero = s := by
  apply ext
  · exact NormalGammaEvidence.hplus_zero _
  · exact NormalGammaEvidence.hplus_zero _
  · exact NormalGammaEvidence.hplus_zero _
  · exact Nat.add_zero _
  · exact Nat.add_zero _
  · exact Nat.add_zero _

noncomputable instance instAddCommMonoid : AddCommMonoid SensorArrayState where
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

noncomputable instance instEvidenceType : EvidenceType SensorArrayState where

end SensorArrayState

/-! ## §3: Evidence Extraction -/

/-- Extract the Normal-Gamma evidence for a given gas type. -/
def gasEvidence (s : SensorArrayState) : GasType → NormalGammaEvidence
  | .ethanol => s.ethanolEvidence
  | .ammonia => s.ammoniaEvidence
  | .toluene => s.tolueneEvidence

/-- Extract the source count for a given gas type. -/
def sourceCount (s : SensorArrayState) : GasType → ℕ
  | .ethanol => s.sourceEthanol
  | .ammonia => s.sourceAmmonia
  | .toluene => s.sourceToluene

/-- Total number of observations across all gas types. -/
def totalSourceCount (s : SensorArrayState) : ℕ :=
  s.sourceEthanol + s.sourceAmmonia + s.sourceToluene

/-- Per-gas exceedance evidence: P(sensor response > c | gas type g). -/
noncomputable def gasExceedanceEvidence
    (spec : ExceedanceSpec) (priors : GasType → NormalGammaPrior)
    (s : SensorArrayState) (g : GasType) (c : ℝ) : Evidence :=
  let ngEvid := gasEvidence s g
  let post := posterior (priors g) ngEvid
  let p := spec.exceedance post c
  let n := ngEvid.n
  ⟨ENNReal.ofReal (p * n), ENNReal.ofReal ((1 - p) * n)⟩

/-! ## §4: Observation Constructors -/

/-- A single sensor reading from a known gas type. -/
noncomputable def gasObs (g : GasType) (x : ℝ) : SensorArrayState :=
  match g with
  | .ethanol => {
      ethanolEvidence := NormalGammaEvidence.single x
      ammoniaEvidence := NormalGammaEvidence.zero
      tolueneEvidence := NormalGammaEvidence.zero
      sourceEthanol := 1
      sourceAmmonia := 0
      sourceToluene := 0 }
  | .ammonia => {
      ethanolEvidence := NormalGammaEvidence.zero
      ammoniaEvidence := NormalGammaEvidence.single x
      tolueneEvidence := NormalGammaEvidence.zero
      sourceEthanol := 0
      sourceAmmonia := 1
      sourceToluene := 0 }
  | .toluene => {
      ethanolEvidence := NormalGammaEvidence.zero
      ammoniaEvidence := NormalGammaEvidence.zero
      tolueneEvidence := NormalGammaEvidence.single x
      sourceEthanol := 0
      sourceAmmonia := 0
      sourceToluene := 1 }

/-! ## §5: Real UCI Fixture Data

Sensor 1 steady-state resistance (ΔR), 5 samples per gas type.
Batch 1 = early calibration (Jan 2007), Batch 10 = late drift (Feb 2011).
Source: UCI Gas Sensor Array Drift Dataset, DOI 10.24432/C5RP6W. -/

/-- Batch 1 ethanol readings (sensor 1 steady-state, ΔR units). -/
noncomputable def batch1Ethanol : SensorArrayState :=
  gasObs .ethanol 15596.2 + gasObs .ethanol 26402.1 +
  gasObs .ethanol 42103.6 + gasObs .ethanol 42826.0 +
  gasObs .ethanol 58151.2

/-- Batch 1 ammonia readings. -/
noncomputable def batch1Ammonia : SensorArrayState :=
  gasObs .ammonia 7858.2 + gasObs .ammonia 4860.7 +
  gasObs .ammonia 6485.3 + gasObs .ammonia 7554.4 +
  gasObs .ammonia 8342.9

/-- Batch 1 toluene readings. -/
noncomputable def batch1Toluene : SensorArrayState :=
  gasObs .toluene 109930.2 + gasObs .toluene 135152.9 +
  gasObs .toluene 142695.1 + gasObs .toluene 149073.8 +
  gasObs .toluene 155186.3

/-- Full batch 1: all 15 observations from early calibration. -/
noncomputable def batch1 : SensorArrayState :=
  batch1Ethanol + batch1Ammonia + batch1Toluene

/-- Batch 10 ethanol readings (sensor drift visible). -/
noncomputable def batch10Ethanol : SensorArrayState :=
  gasObs .ethanol 4485.5 + gasObs .ethanol 85677.8 +
  gasObs .ethanol 63331.5 + gasObs .ethanol 32169.4 +
  gasObs .ethanol 51652.9

/-- Batch 10 ammonia readings. -/
noncomputable def batch10Ammonia : SensorArrayState :=
  gasObs .ammonia (-35.7) + gasObs .ammonia 2992.9 +
  gasObs .ammonia 6277.3 + gasObs .ammonia 3985.1 +
  gasObs .ammonia 14486.8

/-- Batch 10 toluene readings. -/
noncomputable def batch10Toluene : SensorArrayState :=
  gasObs .toluene (-1377.3) + gasObs .toluene 48547.2 +
  gasObs .toluene 30552.5 + gasObs .toluene 15789.0 +
  gasObs .toluene 28252.7

/-- Full batch 10: all 15 observations from late epoch. -/
noncomputable def batch10 : SensorArrayState :=
  batch10Ethanol + batch10Ammonia + batch10Toluene

/-- Combined dataset: all 30 observations across both epochs. -/
noncomputable def fullDataset : SensorArrayState := batch1 + batch10

/-! ## §6: Priors

Weak priors centered roughly at mid-range sensor responses for each gas.
The data will dominate quickly. -/

/-- Ethanol prior: mid-range for ΔR in early batches. -/
noncomputable def ethanolPrior : NormalGammaPrior where
  μ₀ := 50000
  κ₀ := 0.1
  α₀ := 2
  β₀ := 1e8
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Ammonia prior: lower range. -/
noncomputable def ammoniaPrior : NormalGammaPrior where
  μ₀ := 10000
  κ₀ := 0.1
  α₀ := 2
  β₀ := 1e7
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Toluene prior: higher range. -/
noncomputable def toluenePrior : NormalGammaPrior where
  μ₀ := 100000
  κ₀ := 0.1
  α₀ := 2
  β₀ := 1e9
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Gas-type-indexed prior lookup. -/
noncomputable def gasPriors : GasType → NormalGammaPrior
  | .ethanol => ethanolPrior
  | .ammonia => ammoniaPrior
  | .toluene => toluenePrior

/-- High-response threshold for classification: sensor response above this
    suggests a heavy organic (ethanol/toluene) rather than ammonia. -/
def highResponseThreshold : ℝ := 50000

/-! ## §7: Realizability Side Conditions -/

theorem single_realizable (x : ℝ) :
    (NormalGammaEvidence.single x).Realizable := by
  intro h; simp [NormalGammaEvidence.single] at h

private theorem batch_realizable_5
    (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    (NormalGammaEvidence.single x₁ + NormalGammaEvidence.single x₂ +
     NormalGammaEvidence.single x₃ + NormalGammaEvidence.single x₄ +
     NormalGammaEvidence.single x₅).Realizable := by
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _

theorem batch1Ethanol_realizable : batch1Ethanol.ethanolEvidence.Realizable := by
  simp only [batch1Ethanol, gasObs, SensorArrayState.add_ethanolEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem batch1Ammonia_realizable : batch1Ammonia.ammoniaEvidence.Realizable := by
  simp only [batch1Ammonia, gasObs, SensorArrayState.add_ammoniaEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem batch1Toluene_realizable : batch1Toluene.tolueneEvidence.Realizable := by
  simp only [batch1Toluene, gasObs, SensorArrayState.add_tolueneEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem batch10Ethanol_realizable : batch10Ethanol.ethanolEvidence.Realizable := by
  simp only [batch10Ethanol, gasObs, SensorArrayState.add_ethanolEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem batch10Ammonia_realizable : batch10Ammonia.ammoniaEvidence.Realizable := by
  simp only [batch10Ammonia, gasObs, SensorArrayState.add_ammoniaEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem batch10Toluene_realizable : batch10Toluene.tolueneEvidence.Realizable := by
  simp only [batch10Toluene, gasObs, SensorArrayState.add_tolueneEvidence]
  exact batch_realizable_5 _ _ _ _ _

/-! ## §7b: Bridge Theorems — Closed-Form Posterior Parameters (Batch 1)

Pin (μ, κ, α, β) for each gas type after batch 1, bridging Lean proofs to
the Python numerical layer's credible intervals and exceedance probabilities. -/

-- Ethanol (batch 1)
theorem ethanol_batch1_posterior_mu :
    (posterior ethanolPrior batch1Ethanol.ethanolEvidence).μ₀ =
      (ethanolPrior.κ₀ * ethanolPrior.μ₀ + batch1Ethanol.ethanolEvidence.sum) /
      (ethanolPrior.κ₀ + batch1Ethanol.ethanolEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ batch1Ethanol_realizable

theorem ethanol_batch1_posterior_kappa :
    (posterior ethanolPrior batch1Ethanol.ethanolEvidence).κ₀ =
      ethanolPrior.κ₀ + batch1Ethanol.ethanolEvidence.n := rfl

theorem ethanol_batch1_posterior_alpha :
    (posterior ethanolPrior batch1Ethanol.ethanolEvidence).α₀ =
      ethanolPrior.α₀ + (batch1Ethanol.ethanolEvidence.n : ℝ) / 2 := rfl

theorem ethanol_batch1_posterior_beta :
    (posterior ethanolPrior batch1Ethanol.ethanolEvidence).β₀ =
      ethanolPrior.β₀ +
        (batch1Ethanol.ethanolEvidence.sumSq + ethanolPrior.κ₀ * ethanolPrior.μ₀ ^ 2
          - (ethanolPrior.κ₀ * ethanolPrior.μ₀ + batch1Ethanol.ethanolEvidence.sum) ^ 2 /
            (ethanolPrior.κ₀ + batch1Ethanol.ethanolEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ batch1Ethanol_realizable

-- Ammonia (batch 1)
theorem ammonia_batch1_posterior_mu :
    (posterior ammoniaPrior batch1Ammonia.ammoniaEvidence).μ₀ =
      (ammoniaPrior.κ₀ * ammoniaPrior.μ₀ + batch1Ammonia.ammoniaEvidence.sum) /
      (ammoniaPrior.κ₀ + batch1Ammonia.ammoniaEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ batch1Ammonia_realizable

theorem ammonia_batch1_posterior_kappa :
    (posterior ammoniaPrior batch1Ammonia.ammoniaEvidence).κ₀ =
      ammoniaPrior.κ₀ + batch1Ammonia.ammoniaEvidence.n := rfl

theorem ammonia_batch1_posterior_alpha :
    (posterior ammoniaPrior batch1Ammonia.ammoniaEvidence).α₀ =
      ammoniaPrior.α₀ + (batch1Ammonia.ammoniaEvidence.n : ℝ) / 2 := rfl

theorem ammonia_batch1_posterior_beta :
    (posterior ammoniaPrior batch1Ammonia.ammoniaEvidence).β₀ =
      ammoniaPrior.β₀ +
        (batch1Ammonia.ammoniaEvidence.sumSq + ammoniaPrior.κ₀ * ammoniaPrior.μ₀ ^ 2
          - (ammoniaPrior.κ₀ * ammoniaPrior.μ₀ + batch1Ammonia.ammoniaEvidence.sum) ^ 2 /
            (ammoniaPrior.κ₀ + batch1Ammonia.ammoniaEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ batch1Ammonia_realizable

-- Toluene (batch 1)
theorem toluene_batch1_posterior_mu :
    (posterior toluenePrior batch1Toluene.tolueneEvidence).μ₀ =
      (toluenePrior.κ₀ * toluenePrior.μ₀ + batch1Toluene.tolueneEvidence.sum) /
      (toluenePrior.κ₀ + batch1Toluene.tolueneEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ batch1Toluene_realizable

theorem toluene_batch1_posterior_kappa :
    (posterior toluenePrior batch1Toluene.tolueneEvidence).κ₀ =
      toluenePrior.κ₀ + batch1Toluene.tolueneEvidence.n := rfl

theorem toluene_batch1_posterior_alpha :
    (posterior toluenePrior batch1Toluene.tolueneEvidence).α₀ =
      toluenePrior.α₀ + (batch1Toluene.tolueneEvidence.n : ℝ) / 2 := rfl

theorem toluene_batch1_posterior_beta :
    (posterior toluenePrior batch1Toluene.tolueneEvidence).β₀ =
      toluenePrior.β₀ +
        (batch1Toluene.tolueneEvidence.sumSq + toluenePrior.κ₀ * toluenePrior.μ₀ ^ 2
          - (toluenePrior.κ₀ * toluenePrior.μ₀ + batch1Toluene.tolueneEvidence.sum) ^ 2 /
            (toluenePrior.κ₀ + batch1Toluene.tolueneEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ batch1Toluene_realizable

/-! ## §8: Main Theorems -/

/-- **Per-gas sleep consolidation**: batch replay = sequential Bayesian update
    for any gas type.  Generalizes widget factory to 3 sources. -/
theorem sleep_consolidation_generic (prior : NormalGammaPrior)
    (e₁ e₂ : NormalGammaEvidence)
    (h₁ : e₁.Realizable) (h₂ : e₂.Realizable) :
    posterior prior (e₁ + e₂) = posterior (posterior prior e₁) e₂ :=
  posterior_hplus_of_realizable prior e₁ e₂ h₁ h₂

/-- Sleep consolidation for ethanol across two batches. -/
theorem sleep_consolidation_ethanol :
    posterior ethanolPrior (batch1Ethanol.ethanolEvidence + batch10Ethanol.ethanolEvidence) =
    posterior (posterior ethanolPrior batch1Ethanol.ethanolEvidence)
      batch10Ethanol.ethanolEvidence :=
  posterior_hplus_of_realizable ethanolPrior _ _
    batch1Ethanol_realizable batch10Ethanol_realizable

/-- Sleep consolidation for ammonia across two batches. -/
theorem sleep_consolidation_ammonia :
    posterior ammoniaPrior (batch1Ammonia.ammoniaEvidence + batch10Ammonia.ammoniaEvidence) =
    posterior (posterior ammoniaPrior batch1Ammonia.ammoniaEvidence)
      batch10Ammonia.ammoniaEvidence :=
  posterior_hplus_of_realizable ammoniaPrior _ _
    batch1Ammonia_realizable batch10Ammonia_realizable

/-- Sleep consolidation for toluene across two batches. -/
theorem sleep_consolidation_toluene :
    posterior toluenePrior (batch1Toluene.tolueneEvidence + batch10Toluene.tolueneEvidence) =
    posterior (posterior toluenePrior batch1Toluene.tolueneEvidence)
      batch10Toluene.tolueneEvidence :=
  posterior_hplus_of_realizable toluenePrior _ _
    batch1Toluene_realizable batch10Toluene_realizable

/-- **Cross-gas independence**: ethanol observations don't affect ammonia evidence. -/
theorem ethanol_obs_ammonia_zero (x : ℝ) :
    (gasObs .ethanol x).ammoniaEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-gas independence: ethanol observations don't affect toluene evidence. -/
theorem ethanol_obs_toluene_zero (x : ℝ) :
    (gasObs .ethanol x).tolueneEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-gas independence: ammonia observations don't affect ethanol evidence. -/
theorem ammonia_obs_ethanol_zero (x : ℝ) :
    (gasObs .ammonia x).ethanolEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-gas independence: ammonia observations don't affect toluene evidence. -/
theorem ammonia_obs_toluene_zero (x : ℝ) :
    (gasObs .ammonia x).tolueneEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-gas independence: toluene observations don't affect ethanol evidence. -/
theorem toluene_obs_ethanol_zero (x : ℝ) :
    (gasObs .toluene x).ethanolEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-gas independence: toluene observations don't affect ammonia evidence. -/
theorem toluene_obs_ammonia_zero (x : ℝ) :
    (gasObs .toluene x).ammoniaEvidence = NormalGammaEvidence.zero := rfl

/-- **Source attribution**: each observation increments exactly one gas counter. -/
theorem gasObs_source_ethanol (x : ℝ) :
    (gasObs .ethanol x).sourceEthanol = 1 ∧
    (gasObs .ethanol x).sourceAmmonia = 0 ∧
    (gasObs .ethanol x).sourceToluene = 0 := ⟨rfl, rfl, rfl⟩

theorem gasObs_source_ammonia (x : ℝ) :
    (gasObs .ammonia x).sourceEthanol = 0 ∧
    (gasObs .ammonia x).sourceAmmonia = 1 ∧
    (gasObs .ammonia x).sourceToluene = 0 := ⟨rfl, rfl, rfl⟩

theorem gasObs_source_toluene (x : ℝ) :
    (gasObs .toluene x).sourceEthanol = 0 ∧
    (gasObs .toluene x).sourceAmmonia = 0 ∧
    (gasObs .toluene x).sourceToluene = 1 := ⟨rfl, rfl, rfl⟩

/-- **Confidence monotonicity**: more observations → higher confidence. -/
theorem confidence_monotone_add (e₁ e₂ : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e₁.toConfidence κ ≤ (e₁ + e₂).toConfidence κ :=
  EvidenceNormalGamma.confidence_monotone _ _ _ hκ (Nat.le_add_right _ _)

/-- **Exceedance anti-threshold**: higher threshold → lower exceedance probability. -/
theorem exceedance_anti_threshold (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (e : NormalGammaEvidence) (c₁ c₂ : ℝ) (h : c₁ ≤ c₂) :
    spec.exceedance (posterior prior e) c₂ ≤
    spec.exceedance (posterior prior e) c₁ :=
  spec.exceedance_anti_threshold _ _ _ h

/-- **Multi-batch composition**: the combined dataset state is the sum of batches. -/
theorem fullDataset_eq : fullDataset = batch1 + batch10 := rfl

/-- **Batch decomposition**: batch 1 decomposes into its gas-type components. -/
theorem batch1_eq : batch1 = batch1Ethanol + batch1Ammonia + batch1Toluene := rfl

/-- **Batch 10 decomposition**: batch 10 decomposes into its components. -/
theorem batch10_eq : batch10 = batch10Ethanol + batch10Ammonia + batch10Toluene := rfl

/-- **Multi-batch associativity**: processing 3 gas batches then combining epochs
    is the same as combining all at once. -/
theorem multi_batch_assoc :
    batch1Ethanol + batch1Ammonia + batch1Toluene +
      (batch10Ethanol + batch10Ammonia + batch10Toluene) =
    fullDataset := by
  unfold fullDataset batch1 batch10
  rfl

/-- Per-gas exceedance evidence is independent of other gases' observations. -/
theorem exceedance_ethanol_independent_of_ammonia
    (spec : ExceedanceSpec) (s₁ s₂ : SensorArrayState) (c : ℝ)
    (hE : s₁.ethanolEvidence = s₂.ethanolEvidence) :
    gasExceedanceEvidence spec gasPriors s₁ .ethanol c =
    gasExceedanceEvidence spec gasPriors s₂ .ethanol c := by
  simp [gasExceedanceEvidence, gasEvidence, gasPriors, hE]

/-- Source weight normalization for 3-way classification. -/
theorem source_weights_sum_to_one (nE nA nT : ℕ) (h : 0 < nE + nA + nT) :
    (nE : ℝ) / (nE + nA + nT) + (nA : ℝ) / (nE + nA + nT) +
    (nT : ℝ) / (nE + nA + nT) = 1 := by
  have hpos : (0 : ℝ) < (nE + nA + nT : ℕ) := Nat.cast_pos.mpr h
  rw [Nat.cast_add, Nat.cast_add] at hpos
  have hne : ((nE : ℝ) + (nA : ℝ) + (nT : ℝ)) ≠ 0 := ne_of_gt hpos
  field_simp [hne]

/-! ## §9: Canary Tests -/

/-- Canary: state addition is commutative. -/
theorem canary_add_comm : batch1 + batch10 = batch10 + batch1 :=
  SensorArrayState.add_comm _ _

/-- Canary: batch 1 ethanol has 5 observations. -/
theorem canary_batch1_ethanol_count : batch1Ethanol.ethanolEvidence.n = 5 := by
  simp only [batch1Ethanol, gasObs, SensorArrayState.add_ethanolEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: batch 1 ammonia has 5 observations. -/
theorem canary_batch1_ammonia_count : batch1Ammonia.ammoniaEvidence.n = 5 := by
  simp only [batch1Ammonia, gasObs, SensorArrayState.add_ammoniaEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: batch 1 toluene has 5 observations. -/
theorem canary_batch1_toluene_count : batch1Toluene.tolueneEvidence.n = 5 := by
  simp only [batch1Toluene, gasObs, SensorArrayState.add_tolueneEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: batch 1 has 15 total source observations. -/
theorem canary_batch1_total_sources :
    totalSourceCount batch1 = 15 := by
  simp only [totalSourceCount, batch1, batch1Ethanol, batch1Ammonia, batch1Toluene,
    gasObs, SensorArrayState.add_sourceEthanol, SensorArrayState.add_sourceAmmonia,
    SensorArrayState.add_sourceToluene]

/-- Canary: batch 10 ethanol has 5 observations. -/
theorem canary_batch10_ethanol_count : batch10Ethanol.ethanolEvidence.n = 5 := by
  simp only [batch10Ethanol, gasObs, SensorArrayState.add_ethanolEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: full dataset has 30 total source observations. -/
theorem canary_fullDataset_total_sources :
    totalSourceCount fullDataset = 30 := by
  simp only [totalSourceCount, fullDataset, batch1, batch10,
    batch1Ethanol, batch1Ammonia, batch1Toluene,
    batch10Ethanol, batch10Ammonia, batch10Toluene,
    gasObs, SensorArrayState.add_sourceEthanol,
    SensorArrayState.add_sourceAmmonia, SensorArrayState.add_sourceToluene]

/-- Canary: ethanol batch has no ammonia evidence. -/
theorem canary_ethanol_no_ammonia :
    batch1Ethanol.ammoniaEvidence = NormalGammaEvidence.zero := by
  simp only [batch1Ethanol, gasObs, SensorArrayState.add_ammoniaEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: ammonia batch has no ethanol evidence. -/
theorem canary_ammonia_no_ethanol :
    batch1Ammonia.ethanolEvidence = NormalGammaEvidence.zero := by
  simp only [batch1Ammonia, gasObs, SensorArrayState.add_ethanolEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: toluene batch has no ethanol evidence. -/
theorem canary_toluene_no_ethanol :
    batch1Toluene.ethanolEvidence = NormalGammaEvidence.zero := by
  simp only [batch1Toluene, gasObs, SensorArrayState.add_ethanolEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: 5 ethanol + 5 ammonia + 5 toluene source obs in batch 1. -/
theorem canary_batch1_source_breakdown :
    batch1.sourceEthanol = 5 ∧
    batch1.sourceAmmonia = 5 ∧
    batch1.sourceToluene = 5 := by
  simp only [batch1, batch1Ethanol, batch1Ammonia, batch1Toluene,
    gasObs, SensorArrayState.add_sourceEthanol,
    SensorArrayState.add_sourceAmmonia, SensorArrayState.add_sourceToluene]
  trivial

/-- Canary: full dataset has 10 ethanol observations total (5 + 5). -/
theorem canary_fullDataset_ethanol_count :
    fullDataset.ethanolEvidence.n = 10 := by
  simp only [fullDataset, batch1, batch10,
    batch1Ethanol, batch1Ammonia, batch1Toluene,
    batch10Ethanol, batch10Ammonia, batch10Toluene,
    gasObs, SensorArrayState.add_ethanolEvidence,
    hplus_n, NormalGammaEvidence.single, NormalGammaEvidence.zero]

end Mettapedia.Logic.PLNGasSensorDriftDemo
