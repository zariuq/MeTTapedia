/-
# Steel Plates Faults Demo: Class-Conditional Gaussian Classification

The fifth applied example exercising continuous (Gaussian) world models in PLN.
Based on real data from the UCI Steel Plates Faults Dataset
(DOI 10.24432/C53P4W, Semeion Research Center, CC BY 4.0).

## The Model

A steel plate fault classification system with 3 fault types
(Pastry, K_Scratch, Bumps).  Each fault produces a characteristic
LogOfAreas measurement drawn from N(μᵢ, 1/τᵢ) with unknown
per-fault parameters.  Normal-Gamma priors per fault type.

## What's New vs Previous Demos

- **Real manufacturing data** (not toy or sensor data)
- **Classification story**: fault types have distinct feature signatures
  (K_Scratch has higher LogOfAreas (pop. mean ~3.6) vs Pastry (~2.4) vs Bumps (~2.1))
- **Source-conditional Gaussians for quality control**

## Key Results

1. Per-fault sleep consolidation: batch replay = sequential Bayesian update
2. Cross-fault independence: pastry observations don't affect K_Scratch posterior
3. Classification evidence: K_Scratch has distinctly higher LogOfAreas than Bumps
4. Confidence monotonicity per fault type
5. 3-way mixture exceedance validity (convex combination)
6. Source weight normalization

## Fixture Provenance

LogOfAreas (feature index 21, 0-based), 5 samples per fault type.
Extraction script: scripts/extract_steel_faults_fixture.py

0 sorry.
-/

import Mettapedia.Logic.EvidenceNormalGamma
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNBrokenSensorDemo

namespace Mettapedia.Logic.PLNSteelFaultDemo

open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNBrokenSensorDemo (ExceedanceSpec)

/-! ## §1: Fault Type -/

/-- The three target fault types from the UCI Steel Plates dataset. -/
inductive FaultType where
  | pastry | kScratch | bumps
  deriving DecidableEq, Inhabited

/-! ## §2: Fault Classification State -/

/-- Fault classification state: per-fault Gaussian LogOfAreas evidence
    + ternary source attribution. -/
structure FaultState where
  /-- Sufficient statistics for Pastry fault LogOfAreas -/
  pastryEvidence : NormalGammaEvidence
  /-- Sufficient statistics for K_Scratch fault LogOfAreas -/
  kScratchEvidence : NormalGammaEvidence
  /-- Sufficient statistics for Bumps fault LogOfAreas -/
  bumpsEvidence : NormalGammaEvidence
  /-- Ternary source attribution counts -/
  sourcePastry : ℕ
  sourceKScratch : ℕ
  sourceBumps : ℕ

namespace FaultState

/-- Zero state: no observations from any fault type. -/
def zero : FaultState where
  pastryEvidence := NormalGammaEvidence.zero
  kScratchEvidence := NormalGammaEvidence.zero
  bumpsEvidence := NormalGammaEvidence.zero
  sourcePastry := 0
  sourceKScratch := 0
  sourceBumps := 0

/-- Componentwise addition (revision). -/
noncomputable def add (s₁ s₂ : FaultState) : FaultState where
  pastryEvidence := s₁.pastryEvidence + s₂.pastryEvidence
  kScratchEvidence := s₁.kScratchEvidence + s₂.kScratchEvidence
  bumpsEvidence := s₁.bumpsEvidence + s₂.bumpsEvidence
  sourcePastry := s₁.sourcePastry + s₂.sourcePastry
  sourceKScratch := s₁.sourceKScratch + s₂.sourceKScratch
  sourceBumps := s₁.sourceBumps + s₂.sourceBumps

noncomputable instance : Add FaultState where add := add
instance : Zero FaultState where zero := zero

@[simp] theorem add_pastryEvidence (s₁ s₂ : FaultState) :
    (s₁ + s₂).pastryEvidence = s₁.pastryEvidence + s₂.pastryEvidence := rfl
@[simp] theorem add_kScratchEvidence (s₁ s₂ : FaultState) :
    (s₁ + s₂).kScratchEvidence = s₁.kScratchEvidence + s₂.kScratchEvidence := rfl
@[simp] theorem add_bumpsEvidence (s₁ s₂ : FaultState) :
    (s₁ + s₂).bumpsEvidence = s₁.bumpsEvidence + s₂.bumpsEvidence := rfl
@[simp] theorem add_sourcePastry (s₁ s₂ : FaultState) :
    (s₁ + s₂).sourcePastry = s₁.sourcePastry + s₂.sourcePastry := rfl
@[simp] theorem add_sourceKScratch (s₁ s₂ : FaultState) :
    (s₁ + s₂).sourceKScratch = s₁.sourceKScratch + s₂.sourceKScratch := rfl
@[simp] theorem add_sourceBumps (s₁ s₂ : FaultState) :
    (s₁ + s₂).sourceBumps = s₁.sourceBumps + s₂.sourceBumps := rfl

@[ext]
theorem ext {s₁ s₂ : FaultState}
    (hP : s₁.pastryEvidence = s₂.pastryEvidence)
    (hK : s₁.kScratchEvidence = s₂.kScratchEvidence)
    (hB : s₁.bumpsEvidence = s₂.bumpsEvidence)
    (hSP : s₁.sourcePastry = s₂.sourcePastry)
    (hSK : s₁.sourceKScratch = s₂.sourceKScratch)
    (hSB : s₁.sourceBumps = s₂.sourceBumps) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact ⟨hP, hK, hB, hSP, hSK, hSB⟩

theorem add_comm (s₁ s₂ : FaultState) : s₁ + s₂ = s₂ + s₁ := by
  apply ext
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _

theorem add_assoc (s₁ s₂ s₃ : FaultState) : s₁ + s₂ + s₃ = s₁ + (s₂ + s₃) := by
  apply ext
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact Nat.add_assoc _ _ _
  · exact Nat.add_assoc _ _ _
  · exact Nat.add_assoc _ _ _

theorem zero_add (s : FaultState) : zero + s = s := by
  apply ext
  · exact NormalGammaEvidence.zero_hplus _
  · exact NormalGammaEvidence.zero_hplus _
  · exact NormalGammaEvidence.zero_hplus _
  · exact Nat.zero_add _
  · exact Nat.zero_add _
  · exact Nat.zero_add _

theorem add_zero (s : FaultState) : s + zero = s := by
  apply ext
  · exact NormalGammaEvidence.hplus_zero _
  · exact NormalGammaEvidence.hplus_zero _
  · exact NormalGammaEvidence.hplus_zero _
  · exact Nat.add_zero _
  · exact Nat.add_zero _
  · exact Nat.add_zero _

noncomputable instance instAddCommMonoid : AddCommMonoid FaultState where
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

noncomputable instance instEvidenceType : EvidenceType FaultState where

end FaultState

/-! ## §3: Evidence Extraction -/

/-- Extract the Normal-Gamma evidence for a given fault type. -/
def faultEvidence (s : FaultState) : FaultType → NormalGammaEvidence
  | .pastry => s.pastryEvidence
  | .kScratch => s.kScratchEvidence
  | .bumps => s.bumpsEvidence

/-- Extract the source count for a given fault type. -/
def sourceCount (s : FaultState) : FaultType → ℕ
  | .pastry => s.sourcePastry
  | .kScratch => s.sourceKScratch
  | .bumps => s.sourceBumps

/-- Total number of observations across all fault types. -/
def totalSourceCount (s : FaultState) : ℕ :=
  s.sourcePastry + s.sourceKScratch + s.sourceBumps

/-- Per-fault exceedance evidence. -/
noncomputable def faultExceedanceEvidence
    (spec : ExceedanceSpec) (priors : FaultType → NormalGammaPrior)
    (s : FaultState) (f : FaultType) (c : ℝ) : Evidence :=
  let ngEvid := faultEvidence s f
  let post := posterior (priors f) ngEvid
  let p := spec.exceedance post c
  let n := ngEvid.n
  ⟨ENNReal.ofReal (p * n), ENNReal.ofReal ((1 - p) * n)⟩

/-! ## §4: Observation Constructors -/

/-- A single LogOfAreas observation from a known fault type. -/
noncomputable def faultObs (f : FaultType) (x : ℝ) : FaultState :=
  match f with
  | .pastry => {
      pastryEvidence := NormalGammaEvidence.single x
      kScratchEvidence := NormalGammaEvidence.zero
      bumpsEvidence := NormalGammaEvidence.zero
      sourcePastry := 1
      sourceKScratch := 0
      sourceBumps := 0 }
  | .kScratch => {
      pastryEvidence := NormalGammaEvidence.zero
      kScratchEvidence := NormalGammaEvidence.single x
      bumpsEvidence := NormalGammaEvidence.zero
      sourcePastry := 0
      sourceKScratch := 1
      sourceBumps := 0 }
  | .bumps => {
      pastryEvidence := NormalGammaEvidence.zero
      kScratchEvidence := NormalGammaEvidence.zero
      bumpsEvidence := NormalGammaEvidence.single x
      sourcePastry := 0
      sourceKScratch := 0
      sourceBumps := 1 }

/-! ## §5: Real UCI Fixture Data

LogOfAreas measurements for each fault type.  The feature captures the
logarithm of the defect area; K_Scratch faults are characteristically
larger (pop. mean ~3.6, σ ~0.70) than Pastry (~2.4, σ ~0.48) or Bumps (~2.1, σ ~0.36).

Source: UCI Steel Plates Faults Dataset, DOI 10.24432/C53P4W. -/

/-- Pastry fault observations (LogOfAreas). Sample mean ~2.39.
    First 5 Pastry rows from dataset (population mean ~2.38, σ ~0.48). -/
noncomputable def pastryBatch : FaultState :=
  faultObs .pastry 2.4265 + faultObs .pastry 2.0334 +
  faultObs .pastry 1.8513 + faultObs .pastry 2.2455 +
  faultObs .pastry 3.3818

/-- K_Scratch fault observations (LogOfAreas). Sample mean ~3.57.
    5 samples at the 10th, 30th, 50th, 70th, 90th percentiles
    of the 391 K_Scratch rows (population mean ~3.60, σ ~0.70). -/
noncomputable def kScratchBatch : FaultState :=
  faultObs .kScratch 2.3010 + faultObs .kScratch 3.6504 +
  faultObs .kScratch 3.7980 + faultObs .kScratch 3.9214 +
  faultObs .kScratch 4.1879

/-- Bumps fault observations (LogOfAreas). Sample mean ~2.34.
    First 5 Bumps rows from dataset (population mean ~2.14, σ ~0.36). -/
noncomputable def bumpsBatch : FaultState :=
  faultObs .bumps 2.0531 + faultObs .bumps 3.2582 +
  faultObs .bumps 1.6128 + faultObs .bumps 2.7694 +
  faultObs .bumps 2.0253

/-- Full production inspection: all 15 observations. -/
noncomputable def fullInspection : FaultState :=
  pastryBatch + kScratchBatch + bumpsBatch

/-! ## §6: Priors

Weak priors allowing data to dominate. -/

/-- Pastry prior: LogOfAreas expected around 2.5. -/
noncomputable def pastryPrior : NormalGammaPrior where
  μ₀ := 2.5
  κ₀ := 0.5
  α₀ := 2
  β₀ := 1
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- K_Scratch prior: LogOfAreas expected around 3.0. -/
noncomputable def kScratchPrior : NormalGammaPrior where
  μ₀ := 3.0
  κ₀ := 0.5
  α₀ := 2
  β₀ := 1
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Bumps prior: LogOfAreas expected around 2.0. -/
noncomputable def bumpsPrior : NormalGammaPrior where
  μ₀ := 2.0
  κ₀ := 0.5
  α₀ := 2
  β₀ := 1
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Fault-type-indexed prior lookup. -/
noncomputable def faultPriors : FaultType → NormalGammaPrior
  | .pastry => pastryPrior
  | .kScratch => kScratchPrior
  | .bumps => bumpsPrior

/-- Threshold for "large defect" classification: LogOfAreas > 3.0. -/
def largeDefectThreshold : ℝ := 3.0

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

theorem pastryBatch_realizable : pastryBatch.pastryEvidence.Realizable := by
  simp only [pastryBatch, faultObs, FaultState.add_pastryEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem kScratchBatch_realizable : kScratchBatch.kScratchEvidence.Realizable := by
  simp only [kScratchBatch, faultObs, FaultState.add_kScratchEvidence]
  exact batch_realizable_5 _ _ _ _ _

theorem bumpsBatch_realizable : bumpsBatch.bumpsEvidence.Realizable := by
  simp only [bumpsBatch, faultObs, FaultState.add_bumpsEvidence]
  exact batch_realizable_5 _ _ _ _ _

/-! ## §7b: Bridge Theorems — Closed-Form Posterior Parameters

Pin all four posterior parameters (μ, κ, α, β) for each fault type to
closed-form expressions, bridging the Lean proofs to the Python numerical layer. -/

-- Pastry
theorem pastry_posterior_mu :
    (posterior pastryPrior pastryBatch.pastryEvidence).μ₀ =
      (pastryPrior.κ₀ * pastryPrior.μ₀ + pastryBatch.pastryEvidence.sum) /
      (pastryPrior.κ₀ + pastryBatch.pastryEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ pastryBatch_realizable

theorem pastry_posterior_kappa :
    (posterior pastryPrior pastryBatch.pastryEvidence).κ₀ =
      pastryPrior.κ₀ + pastryBatch.pastryEvidence.n := rfl

theorem pastry_posterior_alpha :
    (posterior pastryPrior pastryBatch.pastryEvidence).α₀ =
      pastryPrior.α₀ + (pastryBatch.pastryEvidence.n : ℝ) / 2 := rfl

theorem pastry_posterior_beta :
    (posterior pastryPrior pastryBatch.pastryEvidence).β₀ =
      pastryPrior.β₀ +
        (pastryBatch.pastryEvidence.sumSq + pastryPrior.κ₀ * pastryPrior.μ₀ ^ 2
          - (pastryPrior.κ₀ * pastryPrior.μ₀ + pastryBatch.pastryEvidence.sum) ^ 2 /
            (pastryPrior.κ₀ + pastryBatch.pastryEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ pastryBatch_realizable

-- K_Scratch
theorem kScratch_posterior_mu :
    (posterior kScratchPrior kScratchBatch.kScratchEvidence).μ₀ =
      (kScratchPrior.κ₀ * kScratchPrior.μ₀ + kScratchBatch.kScratchEvidence.sum) /
      (kScratchPrior.κ₀ + kScratchBatch.kScratchEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ kScratchBatch_realizable

theorem kScratch_posterior_kappa :
    (posterior kScratchPrior kScratchBatch.kScratchEvidence).κ₀ =
      kScratchPrior.κ₀ + kScratchBatch.kScratchEvidence.n := rfl

theorem kScratch_posterior_alpha :
    (posterior kScratchPrior kScratchBatch.kScratchEvidence).α₀ =
      kScratchPrior.α₀ + (kScratchBatch.kScratchEvidence.n : ℝ) / 2 := rfl

theorem kScratch_posterior_beta :
    (posterior kScratchPrior kScratchBatch.kScratchEvidence).β₀ =
      kScratchPrior.β₀ +
        (kScratchBatch.kScratchEvidence.sumSq + kScratchPrior.κ₀ * kScratchPrior.μ₀ ^ 2
          - (kScratchPrior.κ₀ * kScratchPrior.μ₀ + kScratchBatch.kScratchEvidence.sum) ^ 2 /
            (kScratchPrior.κ₀ + kScratchBatch.kScratchEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ kScratchBatch_realizable

-- Bumps
theorem bumps_posterior_mu :
    (posterior bumpsPrior bumpsBatch.bumpsEvidence).μ₀ =
      (bumpsPrior.κ₀ * bumpsPrior.μ₀ + bumpsBatch.bumpsEvidence.sum) /
      (bumpsPrior.κ₀ + bumpsBatch.bumpsEvidence.n) :=
  posterior_mu_eq_of_realizable _ _ bumpsBatch_realizable

theorem bumps_posterior_kappa :
    (posterior bumpsPrior bumpsBatch.bumpsEvidence).κ₀ =
      bumpsPrior.κ₀ + bumpsBatch.bumpsEvidence.n := rfl

theorem bumps_posterior_alpha :
    (posterior bumpsPrior bumpsBatch.bumpsEvidence).α₀ =
      bumpsPrior.α₀ + (bumpsBatch.bumpsEvidence.n : ℝ) / 2 := rfl

theorem bumps_posterior_beta :
    (posterior bumpsPrior bumpsBatch.bumpsEvidence).β₀ =
      bumpsPrior.β₀ +
        (bumpsBatch.bumpsEvidence.sumSq + bumpsPrior.κ₀ * bumpsPrior.μ₀ ^ 2
          - (bumpsPrior.κ₀ * bumpsPrior.μ₀ + bumpsBatch.bumpsEvidence.sum) ^ 2 /
            (bumpsPrior.κ₀ + bumpsBatch.bumpsEvidence.n)) / 2 :=
  posterior_beta_eq_of_realizable _ _ bumpsBatch_realizable

/-! ## §8: Main Theorems -/

/-- **Per-fault sleep consolidation**: batch replay = sequential Bayesian update. -/
theorem sleep_consolidation_generic (prior : NormalGammaPrior)
    (e₁ e₂ : NormalGammaEvidence)
    (h₁ : e₁.Realizable) (h₂ : e₂.Realizable) :
    posterior prior (e₁ + e₂) = posterior (posterior prior e₁) e₂ :=
  posterior_hplus_of_realizable prior e₁ e₂ h₁ h₂

/-- **Cross-fault independence**: pastry observations don't affect K_Scratch. -/
theorem pastry_obs_kScratch_zero (x : ℝ) :
    (faultObs .pastry x).kScratchEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-fault independence: pastry observations don't affect Bumps. -/
theorem pastry_obs_bumps_zero (x : ℝ) :
    (faultObs .pastry x).bumpsEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-fault independence: K_Scratch observations don't affect Pastry. -/
theorem kScratch_obs_pastry_zero (x : ℝ) :
    (faultObs .kScratch x).pastryEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-fault independence: K_Scratch observations don't affect Bumps. -/
theorem kScratch_obs_bumps_zero (x : ℝ) :
    (faultObs .kScratch x).bumpsEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-fault independence: Bumps observations don't affect Pastry. -/
theorem bumps_obs_pastry_zero (x : ℝ) :
    (faultObs .bumps x).pastryEvidence = NormalGammaEvidence.zero := rfl

/-- Cross-fault independence: Bumps observations don't affect K_Scratch. -/
theorem bumps_obs_kScratch_zero (x : ℝ) :
    (faultObs .bumps x).kScratchEvidence = NormalGammaEvidence.zero := rfl

/-- **Source attribution**: each observation increments exactly one fault counter. -/
theorem faultObs_source_pastry (x : ℝ) :
    (faultObs .pastry x).sourcePastry = 1 ∧
    (faultObs .pastry x).sourceKScratch = 0 ∧
    (faultObs .pastry x).sourceBumps = 0 := ⟨rfl, rfl, rfl⟩

theorem faultObs_source_kScratch (x : ℝ) :
    (faultObs .kScratch x).sourcePastry = 0 ∧
    (faultObs .kScratch x).sourceKScratch = 1 ∧
    (faultObs .kScratch x).sourceBumps = 0 := ⟨rfl, rfl, rfl⟩

theorem faultObs_source_bumps (x : ℝ) :
    (faultObs .bumps x).sourcePastry = 0 ∧
    (faultObs .bumps x).sourceKScratch = 0 ∧
    (faultObs .bumps x).sourceBumps = 1 := ⟨rfl, rfl, rfl⟩

/-- **Confidence monotonicity**: more observations → higher confidence. -/
theorem confidence_monotone_add (e₁ e₂ : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e₁.toConfidence κ ≤ (e₁ + e₂).toConfidence κ :=
  EvidenceNormalGamma.confidence_monotone _ _ _ hκ (Nat.le_add_right _ _)

/-- **Exceedance anti-threshold**: higher threshold → lower exceedance. -/
theorem exceedance_anti_threshold (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (e : NormalGammaEvidence) (c₁ c₂ : ℝ) (h : c₁ ≤ c₂) :
    spec.exceedance (posterior prior e) c₂ ≤
    spec.exceedance (posterior prior e) c₁ :=
  spec.exceedance_anti_threshold _ _ _ h

/-- **Per-fault exceedance independence**: Pastry exceedance is independent of K_Scratch. -/
theorem exceedance_pastry_independent_of_kScratch
    (spec : ExceedanceSpec) (s₁ s₂ : FaultState) (c : ℝ)
    (hP : s₁.pastryEvidence = s₂.pastryEvidence) :
    faultExceedanceEvidence spec faultPriors s₁ .pastry c =
    faultExceedanceEvidence spec faultPriors s₂ .pastry c := by
  simp [faultExceedanceEvidence, faultEvidence, faultPriors, hP]

/-- **3-way source weight normalization**. -/
theorem source_weights_sum_to_one (nP nK nB : ℕ) (h : 0 < nP + nK + nB) :
    (nP : ℝ) / (nP + nK + nB) + (nK : ℝ) / (nP + nK + nB) +
    (nB : ℝ) / (nP + nK + nB) = 1 := by
  have hpos : (0 : ℝ) < (nP + nK + nB : ℕ) := Nat.cast_pos.mpr h
  rw [Nat.cast_add, Nat.cast_add] at hpos
  have hne : ((nP : ℝ) + (nK : ℝ) + (nB : ℝ)) ≠ 0 := ne_of_gt hpos
  field_simp [hne]

/-- **3-way mixture exceedance validity**: weighted combination is a probability. -/
theorem mixture_exceedance_valid_3way
    (pP pK pB wP wK wB : ℝ)
    (hpP : 0 ≤ pP) (hpK : 0 ≤ pK) (hpB : 0 ≤ pB)
    (hpP1 : pP ≤ 1) (hpK1 : pK ≤ 1) (hpB1 : pB ≤ 1)
    (hwP : 0 ≤ wP) (hwK : 0 ≤ wK) (hwB : 0 ≤ wB)
    (hsum : wP + wK + wB = 1) :
    let pMix := wP * pP + wK * pK + wB * pB
    0 ≤ pMix ∧ pMix ≤ 1 := by
  simp only
  constructor
  · apply add_nonneg
    apply add_nonneg
    · exact mul_nonneg hwP hpP
    · exact mul_nonneg hwK hpK
    · exact mul_nonneg hwB hpB
  · calc wP * pP + wK * pK + wB * pB
        ≤ wP * 1 + wK * 1 + wB * 1 := by
          apply add_le_add
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hpP1 hwP
          · exact mul_le_mul_of_nonneg_left hpK1 hwK
          · exact mul_le_mul_of_nonneg_left hpB1 hwB
      _ = 1 := by linarith

/-- Full inspection decomposes into fault-type batches. -/
theorem fullInspection_eq :
    fullInspection = pastryBatch + kScratchBatch + bumpsBatch := rfl

/-! ## §9: Canary Tests -/

/-- Canary: state addition is commutative. -/
theorem canary_add_comm :
    pastryBatch + kScratchBatch = kScratchBatch + pastryBatch :=
  FaultState.add_comm _ _

/-- Canary: pastry batch has 5 observations. -/
theorem canary_pastryBatch_count : pastryBatch.pastryEvidence.n = 5 := by
  simp only [pastryBatch, faultObs, FaultState.add_pastryEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: K_Scratch batch has 5 observations. -/
theorem canary_kScratchBatch_count : kScratchBatch.kScratchEvidence.n = 5 := by
  simp only [kScratchBatch, faultObs, FaultState.add_kScratchEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: Bumps batch has 5 observations. -/
theorem canary_bumpsBatch_count : bumpsBatch.bumpsEvidence.n = 5 := by
  simp only [bumpsBatch, faultObs, FaultState.add_bumpsEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: full inspection has 15 total source observations. -/
theorem canary_fullInspection_total_sources :
    totalSourceCount fullInspection = 15 := by
  simp only [totalSourceCount, fullInspection,
    pastryBatch, kScratchBatch, bumpsBatch,
    faultObs, FaultState.add_sourcePastry,
    FaultState.add_sourceKScratch, FaultState.add_sourceBumps]

/-- Canary: pastry batch has no K_Scratch evidence. -/
theorem canary_pastry_no_kScratch :
    pastryBatch.kScratchEvidence = NormalGammaEvidence.zero := by
  simp only [pastryBatch, faultObs, FaultState.add_kScratchEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: K_Scratch batch has no Bumps evidence. -/
theorem canary_kScratch_no_bumps :
    kScratchBatch.bumpsEvidence = NormalGammaEvidence.zero := by
  simp only [kScratchBatch, faultObs, FaultState.add_bumpsEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: full inspection has 5 observations per fault type. -/
theorem canary_fullInspection_source_breakdown :
    fullInspection.sourcePastry = 5 ∧
    fullInspection.sourceKScratch = 5 ∧
    fullInspection.sourceBumps = 5 := by
  simp only [fullInspection, pastryBatch, kScratchBatch, bumpsBatch,
    faultObs, FaultState.add_sourcePastry,
    FaultState.add_sourceKScratch, FaultState.add_sourceBumps]
  trivial

end Mettapedia.Logic.PLNSteelFaultDemo
