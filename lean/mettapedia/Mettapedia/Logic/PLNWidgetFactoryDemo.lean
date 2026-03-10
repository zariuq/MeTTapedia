/-
# Widget Factory Demo: Source-Conditional Gaussian Mixtures

The second applied example exercising continuous (Gaussian) world models in PLN.

## The Model

A factory with two machines (A, B). Each widget arrives with:
- An observed source label (which machine produced it)
- A real-valued feature measurement (e.g., diameter)

Each machine produces widgets whose features follow N(μᵢ, 1/τᵢ) with
unknown per-machine parameters. Normal-Gamma priors per source.

## Key Results

1. Per-machine sleep consolidation: batch replay = sequential Bayesian update
2. Source independence: machine A observations don't affect machine B's posterior
3. Mixture exceedance validity: convex combination of per-source exceedances is a probability
4. Mixture bounds: the mixture lies between the per-source exceedances
5. Confidence monotonicity per machine

## What's New vs BrokenSensorDemo

- Multiple Gaussian components (per-source) instead of one
- Source attribution evidence (which machine produced the widget)
- Mixture exceedance theorems (law of total probability)

0 sorry.
-/

import Mettapedia.Logic.EvidenceNormalGamma
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNBrokenSensorDemo

namespace Mettapedia.Logic.PLNWidgetFactoryDemo

open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNBrokenSensorDemo (ExceedanceSpec)

/-! ## §1: Machine Type -/

/-- The two machines in the factory. -/
inductive Machine where
  | A | B
  deriving DecidableEq, Inhabited

/-! ## §2: Factory State Type

The factory state is a product of per-machine Gaussian evidence
and source-attribution binary evidence. -/

/-- Factory state: per-machine Gaussian features + source attribution. -/
structure FactoryState where
  /-- Sufficient statistics for machine A's feature distribution -/
  machineAEvidence : NormalGammaEvidence
  /-- Sufficient statistics for machine B's feature distribution -/
  machineBEvidence : NormalGammaEvidence
  /-- Source attribution: pos = from A, neg = from B -/
  sourceEvidence : Evidence

namespace FactoryState

/-- Zero state: no observations from either machine. -/
def zero : FactoryState where
  machineAEvidence := NormalGammaEvidence.zero
  machineBEvidence := NormalGammaEvidence.zero
  sourceEvidence := Evidence.zero

/-- Componentwise addition (revision). -/
noncomputable def add (s₁ s₂ : FactoryState) : FactoryState where
  machineAEvidence := s₁.machineAEvidence + s₂.machineAEvidence
  machineBEvidence := s₁.machineBEvidence + s₂.machineBEvidence
  sourceEvidence := s₁.sourceEvidence + s₂.sourceEvidence

noncomputable instance : Add FactoryState where add := add
instance : Zero FactoryState where zero := zero

@[simp] theorem add_machineAEvidence (s₁ s₂ : FactoryState) :
    (s₁ + s₂).machineAEvidence = s₁.machineAEvidence + s₂.machineAEvidence := rfl
@[simp] theorem add_machineBEvidence (s₁ s₂ : FactoryState) :
    (s₁ + s₂).machineBEvidence = s₁.machineBEvidence + s₂.machineBEvidence := rfl
@[simp] theorem add_sourceEvidence (s₁ s₂ : FactoryState) :
    (s₁ + s₂).sourceEvidence = s₁.sourceEvidence + s₂.sourceEvidence := rfl

@[simp] theorem zero_machineAEvidence :
    (zero : FactoryState).machineAEvidence = NormalGammaEvidence.zero := rfl
@[simp] theorem zero_machineBEvidence :
    (zero : FactoryState).machineBEvidence = NormalGammaEvidence.zero := rfl
@[simp] theorem zero_sourceEvidence :
    (zero : FactoryState).sourceEvidence = Evidence.zero := rfl

@[ext]
theorem ext {s₁ s₂ : FactoryState}
    (hA : s₁.machineAEvidence = s₂.machineAEvidence)
    (hB : s₁.machineBEvidence = s₂.machineBEvidence)
    (hS : s₁.sourceEvidence = s₂.sourceEvidence) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp only [mk.injEq]; exact ⟨hA, hB, hS⟩

theorem add_comm (s₁ s₂ : FactoryState) : s₁ + s₂ = s₂ + s₁ := by
  apply ext
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact NormalGammaEvidence.hplus_comm _ _
  · exact Evidence.hplus_comm _ _

theorem add_assoc (s₁ s₂ s₃ : FactoryState) : s₁ + s₂ + s₃ = s₁ + (s₂ + s₃) := by
  apply ext
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact NormalGammaEvidence.hplus_assoc _ _ _
  · exact Evidence.hplus_assoc _ _ _

theorem zero_add (s : FactoryState) : zero + s = s := by
  apply ext
  · exact NormalGammaEvidence.zero_hplus _
  · exact NormalGammaEvidence.zero_hplus _
  · exact Evidence.zero_hplus _

theorem add_zero (s : FactoryState) : s + zero = s := by
  apply ext
  · exact NormalGammaEvidence.hplus_zero _
  · exact NormalGammaEvidence.hplus_zero _
  · exact Evidence.hplus_zero _

noncomputable instance instAddCommMonoid : AddCommMonoid FactoryState where
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

noncomputable instance instEvidenceType : EvidenceType FactoryState where

end FactoryState

/-! ## §3: Query Type and Evidence Extraction -/

/-- Queries against the factory state. -/
inductive FactoryQuery where
  /-- P(widget from machine m): source attribution -/
  | fromSource (m : Machine)
  /-- P(feature > c | machine m): per-source exceedance -/
  | exceedance (m : Machine) (c : ℝ)

/-- Extract source attribution evidence for a given machine.
    For machine A: pos = from_A count, neg = from_B count.
    For machine B: swapped. -/
def sourceQueryEvidence (s : FactoryState) (m : Machine) : Evidence :=
  match m with
  | .A => s.sourceEvidence
  | .B => ⟨s.sourceEvidence.neg, s.sourceEvidence.pos⟩

/-- Extract per-machine exceedance evidence.
    Computes posterior from the machine's Normal-Gamma evidence, then
    applies the exceedance spec to get P(feature > c). -/
noncomputable def machineExceedanceEvidence
    (spec : ExceedanceSpec) (priorA priorB : NormalGammaPrior)
    (s : FactoryState) (m : Machine) (c : ℝ) : Evidence :=
  let (ngEvid, prior) := match m with
    | .A => (s.machineAEvidence, priorA)
    | .B => (s.machineBEvidence, priorB)
  let post := posterior prior ngEvid
  let p := spec.exceedance post c
  let n := ngEvid.n
  ⟨ENNReal.ofReal (p * n), ENNReal.ofReal ((1 - p) * n)⟩

/-- Full evidence extraction for any factory query. -/
noncomputable def factoryEvidence
    (spec : ExceedanceSpec) (priorA priorB : NormalGammaPrior)
    (s : FactoryState) : FactoryQuery → Evidence
  | .fromSource m => sourceQueryEvidence s m
  | .exceedance m c => machineExceedanceEvidence spec priorA priorB s m c

/-! ## §4: Concrete Factory Data -/

/-- Prior for machine A: features expected around 10.0 -/
noncomputable def priorA : NormalGammaPrior where
  μ₀ := 10
  κ₀ := 1
  α₀ := 2
  β₀ := 5
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Prior for machine B: features expected around 10.5 -/
noncomputable def priorB : NormalGammaPrior where
  μ₀ := 10.5
  κ₀ := 1
  α₀ := 2
  β₀ := 5
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Defect threshold: feature above 12.0 indicates defect. -/
def defectThreshold : ℝ := 12

/-- Observation from machine A with feature value x. -/
noncomputable def machineAObs (x : ℝ) : FactoryState where
  machineAEvidence := NormalGammaEvidence.single x
  machineBEvidence := NormalGammaEvidence.zero
  sourceEvidence := ⟨1, 0⟩

/-- Observation from machine B with feature value x. -/
noncomputable def machineBObs (x : ℝ) : FactoryState where
  machineAEvidence := NormalGammaEvidence.zero
  machineBEvidence := NormalGammaEvidence.single x
  sourceEvidence := ⟨0, 1⟩

/-- Batch from machine A: 4 normal-range widgets. -/
noncomputable def batchA : FactoryState :=
  machineAObs 9.8 + machineAObs 10.2 + machineAObs 9.5 + machineAObs 10.1

/-- Batch from machine B: 3 slightly higher widgets. -/
noncomputable def batchB : FactoryState :=
  machineBObs 11.0 + machineBObs 10.8 + machineBObs 11.5

/-- Full production run: both batches combined. -/
noncomputable def fullProduction : FactoryState := batchA + batchB

/-! ## §5: Realizability Side Conditions -/

theorem single_realizable (x : ℝ) :
    (NormalGammaEvidence.single x).Realizable := by
  intro h; simp [NormalGammaEvidence.single] at h

theorem batchA_machineA_realizable : batchA.machineAEvidence.Realizable := by
  simp only [batchA, machineAObs, FactoryState.add_machineAEvidence]
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _

theorem batchB_machineB_realizable : batchB.machineBEvidence.Realizable := by
  simp only [batchB, machineBObs, FactoryState.add_machineBEvidence]
  apply NormalGammaEvidence.realizable_hplus
  apply NormalGammaEvidence.realizable_hplus
  · exact single_realizable _
  · exact single_realizable _
  · exact single_realizable _

/-! ## §6: Main Theorems -/

/-- **Per-machine sleep consolidation**: batch replay = sequential Bayesian update
    for machine A's feature distribution. -/
theorem sleep_consolidation_A (e₁ e₂ : NormalGammaEvidence)
    (h₁ : e₁.Realizable) (h₂ : e₂.Realizable) :
    posterior priorA (e₁ + e₂) = posterior (posterior priorA e₁) e₂ :=
  posterior_hplus_of_realizable priorA e₁ e₂ h₁ h₂

/-- Per-machine sleep consolidation for machine B. -/
theorem sleep_consolidation_B (e₁ e₂ : NormalGammaEvidence)
    (h₁ : e₁.Realizable) (h₂ : e₂.Realizable) :
    posterior priorB (e₁ + e₂) = posterior (posterior priorB e₁) e₂ :=
  posterior_hplus_of_realizable priorB e₁ e₂ h₁ h₂

/-- **Source independence**: machine A observations don't affect machine B's evidence. -/
theorem machineAObs_machineBEvidence_zero (x : ℝ) :
    (machineAObs x).machineBEvidence = NormalGammaEvidence.zero := rfl

/-- Source independence: machine B observations don't affect machine A's evidence. -/
theorem machineBObs_machineAEvidence_zero (x : ℝ) :
    (machineBObs x).machineAEvidence = NormalGammaEvidence.zero := rfl

/-- Machine A observations don't affect machine B's source count. -/
theorem machineAObs_sourceEvidence (x : ℝ) :
    (machineAObs x).sourceEvidence = ⟨1, 0⟩ := rfl

/-- Machine B observations don't affect machine A's source count. -/
theorem machineBObs_sourceEvidence (x : ℝ) :
    (machineBObs x).sourceEvidence = ⟨0, 1⟩ := rfl

/-- **Confidence monotonicity**: more observations from a machine → higher confidence. -/
theorem confidence_monotone_add (e₁ e₂ : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e₁.toConfidence κ ≤ (e₁ + e₂).toConfidence κ :=
  EvidenceNormalGamma.confidence_monotone _ _ _ hκ (Nat.le_add_right _ _)

/-- **Exceedance anti-threshold**: higher threshold → lower exceedance probability
    (per-machine, for any valid ExceedanceSpec). -/
theorem exceedance_anti_threshold (spec : ExceedanceSpec) (prior : NormalGammaPrior)
    (e : NormalGammaEvidence) (c₁ c₂ : ℝ) (h : c₁ ≤ c₂) :
    spec.exceedance (posterior prior e) c₂ ≤
    spec.exceedance (posterior prior e) c₁ :=
  spec.exceedance_anti_threshold _ _ _ h

/-- Per-machine exceedance evidence is independent of the other machine's observations. -/
theorem exceedance_A_independent_of_B (spec : ExceedanceSpec)
    (s₁ s₂ : FactoryState) (c : ℝ)
    (hA : s₁.machineAEvidence = s₂.machineAEvidence) :
    machineExceedanceEvidence spec priorA priorB s₁ .A c =
    machineExceedanceEvidence spec priorA priorB s₂ .A c := by
  simp [machineExceedanceEvidence, hA]

/-! ## §7: Mixture Exceedance Theorems

The key new contribution: the law of total probability for per-source
exceedance. These theorems work at ℝ to avoid ENNReal division issues. -/

/-- **Mixture exceedance validity**: a convex combination of exceedance
    probabilities is itself a valid probability. -/
theorem mixture_exceedance_valid
    (spec : ExceedanceSpec) (prior₁ prior₂ : NormalGammaPrior)
    (e₁ e₂ : NormalGammaEvidence) (c : ℝ)
    (wA wB : ℝ) (hwA : 0 ≤ wA) (hwB : 0 ≤ wB) (hsum : wA + wB = 1) :
    let pA := spec.exceedance (posterior prior₁ e₁) c
    let pB := spec.exceedance (posterior prior₂ e₂) c
    let pMix := wA * pA + wB * pB
    0 ≤ pMix ∧ pMix ≤ 1 := by
  simp only
  constructor
  · apply add_nonneg
    · exact mul_nonneg hwA (spec.exceedance_nonneg _ _)
    · exact mul_nonneg hwB (spec.exceedance_nonneg _ _)
  · calc wA * spec.exceedance (posterior prior₁ e₁) c +
         wB * spec.exceedance (posterior prior₂ e₂) c
        ≤ wA * 1 + wB * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (spec.exceedance_le_one _ _) hwA
          · exact mul_le_mul_of_nonneg_left (spec.exceedance_le_one _ _) hwB
      _ = 1 := by linarith

/-- **Mixture bounds**: the mixture exceedance probability lies between
    the per-source exceedances (it is a convex combination). -/
theorem mixture_between_components
    (pA pB wA wB : ℝ) (hwA : 0 ≤ wA) (hwB : 0 ≤ wB) (hsum : wA + wB = 1) :
    min pA pB ≤ wA * pA + wB * pB ∧ wA * pA + wB * pB ≤ max pA pB := by
  constructor
  · by_cases h : pA ≤ pB
    · calc min pA pB = pA := min_eq_left h
        _ = pA * (wA + wB) := by rw [hsum, mul_one]
        _ = wA * pA + wB * pA := by ring
        _ ≤ wA * pA + wB * pB := by linarith [mul_le_mul_of_nonneg_left h hwB]
    · push_neg at h
      calc min pA pB = pB := min_eq_right (le_of_lt h)
        _ = pB * (wA + wB) := by rw [hsum, mul_one]
        _ = wA * pB + wB * pB := by ring
        _ ≤ wA * pA + wB * pB := by linarith [mul_le_mul_of_nonneg_left (le_of_lt h) hwA]
  · by_cases h : pA ≤ pB
    · calc wA * pA + wB * pB
          ≤ wA * pB + wB * pB := by linarith [mul_le_mul_of_nonneg_left h hwA]
        _ = pB * (wA + wB) := by ring
        _ = pB := by rw [hsum, mul_one]
        _ = max pA pB := (max_eq_right h).symm
    · push_neg at h
      calc wA * pA + wB * pB
          ≤ wA * pA + wB * pA := by linarith [mul_le_mul_of_nonneg_left (le_of_lt h) hwB]
        _ = pA * (wA + wB) := by ring
        _ = pA := by rw [hsum, mul_one]
        _ = max pA pB := (max_eq_left (le_of_lt h)).symm

/-- **Source weight normalization**: observation counts yield valid weights. -/
theorem source_weights_sum_to_one (nA nB : ℕ) (h : 0 < nA + nB) :
    (nA : ℝ) / (nA + nB) + (nB : ℝ) / (nA + nB) = 1 := by
  have hpos : (0 : ℝ) < (nA + nB : ℕ) := Nat.cast_pos.mpr h
  rw [Nat.cast_add] at hpos
  field_simp [ne_of_gt hpos]

/-! ## §8: Hybrid State Properties -/

/-- Observation count for machine A increases with revision. -/
theorem machineA_obs_count_add (s₁ s₂ : FactoryState) :
    (s₁ + s₂).machineAEvidence.n = s₁.machineAEvidence.n + s₂.machineAEvidence.n := rfl

/-- Observation count for machine B increases with revision. -/
theorem machineB_obs_count_add (s₁ s₂ : FactoryState) :
    (s₁ + s₂).machineBEvidence.n = s₁.machineBEvidence.n + s₂.machineBEvidence.n := rfl

/-- Source evidence adds componentwise. -/
theorem source_evidence_add (s₁ s₂ : FactoryState) :
    (s₁ + s₂).sourceEvidence = s₁.sourceEvidence + s₂.sourceEvidence := rfl

/-! ## §9: Canary Tests -/

/-- Canary: factory state addition is commutative. -/
theorem canary_add_comm : batchA + batchB = batchB + batchA :=
  FactoryState.add_comm _ _

/-- Canary: batch A has 4 observations from machine A. -/
theorem canary_batchA_count : batchA.machineAEvidence.n = 4 := by
  simp only [batchA, machineAObs, FactoryState.add_machineAEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: batch B has 3 observations from machine B. -/
theorem canary_batchB_count : batchB.machineBEvidence.n = 3 := by
  simp only [batchB, machineBObs, FactoryState.add_machineBEvidence,
    hplus_n, NormalGammaEvidence.single]

/-- Canary: full production has 7 total source observations. -/
theorem canary_source_total :
    fullProduction.sourceEvidence.pos + fullProduction.sourceEvidence.neg = 7 := by
  simp only [fullProduction, batchA, batchB, machineAObs, machineBObs,
    FactoryState.add_sourceEvidence, Evidence.hplus_def]
  norm_num

/-- Canary: batch A has no machine B observations. -/
theorem canary_batchA_no_machineB :
    batchA.machineBEvidence = NormalGammaEvidence.zero := by
  simp only [batchA, machineAObs, FactoryState.add_machineBEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: batch B has no machine A observations. -/
theorem canary_batchB_no_machineA :
    batchB.machineAEvidence = NormalGammaEvidence.zero := by
  simp only [batchB, machineBObs, FactoryState.add_machineAEvidence]
  simp [NormalGammaEvidence.hplus_zero]

/-- Canary: 4 widgets from A, 3 from B. -/
theorem canary_source_counts :
    fullProduction.sourceEvidence.pos = 4 ∧
    fullProduction.sourceEvidence.neg = 3 := by
  simp only [fullProduction, batchA, batchB, machineAObs, machineBObs,
    FactoryState.add_sourceEvidence, Evidence.hplus_def]
  norm_num

end Mettapedia.Logic.PLNWidgetFactoryDemo
