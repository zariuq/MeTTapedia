import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Basic
import Mettapedia.Logic.ConjugateEvidenceSurface
import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.EvidenceNormalGamma

namespace Mettapedia.Logic.EvidenceWeightedNormalGamma

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface

abbrev DiscreteNormalGammaEvidence := Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence
abbrev NormalGammaPrior := Mettapedia.Logic.EvidenceNormalGamma.NormalGammaPrior

/-!
# Weighted Normal-Gamma BinaryEvidence

This file generalizes `EvidenceNormalGamma` from integer sample counts to
nonnegative real-valued effective sample weights.

The main use-case is soft assignment, e.g. Gaussian-mixture responsibilities,
where evidence contributes fractionally rather than as whole observations.

The additive carrier remains the same sufficient-statistics pattern:

- `weight` = effective sample size
- `sum` = weighted sum of observations
- `sumSq` = weighted sum of squared observations

Hard-labeled evidence embeds into the weighted carrier via `ofDiscrete`.
-/

/-- Weighted sufficient statistics for Normal-Gamma inference. -/
structure WeightedNormalGammaEvidence where
  /-- Effective sample size / total responsibility mass. -/
  weight : ℝ
  /-- Effective sample size is nonnegative. -/
  weight_nonneg : 0 ≤ weight
  /-- Weighted sum of observations. -/
  sum : ℝ
  /-- Weighted sum of squared observations. -/
  sumSq : ℝ
  /-- Weighted sum of squares is nonnegative. -/
  sumSq_nonneg : 0 ≤ sumSq
  /-- Weighted Cauchy-Schwarz validity: `weight * sumSq ≥ sum^2`. -/
  cauchy_schwarz : weight * sumSq ≥ sum ^ 2

namespace WeightedNormalGammaEvidence

/-! ## Basic Operations -/

/-- Zero weighted evidence. -/
def zero : WeightedNormalGammaEvidence where
  weight := 0
  weight_nonneg := le_rfl
  sum := 0
  sumSq := 0
  sumSq_nonneg := le_rfl
  cauchy_schwarz := by simp

/-- One observation with a nonnegative fractional weight. -/
def single (w : NNReal) (x : ℝ) : WeightedNormalGammaEvidence where
  weight := (w : ℝ)
  weight_nonneg := w.2
  sum := (w : ℝ) * x
  sumSq := (w : ℝ) * x ^ 2
  sumSq_nonneg := mul_nonneg w.2 (sq_nonneg x)
  cauchy_schwarz := by
    nlinarith [w.2, sq_nonneg x]

/-- Additive aggregation of weighted sufficient statistics. -/
def hplus (e₁ e₂ : WeightedNormalGammaEvidence) : WeightedNormalGammaEvidence where
  weight := e₁.weight + e₂.weight
  weight_nonneg := add_nonneg e₁.weight_nonneg e₂.weight_nonneg
  sum := e₁.sum + e₂.sum
  sumSq := e₁.sumSq + e₂.sumSq
  sumSq_nonneg := add_nonneg e₁.sumSq_nonneg e₂.sumSq_nonneg
  cauchy_schwarz := by
    have h1 := e₁.cauchy_schwarz
    have h2 := e₂.cauchy_schwarz
    have hw1 := e₁.weight_nonneg
    have hw2 := e₂.weight_nonneg
    have hss1 := e₁.sumSq_nonneg
    have hss2 := e₂.sumSq_nonneg
    have hprod :
        (e₁.weight * e₁.sumSq) * (e₂.weight * e₂.sumSq) ≥ e₁.sum ^ 2 * e₂.sum ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hw1 hss1)
    have hcross_prod :
        (e₁.weight * e₂.sumSq) * (e₂.weight * e₁.sumSq) ≥ (e₁.sum * e₂.sum) ^ 2 := by
      have heq :
          (e₁.weight * e₂.sumSq) * (e₂.weight * e₁.sumSq) =
            (e₁.weight * e₁.sumSq) * (e₂.weight * e₂.sumSq) := by ring
      rw [heq]
      calc
        (e₁.weight * e₁.sumSq) * (e₂.weight * e₂.sumSq) ≥ e₁.sum ^ 2 * e₂.sum ^ 2 := hprod
        _ = (e₁.sum * e₂.sum) ^ 2 := by ring
    have hws1 : 0 ≤ e₁.weight * e₂.sumSq := mul_nonneg hw1 hss2
    have hws2 : 0 ≤ e₂.weight * e₁.sumSq := mul_nonneg hw2 hss1
    have ham_gm :
        e₁.weight * e₂.sumSq + e₂.weight * e₁.sumSq ≥
          2 * Real.sqrt ((e₁.weight * e₂.sumSq) * (e₂.weight * e₁.sumSq)) := by
      have htwo := two_mul_le_add_sq (Real.sqrt (e₁.weight * e₂.sumSq))
        (Real.sqrt (e₂.weight * e₁.sumSq))
      simp only [Real.sq_sqrt hws1, Real.sq_sqrt hws2] at htwo
      linarith [Real.sqrt_mul hws1 (e₂.weight * e₁.sumSq)]
    have hsqrt_bound :
        Real.sqrt ((e₁.weight * e₂.sumSq) * (e₂.weight * e₁.sumSq)) ≥ |e₁.sum * e₂.sum| := by
      have h := Real.sqrt_le_sqrt hcross_prod
      rw [Real.sqrt_sq_eq_abs] at h
      exact h
    have habs_bound : |e₁.sum * e₂.sum| ≥ e₁.sum * e₂.sum := le_abs_self _
    calc
      (e₁.weight + e₂.weight) * (e₁.sumSq + e₂.sumSq)
          = e₁.weight * e₁.sumSq + e₂.weight * e₂.sumSq +
              (e₁.weight * e₂.sumSq + e₂.weight * e₁.sumSq) := by ring
      _ ≥ e₁.sum ^ 2 + e₂.sum ^ 2 +
            2 * Real.sqrt ((e₁.weight * e₂.sumSq) * (e₂.weight * e₁.sumSq)) := by
          linarith
      _ ≥ e₁.sum ^ 2 + e₂.sum ^ 2 + 2 * |e₁.sum * e₂.sum| := by
          linarith [hsqrt_bound]
      _ ≥ e₁.sum ^ 2 + e₂.sum ^ 2 + 2 * (e₁.sum * e₂.sum) := by
          linarith [habs_bound]
      _ = (e₁.sum + e₂.sum) ^ 2 := by ring

instance : Add WeightedNormalGammaEvidence where
  add := hplus

instance : Zero WeightedNormalGammaEvidence where
  zero := zero

@[ext]
theorem ext {e₁ e₂ : WeightedNormalGammaEvidence}
    (hw : e₁.weight = e₂.weight) (hs : e₁.sum = e₂.sum) (hss : e₁.sumSq = e₂.sumSq) :
    e₁ = e₂ := by
  cases e₁
  cases e₂
  simp only [WeightedNormalGammaEvidence.mk.injEq] at *
  exact ⟨hw, hs, hss⟩

theorem hplus_comm (e₁ e₂ : WeightedNormalGammaEvidence) : e₁ + e₂ = e₂ + e₁ := by
  ext
  · exact add_comm _ _
  · exact add_comm _ _
  · exact add_comm _ _

theorem hplus_assoc (e₁ e₂ e₃ : WeightedNormalGammaEvidence) :
    e₁ + e₂ + e₃ = e₁ + (e₂ + e₃) := by
  ext
  · exact add_assoc _ _ _
  · exact add_assoc _ _ _
  · exact add_assoc _ _ _

theorem hplus_zero (e : WeightedNormalGammaEvidence) : e + zero = e := by
  ext
  · exact add_zero _
  · exact add_zero _
  · exact add_zero _

theorem zero_hplus (e : WeightedNormalGammaEvidence) : zero + e = e := by
  rw [hplus_comm]
  exact hplus_zero e

theorem sum_eq_zero_of_weight_eq_zero (e : WeightedNormalGammaEvidence) (hw : e.weight = 0) :
    e.sum = 0 := by
  have hcs := e.cauchy_schwarz
  simp [hw] at hcs
  have hsq : e.sum ^ 2 = 0 := by
    nlinarith [sq_nonneg e.sum, hcs]
  exact sq_eq_zero_iff.mp hsq

/-- Realizability rules out spurious positive variance mass at zero weight. -/
def Realizable (e : WeightedNormalGammaEvidence) : Prop :=
  e.weight = 0 → e.sumSq = 0

theorem realizable_zero : Realizable zero := by
  intro _; rfl

theorem realizable_single (w : NNReal) (x : ℝ) : Realizable (single w x) := by
  intro hw
  simp [single] at hw
  simp [single, hw]

theorem realizable_hplus {e₁ e₂ : WeightedNormalGammaEvidence}
    (h₁ : Realizable e₁) (h₂ : Realizable e₂) :
    Realizable (e₁ + e₂) := by
  intro hsum
  have hw1 : e₁.weight = 0 := by
    have hw1_le : e₁.weight ≤ 0 := by
      nlinarith [e₂.weight_nonneg, show e₁.weight + e₂.weight = 0 from hsum]
    exact le_antisymm hw1_le e₁.weight_nonneg
  have hw2 : e₂.weight = 0 := by
    have hw2_le : e₂.weight ≤ 0 := by
      nlinarith [e₁.weight_nonneg, show e₁.weight + e₂.weight = 0 from hsum]
    exact le_antisymm hw2_le e₂.weight_nonneg
  change e₁.sumSq + e₂.sumSq = 0
  simp [h₁ hw1, h₂ hw2]

instance instAddCommMonoid : AddCommMonoid WeightedNormalGammaEvidence where
  add_assoc := hplus_assoc
  zero := zero
  zero_add := zero_hplus
  add_zero := hplus_zero
  add_comm := hplus_comm
  nsmul := nsmulRec

instance instEvidenceType : EvidenceType WeightedNormalGammaEvidence where

/-- Weighted Normal-Gamma evidence is conjugate evidence with total observation
mass given by the effective sample weight. -/
instance instConjugateEvidenceWeightedNormalGamma :
    ConjugateEvidence WeightedNormalGammaEvidence where
  observationCount e := ENNReal.ofReal e.weight
  observationCount_add e₁ e₂ := by
    simpa using ENNReal.ofReal_add e₁.weight_nonneg e₂.weight_nonneg
  observationCount_zero := by
    show ENNReal.ofReal WeightedNormalGammaEvidence.zero.weight = 0
    simp [WeightedNormalGammaEvidence.zero]

@[simp] theorem observationCount_eq_weight (e : WeightedNormalGammaEvidence) :
    ConjugateEvidence.observationCount e = ENNReal.ofReal e.weight := rfl

@[simp] theorem observationCount_single (w : NNReal) (x : ℝ) :
    ConjugateEvidence.observationCount (single w x) = (w : ENNReal) := by
  change ENNReal.ofReal (w : ℝ) = (w : ENNReal)
  simp

/-! ## View Functions -/

/-- Weighted mean. -/
noncomputable def toMean (e : WeightedNormalGammaEvidence) : ℝ :=
  if e.weight = 0 then 0 else e.sum / e.weight

/-- Weighted sum of squared deviations from the weighted mean. -/
noncomputable def sumSquaredDeviations (e : WeightedNormalGammaEvidence) : ℝ :=
  if e.weight = 0 then 0 else e.sumSq - e.sum ^ 2 / e.weight

theorem sumSquaredDeviations_nonneg (e : WeightedNormalGammaEvidence) :
    0 ≤ e.sumSquaredDeviations := by
  unfold sumSquaredDeviations
  by_cases hw : e.weight = 0
  · simp [hw]
  · simp [hw]
    have hw_pos : 0 < e.weight := by
      exact lt_of_le_of_ne e.weight_nonneg (Ne.symm hw)
    have hge : e.sumSq ≥ e.sum ^ 2 / e.weight := by
      rw [ge_iff_le, div_le_iff₀ hw_pos]
      linarith [e.cauchy_schwarz]
    linarith

/-- Confidence from effective sample size. -/
noncomputable def toConfidence (e : WeightedNormalGammaEvidence) (κ : ℝ) : ℝ :=
  e.weight / (e.weight + κ)

theorem toConfidence_nonneg (e : WeightedNormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    0 ≤ e.toConfidence κ := by
  unfold toConfidence
  apply div_nonneg
  · exact e.weight_nonneg
  · linarith [e.weight_nonneg, hκ]

theorem toConfidence_lt_one (e : WeightedNormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e.toConfidence κ < 1 := by
  unfold toConfidence
  have hden : 0 < e.weight + κ := by linarith [e.weight_nonneg, hκ]
  rw [div_lt_one hden]
  linarith

/-! ## Hard-Label Embedding -/

/-- Embed integer-count Normal-Gamma evidence into the weighted carrier. -/
def ofDiscrete (e : DiscreteNormalGammaEvidence) : WeightedNormalGammaEvidence where
  weight := e.n
  weight_nonneg := Nat.cast_nonneg _
  sum := e.sum
  sumSq := e.sumSq
  sumSq_nonneg := e.sumSq_nonneg
  cauchy_schwarz := e.cauchy_schwarz

@[simp] theorem observationCount_ofDiscrete (e : DiscreteNormalGammaEvidence) :
    ConjugateEvidence.observationCount (ofDiscrete e) = (e.n : ENNReal) := by
  change ENNReal.ofReal (e.n : ℝ) = (e.n : ENNReal)
  simp

@[simp] theorem ofDiscrete_weight (e : DiscreteNormalGammaEvidence) :
    (ofDiscrete e).weight = e.n := rfl

@[simp] theorem ofDiscrete_sum (e : DiscreteNormalGammaEvidence) :
    (ofDiscrete e).sum = e.sum := rfl

@[simp] theorem ofDiscrete_sumSq (e : DiscreteNormalGammaEvidence) :
    (ofDiscrete e).sumSq = e.sumSq := rfl

@[simp] theorem ofDiscrete_zero :
    ofDiscrete Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.zero = zero := by
  ext
  · simp [ofDiscrete, zero, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.zero]
  · simp [ofDiscrete, zero, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.zero]
  · simp [ofDiscrete, zero, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.zero]

@[simp] theorem ofDiscrete_single (x : ℝ) :
    ofDiscrete (Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.single x) = single (1 : NNReal) x := by
  ext
  · norm_num [ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.single, single]
  · norm_num [ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.single, single]
  · norm_num [ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.single, single]

@[simp] theorem single_zero (x : ℝ) :
    single (0 : NNReal) x = zero := by
  ext
  · norm_num [single, zero]
  · norm_num [single, zero]
  · norm_num [single, zero]

theorem ofDiscrete_hplus (e₁ e₂ : DiscreteNormalGammaEvidence) :
    ofDiscrete (e₁ + e₂) = ofDiscrete e₁ + ofDiscrete e₂ := by
  ext
  · change (((e₁.n + e₂.n : ℕ) : ℝ) = (e₁.n : ℝ) + (e₂.n : ℝ))
    exact Nat.cast_add _ _
  · change e₁.sum + e₂.sum = e₁.sum + e₂.sum
    rfl
  · change e₁.sumSq + e₂.sumSq = e₁.sumSq + e₂.sumSq
    rfl

theorem realizable_ofDiscrete (e : DiscreteNormalGammaEvidence)
    (h : Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.Realizable e) :
    Realizable (ofDiscrete e) := by
  intro hw
  have hn : e.n = 0 := by
    exact Nat.cast_eq_zero.mp hw
  simpa [ofDiscrete] using h hn

theorem toMean_ofDiscrete (e : DiscreteNormalGammaEvidence) :
    (ofDiscrete e).toMean =
      Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.toMean e := by
  unfold toMean Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.toMean
  by_cases hn : e.n = 0
  · simp [ofDiscrete, hn]
  · have hnr : (e.n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    simp [ofDiscrete, hn, hnr]

theorem sumSquaredDeviations_ofDiscrete (e : DiscreteNormalGammaEvidence) :
    (ofDiscrete e).sumSquaredDeviations =
      Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.sumSquaredDeviations e := by
  unfold sumSquaredDeviations
  unfold Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.sumSquaredDeviations
  by_cases hn : e.n = 0
  · simp [ofDiscrete, hn]
  · have hnr : (e.n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    simp [ofDiscrete, hn, hnr]

theorem toConfidence_ofDiscrete (e : DiscreteNormalGammaEvidence) (κ : ℝ) :
    (ofDiscrete e).toConfidence κ =
      Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.toConfidence e κ := by
  unfold toConfidence
  unfold Mettapedia.Logic.EvidenceNormalGamma.NormalGammaEvidence.toConfidence
  simp [ofDiscrete]

/-! ## Conjugate Posterior Update -/

/-- Weighted conjugate update for Normal-Gamma evidence. -/
noncomputable def posterior (prior : NormalGammaPrior) (e : WeightedNormalGammaEvidence) :
    NormalGammaPrior where
  μ₀ := if e.weight = 0 then prior.μ₀
        else (prior.κ₀ * prior.μ₀ + e.sum) / (prior.κ₀ + e.weight)
  κ₀ := prior.κ₀ + e.weight
  α₀ := prior.α₀ + e.weight / 2
  β₀ := if e.weight = 0 then prior.β₀
        else prior.β₀ + e.sumSquaredDeviations / 2 +
          prior.κ₀ * e.weight * (e.sum / e.weight - prior.μ₀) ^ 2 /
            (2 * (prior.κ₀ + e.weight))
  κ₀_pos := by
    linarith [prior.κ₀_pos, e.weight_nonneg]
  α₀_pos := by
    have h : 0 ≤ e.weight / 2 := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact div_nonneg e.weight_nonneg htwo
    linarith [prior.α₀_pos, h]
  β₀_pos := by
    split_ifs with hw
    · exact prior.β₀_pos
    · have h1 : 0 < prior.β₀ := prior.β₀_pos
      have h2 : 0 ≤ e.sumSquaredDeviations / 2 := by
        exact div_nonneg (sumSquaredDeviations_nonneg e) (by norm_num)
      have h3 :
          0 ≤ prior.κ₀ * e.weight * (e.sum / e.weight - prior.μ₀) ^ 2 /
                (2 * (prior.κ₀ + e.weight)) := by
        apply div_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · exact le_of_lt prior.κ₀_pos
            · exact e.weight_nonneg
          · exact sq_nonneg _
        · apply mul_nonneg
          · norm_num
          · linarith [prior.κ₀_pos, e.weight_nonneg]
      linarith

@[simp] theorem posterior_kappa (prior : NormalGammaPrior) (e : WeightedNormalGammaEvidence) :
    (posterior prior e).κ₀ = prior.κ₀ + e.weight := rfl

@[simp] theorem posterior_alpha (prior : NormalGammaPrior) (e : WeightedNormalGammaEvidence) :
    (posterior prior e).α₀ = prior.α₀ + e.weight / 2 := rfl

theorem posterior_ofDiscrete_eq (prior : NormalGammaPrior) (e : DiscreteNormalGammaEvidence) :
    posterior prior (ofDiscrete e) = Mettapedia.Logic.EvidenceNormalGamma.posterior prior e := by
  ext
  · by_cases hn : e.n = 0
    · simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior, hn]
    · have hnr : (e.n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior, hn, hnr]
  · simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior]
  · simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior]
  · by_cases hn : e.n = 0
    · simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior,
        hn]
    · have hnr : (e.n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      simp [posterior, ofDiscrete, Mettapedia.Logic.EvidenceNormalGamma.posterior, hn, hnr]
      exact sumSquaredDeviations_ofDiscrete e

theorem confidence_monotone (e₁ e₂ : WeightedNormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ)
    (h : e₁.weight ≤ e₂.weight) :
    e₁.toConfidence κ ≤ e₂.toConfidence κ := by
  unfold toConfidence
  have hd1 : 0 < e₁.weight + κ := by linarith [e₁.weight_nonneg, hκ]
  have hd2 : 0 < e₂.weight + κ := by linarith [e₂.weight_nonneg, hκ]
  rw [div_le_div_iff₀ hd1 hd2]
  calc
    e₁.weight * (e₂.weight + κ) = e₁.weight * e₂.weight + e₁.weight * κ := by ring
    _ ≤ e₂.weight * e₁.weight + e₂.weight * κ := by nlinarith
    _ = e₂.weight * (e₁.weight + κ) := by ring

@[simp] theorem hplus_weight (e₁ e₂ : WeightedNormalGammaEvidence) :
    (e₁ + e₂).weight = e₁.weight + e₂.weight := rfl

@[simp] theorem hplus_sum (e₁ e₂ : WeightedNormalGammaEvidence) :
    (e₁ + e₂).sum = e₁.sum + e₂.sum := rfl

@[simp] theorem hplus_sumSq (e₁ e₂ : WeightedNormalGammaEvidence) :
    (e₁ + e₂).sumSq = e₁.sumSq + e₂.sumSq := rfl

/-- The weighted mean of combined nonzero evidence is a weight-averaged mean. -/
theorem toMean_hplus (e₁ e₂ : WeightedNormalGammaEvidence)
    (h₁ : e₁.weight ≠ 0) (h₂ : e₂.weight ≠ 0) :
    (e₁ + e₂).toMean =
      e₁.weight / (e₁.weight + e₂.weight) * e₁.toMean +
      e₂.weight / (e₁.weight + e₂.weight) * e₂.toMean := by
  have h12 : e₁.weight + e₂.weight ≠ 0 := by
    intro hsum
    have hw1_le : e₁.weight ≤ 0 := by linarith [e₂.weight_nonneg, hsum]
    have hw1 : e₁.weight = 0 := le_antisymm hw1_le e₁.weight_nonneg
    exact h₁ hw1
  have hw1 : 0 < e₁.weight := lt_of_le_of_ne e₁.weight_nonneg (Ne.symm h₁)
  have hw2 : 0 < e₂.weight := lt_of_le_of_ne e₂.weight_nonneg (Ne.symm h₂)
  have hw12 : 0 < e₁.weight + e₂.weight := by linarith
  unfold toMean
  simp only [h₁, h₂, h12, hplus_weight, hplus_sum, ↓reduceIte]
  field_simp [ne_of_gt hw1, ne_of_gt hw2, ne_of_gt hw12]

end WeightedNormalGammaEvidence

end Mettapedia.Logic.EvidenceWeightedNormalGamma
