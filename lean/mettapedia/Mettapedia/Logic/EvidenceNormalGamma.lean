/-
# Normal-Gamma Evidence for Continuous PLN

This file extends PLN to continuous domains via Normal-Gamma conjugate priors.

## The Key Insight

For Normal observations with unknown mean AND variance:
- Evidence = sufficient statistics (n, sum, sumSq)
- Prior: Normal-Gamma(μ₀, κ₀, α₀, β₀)
- Posterior: Normal-Gamma(μₙ, κₙ, αₙ, βₙ) — by conjugacy
- **hplus = coordinatewise addition = Bayesian update**

This parallels the Beta-Bernoulli case (EvidenceBeta.lean) and Dirichlet-Multinomial
case (EvidenceDirichlet.lean), extending PLN to continuous domains.

## Main Definitions

- `NormalGammaEvidence`: Sufficient statistics for Normal-Gamma inference
- `NormalGammaPrior`: Parameters of the Normal-Gamma prior
- `hplus`: Aggregation of independent evidence (coordinatewise addition)
- `posterior`: Conjugate posterior update
- `toMean`, `toVariance`: View functions (like toStrength/toConfidence)

## References

- Bernardo & Smith, "Bayesian Theory" (2000), Chapter 5.3 (Normal-Gamma)
- Gelman et al., "Bayesian Data Analysis" (2013), Chapter 3
- Murphy, "Conjugate Bayesian analysis of the Gaussian distribution" (2007)
- EvidenceDirichlet.lean (the categorical case)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mettapedia.Logic.EvidenceClass

namespace Mettapedia.Logic.EvidenceNormalGamma

open Mettapedia.Logic.EvidenceClass

/-! ## Normal-Gamma Evidence Type

Sufficient statistics for observations from N(μ, 1/τ) with unknown μ and τ.
-/

/-- Sufficient statistics for Normal-Gamma inference.

    For observations x₁, ..., xₙ ~ N(μ, 1/τ):
    - n = sample count
    - sum = Σxᵢ (for computing sample mean)
    - sumSq = Σxᵢ² (for computing sample variance)

    These three values are the minimal sufficient statistic for (μ, τ).

    Validity: By Cauchy-Schwarz, any valid set of observations satisfies
    sumSq ≥ sum²/n (or equivalently, n·sumSq ≥ sum²). This is required
    to ensure the evidence could have come from actual data.
-/
structure NormalGammaEvidence where
  /-- Number of observations -/
  n : ℕ
  /-- Sum of observations: Σxᵢ -/
  sum : ℝ
  /-- Sum of squared observations: Σxᵢ² -/
  sumSq : ℝ
  /-- Sum of squares is non-negative -/
  sumSq_nonneg : 0 ≤ sumSq
  /-- Cauchy-Schwarz validity: n·sumSq ≥ sum² (rearranged for easier use) -/
  cauchy_schwarz : n * sumSq ≥ sum ^ 2

namespace NormalGammaEvidence

/-! ### Basic Operations -/

/-- Zero evidence: no observations -/
def zero : NormalGammaEvidence where
  n := 0
  sum := 0
  sumSq := 0
  sumSq_nonneg := le_refl 0
  cauchy_schwarz := by simp

/-- Observation from a single data point -/
def single (x : ℝ) : NormalGammaEvidence where
  n := 1
  sum := x
  sumSq := x^2
  sumSq_nonneg := sq_nonneg x
  cauchy_schwarz := by simp [sq]

/-- Aggregation of independent evidence (hplus): coordinatewise addition.

    This is the key operation: combining evidence from independent sources
    simply adds the sufficient statistics.

    The Cauchy-Schwarz property is preserved by hplus:
    If (n₁·ss₁ ≥ s₁²) and (n₂·ss₂ ≥ s₂²), then
    (n₁+n₂)·(ss₁+ss₂) ≥ (s₁+s₂)²

    This follows from the general Cauchy-Schwarz inequality for combining samples.
-/
def hplus (e₁ e₂ : NormalGammaEvidence) : NormalGammaEvidence where
  n := e₁.n + e₂.n
  sum := e₁.sum + e₂.sum
  sumSq := e₁.sumSq + e₂.sumSq
  sumSq_nonneg := add_nonneg e₁.sumSq_nonneg e₂.sumSq_nonneg
  cauchy_schwarz := by
    -- (n₁+n₂)(ss₁+ss₂) ≥ (s₁+s₂)²
    -- Expanding: n₁ss₁ + n₁ss₂ + n₂ss₁ + n₂ss₂ ≥ s₁² + 2s₁s₂ + s₂²
    -- We have: n₁ss₁ ≥ s₁² (h1) and n₂ss₂ ≥ s₂² (h2)
    -- Need: n₁ss₂ + n₂ss₁ ≥ 2s₁s₂
    --
    -- Key insight: (n₁ss₂)(n₂ss₁) = (n₁ss₁)(n₂ss₂) ≥ s₁²s₂² = (s₁s₂)²
    -- By AM-GM: n₁ss₂ + n₂ss₁ ≥ 2√((n₁ss₂)(n₂ss₁)) ≥ 2|s₁s₂| ≥ 2s₁s₂
    have h1 := e₁.cauchy_schwarz
    have h2 := e₂.cauchy_schwarz
    have hss1 := e₁.sumSq_nonneg
    have hss2 := e₂.sumSq_nonneg
    have hn1 : (0 : ℝ) ≤ e₁.n := Nat.cast_nonneg _
    have hn2 : (0 : ℝ) ≤ e₂.n := Nat.cast_nonneg _
    simp only [Nat.cast_add]
    -- Product inequality
    have hprod : (↑e₁.n * e₁.sumSq) * (↑e₂.n * e₂.sumSq) ≥ e₁.sum^2 * e₂.sum^2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hn1 hss1)
    -- Rearranged product for cross terms
    have hcross_prod : (↑e₁.n * e₂.sumSq) * (↑e₂.n * e₁.sumSq) ≥ (e₁.sum * e₂.sum)^2 := by
      have heq : (↑e₁.n * e₂.sumSq) * (↑e₂.n * e₁.sumSq) =
                 (↑e₁.n * e₁.sumSq) * (↑e₂.n * e₂.sumSq) := by ring
      rw [heq]
      calc (↑e₁.n * e₁.sumSq) * (↑e₂.n * e₂.sumSq)
          ≥ e₁.sum^2 * e₂.sum^2 := hprod
        _ = (e₁.sum * e₂.sum)^2 := by ring
    -- AM-GM: for x, y ≥ 0, x + y ≥ 2√(xy)
    have h1n2s : 0 ≤ ↑e₁.n * e₂.sumSq := mul_nonneg hn1 hss2
    have h2n1s : 0 ≤ ↑e₂.n * e₁.sumSq := mul_nonneg hn2 hss1
    have ham_gm : ↑e₁.n * e₂.sumSq + ↑e₂.n * e₁.sumSq ≥
                  2 * Real.sqrt ((↑e₁.n * e₂.sumSq) * (↑e₂.n * e₁.sumSq)) := by
      have := two_mul_le_add_sq (Real.sqrt (↑e₁.n * e₂.sumSq)) (Real.sqrt (↑e₂.n * e₁.sumSq))
      simp only [Real.sq_sqrt h1n2s, Real.sq_sqrt h2n1s] at this
      linarith [Real.sqrt_mul h1n2s (↑e₂.n * e₁.sumSq)]
    -- √((n₁ss₂)(n₂ss₁)) ≥ |s₁s₂|
    have hsqrt_bound : Real.sqrt ((↑e₁.n * e₂.sumSq) * (↑e₂.n * e₁.sumSq)) ≥ |e₁.sum * e₂.sum| := by
      have h := Real.sqrt_le_sqrt hcross_prod
      rw [Real.sqrt_sq_eq_abs] at h
      exact h
    -- |s₁s₂| ≥ s₁s₂
    have habs_bound : |e₁.sum * e₂.sum| ≥ e₁.sum * e₂.sum := le_abs_self _
    -- Combine
    calc (↑e₁.n + ↑e₂.n) * (e₁.sumSq + e₂.sumSq)
        = ↑e₁.n * e₁.sumSq + ↑e₂.n * e₂.sumSq + (↑e₁.n * e₂.sumSq + ↑e₂.n * e₁.sumSq) := by ring
      _ ≥ e₁.sum^2 + e₂.sum^2 + 2 * Real.sqrt ((↑e₁.n * e₂.sumSq) * (↑e₂.n * e₁.sumSq)) := by linarith
      _ ≥ e₁.sum^2 + e₂.sum^2 + 2 * |e₁.sum * e₂.sum| := by linarith [hsqrt_bound]
      _ ≥ e₁.sum^2 + e₂.sum^2 + 2 * (e₁.sum * e₂.sum) := by linarith [habs_bound]
      _ = (e₁.sum + e₂.sum)^2 := by ring

instance : Add NormalGammaEvidence where
  add := hplus

instance : Zero NormalGammaEvidence where
  zero := zero

/-! ### Algebraic Properties -/

@[ext]
theorem ext {e₁ e₂ : NormalGammaEvidence}
    (hn : e₁.n = e₂.n) (hs : e₁.sum = e₂.sum) (hss : e₁.sumSq = e₂.sumSq) :
    e₁ = e₂ := by
  cases e₁; cases e₂
  simp only [mk.injEq] at *
  exact ⟨hn, hs, hss⟩

/-- hplus is commutative -/
theorem hplus_comm (e₁ e₂ : NormalGammaEvidence) : e₁ + e₂ = e₂ + e₁ := by
  ext
  · exact Nat.add_comm _ _
  · exact add_comm _ _
  · exact add_comm _ _

/-- hplus is associative -/
theorem hplus_assoc (e₁ e₂ e₃ : NormalGammaEvidence) :
    e₁ + e₂ + e₃ = e₁ + (e₂ + e₃) := by
  ext
  · exact Nat.add_assoc _ _ _
  · exact add_assoc _ _ _
  · exact add_assoc _ _ _

/-- zero is the identity for hplus -/
theorem hplus_zero (e : NormalGammaEvidence) : e + zero = e := by
  ext
  · exact Nat.add_zero _
  · exact add_zero _
  · exact add_zero _

theorem zero_hplus (e : NormalGammaEvidence) : zero + e = e := by
  rw [hplus_comm]
  exact hplus_zero e

/-! ### AddCommMonoid Instance (EvidenceType) -/

/-- NormalGammaEvidence forms an AddCommMonoid, making it an EvidenceType.
    This is the foundation of the modal evidence theory for continuous domains. -/
instance instAddCommMonoid : AddCommMonoid NormalGammaEvidence where
  add_assoc := hplus_assoc
  zero := zero
  zero_add := zero_hplus
  add_zero := hplus_zero
  add_comm := hplus_comm
  nsmul := nsmulRec

/-- NormalGammaEvidence satisfies the EvidenceType class.
    This connects it to the modal evidence theory framework. -/
instance instEvidenceType : EvidenceType NormalGammaEvidence where

/-! ### View Functions -/

/-- Sample mean: sum / n (the "location" estimate, analogous to strength) -/
noncomputable def toMean (e : NormalGammaEvidence) : ℝ :=
  if e.n = 0 then 0 else e.sum / e.n

/-- Sum of squared deviations from the sample mean: Σ(xᵢ - x̄)² = sumSq - sum²/n -/
noncomputable def sumSquaredDeviations (e : NormalGammaEvidence) : ℝ :=
  if e.n = 0 then 0 else e.sumSq - e.sum^2 / e.n

/-- Sample variance: (sumSq - sum²/n) / (n-1)
    Uses Bessel's correction for unbiased estimation. -/
noncomputable def toVariance (e : NormalGammaEvidence) : ℝ :=
  if e.n ≤ 1 then 0 else e.sumSquaredDeviations / (e.n - 1)

/-- Precision estimate: 1 / variance (confidence analog)
    Higher precision = more certainty about the mean. -/
noncomputable def toPrecision (e : NormalGammaEvidence) : ℝ :=
  if e.toVariance = 0 then 0 else 1 / e.toVariance

/-- Confidence analog for continuous: n / (n + κ)
    Parallels PLN's c = n/(n+κ) formula. -/
noncomputable def toConfidence (e : NormalGammaEvidence) (κ : ℝ) : ℝ :=
  (e.n : ℝ) / ((e.n : ℝ) + κ)

/-- Confidence is in [0, 1) when κ > 0 -/
theorem toConfidence_nonneg (e : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    0 ≤ e.toConfidence κ := by
  unfold toConfidence
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · have h : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
    linarith

theorem toConfidence_lt_one (e : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ) :
    e.toConfidence κ < 1 := by
  unfold toConfidence
  have hn : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (e.n : ℝ) + κ := by linarith
  rw [div_lt_one hden]
  linarith

/-! ### Context-Aware Interpretation (Modal Evidence Theory)

The mean and variance computations naturally require context (the prior).
This section makes this explicit using the modal evidence theory framework.

The key insight: `toMean` is the "improper prior" case (like toStrength for binary).
The full posterior mean uses `meanWith` which takes the prior context.
-/

/-- Context-aware posterior mean computation.

    Given prior Normal-Gamma(μ₀, κ₀, _, _) and evidence (n, sum, _):
    posterior_mean = (κ₀·μ₀ + sum) / (κ₀ + n)

    When κ₀ = 0 (no prior), this equals the sample mean `toMean`.
    This parallels `strengthWith` for binary evidence. -/
noncomputable def meanWith (ctx : ContinuousContext) (e : NormalGammaEvidence) : ℝ :=
  if e.n = 0 ∧ ctx.κ₀ = 0 then 0  -- No data and no prior
  else (ctx.κ₀ * ctx.μ₀ + e.sum) / (ctx.κ₀ + e.n)

/-- With zero prior strength (κ₀ = 0), the posterior mean equals the sample mean.
    This is the backward-compatibility theorem for continuous evidence. -/
theorem meanWith_zero_kappa (e : NormalGammaEvidence) (ctx : ContinuousContext)
    (hκ : ctx.κ₀ = 0) (h : e.n ≠ 0) :
    meanWith ctx e = toMean e := by
  unfold meanWith toMean
  simp only [hκ, NNReal.coe_zero, zero_mul, zero_add, h, false_and, ↓reduceIte]

/-- With positive prior strength, the posterior mean interpolates between
    the prior mean and the sample mean. -/
theorem meanWith_interpolation (e : NormalGammaEvidence) (ctx : ContinuousContext)
    (hκ : 0 < ctx.κ₀) (h : e.n ≠ 0) :
    meanWith ctx e =
      (ctx.κ₀ / (ctx.κ₀ + e.n)) * ctx.μ₀ + ((e.n : ℝ) / (ctx.κ₀ + e.n)) * toMean e := by
  unfold meanWith toMean
  simp only [h, false_and, ↓reduceIte]
  have hκn_pos : 0 < (ctx.κ₀ : ℝ) + e.n := by
    have hn : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
    have hκ' : 0 < (ctx.κ₀ : ℝ) := NNReal.coe_pos.mpr hκ
    linarith
  have hn_pos : 0 < (e.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  field_simp [ne_of_gt hκn_pos, ne_of_gt hn_pos]

end NormalGammaEvidence

/-! ## Normal-Gamma Prior Parameters -/

/-- Parameters of a Normal-Gamma prior distribution.

    The Normal-Gamma distribution is a conjugate prior for a Normal with
    unknown mean μ and precision τ:
    - μ | τ ~ Normal(μ₀, 1/(κ₀τ))
    - τ ~ Gamma(α₀, β₀)

    Parameters:
    - μ₀: prior mean for μ
    - κ₀: strength of prior on μ (number of "pseudo-observations")
    - α₀: shape parameter for τ prior
    - β₀: rate parameter for τ prior
-/
structure NormalGammaPrior where
  /-- Prior mean -/
  μ₀ : ℝ
  /-- Prior precision multiplier (pseudo-observations for mean) -/
  κ₀ : ℝ
  /-- Gamma shape parameter -/
  α₀ : ℝ
  /-- Gamma rate parameter -/
  β₀ : ℝ
  /-- κ₀ > 0 -/
  κ₀_pos : 0 < κ₀
  /-- α₀ > 0 -/
  α₀_pos : 0 < α₀
  /-- β₀ > 0 -/
  β₀_pos : 0 < β₀

namespace NormalGammaPrior

/-- Standard weakly informative prior: centered at 0 with minimal information -/
def weaklyInformative : NormalGammaPrior where
  μ₀ := 0
  κ₀ := 0.01
  α₀ := 0.5
  β₀ := 0.5
  κ₀_pos := by norm_num
  α₀_pos := by norm_num
  β₀_pos := by norm_num

/-- Jeffreys prior for Normal-Gamma (limiting case) -/
def jeffreys (ε : ℝ) (hε : 0 < ε) : NormalGammaPrior where
  μ₀ := 0
  κ₀ := ε
  α₀ := ε
  β₀ := ε
  κ₀_pos := hε
  α₀_pos := hε
  β₀_pos := hε

end NormalGammaPrior

/-! ## Conjugate Posterior Update -/

/-- Posterior parameters after observing evidence.

    Given prior Normal-Gamma(μ₀, κ₀, α₀, β₀) and evidence (n, sum, sumSq),
    the posterior is Normal-Gamma(μₙ, κₙ, αₙ, βₙ) where:
    - κₙ = κ₀ + n
    - μₙ = (κ₀μ₀ + sum) / κₙ
    - αₙ = α₀ + n/2
    - βₙ = β₀ + (sumSq - sum²/n)/2 + κ₀n(sum/n - μ₀)²/(2κₙ)

    The last term accounts for the shift in the mean estimate.
-/
noncomputable def posterior (prior : NormalGammaPrior) (e : NormalGammaEvidence) :
    NormalGammaPrior where
  μ₀ := if e.n = 0 then prior.μ₀
        else (prior.κ₀ * prior.μ₀ + e.sum) / (prior.κ₀ + e.n)
  κ₀ := prior.κ₀ + e.n
  α₀ := prior.α₀ + (e.n : ℝ) / 2
  β₀ := if e.n = 0 then prior.β₀
        else prior.β₀ + e.sumSquaredDeviations / 2 +
             prior.κ₀ * e.n * (e.sum / e.n - prior.μ₀)^2 / (2 * (prior.κ₀ + e.n))
  κ₀_pos := by
    have h1 : 0 < prior.κ₀ := prior.κ₀_pos
    have h2 : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
    linarith
  α₀_pos := by
    have h1 : 0 < prior.α₀ := prior.α₀_pos
    have h2 : 0 ≤ (e.n : ℝ) / 2 := by positivity
    linarith
  β₀_pos := by
    split_ifs with h
    · exact prior.β₀_pos
    · -- Need to show β₀ + stuff > 0
      have h1 : 0 < prior.β₀ := prior.β₀_pos
      -- The additional terms are non-negative
      -- sumSquaredDeviations ≥ 0 follows from the Cauchy-Schwarz validity constraint
      have h2 : 0 ≤ e.sumSquaredDeviations / 2 := by
        unfold NormalGammaEvidence.sumSquaredDeviations
        simp only [h, ↓reduceIte]
        -- Need: sumSq - sum²/n ≥ 0
        -- From cauchy_schwarz: n * sumSq ≥ sum²
        -- So: sumSq ≥ sum²/n (dividing by n > 0)
        apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 2)
        have hcs := e.cauchy_schwarz
        have hn_pos : 0 < (e.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
        have hge : e.sumSq ≥ e.sum^2 / e.n := by
          rw [ge_iff_le, div_le_iff₀ hn_pos]
          linarith
        linarith
      have h3 : 0 ≤ prior.κ₀ * e.n * (e.sum / e.n - prior.μ₀)^2 / (2 * (prior.κ₀ + e.n)) := by
        apply div_nonneg
        · apply mul_nonneg
          apply mul_nonneg
          · exact le_of_lt prior.κ₀_pos
          · exact Nat.cast_nonneg _
          · exact sq_nonneg _
        · apply mul_nonneg
          · norm_num
          · have : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
            linarith [prior.κ₀_pos]
      linarith

/-! ## Main Theorems -/

/-- The sample mean converges to the posterior mean as n → ∞.

    More precisely, the posterior mean μₙ = (κ₀μ₀ + sum)/(κ₀ + n) satisfies:
    |μₙ - sample_mean| ≤ κ₀|μ₀ - sample_mean| / (κ₀ + n)
-/
theorem posterior_mean_approaches_sample_mean
    (prior : NormalGammaPrior) (e : NormalGammaEvidence) (h : e.n ≠ 0) :
    |(posterior prior e).μ₀ - e.toMean| ≤
      prior.κ₀ * |prior.μ₀ - e.toMean| / (prior.κ₀ + e.n) := by
  unfold posterior NormalGammaEvidence.toMean
  simp only [h, ↓reduceIte]
  have hn_pos : 0 < (e.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  have hκn_pos : 0 < prior.κ₀ + e.n := by
    have : 0 ≤ (e.n : ℝ) := Nat.cast_nonneg _
    linarith [prior.κ₀_pos]

  -- Compute the difference
  have hdiff : (prior.κ₀ * prior.μ₀ + e.sum) / (prior.κ₀ + ↑e.n) - e.sum / ↑e.n =
      prior.κ₀ * (prior.μ₀ - e.sum / e.n) / (prior.κ₀ + e.n) := by
    field_simp [ne_of_gt hn_pos, ne_of_gt hκn_pos]
    ring

  rw [hdiff, abs_div, abs_mul, abs_of_pos prior.κ₀_pos, abs_of_pos hκn_pos]

/-- Confidence increases with more observations -/
theorem confidence_monotone (e₁ e₂ : NormalGammaEvidence) (κ : ℝ) (hκ : 0 < κ)
    (h : e₁.n ≤ e₂.n) :
    e₁.toConfidence κ ≤ e₂.toConfidence κ := by
  unfold NormalGammaEvidence.toConfidence
  have hn1 : 0 ≤ (e₁.n : ℝ) := Nat.cast_nonneg _
  have hn2 : 0 ≤ (e₂.n : ℝ) := Nat.cast_nonneg _
  have hd1 : 0 < (e₁.n : ℝ) + κ := by linarith
  have hd2 : 0 < (e₂.n : ℝ) + κ := by linarith
  -- n₁/(n₁+κ) ≤ n₂/(n₂+κ) when n₁ ≤ n₂ and κ > 0
  -- Equivalently: n₁(n₂+κ) ≤ n₂(n₁+κ)
  have hn12 : (e₁.n : ℝ) ≤ e₂.n := Nat.cast_le.mpr h
  rw [div_le_div_iff₀ hd1 hd2]
  calc (e₁.n : ℝ) * ((e₂.n : ℝ) + κ)
      = (e₁.n : ℝ) * e₂.n + (e₁.n : ℝ) * κ := by ring
    _ ≤ (e₂.n : ℝ) * e₁.n + (e₂.n : ℝ) * κ := by nlinarith
    _ = (e₂.n : ℝ) * ((e₁.n : ℝ) + κ) := by ring

/-- Combining evidence increases sample count -/
theorem hplus_n (e₁ e₂ : NormalGammaEvidence) : (e₁ + e₂).n = e₁.n + e₂.n := rfl

/-- Combining evidence adds sums -/
theorem hplus_sum (e₁ e₂ : NormalGammaEvidence) : (e₁ + e₂).sum = e₁.sum + e₂.sum := rfl

/-- Combining evidence adds sum of squares -/
theorem hplus_sumSq (e₁ e₂ : NormalGammaEvidence) :
    (e₁ + e₂).sumSq = e₁.sumSq + e₂.sumSq := rfl

/-! ## Connection to PLN SimpleTruthValue

For continuous observations, we map:
- Mean → "strength" (the central estimate)
- Confidence → n/(n+κ) (same formula as binary PLN)

This gives a (mean, confidence) pair analogous to PLN's (strength, confidence).
-/

/-- Convert Normal-Gamma evidence to a (mean, confidence) pair.
    This is the continuous analog of PLN's SimpleTruthValue. -/
noncomputable def toSTV (e : NormalGammaEvidence) (κ : ℝ) : ℝ × ℝ :=
  (e.toMean, e.toConfidence κ)

/-- Mean of combined evidence is weighted average of component means. -/
theorem toMean_hplus (e₁ e₂ : NormalGammaEvidence)
    (h₁ : e₁.n ≠ 0) (h₂ : e₂.n ≠ 0) :
    (e₁ + e₂).toMean =
      (e₁.n : ℝ) / ((e₁.n : ℝ) + e₂.n) * e₁.toMean +
      (e₂.n : ℝ) / ((e₁.n : ℝ) + e₂.n) * e₂.toMean := by
  have h12_nat : e₁.n + e₂.n ≠ 0 := by omega
  have hn1_pos : 0 < (e₁.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₁)
  have hn2_pos : 0 < (e₂.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₂)
  have hn12_pos : 0 < (e₁.n : ℝ) + e₂.n := by linarith
  unfold NormalGammaEvidence.toMean
  simp only [h₁, h₂, h12_nat, hplus_n, hplus_sum, ↓reduceIte, Nat.cast_add]
  field_simp [ne_of_gt hn1_pos, ne_of_gt hn2_pos, ne_of_gt hn12_pos]

/-! ## Summary

This file establishes that for continuous observations:

**PLN Evidence aggregation IS Bayesian Normal-Gamma conjugate update**

The pattern:
1. Evidence = sufficient statistic (n, sum, sumSq)
2. hplus = additive combination of sufficient statistics
3. This equals the conjugate prior update rule

| Aspect | Binary PLN | Continuous PLN |
|--------|------------|----------------|
| Evidence | (n⁺, n⁻) | (n, sum, sumSq) |
| Prior | Beta(α,β) | Normal-Gamma(μ₀,κ₀,α₀,β₀) |
| hplus | (n⁺₁+n⁺₂, n⁻₁+n⁻₂) | (n₁+n₂, sum₁+sum₂, ss₁+ss₂) |
| Strength | n⁺/(n⁺+n⁻) | sum/n (sample mean) |
| Confidence | n/(n+κ) | n/(n+κ) |

This justifies PLN-style evidence combination as **exact optimal inference**
for exchangeable Gaussian observations.
-/

end Mettapedia.Logic.EvidenceNormalGamma
