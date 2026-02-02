/-
# PLN Hierarchical Inference Rules

This file formalizes PLN inference rules for hierarchical models like N-schools.

## Key Insight: Shrinkage IS Revision

The Bayesian shrinkage estimator:
  θ̂ⱼ = (1 - Bⱼ)·yⱼ + Bⱼ·μ̂    where Bⱼ = σⱼ²/(σⱼ² + τ²)

is EXACTLY precision-weighted PLN revision:
  - Evidence from observation: weight ∝ 1/σⱼ² (observation precision)
  - Evidence from population: weight ∝ 1/τ² (population precision)

## Main Rules

1. **Precision-Weighted Revision**: Combine evidence with different precisions
2. **Induction (Pooling)**: Aggregate instances → population estimate
3. **Hierarchical Deduction**: Population → individual prior

## References

- Gelman et al., "Bayesian Data Analysis" (2013), Chapter 5 (hierarchical models)
- Rubin, "Estimation in Parallel Randomized Experiments" (1981) (8-schools)
- Goertzel et al., "PLN" (2009), Section 5.10 (revision rule)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace Mettapedia.Logic.PLNHierarchicalRules

/-! ## Precision-Weighted Revision

The core PLN rule for combining evidence from sources with different precisions.

For hierarchical models:
- Source 1: Population prior (μ̂, precision = 1/τ²)
- Source 2: Observation (yⱼ, precision = 1/σⱼ²)

The revision formula combines them by precision weighting.
-/

/-- Precision-weighted revision: the core shrinkage operation.

Given:
- prior: (μ, precision_prior)
- observation: (y, precision_obs)

Returns:
- posterior mean: θ̂ = (μ·precision_prior + y·precision_obs) / (precision_prior + precision_obs)
- posterior precision: precision_prior + precision_obs

This is the fundamental PLN revision rule for continuous data.
-/
noncomputable def precisionWeightedRevision
    (μ : ℝ) (precision_prior : ℝ)
    (y : ℝ) (precision_obs : ℝ) : ℝ × ℝ :=
  let precision_total := precision_prior + precision_obs
  let θ_hat := (μ * precision_prior + y * precision_obs) / precision_total
  (θ_hat, precision_total)

/-- Extract posterior mean from revision result -/
noncomputable def precisionWeightedRevision.mean
    (μ : ℝ) (precision_prior : ℝ) (y : ℝ) (precision_obs : ℝ) : ℝ :=
  (precisionWeightedRevision μ precision_prior y precision_obs).1

/-- Extract posterior precision from revision result -/
noncomputable def precisionWeightedRevision.precision
    (μ : ℝ) (precision_prior : ℝ) (y : ℝ) (precision_obs : ℝ) : ℝ :=
  (precisionWeightedRevision μ precision_prior y precision_obs).2

/-! ## Basic Properties -/

/-- Revision is commutative: swapping prior and observation gives the same result -/
theorem precisionWeightedRevision_comm
    (μ : ℝ) (precision_prior : ℝ) (y : ℝ) (precision_obs : ℝ) :
    precisionWeightedRevision μ precision_prior y precision_obs =
    precisionWeightedRevision y precision_obs μ precision_prior := by
  simp only [precisionWeightedRevision]
  ext <;> ring

/-- Posterior precision is the sum of input precisions -/
theorem precisionWeightedRevision_precision_sum
    (μ : ℝ) (precision_prior : ℝ) (y : ℝ) (precision_obs : ℝ) :
    (precisionWeightedRevision μ precision_prior y precision_obs).2 =
    precision_prior + precision_obs := rfl

/-- Posterior mean is a weighted average when total precision is positive -/
theorem precisionWeightedRevision_is_weighted_avg
    (μ : ℝ) (precision_prior : ℝ) (y : ℝ) (precision_obs : ℝ)
    (h : precision_prior + precision_obs ≠ 0) :
    let (θ_hat, _) := precisionWeightedRevision μ precision_prior y precision_obs
    let w_prior := precision_prior / (precision_prior + precision_obs)
    let w_obs := precision_obs / (precision_prior + precision_obs)
    θ_hat = w_prior * μ + w_obs * y := by
  simp only [precisionWeightedRevision]
  field_simp [h]

/-- Weights sum to 1 when total precision is positive -/
theorem precision_weights_sum_to_one
    (precision_prior precision_obs : ℝ)
    (h : precision_prior + precision_obs ≠ 0) :
    precision_prior / (precision_prior + precision_obs) +
    precision_obs / (precision_prior + precision_obs) = 1 := by
  field_simp [h]

/-! ## Shrinkage Factor

The shrinkage factor Bⱼ = σⱼ²/(σⱼ² + τ²) measures how much we "shrink"
the observation toward the population mean.

- B = 0: No shrinkage (σ² >> τ²), trust the observation
- B = 1: Full shrinkage (σ² << τ²), use the population mean
-/

/-- The shrinkage factor B = σ²/(σ² + τ²) -/
noncomputable def shrinkageFactor (σ_sq τ_sq : ℝ) : ℝ := σ_sq / (σ_sq + τ_sq)

/-- Shrinkage factor is in [0, 1] when variances are positive -/
theorem shrinkageFactor_nonneg (σ_sq τ_sq : ℝ) (hσ : 0 ≤ σ_sq) (_hτ : 0 ≤ τ_sq)
    (h_pos : 0 < σ_sq + τ_sq) :
    0 ≤ shrinkageFactor σ_sq τ_sq := by
  unfold shrinkageFactor
  apply div_nonneg hσ (le_of_lt h_pos)

theorem shrinkageFactor_le_one (σ_sq τ_sq : ℝ) (_hσ : 0 ≤ σ_sq) (hτ : 0 ≤ τ_sq)
    (h_pos : 0 < σ_sq + τ_sq) :
    shrinkageFactor σ_sq τ_sq ≤ 1 := by
  unfold shrinkageFactor
  rw [div_le_one h_pos]
  linarith

theorem shrinkageFactor_bounded (σ_sq τ_sq : ℝ) (hσ : 0 ≤ σ_sq) (hτ : 0 ≤ τ_sq)
    (h_pos : 0 < σ_sq + τ_sq) :
    0 ≤ shrinkageFactor σ_sq τ_sq ∧ shrinkageFactor σ_sq τ_sq ≤ 1 :=
  ⟨shrinkageFactor_nonneg σ_sq τ_sq hσ hτ h_pos,
   shrinkageFactor_le_one σ_sq τ_sq hσ hτ h_pos⟩

/-- 1 - B = τ²/(σ² + τ²) -/
theorem one_sub_shrinkageFactor (σ_sq τ_sq : ℝ) (h : σ_sq + τ_sq ≠ 0) :
    1 - shrinkageFactor σ_sq τ_sq = τ_sq / (σ_sq + τ_sq) := by
  unfold shrinkageFactor
  field_simp [h]
  ring

/-! ## Main Theorem: Shrinkage = Precision-Weighted Revision

This is the key result connecting PLN revision to Bayesian shrinkage.
-/

/-- **Main Theorem**: The shrinkage formula emerges from precision-weighted revision.

Given:
- Population mean μ with precision 1/τ² (between-school variance τ²)
- Observation y with precision 1/σ² (observation variance σ²)

The precision-weighted revision produces the shrinkage estimator:
  θ̂ = (1 - B)·y + B·μ   where B = σ²/(σ² + τ²)

This proves that PLN revision IS Bayesian shrinkage!
-/
theorem shrinkage_from_revision
    (μ y τ_sq σ_sq : ℝ) (hτ : 0 < τ_sq) (hσ : 0 < σ_sq) :
    let (θ_hat, _) := precisionWeightedRevision μ (1/τ_sq) y (1/σ_sq)
    let B := shrinkageFactor σ_sq τ_sq
    θ_hat = (1 - B) * y + B * μ := by
  simp only [precisionWeightedRevision, shrinkageFactor]
  -- Need to show:
  -- (μ * (1/τ_sq) + y * (1/σ_sq)) / (1/τ_sq + 1/σ_sq) = (1 - σ_sq/(σ_sq+τ_sq)) * y + (σ_sq/(σ_sq+τ_sq)) * μ
  have hτ_ne : τ_sq ≠ 0 := ne_of_gt hτ
  have hσ_ne : σ_sq ≠ 0 := ne_of_gt hσ
  have h_sum_ne : σ_sq + τ_sq ≠ 0 := by linarith
  have h_inv_sum_ne : 1/τ_sq + 1/σ_sq ≠ 0 := by
    have h1 : 0 < 1/τ_sq := by positivity
    have h2 : 0 < 1/σ_sq := by positivity
    linarith
  field_simp [hτ_ne, hσ_ne, h_sum_ne, h_inv_sum_ne]
  ring

/-- Corollary: Shrinkage estimator formula in standard form -/
theorem shrinkage_estimator_formula
    (μ y τ_sq σ_sq : ℝ) (hτ : 0 < τ_sq) (hσ : 0 < σ_sq) :
    precisionWeightedRevision.mean μ (1/τ_sq) y (1/σ_sq) =
    (τ_sq / (σ_sq + τ_sq)) * y + (σ_sq / (σ_sq + τ_sq)) * μ := by
  unfold precisionWeightedRevision.mean precisionWeightedRevision
  have hτ_ne : τ_sq ≠ 0 := ne_of_gt hτ
  have hσ_ne : σ_sq ≠ 0 := ne_of_gt hσ
  have h_sum_ne : σ_sq + τ_sq ≠ 0 := by linarith
  have h_inv_sum_ne : 1/τ_sq + 1/σ_sq ≠ 0 := by
    have h1 : 0 < 1/τ_sq := by positivity
    have h2 : 0 < 1/σ_sq := by positivity
    linarith
  field_simp [hτ_ne, hσ_ne, h_sum_ne, h_inv_sum_ne]
  ring

/-! ## Induction (Pooling) Rule

Induction aggregates evidence from multiple instances to estimate a population parameter.
For N-schools, this pools all school observations to get μ̂.
-/

/-- Pool observations with known precisions into a single estimate.

Given observations y₁, ..., yₙ with precisions w₁, ..., wₙ,
the pooled estimate is:
  μ̂ = (Σ wᵢyᵢ) / (Σ wᵢ)
-/
noncomputable def poolWeighted (observations : List (ℝ × ℝ)) : ℝ × ℝ :=
  let total_weight := observations.foldl (fun acc (_, w) => acc + w) 0
  let weighted_sum := observations.foldl (fun acc (y, w) => acc + y * w) 0
  (weighted_sum / total_weight, total_weight)

/-- Pooled mean from weighted observations -/
noncomputable def poolWeighted.mean (observations : List (ℝ × ℝ)) : ℝ :=
  (poolWeighted observations).1

/-- Total precision from weighted observations -/
noncomputable def poolWeighted.precision (observations : List (ℝ × ℝ)) : ℝ :=
  (poolWeighted observations).2

/-- Pooling empty list gives zero -/
theorem poolWeighted_nil : poolWeighted [] = (0, 0) := by
  simp [poolWeighted]

/-- Pooling single observation gives that observation -/
theorem poolWeighted_singleton (y w : ℝ) (hw : w ≠ 0) :
    (poolWeighted [(y, w)]).1 = y := by
  simp [poolWeighted]
  field_simp [hw]

/-- Pooling two observations is the same as precision-weighted revision -/
theorem poolWeighted_pair (y₁ w₁ y₂ w₂ : ℝ) (_h : w₁ + w₂ ≠ 0) :
    poolWeighted [(y₁, w₁), (y₂, w₂)] = precisionWeightedRevision y₁ w₁ y₂ w₂ := by
  simp only [poolWeighted, precisionWeightedRevision, List.foldl_cons, List.foldl_nil]
  simp only [zero_add]

/-! ## Hierarchical Deduction Rule

Hierarchical deduction propagates population estimates to individual instances.
-/

/-- Create a pseudo-observation from a population estimate.

Given population mean μ and between-instance variance τ²,
this creates evidence with precision 1/τ² for use in revision.
-/
noncomputable def populationPrior (μ_pop : ℝ) (τ_sq : ℝ) : ℝ × ℝ :=
  (μ_pop, 1 / τ_sq)

/-- The N-schools inference pipeline.

Given:
- J schools with observations yⱼ and standard errors σⱼ
- Population variance τ² (between-school variance)

For each school, compute the shrunk estimate via:
1. Use population mean μ̂ as prior with precision 1/τ²
2. Revise with observation yⱼ with precision 1/σⱼ²
-/
noncomputable def nSchoolsShrinkage
    (J : ℕ) (y : Fin J → ℝ) (σ_sq : Fin J → ℝ) (μ_pop : ℝ) (τ_sq : ℝ) :
    Fin J → ℝ :=
  fun j => (precisionWeightedRevision μ_pop (1/τ_sq) (y j) (1/(σ_sq j))).1

/-- Each shrunk estimate satisfies the shrinkage formula -/
theorem nSchoolsShrinkage_formula
    (J : ℕ) (y : Fin J → ℝ) (σ_sq : Fin J → ℝ)
    (μ_pop : ℝ) (τ_sq : ℝ)
    (hτ : 0 < τ_sq) (hσ : ∀ j, 0 < σ_sq j) (j : Fin J) :
    let θ_hat := nSchoolsShrinkage J y σ_sq μ_pop τ_sq j
    let B := shrinkageFactor (σ_sq j) τ_sq
    θ_hat = (1 - B) * y j + B * μ_pop := by
  have h := shrinkage_from_revision μ_pop (y j) τ_sq (σ_sq j) hτ (hσ j)
  simp only [nSchoolsShrinkage]
  exact h

/-! ## Properties of Shrinkage Estimates -/

/-- Shrinkage toward population mean -/
theorem shrinkage_between_y_and_mu
    (μ y τ_sq σ_sq : ℝ) (hτ : 0 < τ_sq) (hσ : 0 < σ_sq)
    (h_order : y ≤ μ) :
    y ≤ precisionWeightedRevision.mean μ (1/τ_sq) y (1/σ_sq) ∧
    precisionWeightedRevision.mean μ (1/τ_sq) y (1/σ_sq) ≤ μ := by
  rw [shrinkage_estimator_formula μ y τ_sq σ_sq hτ hσ]
  have h_sum : 0 < σ_sq + τ_sq := by linarith
  have h_wτ : 0 ≤ τ_sq / (σ_sq + τ_sq) := div_nonneg (le_of_lt hτ) (le_of_lt h_sum)
  have h_wσ : 0 ≤ σ_sq / (σ_sq + τ_sq) := div_nonneg (le_of_lt hσ) (le_of_lt h_sum)
  have h_wsum : τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq) = 1 := by
    field_simp [ne_of_gt h_sum]
    ring
  constructor
  · -- y ≤ θ̂
    calc y = y * 1 := by ring
       _ = y * (τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq)) := by rw [h_wsum]
       _ = τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * y := by ring
       _ ≤ τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * μ := by nlinarith [h_order, h_wσ]
  · -- θ̂ ≤ μ
    calc τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * μ
       ≤ τ_sq / (σ_sq + τ_sq) * μ + σ_sq / (σ_sq + τ_sq) * μ := by nlinarith [h_order, h_wτ]
       _ = μ * (τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq)) := by ring
       _ = μ * 1 := by rw [h_wsum]
       _ = μ := by ring

/-- Symmetric case: y ≥ μ -/
theorem shrinkage_between_y_and_mu'
    (μ y τ_sq σ_sq : ℝ) (hτ : 0 < τ_sq) (hσ : 0 < σ_sq)
    (h_order : μ ≤ y) :
    μ ≤ precisionWeightedRevision.mean μ (1/τ_sq) y (1/σ_sq) ∧
    precisionWeightedRevision.mean μ (1/τ_sq) y (1/σ_sq) ≤ y := by
  rw [shrinkage_estimator_formula μ y τ_sq σ_sq hτ hσ]
  have h_sum : 0 < σ_sq + τ_sq := by linarith
  have h_wτ : 0 ≤ τ_sq / (σ_sq + τ_sq) := div_nonneg (le_of_lt hτ) (le_of_lt h_sum)
  have h_wσ : 0 ≤ σ_sq / (σ_sq + τ_sq) := div_nonneg (le_of_lt hσ) (le_of_lt h_sum)
  have h_wsum : τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq) = 1 := by
    field_simp [ne_of_gt h_sum]
    ring
  constructor
  · -- μ ≤ θ̂
    calc μ = μ * 1 := by ring
       _ = μ * (τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq)) := by rw [h_wsum]
       _ = τ_sq / (σ_sq + τ_sq) * μ + σ_sq / (σ_sq + τ_sq) * μ := by ring
       _ ≤ τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * μ := by nlinarith [h_order, h_wτ]
  · -- θ̂ ≤ y
    calc τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * μ
       ≤ τ_sq / (σ_sq + τ_sq) * y + σ_sq / (σ_sq + τ_sq) * y := by nlinarith [h_order, h_wσ]
       _ = y * (τ_sq / (σ_sq + τ_sq) + σ_sq / (σ_sq + τ_sq)) := by ring
       _ = y * 1 := by rw [h_wsum]
       _ = y := by ring

/-! ## Connection to PLN Confidence

In PLN, confidence c = n/(n+κ) where n is evidence count and κ is a prior strength parameter.

For continuous data:
- Evidence "count" = precision = 1/σ²
- Confidence measures certainty about the estimate
-/

/-- PLN-style confidence from precision -/
noncomputable def confidenceFromPrecision (precision κ : ℝ) : ℝ :=
  precision / (precision + κ)

/-- Confidence is bounded in [0, 1) when κ > 0 -/
theorem confidenceFromPrecision_bounded (precision κ : ℝ)
    (h_prec : 0 ≤ precision) (h_κ : 0 < κ) :
    0 ≤ confidenceFromPrecision precision κ ∧ confidenceFromPrecision precision κ < 1 := by
  unfold confidenceFromPrecision
  constructor
  · apply div_nonneg h_prec
    linarith
  · have h : 0 < precision + κ := by linarith
    rw [div_lt_one h]
    linarith

/-- Posterior confidence after revision -/
noncomputable def posteriorConfidence (precision_prior precision_obs κ : ℝ) : ℝ :=
  confidenceFromPrecision (precision_prior + precision_obs) κ

/-- Posterior confidence is at least the max of input confidences -/
theorem posteriorConfidence_increases (precision_prior precision_obs κ : ℝ)
    (h_prior : 0 ≤ precision_prior) (h_obs : 0 ≤ precision_obs) (h_κ : 0 < κ) :
    confidenceFromPrecision precision_prior κ ≤ posteriorConfidence precision_prior precision_obs κ ∧
    confidenceFromPrecision precision_obs κ ≤ posteriorConfidence precision_prior precision_obs κ := by
  unfold posteriorConfidence confidenceFromPrecision
  constructor
  · -- prior confidence ≤ posterior confidence
    have h1 : 0 < precision_prior + κ := by linarith
    have h2 : 0 < precision_prior + precision_obs + κ := by linarith
    rw [div_le_div_iff₀ h1 h2]
    nlinarith
  · -- obs confidence ≤ posterior confidence
    have h1 : 0 < precision_obs + κ := by linarith
    have h2 : 0 < precision_prior + precision_obs + κ := by linarith
    rw [div_le_div_iff₀ h1 h2]
    nlinarith

/-! ## Summary

This file establishes the core PLN rules for hierarchical inference:

1. **Precision-Weighted Revision** = Bayesian shrinkage
2. **Pooling (Induction)** = weighted mean aggregation
3. **Hierarchical Deduction** = population → individual with τ² precision

Main theorem: `shrinkage_from_revision` proves that PLN revision
produces the exact Bayesian shrinkage estimator:
  θ̂ⱼ = (1 - Bⱼ)·yⱼ + Bⱼ·μ̂  where Bⱼ = σⱼ²/(σⱼ² + τ²)

This connects the "logical" PLN view to the "statistical" Bayesian view.
-/

end Mettapedia.Logic.PLNHierarchicalRules
