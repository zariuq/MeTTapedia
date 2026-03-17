/-
# BinaryEvidence-Dirichlet Bridge: Generalized Conjugate Prior Aggregation

This file generalizes the BinaryEvidence-Beta bridge (EvidenceBeta.lean) to the
Dirichlet-Multinomial case, showing that PLN-style evidence aggregation
is the natural sufficient-statistic aggregation for conjugate priors.

## The Key Insight

For k-ary outcomes (generalizing binary True/False):
- BinaryEvidence = count vector (n₁, n₂, ..., nₖ) ∈ ℕᵏ
- Prior: Dirichlet(α₁, ..., αₖ)
- Posterior: Dirichlet(α₁+n₁, ..., αₖ+nₖ) — by Dirichlet-Multinomial conjugacy
- **hplus = coordinatewise addition = Bayesian update**

This is the k-ary generalization of:
- k=2: BinaryEvidence (n⁺, n⁻) with Beta(α+n⁺, β+n⁻) posterior (EvidenceBeta.lean)

## Main Definitions

- `MultiEvidence k`: BinaryEvidence counts for k outcomes
- `DirichletParams k`: Dirichlet distribution parameters
- `evidence_aggregation_is_dirichlet_update`: hplus = Dirichlet conjugate update

## The Conjugate Prior Pattern

The common abstraction across conjugate prior families:

| Family | BinaryEvidence Type | Prior | Posterior | hplus |
|--------|---------------|-------|-----------|-------|
| Beta-Bernoulli | (n⁺, n⁻) | Beta(α,β) | Beta(α+n⁺, β+n⁻) | coordinatewise + |
| Dirichlet-Multinomial | (n₁,...,nₖ) | Dir(α₁,...,αₖ) | Dir(α₁+n₁,...,αₖ+nₖ) | coordinatewise + |
| Normal-Normal | (sum, count) | N(μ₀,σ₀²) | N(μ',σ'²) | additive in sufficient stat |

The key observation: **Conjugate prior update = additive aggregation of sufficient statistics**

## References

- Bernardo & Smith, "Bayesian Theory" (2000), Chapter 5.2 (Conjugate families)
- Gelman et al., "Bayesian Data Analysis" (2013), Chapter 2
- EvidenceBeta.lean (the k=2 special case)

-/

import Mettapedia.Logic.EvidenceBeta
import Mathlib.Data.Fintype.BigOperators

namespace Mettapedia.Logic.EvidenceDirichlet

open Mettapedia.Logic.EvidenceBeta
open BigOperators

/-! ## Multi-Outcome BinaryEvidence (k-ary generalization) -/

/-- BinaryEvidence counts for k possible outcomes.
    This generalizes binary BinaryEvidence (n⁺, n⁻) to k outcomes (n₁, ..., nₖ).
    For k=2 with outcomes {True, False}, this reduces to standard PLN BinaryEvidence. -/
@[ext]
structure MultiEvidence (k : ℕ) where
  counts : Fin k → ℕ
  deriving DecidableEq

namespace MultiEvidence

variable {k : ℕ}

/-- Zero evidence: no observations of any outcome -/
def zero : MultiEvidence k := ⟨fun _ => 0⟩

/-- Total evidence count: n₁ + n₂ + ... + nₖ -/
def total (e : MultiEvidence k) : ℕ := ∑ i, e.counts i

/-- Aggregation of independent evidence (hplus): coordinatewise addition -/
def hplus (e₁ e₂ : MultiEvidence k) : MultiEvidence k :=
  ⟨fun i => e₁.counts i + e₂.counts i⟩

instance : Add (MultiEvidence k) where
  add := hplus

/-- hplus is commutative -/
theorem hplus_comm (e₁ e₂ : MultiEvidence k) : e₁ + e₂ = e₂ + e₁ := by
  ext i
  exact Nat.add_comm _ _

/-- hplus is associative -/
theorem hplus_assoc (e₁ e₂ e₃ : MultiEvidence k) : e₁ + e₂ + e₃ = e₁ + (e₂ + e₃) := by
  ext i
  exact Nat.add_assoc _ _ _

/-- zero is the identity for hplus -/
theorem hplus_zero (e : MultiEvidence k) : e + zero = e := by
  ext i
  exact Nat.add_zero _

theorem zero_hplus (e : MultiEvidence k) : zero + e = e := by
  rw [hplus_comm]
  exact hplus_zero e

/-- Total evidence is additive under hplus -/
theorem total_hplus (e₁ e₂ : MultiEvidence k) : (e₁ + e₂).total = e₁.total + e₂.total := by
  simp only [total, HAdd.hAdd, Add.add, hplus]
  exact Finset.sum_add_distrib

end MultiEvidence

/-! ## Dirichlet Distribution Parameters -/

/-- Parameters for a Dirichlet distribution over k outcomes.
    Dirichlet(α₁, ..., αₖ) is the conjugate prior for Multinomial. -/
structure DirichletParams (k : ℕ) where
  /-- Prior parameters (concentration parameters) -/
  priorParams : Fin k → ℝ
  /-- All parameters are positive -/
  params_pos : ∀ i, 0 < priorParams i

namespace DirichletParams

variable {k : ℕ}

/-- Total concentration: α₁ + ... + αₖ -/
noncomputable def totalConcentration (p : DirichletParams k) : ℝ :=
  ∑ i, p.priorParams i

/-- Total concentration is positive when k > 0 -/
theorem totalConcentration_pos (p : DirichletParams k) (hk : 0 < k) :
    0 < p.totalConcentration := by
  unfold totalConcentration
  have : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk)
  exact Finset.sum_pos (fun i _ => p.params_pos i) this

/-- Uniform Dirichlet prior: all αᵢ = α₀ -/
def uniform (α₀ : ℝ) (hα : 0 < α₀) : DirichletParams k where
  priorParams := fun _ => α₀
  params_pos := fun _ => hα

/-- Symmetric Dirichlet with α₀ = 1 (uniform prior over simplex) -/
def uniformPrior : DirichletParams k := uniform 1 one_pos

/-- Symmetric Dirichlet with α₀ = 1/k (Jeffreys-like for Dirichlet) -/
noncomputable def jeffreysPrior (hk : 0 < k) : DirichletParams k :=
  uniform (1 / k) (by positivity)

end DirichletParams

/-! ## BinaryEvidence to Dirichlet Posterior -/

/-- Combine MultiEvidence with a Dirichlet prior to get posterior parameters.
    This is the Dirichlet-Multinomial conjugate update:
    Prior: Dir(α₁, ..., αₖ)
    BinaryEvidence: (n₁, ..., nₖ)
    Posterior: Dir(α₁+n₁, ..., αₖ+nₖ) -/
structure EvidenceDirichletParams (k : ℕ) where
  prior : DirichletParams k
  evidence : MultiEvidence k

namespace EvidenceDirichletParams

variable {k : ℕ}

/-- Posterior parameter for outcome i: αᵢ + nᵢ -/
noncomputable def posteriorParam (p : EvidenceDirichletParams k) (i : Fin k) : ℝ :=
  p.prior.priorParams i + p.evidence.counts i

/-- All posterior parameters are positive -/
theorem posteriorParam_pos (p : EvidenceDirichletParams k) (i : Fin k) :
    0 < p.posteriorParam i := by
  unfold posteriorParam
  have hα : 0 < p.prior.priorParams i := p.prior.params_pos i
  have hn : 0 ≤ (p.evidence.counts i : ℝ) := Nat.cast_nonneg _
  linarith

/-- Convert to DirichletParams (the posterior) -/
noncomputable def toPosterior (p : EvidenceDirichletParams k) : DirichletParams k where
  priorParams := fun i => p.posteriorParam i
  params_pos := fun i => p.posteriorParam_pos i

/-- Posterior mean for outcome i: (αᵢ + nᵢ) / Σⱼ(αⱼ + nⱼ)
    Note: hk (k > 0) is needed for well-definedness proofs but not the computation. -/
noncomputable def posteriorMean (p : EvidenceDirichletParams k) (_hk : 0 < k) (i : Fin k) : ℝ :=
  p.posteriorParam i / p.toPosterior.totalConcentration

/-- Posterior mean is in [0, 1] -/
theorem posteriorMean_mem_unit (p : EvidenceDirichletParams k) (hk : 0 < k) (i : Fin k) :
    0 ≤ p.posteriorMean hk i ∧ p.posteriorMean hk i ≤ 1 := by
  unfold posteriorMean
  constructor
  · apply div_nonneg
    · exact le_of_lt (p.posteriorParam_pos i)
    · exact le_of_lt (p.toPosterior.totalConcentration_pos hk)
  · rw [div_le_one (p.toPosterior.totalConcentration_pos hk)]
    unfold DirichletParams.totalConcentration toPosterior
    simp only
    exact Finset.single_le_sum (fun j _ => le_of_lt (p.posteriorParam_pos j))
      (Finset.mem_univ i)

end EvidenceDirichletParams

/-! ## Main Theorem: hplus = Dirichlet Conjugate Update -/

/-- **Main Theorem**: BinaryEvidence aggregation (hplus) corresponds to Dirichlet conjugate update.

If we have:
- Prior: Dirichlet(α₁, ..., αₖ)
- BinaryEvidence₁: (n₁₁, ..., n₁ₖ) giving posterior Dir(α₁+n₁₁, ..., αₖ+n₁ₖ)
- BinaryEvidence₂: (n₂₁, ..., n₂ₖ)

Then the combined evidence (n₁₁+n₂₁, ..., n₁ₖ+n₂ₖ) gives
Dir(α₁+n₁₁+n₂₁, ..., αₖ+n₁ₖ+n₂ₖ)

which is exactly the Bayesian posterior after updating with both evidence sets. -/
theorem evidence_aggregation_is_dirichlet_update {k : ℕ}
    (prior : DirichletParams k)
    (e₁ e₂ : MultiEvidence k) (i : Fin k) :
    (⟨prior, e₁ + e₂⟩ : EvidenceDirichletParams k).posteriorParam i =
    (⟨prior, e₁⟩ : EvidenceDirichletParams k).posteriorParam i + e₂.counts i := by
  unfold EvidenceDirichletParams.posteriorParam
  -- LHS: prior.priorParams i + ↑((e₁ + e₂).counts i)
  -- RHS: (prior.priorParams i + ↑(e₁.counts i)) + ↑(e₂.counts i)
  have h1 : (e₁ + e₂).counts i = e₁.counts i + e₂.counts i := rfl
  simp only [h1, Nat.cast_add]
  ring

/-- Corollary: The combined posterior mean approaches the empirical frequency as sample size grows.

    posterior_mean = (αᵢ + nᵢ) / (αsum + n)
    empirical_freq = nᵢ / n

    |posterior_mean - empirical_freq| = |n·αᵢ - αsum·nᵢ| / (n·(αsum + n)) ≤ αsum / n -/
theorem posterior_mean_converges_to_frequency {k : ℕ} (hk : 0 < k)
    (prior : DirichletParams k) (e : MultiEvidence k) (i : Fin k)
    (he : 0 < e.total) :
    let params : EvidenceDirichletParams k := ⟨prior, e⟩
    let empirical_freq := (e.counts i : ℝ) / e.total
    let posterior_mean := params.posteriorMean hk i
    ∃ C : ℝ, |posterior_mean - empirical_freq| ≤ C / e.total := by
  use prior.totalConcentration
  -- Unfold definitions
  simp only [EvidenceDirichletParams.posteriorMean, EvidenceDirichletParams.posteriorParam,
    EvidenceDirichletParams.toPosterior, DirichletParams.totalConcentration]

  -- Setup: let n = e.total, αᵢ = prior.priorParams i, nᵢ = e.counts i
  set n : ℝ := (e.total : ℝ) with hn_def
  set αᵢ : ℝ := prior.priorParams i with hαᵢ_def
  set nᵢ : ℝ := (e.counts i : ℝ) with hnᵢ_def
  set αsum : ℝ := ∑ j, prior.priorParams j with hαsum_def

  -- Positivity facts
  have hn_pos : 0 < n := by simp only [hn_def]; exact_mod_cast he
  have hαᵢ_pos : 0 < αᵢ := prior.params_pos i
  have hnᵢ_nonneg : 0 ≤ nᵢ := Nat.cast_nonneg _
  have hαsum_pos : 0 < αsum := prior.totalConcentration_pos hk

  -- The denominator of posterior mean
  have hαsum_n_pos : 0 < αsum + n := by linarith

  -- posterior_mean = (αᵢ + nᵢ) / (αsum + n)
  -- empirical_freq = nᵢ / n
  -- We need: |(αᵢ + nᵢ)/(αsum + n) - nᵢ/n| ≤ αsum/n

  -- Compute the difference as a single fraction
  have hdiff : (αᵢ + nᵢ) / (αsum + n) - nᵢ / n =
      (n * αᵢ - αsum * nᵢ) / (n * (αsum + n)) := by
    field_simp [ne_of_gt hn_pos, ne_of_gt hαsum_n_pos]
    ring

  -- The total sum of posteriorParams equals αsum + n
  have hsum_eq : ∑ j, (prior.priorParams j + ↑(e.counts j)) = αsum + n := by
    rw [Finset.sum_add_distrib]
    -- After sum split: ∑ j, prior.priorParams j + ∑ j, ↑(e.counts j) = αsum + n
    -- Need: ∑ j, ↑(e.counts j) = ↑(∑ j, e.counts j) = ↑(e.total) = n
    simp only [Nat.cast_sum, hn_def, hαsum_def, MultiEvidence.total]

  rw [hsum_eq, hdiff]

  -- Bound the numerator: |n * αᵢ - αsum * nᵢ| ≤ n * αsum
  -- This follows from: nᵢ ≤ n and αᵢ ≤ αsum
  have hnᵢ_le_n : nᵢ ≤ n := by
    simp only [hnᵢ_def, hn_def]
    have : e.counts i ≤ e.total := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact_mod_cast this

  have hαᵢ_le_αsum : αᵢ ≤ αsum := by
    simp only [hαᵢ_def, hαsum_def]
    exact Finset.single_le_sum (fun j _ => le_of_lt (prior.params_pos j)) (Finset.mem_univ i)

  -- |n * αᵢ - αsum * nᵢ| ≤ n * αsum
  have hnum_bound : |n * αᵢ - αsum * nᵢ| ≤ n * αsum := by
    have h1 : n * αᵢ ≤ n * αsum := mul_le_mul_of_nonneg_left hαᵢ_le_αsum (le_of_lt hn_pos)
    have h2 : 0 ≤ αsum * nᵢ := mul_nonneg (le_of_lt hαsum_pos) hnᵢ_nonneg
    have h3 : αsum * nᵢ ≤ αsum * n := mul_le_mul_of_nonneg_left hnᵢ_le_n (le_of_lt hαsum_pos)
    -- |n * αᵢ - αsum * nᵢ| ≤ max(n*αᵢ, αsum*nᵢ) ≤ max(n*αsum, αsum*n) = n*αsum
    have hlo : -(n * αsum) ≤ n * αᵢ - αsum * nᵢ := by
      -- n * αᵢ ≥ 0 and αsum * nᵢ ≤ αsum * n
      have : 0 ≤ n * αᵢ := mul_nonneg (le_of_lt hn_pos) (le_of_lt hαᵢ_pos)
      linarith
    have hhi : n * αᵢ - αsum * nᵢ ≤ n * αsum := by
      -- n * αᵢ ≤ n * αsum and αsum * nᵢ ≥ 0
      linarith
    exact abs_le.mpr ⟨hlo, hhi⟩

  -- Now: |...| / (n * (αsum + n)) ≤ (n * αsum) / (n * (αsum + n)) = αsum / (αsum + n) ≤ αsum / n
  have hden_pos : 0 < n * (αsum + n) := mul_pos hn_pos hαsum_n_pos

  -- The goal has absolute value around the whole fraction
  rw [abs_div, abs_of_pos hden_pos]

  calc |n * αᵢ - αsum * nᵢ| / (n * (αsum + n))
      ≤ (n * αsum) / (n * (αsum + n)) := by
        exact div_le_div_of_nonneg_right hnum_bound (le_of_lt hden_pos)
    _ = αsum / (αsum + n) := by field_simp [ne_of_gt hn_pos]
    _ ≤ αsum / n := by
        apply div_le_div_of_nonneg_left (le_of_lt hαsum_pos) hn_pos
        linarith

/-! ## Walley IDM Predictive Intervals (Multinomial) -/

section IDMPredictiveIntervals

/-- Context for multinomial IDM predictive intervals (`s > 0` is prior strength). -/
structure IDMPredictiveContext where
  s : ℝ
  s_pos : 0 < s

namespace IDMPredictiveContext

/-- Common IDM default (`s = 2`). -/
def default : IDMPredictiveContext := ⟨2, by norm_num⟩

end IDMPredictiveContext

variable {k : ℕ}

/-- Category count is bounded by total count. -/
theorem count_le_total (e : MultiEvidence k) (i : Fin k) :
    e.counts i ≤ e.total :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Denominator shared by all IDM predictive bounds. -/
noncomputable def idmDenom (ctx : IDMPredictiveContext) (e : MultiEvidence k) : ℝ :=
  (e.total : ℝ) + ctx.s

/-- Walley IDM predictive lower bound for category `i`. -/
noncomputable def idmLower
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) : ℝ :=
  (e.counts i : ℝ) / idmDenom ctx e

/-- Walley IDM predictive upper bound for category `i`. -/
noncomputable def idmUpper
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) : ℝ :=
  ((e.counts i : ℝ) + ctx.s) / idmDenom ctx e

/-- Width of each category interval under IDM (independent of `i`). -/
noncomputable def idmWidth (ctx : IDMPredictiveContext) (e : MultiEvidence k) : ℝ :=
  ctx.s / idmDenom ctx e

theorem idmDenom_pos (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    0 < idmDenom ctx e := by
  unfold idmDenom
  have hTotalNonneg : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
  linarith [ctx.s_pos]

theorem idmLower_nonneg (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    0 ≤ idmLower ctx e i := by
  unfold idmLower
  apply div_nonneg
  · exact Nat.cast_nonneg (e.counts i)
  · exact le_of_lt (idmDenom_pos ctx e)

theorem idmUpper_nonneg (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    0 ≤ idmUpper ctx e i := by
  unfold idmUpper
  apply div_nonneg
  · have hCountNonneg : 0 ≤ (e.counts i : ℝ) := Nat.cast_nonneg (e.counts i)
    linarith [ctx.s_pos.le, hCountNonneg]
  · exact le_of_lt (idmDenom_pos ctx e)

theorem idmLower_le_idmUpper (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    idmLower ctx e i ≤ idmUpper ctx e i := by
  unfold idmLower idmUpper
  apply div_le_div_of_nonneg_right
  · linarith [ctx.s_pos.le]
  · exact le_of_lt (idmDenom_pos ctx e)

theorem idmUpper_le_one (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    idmUpper ctx e i ≤ 1 := by
  unfold idmUpper
  apply (div_le_one (idmDenom_pos ctx e)).2
  have hCountLe : (e.counts i : ℝ) ≤ (e.total : ℝ) := by
    exact_mod_cast (count_le_total e i)
  unfold idmDenom
  linarith [hCountLe]

theorem idmWidth_eq_upper_sub_lower
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) (i : Fin k) :
    idmWidth ctx e = idmUpper ctx e i - idmLower ctx e i := by
  unfold idmWidth idmUpper idmLower idmDenom
  field_simp [ne_of_gt (idmDenom_pos ctx e)]
  ring

theorem idmWidth_nonneg (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    0 ≤ idmWidth ctx e := by
  unfold idmWidth
  exact div_nonneg (le_of_lt ctx.s_pos) (le_of_lt (idmDenom_pos ctx e))

theorem idmWidth_le_one (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    idmWidth ctx e ≤ 1 := by
  unfold idmWidth
  apply (div_le_one (idmDenom_pos ctx e)).2
  unfold idmDenom
  have hTotalNonneg : 0 ≤ (e.total : ℝ) := by exact_mod_cast (Nat.zero_le e.total)
  linarith [hTotalNonneg]

theorem sum_idmLower_eq
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    (∑ i : Fin k, idmLower ctx e i) = (e.total : ℝ) / idmDenom ctx e := by
  unfold idmLower idmDenom
  calc
    (∑ i : Fin k, (e.counts i : ℝ) / ((e.total : ℝ) + ctx.s))
        = (∑ i : Fin k, (e.counts i : ℝ)) / ((e.total : ℝ) + ctx.s) := by
          simp [div_eq_mul_inv, Finset.sum_mul]
    _ = (e.total : ℝ) / ((e.total : ℝ) + ctx.s) := by
          simp [MultiEvidence.total, Nat.cast_sum]

theorem sum_idmUpper_eq
    (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    (∑ i : Fin k, idmUpper ctx e i) =
      ((e.total : ℝ) + (k : ℝ) * ctx.s) / idmDenom ctx e := by
  unfold idmUpper idmDenom
  calc
    (∑ i : Fin k, ((e.counts i : ℝ) + ctx.s) / ((e.total : ℝ) + ctx.s))
        = (∑ i : Fin k, ((e.counts i : ℝ) + ctx.s)) / ((e.total : ℝ) + ctx.s) := by
          simp [div_eq_mul_inv, Finset.sum_mul]
    _ = ((∑ i : Fin k, (e.counts i : ℝ)) + (∑ _i : Fin k, ctx.s)) / ((e.total : ℝ) + ctx.s) := by
          simp [Finset.sum_add_distrib]
    _ = ((e.total : ℝ) + (k : ℝ) * ctx.s) / ((e.total : ℝ) + ctx.s) := by
          simp [MultiEvidence.total, Nat.cast_sum]

theorem sum_idmLower_le_one (ctx : IDMPredictiveContext) (e : MultiEvidence k) :
    (∑ i : Fin k, idmLower ctx e i) ≤ 1 := by
  rw [sum_idmLower_eq]
  apply (div_le_one (idmDenom_pos ctx e)).2
  unfold idmDenom
  linarith [ctx.s_pos.le]

theorem one_le_sum_idmUpper (ctx : IDMPredictiveContext) {k : ℕ} (hk : 0 < k)
    (e : MultiEvidence k) :
    1 ≤ (∑ i : Fin k, idmUpper ctx e i) := by
  rw [sum_idmUpper_eq]
  have hDenPos : 0 < idmDenom ctx e := idmDenom_pos ctx e
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hk)
  have hs_le : ctx.s ≤ (k : ℝ) * ctx.s := by
    simpa using (mul_le_mul_of_nonneg_right hk1 (le_of_lt ctx.s_pos))
  have hNumGe : idmDenom ctx e ≤ (e.total : ℝ) + (k : ℝ) * ctx.s := by
    unfold idmDenom
    linarith [hs_le]
  exact (one_le_div hDenPos).2 hNumGe

end IDMPredictiveIntervals

/-! ## Connection to Binary BinaryEvidence (k=2 case) -/

/-- For k=2, MultiEvidence reduces to binary BinaryEvidence. -/
def binaryEvidence_to_multi (n_pos n_neg : ℕ) : MultiEvidence 2 :=
  ⟨![n_pos, n_neg]⟩

/-- Binary evidence aggregation matches MultiEvidence aggregation. -/
theorem binary_hplus_matches_multi (n₁_pos n₁_neg n₂_pos n₂_neg : ℕ) :
    binaryEvidence_to_multi (n₁_pos + n₂_pos) (n₁_neg + n₂_neg) =
    binaryEvidence_to_multi n₁_pos n₁_neg + binaryEvidence_to_multi n₂_pos n₂_neg := by
  simp only [binaryEvidence_to_multi, MultiEvidence.hplus, HAdd.hAdd, Add.add]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Summary

This file establishes the key generalization:

**PLN BinaryEvidence aggregation IS Bayesian conjugate prior update**

The pattern:
1. BinaryEvidence = sufficient statistic for the likelihood
2. hplus = additive combination of sufficient statistics
3. This equals the conjugate prior update rule

For k outcomes:
- BinaryEvidence: (n₁, ..., nₖ) = multinomial sufficient statistic
- Prior: Dirichlet(α₁, ..., αₖ)
- Posterior: Dirichlet(α₁+n₁, ..., αₖ+nₖ)
- hplus(e₁, e₂) = coordinatewise addition = Bayesian update

This justifies PLN-style evidence combination as the **exact optimal inference**
for exchangeable categorical observations (by de Finetti + conjugacy).
-/

end Mettapedia.Logic.EvidenceDirichlet
