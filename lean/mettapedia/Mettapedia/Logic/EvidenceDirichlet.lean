/-
# Evidence-Dirichlet Bridge: Generalized Conjugate Prior Aggregation

This file generalizes the Evidence-Beta bridge (EvidenceBeta.lean) to the
Dirichlet-Multinomial case, showing that PLN-style evidence aggregation
is the natural sufficient-statistic aggregation for conjugate priors.

## The Key Insight

For k-ary outcomes (generalizing binary True/False):
- Evidence = count vector (n₁, n₂, ..., nₖ) ∈ ℕᵏ
- Prior: Dirichlet(α₁, ..., αₖ)
- Posterior: Dirichlet(α₁+n₁, ..., αₖ+nₖ) — by Dirichlet-Multinomial conjugacy
- **hplus = coordinatewise addition = Bayesian update**

This is the k-ary generalization of:
- k=2: Evidence (n⁺, n⁻) with Beta(α+n⁺, β+n⁻) posterior (EvidenceBeta.lean)

## Main Definitions

- `MultiEvidence k`: Evidence counts for k outcomes
- `DirichletParams k`: Dirichlet distribution parameters
- `evidence_aggregation_is_dirichlet_update`: hplus = Dirichlet conjugate update

## The Conjugate Prior Pattern

The common abstraction across conjugate prior families:

| Family | Evidence Type | Prior | Posterior | hplus |
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

/-! ## Multi-Outcome Evidence (k-ary generalization) -/

/-- Evidence counts for k possible outcomes.
    This generalizes binary Evidence (n⁺, n⁻) to k outcomes (n₁, ..., nₖ).
    For k=2 with outcomes {True, False}, this reduces to standard PLN Evidence. -/
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

/-! ## Evidence to Dirichlet Posterior -/

/-- Combine MultiEvidence with a Dirichlet prior to get posterior parameters.
    This is the Dirichlet-Multinomial conjugate update:
    Prior: Dir(α₁, ..., αₖ)
    Evidence: (n₁, ..., nₖ)
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

/-- **Main Theorem**: Evidence aggregation (hplus) corresponds to Dirichlet conjugate update.

If we have:
- Prior: Dirichlet(α₁, ..., αₖ)
- Evidence₁: (n₁₁, ..., n₁ₖ) giving posterior Dir(α₁+n₁₁, ..., αₖ+n₁ₖ)
- Evidence₂: (n₂₁, ..., n₂ₖ)

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

/-! ## Connection to Binary Evidence (k=2 case) -/

/-- For k=2, MultiEvidence reduces to binary Evidence. -/
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

**PLN Evidence aggregation IS Bayesian conjugate prior update**

The pattern:
1. Evidence = sufficient statistic for the likelihood
2. hplus = additive combination of sufficient statistics
3. This equals the conjugate prior update rule

For k outcomes:
- Evidence: (n₁, ..., nₖ) = multinomial sufficient statistic
- Prior: Dirichlet(α₁, ..., αₖ)
- Posterior: Dirichlet(α₁+n₁, ..., αₖ+nₖ)
- hplus(e₁, e₂) = coordinatewise addition = Bayesian update

This justifies PLN-style evidence combination as the **exact optimal inference**
for exchangeable categorical observations (by de Finetti + conjugacy).
-/

end Mettapedia.Logic.EvidenceDirichlet
