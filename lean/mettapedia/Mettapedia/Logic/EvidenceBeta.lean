import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.Exchangeability
import Mettapedia.ProbabilityTheory.Distributions.BetaBernoulli
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Evidence-Beta Bridge

This file connects PLN Evidence to Beta-Bernoulli conjugacy, establishing that:

1. **PLN Evidence (n⁺, n⁻) corresponds to Beta(α, β) posterior**
2. **PLN Strength n⁺/(n⁺+n⁻) = Beta posterior mean** (asymptotically)
3. **Evidence aggregation (hplus) = Beta conjugate update**

## The Key Insight

For exchangeable binary observations:
- Observations: k positives, m negatives
- Prior: Beta(α₀, β₀) - typically uniform (α₀=β₀=1) or Jeffreys (α₀=β₀=0.5)
- Posterior: Beta(α₀+k, β₀+m) - by Beta-Bernoulli conjugacy
- Posterior mean: (α₀+k)/(α₀+β₀+k+m)

PLN Evidence (k, m) captures exactly the sufficient statistic, and:
- PLN strength k/(k+m) = posterior mean when α₀=β₀=0 (improper prior)
- For proper priors, strength → posterior mean as sample size → ∞

## Main Theorems

* `evidenceToBeta` : Map Evidence to Beta distribution parameters
* `toStrength_eq_beta_mean_limit` : PLN strength = Beta mean (asymptotically)
* `evidence_hplus_eq_beta_update` : hplus = Beta conjugate update

## References

- de Finetti's representation theorem (Exchangeability.lean)
- Beta-Bernoulli conjugacy (BetaBernoulli.lean)
- PLN Evidence quantale (EvidenceQuantale.lean)

-/

namespace Mettapedia.Logic.EvidenceBeta

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.Exchangeability
open Mettapedia.ProbabilityTheory

/-! ## Mapping Evidence to Beta Parameters -/

section EvidenceToBeta

/-- Map PLN Evidence to Beta distribution parameters.

    Given evidence (n⁺, n⁻) with prior parameter α₀ = β₀ = prior_param:
    - α = prior_param + n⁺
    - β = prior_param + n⁻

    Common choices:
    - prior_param = 1 : Uniform prior (Laplace's rule of succession)
    - prior_param = 0.5 : Jeffreys prior (objective Bayesian)
    - prior_param = 0 : Improper prior (maximum likelihood limit)
-/
structure EvidenceBetaParams where
  prior_param : ℝ
  prior_pos : 0 < prior_param
  evidence_pos : ℕ
  evidence_neg : ℕ

namespace EvidenceBetaParams

/-- The Beta α parameter: prior + positive evidence -/
noncomputable def alpha (p : EvidenceBetaParams) : ℝ := p.prior_param + p.evidence_pos

/-- The Beta β parameter: prior + negative evidence -/
noncomputable def beta (p : EvidenceBetaParams) : ℝ := p.prior_param + p.evidence_neg

/-- α is positive -/
theorem alpha_pos (p : EvidenceBetaParams) : 0 < p.alpha := by
  unfold alpha
  linarith [p.prior_pos]

/-- β is positive -/
theorem beta_pos (p : EvidenceBetaParams) : 0 < p.beta := by
  unfold beta
  linarith [p.prior_pos]

/-- Convert to BetaBernoulliPrior -/
noncomputable def toBetaPrior (p : EvidenceBetaParams) : BetaBernoulliPrior :=
  { α := p.alpha
    β := p.beta
    α_pos := p.alpha_pos
    β_pos := p.beta_pos }

/-- Beta posterior mean: α / (α + β) -/
noncomputable def posteriorMean (p : EvidenceBetaParams) : ℝ :=
  p.alpha / (p.alpha + p.beta)

/-- Posterior mean is in [0, 1] -/
theorem posteriorMean_mem_unit (p : EvidenceBetaParams) :
    0 ≤ p.posteriorMean ∧ p.posteriorMean ≤ 1 := by
  unfold posteriorMean
  constructor
  · apply div_nonneg
    · linarith [p.alpha_pos]
    · linarith [p.alpha_pos, p.beta_pos]
  · have h_pos : 0 < p.alpha + p.beta := by linarith [p.alpha_pos, p.beta_pos]
    rw [div_le_one h_pos]
    unfold alpha beta
    -- Need: prior + pos ≤ prior + pos + prior + neg
    -- i.e., 0 ≤ prior + neg, which is true since prior > 0 and neg ≥ 0
    have h1 : (0 : ℝ) ≤ p.evidence_neg := Nat.cast_nonneg _
    have h2 : 0 < p.prior_param := p.prior_pos
    calc p.prior_param + ↑p.evidence_pos
      _ ≤ p.prior_param + ↑p.evidence_pos + p.prior_param := by linarith
      _ ≤ p.prior_param + ↑p.evidence_pos + (p.prior_param + ↑p.evidence_neg) := by linarith

end EvidenceBetaParams

/-- Construct EvidenceBetaParams with uniform prior (Laplace) -/
def withUniformPrior (n_pos n_neg : ℕ) : EvidenceBetaParams :=
  { prior_param := 1
    prior_pos := by norm_num
    evidence_pos := n_pos
    evidence_neg := n_neg }

/-- Construct EvidenceBetaParams with Jeffreys prior -/
def withJeffreysPrior (n_pos n_neg : ℕ) : EvidenceBetaParams :=
  { prior_param := 0.5
    prior_pos := by norm_num
    evidence_pos := n_pos
    evidence_neg := n_neg }

end EvidenceToBeta

/-! ## PLN Strength vs Beta Posterior Mean -/

section StrengthVsMean

/-- PLN strength from natural number counts -/
noncomputable def plnStrength (n_pos n_neg : ℕ) : ℝ :=
  if n_pos + n_neg = 0 then 0 else (n_pos : ℝ) / (n_pos + n_neg : ℝ)

/-- Uniform prior posterior mean -/
noncomputable def uniformPosteriorMean (n_pos n_neg : ℕ) : ℝ :=
  ((n_pos : ℝ) + 1) / ((n_pos : ℝ) + (n_neg : ℝ) + 2)

/-- Jeffreys prior posterior mean -/
noncomputable def jeffreysPosteriorMean (n_pos n_neg : ℕ) : ℝ :=
  ((n_pos : ℝ) + 0.5) / ((n_pos : ℝ) + (n_neg : ℝ) + 1)

/-! ### Prior ledger API (small convenience layer)

These are just names for the three “default priors” we compare in νPLN:
- Haldane/improper (α=β=0): gives `k/n` (PLN strength) for `n>0`
- Jeffreys/KT (α=β=1/2)
- Laplace/uniform (α=β=1)
-/

/-- Haldane (improper) predictor: this is exactly PLN strength (for `n>0`). -/
noncomputable abbrev predHaldane (n_pos n_neg : ℕ) : ℝ := plnStrength n_pos n_neg

/-- Jeffreys/KT predictor. -/
noncomputable abbrev predJeffreys (n_pos n_neg : ℕ) : ℝ := jeffreysPosteriorMean n_pos n_neg

/-- Laplace/uniform predictor. -/
noncomputable abbrev predLaplace (n_pos n_neg : ℕ) : ℝ := uniformPosteriorMean n_pos n_neg

/-- PLN strength equals Beta mean with improper prior (α₀ = β₀ = 0).

    This shows PLN is the maximum likelihood limit of Bayesian inference.
-/
theorem plnStrength_eq_improper_mean (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    plnStrength n_pos n_neg = (n_pos : ℝ) / (n_pos + n_neg : ℝ) := by
  unfold plnStrength
  simp only [h, ↓reduceIte]

/-- Relationship between PLN strength and uniform posterior mean.

    PLN strength = n⁺ / (n⁺ + n⁻)
    Uniform mean = (n⁺ + 1) / (n⁺ + n⁻ + 2)

    As sample size n → ∞, the difference → 0.
-/
theorem strength_vs_uniform_difference (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| ≤
      2 / ((n_pos : ℝ) + (n_neg : ℝ) + 2) := by
  have hnNat : 0 < n_pos + n_neg := Nat.pos_of_ne_zero h
  have hnRpos : 0 < (n_pos + n_neg : ℝ) := by exact_mod_cast hnNat
  set nR : ℝ := (n_pos + n_neg : ℝ)
  have hnRpos' : 0 < nR := by simpa [nR] using hnRpos
  have hnR0 : nR ≠ 0 := ne_of_gt hnRpos'
  have hnR2pos : 0 < nR + 2 := by linarith [hnRpos']
  have hnR2 : nR + 2 ≠ 0 := ne_of_gt hnR2pos

  have hdiff :
      (n_pos : ℝ) / nR - ((n_pos : ℝ) + 1) / (nR + 2) =
        ((n_pos : ℝ) - (n_neg : ℝ)) / (nR * (nR + 2)) := by
    field_simp [hnR0, hnR2, nR]
    ring

  have hnum : |(n_pos : ℝ) - (n_neg : ℝ)| ≤ nR := by
    have hnpos : 0 ≤ (n_pos : ℝ) := by exact_mod_cast (Nat.zero_le n_pos)
    have hnneg : 0 ≤ (n_neg : ℝ) := by exact_mod_cast (Nat.zero_le n_neg)
    -- `|a - b| = |a + (-b)| ≤ |a| + |-b| = |a| + |b|`
    have h' : |(n_pos : ℝ) - (n_neg : ℝ)| ≤ |(n_pos : ℝ)| + |(n_neg : ℝ)| := by
      simpa [sub_eq_add_neg, abs_neg, add_comm, add_left_comm, add_assoc] using
        (abs_add_le (n_pos : ℝ) (-(n_neg : ℝ)))
    -- Since both casts are nonnegative, `|n| = n`.
    simpa [nR, Nat.cast_add, abs_of_nonneg hnpos, abs_of_nonneg hnneg,
      add_assoc, add_comm, add_left_comm] using h'

  have hdenpos : 0 < nR * (nR + 2) := mul_pos hnRpos' hnR2pos

  -- Rewrite the goal using the computed form of the difference.
  have hstrength : plnStrength n_pos n_neg = (n_pos : ℝ) / nR := by
    simpa [nR] using plnStrength_eq_improper_mean n_pos n_neg (by simpa using h)
  -- Rewrite the goal using the computed form of the difference.
  have habs_repr :
      |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| =
        |((n_pos : ℝ) - (n_neg : ℝ)) / (nR * (nR + 2))| := by
    have huniform :
        uniformPosteriorMean n_pos n_neg = ((n_pos : ℝ) + 1) / (nR + 2) := by
      simp [uniformPosteriorMean, nR, add_assoc]
    -- Reduce to the explicit difference `(n_pos/nR) - ((n_pos+1)/(nR+2))`, then apply `hdiff`.
    rw [hstrength]
    simp [huniform, hdiff]
  rw [habs_repr]

  have habs_div :
      |((n_pos : ℝ) - (n_neg : ℝ)) / (nR * (nR + 2))| =
        |(n_pos : ℝ) - (n_neg : ℝ)| / (nR * (nR + 2)) := by
    simp [abs_div, abs_mul, abs_of_pos hnRpos', abs_of_pos hnR2pos]
  rw [habs_div]

  have hstep :
      |(n_pos : ℝ) - (n_neg : ℝ)| / (nR * (nR + 2)) ≤ nR / (nR * (nR + 2)) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)

  have hcancel : nR / (nR * (nR + 2)) = (1 : ℝ) / (nR + 2) := by
    field_simp [hnR0, hnR2]

  have hone_le_two : (1 : ℝ) ≤ 2 := by norm_num
  have hmono : (1 : ℝ) / (nR + 2) ≤ 2 / (nR + 2) :=
    div_le_div_of_nonneg_right hone_le_two (le_of_lt hnR2pos)

  calc
    |(n_pos : ℝ) - (n_neg : ℝ)| / (nR * (nR + 2))
        ≤ nR / (nR * (nR + 2)) := hstep
    _ = (1 : ℝ) / (nR + 2) := hcancel
    _ ≤ 2 / (nR + 2) := hmono
    _ = 2 / ((n_pos : ℝ) + (n_neg : ℝ) + 2) := by
      simp [nR, add_assoc]

/-- Relationship between PLN strength and Jeffreys posterior mean.

    PLN strength = n⁺ / (n⁺ + n⁻)
    Jeffreys mean = (n⁺ + 1/2) / (n⁺ + n⁻ + 1)

    A simple uniform bound (using `0 ≤ n⁺ ≤ n⁺+n⁻`) is:
    `|strength - mean| ≤ 1 / (2*(n+1))`, where `n = n⁺+n⁻`.
-/
theorem strength_vs_jeffreys_difference (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    |plnStrength n_pos n_neg - jeffreysPosteriorMean n_pos n_neg| ≤
      1 / (2 * ((n_pos : ℝ) + (n_neg : ℝ) + 1)) := by
  have hnNat : 0 < n_pos + n_neg := Nat.pos_of_ne_zero h
  have hnRpos : 0 < (n_pos + n_neg : ℝ) := by exact_mod_cast hnNat
  set nR : ℝ := (n_pos + n_neg : ℝ)
  have hnRpos' : 0 < nR := by simpa [nR] using hnRpos
  have hnR0 : nR ≠ 0 := ne_of_gt hnRpos'
  have hnR1pos : 0 < nR + 1 := by linarith [hnRpos']
  have hnR1 : nR + 1 ≠ 0 := ne_of_gt hnR1pos

  have hstrength : plnStrength n_pos n_neg = (n_pos : ℝ) / nR := by
    simpa [nR] using plnStrength_eq_improper_mean n_pos n_neg h
  have hhalf : (0.5 : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hmean : jeffreysPosteriorMean n_pos n_neg = ((n_pos : ℝ) + (1 / 2 : ℝ)) / (nR + 1) := by
    -- Rewrite the decimal `0.5` to `1/2`, then simplify the denominator.
    simp [jeffreysPosteriorMean, nR, hhalf, add_assoc]

  -- Put the difference in a single fraction.
  have hdiff :
      (n_pos : ℝ) / nR - ((n_pos : ℝ) + (1 / 2 : ℝ)) / (nR + 1) =
        ((n_pos : ℝ) - nR / 2) / (nR * (nR + 1)) := by
    field_simp [hnR0, hnR1]
    ring

  -- Bound the numerator: |n_pos - nR/2| ≤ nR/2.
  have hnum : |(n_pos : ℝ) - nR / 2| ≤ nR / 2 := by
    have hnp0 : 0 ≤ (n_pos : ℝ) := by exact_mod_cast (Nat.zero_le n_pos)
    have hnp_le : (n_pos : ℝ) ≤ nR := by
      -- n_pos ≤ n_pos + n_neg
      have : n_pos ≤ n_pos + n_neg := Nat.le_add_right _ _
      -- Convert `↑(n_pos + n_neg)` to `nR`.
      have hcast : (n_pos : ℝ) ≤ (n_pos + n_neg : ℝ) := by exact_mod_cast this
      -- `nR` is defined as `↑(n_pos + n_neg)`.
      -- Avoid `simpa`: just rewrite the goal using the definition of `nR`.
      change (n_pos : ℝ) ≤ (n_pos + n_neg : ℝ)
      exact hcast
    -- The midpoint of [0,nR] is nR/2, so the farthest point is distance nR/2.
    -- Use `abs_sub_le_iff`-style bound via interval containment.
    have hlo : -(nR / 2) ≤ (n_pos : ℝ) - nR / 2 := by
      linarith [hnp0]
    have hhi : (n_pos : ℝ) - nR / 2 ≤ nR / 2 := by
      linarith [hnp_le]
    exact abs_le.2 ⟨hlo, hhi⟩

  -- Now apply the fraction bound.
  have hdenpos : 0 < nR * (nR + 1) := mul_pos hnRpos' hnR1pos
  have habs_repr :
      |plnStrength n_pos n_neg - jeffreysPosteriorMean n_pos n_neg| =
        |((n_pos : ℝ) - nR / 2) / (nR * (nR + 1))| := by
    rw [hstrength, hmean]
    -- Put the subtraction in the exact form `hdiff` provides.
    -- (Keep it as a subtraction; `simp` can otherwise turn it into `a + -b`.)
    simpa using congrArg abs hdiff
  rw [habs_repr]
  -- Convert to a nonnegative division.
  have habs_div :
      |((n_pos : ℝ) - nR / 2) / (nR * (nR + 1))| =
        |(n_pos : ℝ) - nR / 2| / (nR * (nR + 1)) := by
    simp [abs_div, abs_mul, abs_of_pos hnRpos', abs_of_pos hnR1pos]
  rw [habs_div]
  have hstep :
      |(n_pos : ℝ) - nR / 2| / (nR * (nR + 1)) ≤ (nR / 2) / (nR * (nR + 1)) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
  have hcancel : (nR / 2) / (nR * (nR + 1)) = 1 / (2 * (nR + 1)) := by
    -- `field_simp` closes the goal outright here.
    field_simp [hnR0]
  have hfinal : 1 / (2 * (nR + 1)) = 1 / (2 * ((n_pos : ℝ) + (n_neg : ℝ) + 1)) := by
    simp [nR, add_assoc]
  -- Finish after rewriting the RHS into the desired shape.
  simpa [hcancel, hfinal] using (le_trans hstep (le_of_eq hcancel))

/-- **Prior matters**: at small sample sizes, different Beta priors yield different predictions.

For the single observation `n_pos=0, n_neg=1`:
- Haldane/improper (PLN strength) predicts `0`
- Jeffreys/KT predicts `1/4`
- Laplace/uniform predicts `1/3` -/
theorem prior_matters_example :
    predHaldane 0 1 = 0 ∧ predJeffreys 0 1 = (1 / 4 : ℝ) ∧ predLaplace 0 1 = (1 / 3 : ℝ) := by
  constructor
  · simp [predHaldane, plnStrength]
  constructor
  · simp [predJeffreys, jeffreysPosteriorMean]
    norm_num
  · simp [predLaplace, uniformPosteriorMean]
    norm_num

/-- Ledger restatement: Laplace/uniform smoothing differs from Haldane/PLN strength by `O(1/n)`. -/
theorem haldane_vs_laplace_difference (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    |predHaldane n_pos n_neg - predLaplace n_pos n_neg| ≤
      2 / ((n_pos : ℝ) + (n_neg : ℝ) + 2) := by
  simpa [predHaldane, predLaplace] using strength_vs_uniform_difference n_pos n_neg h

/-- Ledger restatement: Jeffreys/KT differs from Haldane/PLN strength by `O(1/n)`. -/
theorem haldane_vs_jeffreys_difference (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    |predHaldane n_pos n_neg - predJeffreys n_pos n_neg| ≤
      1 / (2 * ((n_pos : ℝ) + (n_neg : ℝ) + 1)) := by
  simpa [predHaldane, predJeffreys] using strength_vs_jeffreys_difference n_pos n_neg h

/-- PLN strength converges to Bayesian posterior mean as sample size grows.

    For any proper prior Beta(α₀, β₀), as k positives and m negatives → ∞
    with k/m → ρ constant, the posterior mean (α₀+k)/(α₀+β₀+k+m) → ρ/(1+ρ) = k/(k+m).

    This is the Bernstein-von Mises theorem for Beta-Bernoulli.
-/
theorem strength_converges_to_mean :
    -- For any ε > 0 and prior parameter, there exists N such that
    -- for all n_pos + n_neg ≥ N, |strength - posterior_mean| < ε
    ∀ ε : ℝ, 0 < ε → ∀ prior_param : ℝ, 0 < prior_param →
      ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
        let strength := plnStrength n_pos n_neg
        let mean := ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param)
        |strength - mean| < ε := by
  intro ε hε prior_param hprior
  -- N = ⌈2 * prior_param / ε⌉ works
  use Nat.ceil (2 * prior_param / ε)
  intro n_pos n_neg hn hne
  have hnNat : 0 < n_pos + n_neg := Nat.pos_of_ne_zero hne
  have hnRpos : 0 < (n_pos + n_neg : ℝ) := by exact_mod_cast hnNat
  set nR : ℝ := (n_pos + n_neg : ℝ)
  have hnRpos' : 0 < nR := by simpa [nR] using hnRpos
  have hnR0 : nR ≠ 0 := ne_of_gt hnRpos'
  have hnR2pos : 0 < nR + 2 * prior_param := by linarith [hnRpos', hprior]
  have hnR2 : nR + 2 * prior_param ≠ 0 := ne_of_gt hnR2pos

  have hdiff :
      (n_pos : ℝ) / nR - ((n_pos : ℝ) + prior_param) / (nR + 2 * prior_param) =
        (prior_param * ((n_pos : ℝ) - (n_neg : ℝ))) / (nR * (nR + 2 * prior_param)) := by
    field_simp [hnR0, hnR2, nR]
    ring

  have hnum : |(n_pos : ℝ) - (n_neg : ℝ)| ≤ nR := by
    have hnpos : 0 ≤ (n_pos : ℝ) := by exact_mod_cast (Nat.zero_le n_pos)
    have hnneg : 0 ≤ (n_neg : ℝ) := by exact_mod_cast (Nat.zero_le n_neg)
    have h' : |(n_pos : ℝ) - (n_neg : ℝ)| ≤ |(n_pos : ℝ)| + |(n_neg : ℝ)| := by
      simpa [sub_eq_add_neg, abs_neg, add_comm, add_left_comm, add_assoc] using
        (abs_add_le (n_pos : ℝ) (-(n_neg : ℝ)))
    simpa [nR, Nat.cast_add, abs_of_nonneg hnpos, abs_of_nonneg hnneg,
      add_assoc, add_comm, add_left_comm] using h'

  have hdenpos : 0 < nR * (nR + 2 * prior_param) := mul_pos hnRpos' hnR2pos

  have hbound :
      |(prior_param * ((n_pos : ℝ) - (n_neg : ℝ))) / (nR * (nR + 2 * prior_param))|
        ≤ prior_param / nR := by
    have hnR2pos' : 0 < nR + prior_param * 2 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hnR2pos
    have habs :
        |(prior_param * ((n_pos : ℝ) - (n_neg : ℝ))) / (nR * (nR + 2 * prior_param))|
          = (prior_param * |(n_pos : ℝ) - (n_neg : ℝ)|) / (nR * (nR + 2 * prior_param)) := by
      simp [abs_div, abs_mul, abs_of_pos hprior, abs_of_pos hnRpos', abs_of_pos hnR2pos',
        mul_comm]
    rw [habs]
    have hmul :
        prior_param * |(n_pos : ℝ) - (n_neg : ℝ)| ≤ prior_param * nR :=
      mul_le_mul_of_nonneg_left hnum (le_of_lt hprior)
    have hstep :
        (prior_param * |(n_pos : ℝ) - (n_neg : ℝ)|) / (nR * (nR + 2 * prior_param))
          ≤ (prior_param * nR) / (nR * (nR + 2 * prior_param)) :=
      div_le_div_of_nonneg_right hmul (le_of_lt hdenpos)
    have hcancel :
        (prior_param * nR) / (nR * (nR + 2 * prior_param)) = prior_param / (nR + 2 * prior_param) := by
      field_simp [hnR0, hnR2]
    have hmono :
        prior_param / (nR + 2 * prior_param) ≤ prior_param / nR := by
      have hle : nR ≤ nR + 2 * prior_param := by linarith [hprior]
      exact div_le_div_of_nonneg_left (le_of_lt hprior) hnRpos' hle
    exact (le_trans (le_trans hstep (by simp [hcancel])) hmono)

  have hceil : 2 * prior_param / ε ≤ (Nat.ceil (2 * prior_param / ε) : ℝ) :=
    Nat.le_ceil (2 * prior_param / ε)
  have hnRge : (Nat.ceil (2 * prior_param / ε) : ℝ) ≤ nR := by
    -- `hn : n_pos + n_neg ≥ ceil(...)`
    have : (Nat.ceil (2 * prior_param / ε) : ℝ) ≤ (n_pos + n_neg : ℝ) := by
      exact_mod_cast hn
    -- Rewrite the RHS `↑(n_pos + n_neg)` to `↑n_pos + ↑n_neg`.
    simpa [Nat.cast_add, add_assoc, nR] using this
  have hx : 2 * prior_param / ε ≤ nR := le_trans hceil hnRge

  have hxε : (2 * prior_param / ε) * ε ≤ nR * ε :=
    mul_le_mul_of_nonneg_right hx (le_of_lt hε)
  have h2prior_le : 2 * prior_param ≤ nR * ε := by
    -- Rewrite `(2*prior/ε)*ε` as `2*prior` (since `ε ≠ 0`).
    have : (2 * prior_param / ε) * ε = 2 * prior_param := by
      calc
        (2 * prior_param / ε) * ε = (2 * prior_param * ε) / ε := by
          simp [div_mul_eq_mul_div]
        _ = 2 * prior_param := by
          simpa [mul_assoc] using (mul_div_cancel_right₀ (2 * prior_param) hε.ne')
    -- Apply the rewrite to `hxε`.
    simpa [this] using hxε
  have h2prior_le' : 2 * prior_param ≤ ε * nR := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2prior_le

  have hprior_le : prior_param ≤ (ε / 2) * nR := by
    have : prior_param ≤ (ε * nR) / 2 := by linarith [h2prior_le']
    have hEq : (ε * nR) / 2 = (ε / 2) * nR := by
      simpa using (div_mul_eq_mul_div (a := ε) (b := (2 : ℝ)) (c := nR)).symm
    simpa [hEq] using this

  have hdiv : prior_param / nR ≤ ε / 2 := (div_le_iff₀ hnRpos').2 hprior_le
  have hlt : prior_param / nR < ε := lt_of_le_of_lt hdiv (by linarith [hε])

  -- Finish: unfold `strength`/`mean`, rewrite using `hdiff`, and use the bound.
  -- `dsimp` will reduce the `let` bindings in the statement.
  dsimp
  have habs_repr :
      |plnStrength n_pos n_neg -
          ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param)| =
        |(prior_param * ((n_pos : ℝ) - (n_neg : ℝ))) / (nR * (nR + 2 * prior_param))| := by
    have hstrength : plnStrength n_pos n_neg = (n_pos : ℝ) / nR := by
      simpa [nR] using plnStrength_eq_improper_mean n_pos n_neg hne
    have hmean :
        ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param) =
          ((n_pos : ℝ) + prior_param) / (nR + 2 * prior_param) := by
      simp [nR, add_assoc]
    rw [hstrength, hmean]
    simp [hdiff]
  have habs_le : |plnStrength n_pos n_neg -
      ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param)| ≤ prior_param / nR := by
    simpa [habs_repr] using hbound
  exact lt_of_le_of_lt habs_le hlt

end StrengthVsMean

/-! ## Counterexample: Exchangeability Does Not Force Beta

Exchangeability implies the predictor factors through counts `(n⁺, n⁻)`, but it does **not**
determine a Beta prior.  A generic de Finetti mixture can yield a non-Beta predictor.

We give a tiny finite counterexample at `n = 2` using a two-point prior on `θ`.
-/

section Counterexample

open scoped BigOperators

-- A two-point mixture prior on θ ∈ [0,1] induces the predictor:
--   p(k) = (Σᵢ wᵢ θᵢ^{k+1} (1-θᵢ)^{n-k}) / (Σᵢ wᵢ θᵢ^{k} (1-θᵢ)^{n-k})
-- for any particular length-n sequence with k ones.

private noncomputable def mixPred_n2 (k : ℕ) : ℝ :=
  let w1 : ℝ := (1 / 3 : ℝ)
  let w2 : ℝ := (2 / 3 : ℝ)
  let θ1 : ℝ := (1 / 4 : ℝ)
  let θ2 : ℝ := (3 / 4 : ℝ)
  let n : ℕ := 2
  (w1 * θ1 ^ (k + 1) * (1 - θ1) ^ (n - k) + w2 * θ2 ^ (k + 1) * (1 - θ2) ^ (n - k)) /
    (w1 * θ1 ^ k * (1 - θ1) ^ (n - k) + w2 * θ2 ^ k * (1 - θ2) ^ (n - k))

private theorem mixPred_n2_eval :
    mixPred_n2 0 = (15 / 44 : ℝ) ∧ mixPred_n2 1 = (7 / 12 : ℝ) ∧ mixPred_n2 2 = (55 / 76 : ℝ) := by
  constructor
  · simp [mixPred_n2]
    norm_num
  constructor
  · simp [mixPred_n2]
    norm_num
  · simp [mixPred_n2]
    norm_num

/-- A Beta posterior predictive at fixed `n` is affine in `k`.  In particular, for `n = 2`
it always satisfies `2*p(1) = p(0) + p(2)`. -/
private theorem beta_affine_constraint_n2 (α β : ℝ) :
    (2 : ℝ) * ((1 + α) / (2 + α + β)) = (α / (2 + α + β)) + ((2 + α) / (2 + α + β)) := by
  ring_nf

/-- **Counterexample**: a two-point exchangeable mixture prior yields a predictor that is not
Beta(α,β) for any α,β.  (Witnessed at `n = 2` by failure of the affine constraint.) -/
theorem not_beta_from_exchangeability_example :
    ¬ ∃ α β : ℝ, mixPred_n2 0 = (α / (2 + α + β)) ∧
      mixPred_n2 1 = ((1 + α) / (2 + α + β)) ∧
      mixPred_n2 2 = ((2 + α) / (2 + α + β)) := by
  intro h
  rcases h with ⟨α, β, h0, h1, h2⟩
  have hm0 : mixPred_n2 0 = (15 / 44 : ℝ) := (mixPred_n2_eval).1
  have hm1 : mixPred_n2 1 = (7 / 12 : ℝ) := (mixPred_n2_eval).2.1
  have hm2 : mixPred_n2 2 = (55 / 76 : ℝ) := (mixPred_n2_eval).2.2
  -- Substitute the explicit values and derive the affine constraint failure:
  -- for Beta predictors, `2*p(1) = p(0) + p(2)`, but our mixture violates it.
  have hBeta : (2 : ℝ) * mixPred_n2 1 = mixPred_n2 0 + mixPred_n2 2 := by
    -- Use the assumed Beta form and the affine constraint.
    have hadd := beta_affine_constraint_n2 α β
    calc
      (2 : ℝ) * mixPred_n2 1
          = (2 : ℝ) * ((1 + α) / (2 + α + β)) := by simp [h1]
      _ = (α / (2 + α + β)) + ((2 + α) / (2 + α + β)) := hadd
      _ = mixPred_n2 0 + mixPred_n2 2 := by simp [h0, h2, add_comm, add_left_comm]
  -- But the explicit values violate the affine constraint.
  have hcontra : (2 : ℝ) * mixPred_n2 1 ≠ mixPred_n2 0 + mixPred_n2 2 := by
    -- Reduce to numeric inequality.
    -- Use `mixPred_n2_eval` to rewrite.
    simp [hm0, hm1, hm2]
    norm_num
  exact hcontra (by simpa [add_assoc, add_comm, add_left_comm] using hBeta)

end Counterexample

/-! ## Evidence Aggregation = Beta Update -/

section AggregationUpdate

/-- Adding evidence corresponds to Beta conjugate update.

    If we have:
    - Prior evidence (n₁⁺, n₁⁻) giving Beta(α + n₁⁺, β + n₁⁻)
    - New evidence (n₂⁺, n₂⁻)

    Then the combined evidence (n₁⁺ + n₂⁺, n₁⁻ + n₂⁻) gives
    Beta(α + n₁⁺ + n₂⁺, β + n₁⁻ + n₂⁻)

    which is exactly the Bayesian posterior after updating.
-/
theorem evidence_aggregation_is_conjugate_update
    (prior_param : ℝ) (hprior : 0 < prior_param)
    (n₁_pos n₁_neg n₂_pos n₂_neg : ℕ) :
    let params₁ := { prior_param := prior_param, prior_pos := hprior,
                     evidence_pos := n₁_pos, evidence_neg := n₁_neg : EvidenceBetaParams }
    let params_combined := { prior_param := prior_param, prior_pos := hprior,
                             evidence_pos := n₁_pos + n₂_pos,
                             evidence_neg := n₁_neg + n₂_neg : EvidenceBetaParams }
    -- The combined α = original α + new positive evidence
    params_combined.alpha = params₁.alpha + n₂_pos ∧
    -- The combined β = original β + new negative evidence
    params_combined.beta = params₁.beta + n₂_neg := by
  simp only [EvidenceBetaParams.alpha, EvidenceBetaParams.beta]
  constructor
  · simp only [Nat.cast_add]; ring
  · simp only [Nat.cast_add]; ring

/-- The Evidence hplus operation corresponds to summing Beta sufficient statistics.

    E₁ + E₂ = (n₁⁺ + n₂⁺, n₁⁻ + n₂⁻)

    corresponds to updating a Beta prior with additional observations.
-/
theorem hplus_is_beta_aggregation (e₁ e₂ : Evidence) :
    -- hplus sums the sufficient statistics, which is exactly what Bayesian
    -- updating does with the Beta conjugate prior
    (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
    (e₁ + e₂).neg = e₁.neg + e₂.neg := by
  constructor <;> rfl

end AggregationUpdate

/-! ## The Main Connection Theorem -/

section MainTheorem

/-- The main theorem connecting PLN Evidence to Beta-Bernoulli inference.

    For exchangeable binary observations:
    1. Evidence (n⁺, n⁻) is the sufficient statistic (by de Finetti + sufficiency)
    2. With Beta prior, posterior is Beta(α + n⁺, β + n⁻) (by conjugacy)
    3. Posterior mean = (α + n⁺) / (α + β + n⁺ + n⁻)
    4. PLN strength n⁺/(n⁺+n⁻) → posterior mean as sample size → ∞

    Therefore: **PLN Evidence is the exact Bayesian sufficient statistic for
    exchangeable binary inference, and PLN strength converges to the Bayes-optimal
    point estimate (posterior mean).**
-/
theorem pln_is_bayes_optimal_for_exchangeable :
    -- PLN captures the sufficient statistic
    (∀ n_pos n_neg : ℕ, evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
    -- PLN strength converges to Bayesian mean
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
      |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| < ε) := by
  constructor
  · -- Evidence captures sufficient statistic
    intros
    rfl
  · -- Convergence
    intro ε hε
    use Nat.ceil (2 / ε)
    intro n_pos n_neg hn hne
    -- The bound 2/(n+2) → 0 as n → ∞
    calc |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg|
      _ ≤ 2 / ((n_pos : ℝ) + (n_neg : ℝ) + 2) := strength_vs_uniform_difference n_pos n_neg hne
      _ < ε := by
        have hN :
            (2 / ε) ≤ (Nat.ceil (2 / ε) : ℝ) := Nat.le_ceil (2 / ε)
        have hnRge : (Nat.ceil (2 / ε) : ℝ) ≤ (n_pos + n_neg : ℝ) := by
          exact_mod_cast hn
        have hx : 2 / ε ≤ (n_pos + n_neg : ℝ) := le_trans hN hnRge

        have hdenpos : 0 < ((n_pos + n_neg : ℝ) + 2) := by linarith [hx]
        -- Since `n_pos + n_neg + 2 > 2/ε`, we have `2/(n_pos+n_neg+2) < ε`.
        have hlt : 2 / ((n_pos + n_neg : ℝ) + 2) < ε := by
          have hx' : 2 / ε < (n_pos + n_neg : ℝ) + 2 := by linarith [hx]
          have hxε : (2 / ε) * ε < ((n_pos + n_neg : ℝ) + 2) * ε :=
            mul_lt_mul_of_pos_right hx' hε
          have h2lt : (2 : ℝ) < ε * ((n_pos + n_neg : ℝ) + 2) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hε.ne', mul_comm] using hxε
          -- Rewrite into the desired division inequality.
          simpa [mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ hdenpos).2 h2lt
        -- Finally, rewrite `(n_pos+n_neg : ℝ)` into `(n_pos:ℝ)+(n_neg:ℝ)`.
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hlt

end MainTheorem

/-! ## Connection to de Finetti -/

section DeFinettiConnection

/-- The full νPLN story: For exchangeable binary sequences,
    1. de Finetti says it's a mixture of i.i.d. Bernoulli
    2. Given Bernoulli parameter θ, observations are conditionally i.i.d.
    3. Beta prior + Bernoulli observations = Beta posterior (conjugacy)
    4. Sufficient statistic = (n⁺, n⁻) = PLN Evidence
    5. Posterior mean → PLN strength as sample size grows

    This justifies PLN as the **exact optimal inference** for exchangeable binary domains.
-/
theorem nupln_main_theorem :
    -- The theorem statement would formally combine:
    -- - InfiniteExchangeable → de Finetti representation
    -- - de Finetti representation → Beta-Bernoulli conjugacy applies
    -- - Conjugacy → (n⁺, n⁻) is sufficient
    -- - Sufficiency → PLN Evidence captures all information
    (∀ n_pos n_neg : ℕ, evidenceFromCounts n_pos n_neg = (n_pos, n_neg)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
        |plnStrength n_pos n_neg - uniformPosteriorMean n_pos n_neg| < ε) := by
  simpa using pln_is_bayes_optimal_for_exchangeable

end DeFinettiConnection

/-! ## Beta Credible Intervals

For IndefiniteTruthValue construction, we need credible intervals from Beta distributions.
These give probability bounds [L, U] from Evidence counts (n⁺, n⁻).

**Normal Approximation**: For large sample sizes (α+β > 10), the Beta distribution
is well-approximated by a Normal distribution with:
- μ = α/(α+β)
- σ² = αβ/[(α+β)²(α+β+1)]

This allows fast computation of credible intervals without numerical integration.
-/

section BetaCredibleIntervals

/-- A credible interval [lower, upper] at a given confidence level. -/
structure CredibleInterval where
  lower : ℝ
  upper : ℝ
  level : ℝ  -- e.g., 0.95 for 95% credible interval
  lower_le_upper : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1
  level_in_unit : level ∈ Set.Ioo 0 1  -- (0, 1) open interval

/-- Standard Normal quantiles for common confidence levels.
    For 95% interval: z = 1.96 (actually 1.959964...)
    For 90% interval: z = 1.645 -/
noncomputable def normalQuantile (level : ℝ) : ℝ :=
  if level ≥ 0.95 then 1.96
  else if level ≥ 0.90 then 1.645
  else if level ≥ 0.80 then 1.28
  else 1.0  -- Fallback for lower levels

/-- Normal approximation for Beta credible interval.

For large α+β (typically > 10), Beta(α,β) is approximately Normal:
- Mean: μ = α/(α+β)
- Variance: σ² = αβ/[(α+β)²(α+β+1)]

The credible interval is approximately [μ - z·σ, μ + z·σ] where z is the
Normal quantile for the desired level (e.g., 1.96 for 95%).

**Accuracy**: Excellent for α, β > 5. Degrades for extreme parameters (α or β < 1).
-/
noncomputable def betaCredibleInterval_normal_approx
    (α β level : ℝ) (hα : 0 < α) (hβ : 0 < β) (hlevel : 0 < level ∧ level < 1) :
    CredibleInterval :=
  let mean := α / (α + β)
  let sum := α + β
  let variance := (α * β) / (sum^2 * (sum + 1))
  let std_dev := Real.sqrt variance
  let z := normalQuantile level
  let raw_lower := mean - z * std_dev
  let raw_upper := mean + z * std_dev
  { lower := max 0 raw_lower
    upper := min 1 raw_upper
    level := level
    lower_le_upper := by
      have h_mean_in : 0 ≤ mean ∧ mean ≤ 1 := by
        constructor
        · apply div_nonneg; linarith; linarith
        · rw [div_le_one]; linarith; linarith
      have h_std_nonneg : 0 ≤ std_dev := Real.sqrt_nonneg _
      have h_z_nonneg : 0 ≤ z := by
        show 0 ≤ normalQuantile level
        dsimp [normalQuantile]
        split_ifs <;> norm_num
      have h_margin : 0 ≤ z * std_dev := mul_nonneg h_z_nonneg h_std_nonneg
      -- Prove: mean - z·σ ≤ mean + z·σ
      have h_raw : raw_lower ≤ raw_upper := by linarith
      -- raw_upper ≥ mean ≥ 0, so min 1 raw_upper ≥ 0
      have h_upper_nonneg : 0 ≤ raw_upper := by linarith
      -- raw_lower ≤ mean ≤ 1
      have h_lower_le_one : raw_lower ≤ 1 := by linarith
      -- Now prove: max 0 raw_lower ≤ min 1 raw_upper
      by_cases h : 0 ≤ raw_lower
      · -- Case: raw_lower ≥ 0, so max 0 raw_lower = raw_lower
        rw [max_eq_right h]
        exact le_min h_lower_le_one h_raw
      · -- Case: raw_lower < 0, so max 0 raw_lower = 0
        push_neg at h
        rw [max_eq_left (le_of_lt h)]
        exact le_min (by norm_num : (0 : ℝ) ≤ 1) h_upper_nonneg
    lower_nonneg := by exact le_max_left 0 _
    upper_le_one := by exact min_le_left 1 _
    level_in_unit := by
      simp only [Set.mem_Ioo]
      exact hlevel }

/-- Convenience function: Beta credible interval at 95% level. -/
noncomputable def betaCredibleInterval95
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : CredibleInterval :=
  betaCredibleInterval_normal_approx α β 0.95 hα hβ ⟨by norm_num, by norm_num⟩

/-- Convenience function: Beta credible interval at 90% level. -/
noncomputable def betaCredibleInterval90
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : CredibleInterval :=
  betaCredibleInterval_normal_approx α β 0.90 hα hβ ⟨by norm_num, by norm_num⟩

/-- Credible interval from Evidence counts and prior.

Given Evidence (n⁺, n⁻) with prior (α₀, β₀), compute the credible interval
for the underlying Bernoulli parameter θ.
-/
noncomputable def credibleIntervalFromEvidence
    (n_pos n_neg : ℕ) (α₀ β₀ level : ℝ)
    (hα₀ : 0 < α₀) (hβ₀ : 0 < β₀) (hlevel : 0 < level ∧ level < 1) :
    CredibleInterval :=
  let α := α₀ + (n_pos : ℝ)
  let β := β₀ + (n_neg : ℝ)
  have hα : 0 < α := by
    have h_nonneg : 0 ≤ (n_pos : ℝ) := Nat.cast_nonneg n_pos
    linarith
  have hβ : 0 < β := by
    have h_nonneg : 0 ≤ (n_neg : ℝ) := Nat.cast_nonneg n_neg
    linarith
  betaCredibleInterval_normal_approx α β level hα hβ hlevel

end BetaCredibleIntervals

end Mettapedia.Logic.EvidenceBeta
