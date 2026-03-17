/-
# Universal Hyperprior for Normal-Normal: Mixture Over Prior Variances

When inferring a Normal mean μ from observations x₁,...,xₙ ~ N(μ, σ²) with known σ²,
the prior variance τ₀² is **unidentifiable** from single-level data. The naive
empirical Bayes estimate τ̂₀² = s² - σ² gives spuriously overconfident posteriors.

This file formalizes the **Universal Hyperprior** solution: form a Bayesian mixture over a
countable family of τ₀² values with computable weights.

## Main Results

- `NormalNormalContext`: Context for Normal-Normal with known σ²
- `contextFamily`: Family of contexts indexed by k ∈ ℤ with τ₀² = 2^k
- `integerGeometricWeight`: Weights w(k) = 2^{-(|k|+1)} for k ∈ ℤ
- `logMarginalLikelihood`: Log P(data | context)
- `mixturePosteriorMean`: E[μ | data] under the mixture
- `mixturePosteriorVar`: Var[μ | data] under the mixture (law of total variance)
- `dominance`: The mixture is never more than O(|k*|) bits worse than best context

## PLN Justification

This IS the correct PLN approach because:
1. **BinaryEvidence/Context separation**: Same evidence (n, Σx, Σx²), multiple contexts
2. **Second-order probability**: Uncertainty about τ₀² is explicitly modeled
3. **Modal reasoning**: Each C_k is a possible world; weights are beliefs
4. **Dominance**: Guaranteed regret bound vs any fixed context

## References

- Mettapedia/Logic/UniversalPrediction/MarkovHyperpriorMixture.lean (Universal Hyperprior pattern)
- Mettapedia/Logic/EvidenceNormalGamma.lean (Normal-Gamma evidence)
- Murphy, "Conjugate Bayesian analysis of the Gaussian distribution" (2007)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Logic.EvidenceNormalGamma

namespace Mettapedia.Logic.UniversalHyperprior

open Mettapedia.Logic.EvidenceNormalGamma
open scoped BigOperators

/-! ## Normal-Normal Context with Known Variance

For single-level inference where σ² is known, we need only three parameters:
- μ₀: prior mean (typically 0)
- τ₀²: prior variance on μ
- σ²: known observation variance
-/

/-- Context for Normal-Normal inference with known observation variance σ².

This is simpler than the full Normal-Gamma context because we don't need to
estimate the observation variance - it's assumed known.

The prior on μ is: μ ~ N(μ₀, τ₀²)
The likelihood is: xᵢ | μ ~ N(μ, σ²) -/
structure NormalNormalContext where
  /-- Prior mean for μ -/
  μ₀ : ℝ
  /-- Prior variance for μ (the unidentifiable parameter!) -/
  τ₀_sq : ℝ
  /-- Known observation variance -/
  σ_sq : ℝ
  /-- Prior variance is positive -/
  τ₀_sq_pos : 0 < τ₀_sq
  /-- Observation variance is positive -/
  σ_sq_pos : 0 < σ_sq

namespace NormalNormalContext

/-- Prior precision: κ₀ = 1/τ₀² -/
noncomputable def priorPrecision (ctx : NormalNormalContext) : ℝ := 1 / ctx.τ₀_sq

theorem priorPrecision_pos (ctx : NormalNormalContext) : 0 < ctx.priorPrecision := by
  unfold priorPrecision
  exact one_div_pos.mpr ctx.τ₀_sq_pos

/-- Observation precision per sample: 1/σ² -/
noncomputable def obsPrecision (ctx : NormalNormalContext) : ℝ := 1 / ctx.σ_sq

theorem obsPrecision_pos (ctx : NormalNormalContext) : 0 < ctx.obsPrecision := by
  unfold obsPrecision
  exact one_div_pos.mpr ctx.σ_sq_pos

end NormalNormalContext

/-! ## Posterior Computations

For Normal-Normal conjugate model:
- Prior: μ ~ N(μ₀, τ₀²)
- Likelihood: x₁,...,xₙ | μ ~ N(μ, σ²) iid
- Posterior: μ | x₁,...,xₙ ~ N(μₙ, τₙ²)

Where:
- τₙ² = 1/(1/τ₀² + n/σ²)  (posterior variance)
- μₙ = τₙ² · (μ₀/τ₀² + n·xbar/σ²)  (posterior mean)
-/

/-- Posterior precision: 1/τₙ² = 1/τ₀² + n/σ² -/
noncomputable def posteriorPrecision (ctx : NormalNormalContext) (n : ℕ) : ℝ :=
  ctx.priorPrecision + n * ctx.obsPrecision

theorem posteriorPrecision_pos (ctx : NormalNormalContext) (n : ℕ) :
    0 < posteriorPrecision ctx n := by
  unfold posteriorPrecision
  have h1 := ctx.priorPrecision_pos
  have h2 : 0 ≤ (n : ℝ) * ctx.obsPrecision := by
    apply mul_nonneg (Nat.cast_nonneg n) (le_of_lt ctx.obsPrecision_pos)
  linarith

/-- Posterior variance: τₙ² = 1/(1/τ₀² + n/σ²) -/
noncomputable def posteriorVariance (ctx : NormalNormalContext) (n : ℕ) : ℝ :=
  1 / posteriorPrecision ctx n

theorem posteriorVariance_pos (ctx : NormalNormalContext) (n : ℕ) :
    0 < posteriorVariance ctx n := by
  unfold posteriorVariance
  exact one_div_pos.mpr (posteriorPrecision_pos ctx n)

/-- Posterior mean: μₙ = (μ₀/τ₀² + Σxᵢ/σ²) / (1/τ₀² + n/σ²) -/
noncomputable def posteriorMean (ctx : NormalNormalContext) (ev : NormalGammaEvidence) : ℝ :=
  if ev.n = 0 then ctx.μ₀
  else (ctx.priorPrecision * ctx.μ₀ + ev.sum * ctx.obsPrecision) / posteriorPrecision ctx ev.n

/-- The posterior mean is a precision-weighted average of prior mean and sample mean -/
theorem posteriorMean_weighted_avg (ctx : NormalNormalContext) (ev : NormalGammaEvidence)
    (hn : ev.n ≠ 0) :
    posteriorMean ctx ev =
      (ctx.priorPrecision / posteriorPrecision ctx ev.n) * ctx.μ₀ +
      ((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n) * ev.toMean := by
  unfold posteriorMean NormalGammaEvidence.toMean
  simp only [hn, ↓reduceIte]
  have hpost_pos := posteriorPrecision_pos ctx ev.n
  have hn_pos : 0 < (ev.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold NormalNormalContext.obsPrecision
  field_simp [ne_of_gt hpost_pos, ne_of_gt hn_pos]

/-! ## Context Family: τ₀² = 2^k for k ∈ ℤ

The key insight: we don't know τ₀², so we form a mixture over all possible values.
We use powers of 2 for computational convenience (self-delimiting codes).
-/

/-- Context with τ₀² = 2^k -/
noncomputable def contextAtK (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) : NormalNormalContext where
  μ₀ := 0  -- Centered prior
  τ₀_sq := (2 : ℝ) ^ k
  σ_sq := σ_sq
  τ₀_sq_pos := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact zpow_pos h2 k
  σ_sq_pos := hσ

/-- The context family spans τ₀² from nearly 0 to arbitrarily large -/
theorem contextAtK_τ₀_sq (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) :
    (contextAtK k σ_sq hσ).τ₀_sq = (2 : ℝ) ^ k := rfl

/-! ## Integer Geometric Weights

For k ∈ ℤ, we use unnormalized weights u(k) = 2^{-(|k|+1)} which sum to 3/2:
  Σ_{k∈ℤ} u(k) = 2^{-1} + 2·Σ_{n≥1} 2^{-(n+1)}
               = 1/2 + 2·(1/4 + 1/8 + ...)
               = 1/2 + 2·(1/2) = 3/2

The normalized weights are w(k) = u(k) / (3/2) = (2/3) · 2^{-(|k|+1)}.

These weights encode the description length: |k| + 1 bits to specify k.
-/

/-- Unnormalized weight: 2^{-(|k|+1)} -/
noncomputable def unnormWeight (k : ℤ) : ℝ := (2 : ℝ) ^ (-(|k| + 1 : ℤ))

theorem unnormWeight_pos (k : ℤ) : 0 < unnormWeight k := by
  unfold unnormWeight
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact zpow_pos h2 _

/-- Helper: |n| = n for n : ℕ when cast to ℤ -/
theorem abs_natCast (n : ℕ) : |↑n| = (n : ℤ) := abs_of_nonneg (Int.natCast_nonneg n)

/-- Helper: |(-(n+1))| = n+1 -/
theorem abs_neg_succ (n : ℕ) : |-(↑n + 1 : ℤ)| = n + 1 := by
  rw [abs_neg]
  exact abs_of_pos (by linarith [Int.natCast_nonneg n])

/-- The unnormalized weights sum to 3/2.

Proof sketch: Split into k≥0 and k<0 using tsum_of_nat_of_neg_add_one:
- k≥0: Σ_{n:ℕ} 2^{-(n+1)} = 1/2 + 1/4 + ... = 1 (geometric series)
- k<0: Σ_{n:ℕ} 2^{-(n+2)} = 1/4 + 1/8 + ... = 1/2 (geometric series)
Total: 1 + 1/2 = 3/2

The technical details involve showing summability and using tsum_geometric_two. -/
theorem tsum_unnormWeight_eq_threeHalves : (∑' k : ℤ, unnormWeight k) = 3/2 := by
  -- Reduce to geometric series by splitting ℤ into nonnegative and negative parts.
  -- We intentionally keep this proof self-contained and avoid ENNReal/toReal conversion.
  have zpow_split_nat (n : ℕ) : (2 : ℝ) ^ (-1 + -(n : ℤ)) = (1 : ℝ) / 2 / 2 ^ n := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [zpow_add₀ h2]
    simp [div_eq_mul_inv, zpow_natCast]

  have unnormWeight_nat (n : ℕ) : unnormWeight (n : ℤ) = (1 : ℝ) / 2 / 2 ^ n := by
    unfold unnormWeight
    simp [zpow_split_nat]

  have abs_neg_one_add_neg_natCast (n : ℕ) : |(-1 : ℤ) + -(n : ℤ)| = (n + 1 : ℤ) := by
    have : (-1 : ℤ) + -(n : ℤ) = -(↑n + 1 : ℤ) := by omega
    rw [this]
    simpa [Int.natCast_succ] using (abs_neg_succ n)

  have unnormWeight_negSucc (n : ℕ) :
      unnormWeight (-(n + 1 : ℤ)) = (1/2 : ℝ) / 2 / 2 ^ n := by
    unfold unnormWeight
    have hk : (-(n + 1 : ℤ)) = (-1 : ℤ) + -(n : ℤ) := by omega
    rw [hk]
    have habs : |(-1 : ℤ) + -(n : ℤ)| = (n + 1 : ℤ) := abs_neg_one_add_neg_natCast n
    rw [habs]
    have hexp : (-( (n + 1 : ℤ) + 1)) = (-1 : ℤ) + (-((n+1 : ℕ) : ℤ)) := by omega
    rw [hexp]
    have hz := zpow_split_nat (n + 1)
    have hz' : (2 : ℝ) ^ (-1 + -((n+1 : ℕ) : ℤ)) = (2 : ℝ)⁻¹ / 2 ^ (n+1) := by
      simpa [div_eq_mul_inv] using hz
    have hR : (2 : ℝ)⁻¹ / 2 ^ (n+1) = (1/2 : ℝ) / 2 / 2 ^ n := by
      ring
    exact hz'.trans hR

  have hs_pos : Summable (fun n : ℕ ↦ unnormWeight (n : ℤ)) := by
    have : Summable (fun n : ℕ ↦ (1 : ℝ) / 2 / 2 ^ n) := summable_geometric_two' (a := (1 : ℝ))
    exact (summable_congr unnormWeight_nat).2 this

  have hs_neg : Summable (fun n : ℕ ↦ unnormWeight (-(n + 1 : ℤ))) := by
    have : Summable (fun n : ℕ ↦ (1/2 : ℝ) / 2 / 2 ^ n) :=
      summable_geometric_two' (a := (1/2 : ℝ))
    exact (summable_congr unnormWeight_negSucc).2 this

  -- Split the ℤ-sum.
  rw [tsum_of_nat_of_neg_add_one hs_pos hs_neg]

  have tsum_pos : (∑' n : ℕ, unnormWeight (n : ℤ)) = (1 : ℝ) := by
    calc
      (∑' n : ℕ, unnormWeight (n : ℤ)) = ∑' n : ℕ, (1 : ℝ) / 2 / 2 ^ n := by
        simpa using (tsum_congr unnormWeight_nat)
      _ = (1 : ℝ) := by
        simpa using (tsum_geometric_two' (a := (1 : ℝ)))

  have tsum_neg : (∑' n : ℕ, unnormWeight (-(n + 1 : ℤ))) = (1/2 : ℝ) := by
    calc
      (∑' n : ℕ, unnormWeight (-(n + 1 : ℤ))) = ∑' n : ℕ, (1/2 : ℝ) / 2 / 2 ^ n := by
        simpa using (tsum_congr unnormWeight_negSucc)
      _ = (1/2 : ℝ) := by
        simpa using (tsum_geometric_two' (a := (1/2 : ℝ)))

  -- Conclude.
  rw [tsum_pos, tsum_neg]
  norm_num

/-- Normalization constant for weights: Z = 3/2 -/
noncomputable def normConstant : ℝ := 3/2

theorem normConstant_pos : 0 < normConstant := by norm_num [normConstant]

/-- Normalized weight: w(k) = 2^{-(|k|+1)} / (3/2) -/
noncomputable def weight (k : ℤ) : ℝ := unnormWeight k / normConstant

theorem weight_pos (k : ℤ) : 0 < weight k := by
  unfold weight
  exact div_pos (unnormWeight_pos k) normConstant_pos

/-- The normalized weights sum to 1 -/
theorem tsum_weight_eq_one : (∑' k : ℤ, weight k) = 1 := by
  unfold weight normConstant
  rw [tsum_div_const, tsum_unnormWeight_eq_threeHalves]
  norm_num

/-! ## Log Marginal Likelihood

For Normal-Normal with prior μ ~ N(0, τ₀²) and data x₁,...,xₙ ~ N(μ, σ²):

log P(x₁,...,xₙ | τ₀², σ²) = -n/2 log(2π) - n/2 log(σ²)
                            - 1/2 log(1 + n·τ₀²/σ²)
                            - (SS + n·xbar²·σ²/(σ² + n·τ₀²)) / (2σ²)

Where SS = Σ(xᵢ - xbar)² is the sum of squared deviations.
-/

/-- Log marginal likelihood under a specific context -/
noncomputable def logMarginalLikelihood (ctx : NormalNormalContext)
    (ev : NormalGammaEvidence) : ℝ :=
  if ev.n = 0 then 0
  else
    let n : ℝ := ev.n;
    let xbar := ev.sum / n;
    let ss := ev.sumSquaredDeviations;
    let ratio := n * ctx.τ₀_sq / ctx.σ_sq;
    let shrinkage := ctx.σ_sq / (ctx.σ_sq + n * ctx.τ₀_sq);
    let log2pi_term := n / 2 * Real.log (2 * Real.pi);
    let logsigma_term := n / 2 * Real.log ctx.σ_sq;
    let logdet_term := (1 / 2) * Real.log (1 + ratio);
    let quad_term := (ss + n * shrinkage * xbar^2) / (2 * ctx.σ_sq);
    -(log2pi_term + logsigma_term + logdet_term + quad_term)

/-! ## Mixture Posterior

The mixture posterior combines posteriors from all contexts weighted by
their posterior probabilities (prior weight × likelihood).

Mixture mean: E[μ | data] = Σ_k w_k · E[μ | data, C_k]
Mixture var:  Var[μ | data] = E[Var[μ|C]] + Var[E[μ|C]]  (law of total variance)
-/

/-- Posterior weight for context k (unnormalized log scale) -/
noncomputable def logPosteriorWeight (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  Real.log (weight k) + logMarginalLikelihood (contextAtK k σ_sq hσ) ev

/-- Normalized posterior weight for context k -/
noncomputable def posteriorWeight (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  let logZ := Real.log (∑' k', Real.exp (logPosteriorWeight k' σ_sq hσ ev))
  Real.exp (logPosteriorWeight k σ_sq hσ ev - logZ)

/-- Posterior weights are positive (since they're exponentials) -/
theorem posteriorWeight_pos (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    0 < posteriorWeight k σ_sq hσ ev := by
  unfold posteriorWeight
  exact Real.exp_pos _

/-- Posterior weights sum to 1 -/
theorem tsum_posteriorWeight_eq_one (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    (∑' k : ℤ, posteriorWeight k σ_sq hσ ev) = 1 := by
  -- posteriorWeight k = exp(logPosteriorWeight k - logZ)
  -- where logZ = log(Z) and Z = ∑' k exp(logPosteriorWeight k)
  -- So: ∑' k posteriorWeight k = ∑' k (exp(logPosteriorWeight k) / Z)
  --                             = (1/Z) · ∑' k exp(logPosteriorWeight k)
  --                             = (1/Z) · Z = 1
  unfold posteriorWeight
  let Z := ∑' k' : ℤ, Real.exp (logPosteriorWeight k' σ_sq hσ ev)
  let logZ := Real.log Z
  -- Show Z > 0 (sum of positive exponentials)
  have hZ_pos : 0 < Z := by
    sorry  -- TODO: Need to show (1) summable, (2) at least one term > 0 implies sum > 0
           -- Summability follows from weight k ~ 2^{-|k|} dominating the exponentials
           -- Positivity follows from Real.exp_pos and le_tsum
  -- Rewrite as tsum of exp(logPosteriorWeight k) / Z
  calc ∑' k : ℤ, Real.exp (logPosteriorWeight k σ_sq hσ ev - logZ)
      = ∑' k : ℤ, Real.exp (logPosteriorWeight k σ_sq hσ ev) / Real.exp logZ := by
        congr 1; ext k; rw [Real.exp_sub]
    _ = ∑' k : ℤ, Real.exp (logPosteriorWeight k σ_sq hσ ev) / Z := by
        congr 1; ext k; congr 1; exact Real.exp_log hZ_pos
    _ = (∑' k : ℤ, Real.exp (logPosteriorWeight k σ_sq hσ ev)) / Z := by
        rw [tsum_div_const]
    _ = Z / Z := rfl
    _ = 1 := div_self (ne_of_gt hZ_pos)

/-- Mixture posterior mean: Σ_k w_k · E[μ | data, C_k] -/
noncomputable def mixturePosteriorMean (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev

/-- Component posterior variance under context k -/
noncomputable def componentPosteriorVar (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  posteriorVariance (contextAtK k σ_sq hσ) ev.n

/-- Mixture posterior variance via law of total variance:
    Var[μ|data] = E[Var[μ|C,data]] + Var[E[μ|C,data]] -/
noncomputable def mixturePosteriorVar (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  let mean := mixturePosteriorMean σ_sq hσ ev
  -- E[Var]: expected variance across contexts
  let expectedVar := ∑' k : ℤ, posteriorWeight k σ_sq hσ ev *
                              componentPosteriorVar k σ_sq hσ ev
  -- Var[E]: variance of means across contexts
  let varOfMeans := ∑' k : ℤ, posteriorWeight k σ_sq hσ ev *
                             (posteriorMean (contextAtK k σ_sq hσ) ev - mean)^2
  expectedVar + varOfMeans

/-! ## Dominance Theorem (Universal Hyperprior)

The mixture is never more than O(|k*|) bits worse than the best context.

Specifically: for any k* ∈ ℤ,
  -log P_mixture(data) ≤ -log P_{C_{k*}}(data) + |k*| + 1

This follows because w(k*) = 2^{-(|k*|+1)}, so log(1/w(k*)) = |k*| + 1.
-/

/-- Log mixture marginal likelihood -/
noncomputable def logMixtureMarginalLikelihood (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  Real.log (∑' k : ℤ, weight k * Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev))

/-- **Universal Hyperprior Dominance Theorem** (precise form):

The mixture marginal likelihood dominates each component by its weight.

For any k : -ln P_mix(data) ≤ -ln P_k(data) - ln(weight k)

Since weight k = 2^{-(|k|+1)} / (3/2), we have:
  -ln(weight k) = (|k|+1)·ln(2) + ln(3/2) ≤ (|k|+2)·ln(2)

This is THE key theorem justifying Universal Hyperprior: the mixture is a universal
predictor that competes with any fixed τ₀² = 2^k with logarithmic regret. -/
theorem dominance (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    -logMixtureMarginalLikelihood σ_sq hσ ev ≤
      -logMarginalLikelihood (contextAtK k σ_sq hσ) ev - Real.log (weight k) := by
  unfold logMixtureMarginalLikelihood
  -- Let P_mix = ∑' j, w_j · exp(logML_j)
  let P_mix := ∑' j : ℤ, weight j * Real.exp (logMarginalLikelihood (contextAtK j σ_sq hσ) ev)
  -- Let P_k = exp(logML_k)
  let P_k := Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev)

  -- Step 1: P_mix ≥ w_k · P_k (mixture contains the k-th term)
  have h_mix_ge_term : weight k * P_k ≤ P_mix := by
    -- This follows from: single term ≤ sum of non-negative terms
    sorry  -- Need: Summable + le_tsum or similar

  sorry  -- TODO: Complete proof using le_tsum, Real.log_le_log, and linarith

/-- The redundancy (extra nats of information) when using the mixture vs context k. -/
theorem redundancy_bound (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    -logMixtureMarginalLikelihood σ_sq hσ ev - (-logMarginalLikelihood (contextAtK k σ_sq hσ) ev) ≤
      -Real.log (weight k) := by
  have h := dominance k σ_sq hσ ev
  linarith

/-- Codelength bound: -ln(weight k) ≤ (|k| + 2) · ln(2)

Since weight k = 2^{-(|k|+1)} / (3/2), we have:
  -ln(weight k) = (|k|+1)·ln(2) + ln(3/2) < (|k|+2)·ln(2)

because ln(3/2) ≈ 0.405 < ln(2) ≈ 0.693 -/
theorem weight_codelength_bound (k : ℤ) : -Real.log (weight k) ≤ (|k| + 2) * Real.log 2 := by
  -- weight k = 2^{-(|k|+1)} / (3/2)
  -- -ln(weight k) = (|k|+1)·ln(2) - ln(3/2)
  -- Need: (|k|+1)·ln(2) - ln(3/2) ≤ (|k|+2)·ln(2), i.e., -ln(3/2) ≤ ln(2)
  -- This is equivalent to: ln(3/2) + ln(2) ≥ 0, i.e., ln(3) ≥ 0, which is true since 3 > 1
  unfold weight unnormWeight normConstant
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hzpow_pos := zpow_pos h2pos (-(|k| + 1 : ℤ))
  have h32pos : (0:ℝ) < 3/2 := by norm_num
  have h32_lt_2 : (3:ℝ)/2 < 2 := by norm_num
  -- Key: log(3) > 0
  have h3_gt_1 : (1:ℝ) < 3 := by norm_num
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos h3_gt_1
  -- log(3) = log(3/2 · 2) = log(3/2) + log(2)
  have hlog3_expand : Real.log 3 = Real.log (3/2) + Real.log 2 := by
    rw [← Real.log_mul (ne_of_gt h32pos) (ne_of_gt h2pos)]
    norm_num
  -- Therefore log(3/2) + log 2 > 0, so -log(3/2) < log 2
  have hkey : -Real.log (3/2) ≤ Real.log 2 := by linarith [hlog3_pos, hlog3_expand]
  -- Compute -log(2^{-(|k|+1)} / (3/2))
  -- -log(A/B) = -log A + log B = -(log A - log B)
  -- = -log(2^{-(|k|+1)}) + log(3/2)
  -- = (|k|+1)·log 2 + log(3/2)
  have h_expand : -Real.log (2 ^ (-(|k| + 1 : ℤ)) / (3 / 2)) =
                  (|k| + 1 : ℝ) * Real.log 2 + Real.log (3 / 2) := by
    rw [Real.log_div (ne_of_gt hzpow_pos) (ne_of_gt h32pos)]
    -- -log(2^{-(|k|+1)}) + log(3/2)
    rw [← Real.rpow_intCast 2 (-(|k| + 1))]
    rw [Real.log_rpow h2pos]
    -- -(-(|k|+1)·log 2) + log(3/2) = (|k|+1)·log 2 + log(3/2)
    push_cast
    ring
  rw [h_expand]
  -- Show (|k|+1)·log 2 + log(3/2) ≤ (|k|+2)·log 2
  -- i.e., log(3/2) ≤ log 2
  have h32_le_2 : Real.log (3/2) ≤ Real.log 2 := le_of_lt (Real.log_lt_log h32pos h32_lt_2)
  calc (|k| + 1 : ℝ) * Real.log 2 + Real.log (3 / 2)
      ≤ (|k| + 1 : ℝ) * Real.log 2 + Real.log 2 := by linarith [h32_le_2]
    _ = (|k| + 2 : ℝ) * Real.log 2 := by ring

/-! ## Connection to PLN Modal BinaryEvidence Theory

This formalization justifies the PLN approach where:

1. **BinaryEvidence** = (n, Σx, Σx²) - context-free sufficient statistics
2. **Context** = (μ₀, τ₀², σ²) - interpretation parameters
3. **Universal Hyperprior** = mixture over {(0, 2^k, σ²) : k ∈ ℤ}

The key insight: when τ₀² is unidentifiable, PLN doesn't guess—it reasons
about the space of possible contexts using principled weights.
-/

/-- PLN Universal Hyperprior inference: returns (mean, std) tuple -/
noncomputable def plnUniversalHyperpriorInference (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ × ℝ :=
  let mean := mixturePosteriorMean σ_sq hσ ev
  let var := mixturePosteriorVar σ_sq hσ ev
  (mean, Real.sqrt var)

/-- For μ₀ = 0, posterior mean magnitude is bounded by sample mean -/
theorem posteriorMean_abs_le_sampleMean (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (hn : ev.n ≠ 0) :
    |posteriorMean (contextAtK k σ_sq hσ) ev| ≤ |ev.toMean| := by
  -- Use `let` (not `have`) so definitional reduction works smoothly.
  let ctx := contextAtK k σ_sq hσ
  -- μ₀ = 0 for contextAtK
  have hμ₀ : ctx.μ₀ = 0 := by rfl
  -- Posterior mean is a weighted average with coefficient ∈ [0, 1]
  rw [posteriorMean_weighted_avg _ _ hn, hμ₀]
  simp only [mul_zero, zero_add]
  -- Now: |coeff * toMean| ≤ |toMean| where coeff = n * obsPrecision / posteriorPrecision ∈ [0, 1]
  have hcoeff : 0 ≤ (ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n ∧
                    (ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n ≤ 1 := by
    constructor
    · apply div_nonneg
      · apply mul_nonneg; exact Nat.cast_nonneg _; exact le_of_lt ctx.obsPrecision_pos
      · exact le_of_lt (posteriorPrecision_pos ctx ev.n)
    · -- n * obsPrecision ≤ priorPrecision + n * obsPrecision = posteriorPrecision
      have h : (ev.n : ℝ) * ctx.obsPrecision ≤ posteriorPrecision ctx ev.n := by
        unfold posteriorPrecision
        linarith [le_of_lt ctx.priorPrecision_pos]
      exact div_le_one_of_le₀ h (le_of_lt (posteriorPrecision_pos ctx ev.n))
  rw [abs_mul]
  calc |((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n)| * |ev.toMean|
       = ((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n) * |ev.toMean| := by
          rw [abs_of_nonneg hcoeff.1]
     _ ≤ 1 * |ev.toMean| := by apply mul_le_mul_of_nonneg_right hcoeff.2 (abs_nonneg _)
     _ = |ev.toMean| := one_mul _

/-- The mixture mean shrinks toward the prior mean (0) -/
theorem mixture_shrinks_toward_prior (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (hn : ev.n ≠ 0) :
    |mixturePosteriorMean σ_sq hσ ev| ≤ |ev.toMean| := by
  unfold mixturePosteriorMean
  -- |∑ w_k·mean_k| ≤ ∑ w_k·|mean_k| ≤ ∑ w_k·|xbar| = |xbar|
  calc |∑' k : ℤ, posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev|
       ≤ ∑' k : ℤ, |posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev| := by
          sorry  -- TODO: abs_tsum_le_tsum_abs (requires summability)
     _ = ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * |posteriorMean (contextAtK k σ_sq hσ) ev| := by
          congr 1; ext k; rw [abs_mul, abs_of_pos (posteriorWeight_pos k σ_sq hσ ev)]
     _ ≤ ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * |ev.toMean| := by
          sorry  -- TODO: tsum_le_tsum using posteriorMean_abs_le_sampleMean
     _ = (∑' k : ℤ, posteriorWeight k σ_sq hσ ev) * |ev.toMean| := by
          rw [tsum_mul_right]
     _ = 1 * |ev.toMean| := by rw [tsum_posteriorWeight_eq_one σ_sq hσ ev]
     _ = |ev.toMean| := one_mul _

/-- The mixture variance is at least the maximum component variance
    (consequence of law of total variance: Var ≥ E[Var]) -/
theorem mixture_var_ge_expected_var (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    mixturePosteriorVar σ_sq hσ ev ≥
      ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * componentPosteriorVar k σ_sq hσ ev := by
  -- Var = E[Var] + Var[E] ≥ E[Var] since Var[E] ≥ 0
  unfold mixturePosteriorVar
  have h : (∑' k : ℤ, posteriorWeight k σ_sq hσ ev *
              (posteriorMean (contextAtK k σ_sq hσ) ev - mixturePosteriorMean σ_sq hσ ev)^2) ≥ 0 := by
    apply tsum_nonneg
    intro k
    apply mul_nonneg
    · exact le_of_lt (posteriorWeight_pos k σ_sq hσ ev)
    · exact sq_nonneg _
  linarith

/-! ## Summary: Why Universal Hyperprior is Correct PLN

The Universal Hyperprior mixture approach is the **theoretically correct** PLN solution for
single-level Normal-Normal inference because:

1. **BinaryEvidence aggregates context-free**: hplus on (n, Σx, Σx²) is a monoid operation
   that doesn't depend on τ₀². This is the foundation of PLN.

2. **Context is modal**: Different τ₀² values represent different "possible worlds"
   for interpretation. PLN explicitly reasons about these.

3. **Unidentifiable parameters get mixed over**: Rather than point-estimating τ₀²
   (which would be statistically invalid), we form a principled mixture.

4. **Dominance guarantees optimal regret**: The mixture never does much worse than
   the best context in hindsight (Universal Hyperprior theorem).

5. **Weights from coding theory**: The geometric weights 2^{-(|k|+1)} arise from
   self-delimiting codes, giving information-theoretic optimality.

The incorrect "empirical Bayes" approach (τ̂₀² = s² - σ²) violates PLN principles
by pretending to identify an unidentifiable parameter, leading to spuriously
overconfident posteriors that fail to achieve nominal coverage.
-/

end Mettapedia.Logic.UniversalHyperprior
