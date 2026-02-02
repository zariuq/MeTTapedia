import Mettapedia.UniversalAI.GrainOfTruth.Core
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.BayesianAgents.HistoryProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Grain of Truth: Core Theory

This file provides the theoretical foundation for the Grain of Truth convergence theorem.
It builds on the existing infrastructure in `BayesianAgents.lean` rather than duplicating it.

## Key Insight

`BayesianAgents.lean` already contains:
- `value μ π γ h n` - The expected value V^π_μ(h) under policy π
- `qValue μ π γ h a n` - The Q-value Q^π_μ(h,a)
- `optimalValue μ γ h n` - The optimal value V*_μ(h)
- `optimalValue_ge_value` - **The key theorem: V* ≥ V^π**

We use these directly rather than redefining them.

## Main Definitions

* `Regret` - V* - V^π, the performance gap (uses existing `optimalValue` and `value`)
* `HistoryProbability` - Probability that environment μ generates history h
* `BayesianPosteriorWeight` - Proper Bayesian update formula
* `ExpectedRegretOverPrior` - Weighted regret over environment class

## References

- Leike (2016). PhD Thesis, Chapter 7
- Hutter (2005). "Universal Artificial Intelligence"

-/

namespace Mettapedia.UniversalAI.GrainOfTruth.FixedPoint

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal

/-! ## Regret Using Existing Infrastructure

The regret is simply V* - V^π. We use the existing `optimalValue` and `value`
from BayesianAgents.lean.
-/

/-- Instantaneous regret: gap between optimal value and policy value.
    Uses the existing `optimalValue` and `value` from BayesianAgents. -/
noncomputable def regret (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) : ℝ :=
  optimalValue μ γ h horizon - value μ π γ h horizon

/-- **Regret is always non-negative**.
    This follows directly from `optimalValue_ge_value` in BayesianAgents.lean. -/
theorem regret_nonneg (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) :
    0 ≤ regret μ π γ h horizon := by
  unfold regret
  -- Use the existing theorem from BayesianAgents
  have h := optimalValue_ge_value μ γ h horizon π
  linarith

/-- Regret is bounded by the optimal value. -/
theorem regret_le_optimalValue (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) :
    regret μ π γ h horizon ≤ optimalValue μ γ h horizon := by
  unfold regret
  have hv := value_nonneg μ π γ h horizon
  linarith

/-! ## Bayesian Posterior

The proper Bayesian update formula.
Given a prior w over environments and observed history h:
  w(ν | h) = w(ν) · ν(h) / ξ(h)
where ξ(h) = Σ_ν w(ν) · ν(h) is the mixture probability.
-/

/-- Environment in the class with its prior weight. -/
structure WeightedEnvironment (O : Oracle) (M : ReflectiveEnvironmentClass O) where
  /-- Index into the environment class -/
  idx : EnvironmentIndex
  /-- The actual environment (would be computed from oracle) -/
  env : Environment
  /-- Prior weight -/
  priorWeight : ℝ≥0∞
  /-- Weight is positive -/
  weight_pos : 0 < priorWeight

/-- The mixture probability ξ(h) = Σ_ν w(ν) · ν(h). -/
noncomputable def mixtureProbability (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (h : History) : ℝ≥0∞ :=
  ∑' i, prior.weight i * historyProbability (envs i) h

/-- Bayesian posterior weight: w(ν | h) = w(ν) · ν(h) / ξ(h).
    This is the proper Bayesian update, not a placeholder. -/
noncomputable def bayesianPosteriorWeight (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (h : History) : ℝ≥0∞ :=
  let numerator := prior.weight ν_idx * historyProbability (envs ν_idx) h
  let denominator := mixtureProbability O M prior envs h
  if denominator = 0 then prior.weight ν_idx  -- Fallback to prior if ξ(h) = 0
  else numerator / denominator

/-- Posterior weights sum to 1 (when ξ(h) > 0).
    Proof sketch: w(ν|h) = w(ν)·ν(h) / ξ(h), so
    Σ_ν w(ν|h) = Σ_ν w(ν)·ν(h) / ξ(h) = ξ(h)/ξ(h) = 1
    Requires: tsum_div_const or ENNReal division lemmas -/
theorem bayesianPosterior_sum_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (h : History)
    (h_mix_pos : mixtureProbability O M prior envs h > 0) :
    ∑' i, bayesianPosteriorWeight O M prior envs i h = 1 := by
  classical
  set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
  have hden_ne0 : denom ≠ 0 := ne_of_gt h_mix_pos
  have hden_le_one : denom ≤ 1 := by
    have h_term : ∀ i : ℕ, prior.weight i * historyProbability (envs i) h ≤ prior.weight i := by
      intro i
      have h_prob : historyProbability (envs i) h ≤ 1 := historyProbability_le_one (envs i) h
      simpa [mul_one] using (mul_le_mul_right h_prob (prior.weight i))
    have h_le : denom ≤ ∑' i, prior.weight i := by
      simpa [denom, mixtureProbability] using (ENNReal.tsum_le_tsum h_term)
    exact le_trans h_le prior.tsum_le_one
  have hden_ne_top : denom ≠ ∞ :=
    (lt_of_le_of_lt hden_le_one ENNReal.one_lt_top).ne_top

  calc
    (∑' i, bayesianPosteriorWeight O M prior envs i h)
        = ∑' i, (prior.weight i * historyProbability (envs i) h) / denom := by
            simp [bayesianPosteriorWeight, denom, hden_ne0]
    _ = ∑' i, (prior.weight i * historyProbability (envs i) h) * denom⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑' i, prior.weight i * historyProbability (envs i) h) * denom⁻¹ := by
          simpa using (ENNReal.tsum_mul_right (f := fun i => prior.weight i * historyProbability (envs i) h)
            (a := denom⁻¹))
    _ = denom * denom⁻¹ := by
          simp [denom, mixtureProbability]
    _ = 1 := ENNReal.mul_inv_cancel hden_ne0 hden_ne_top

/-! ## Expected Regret Over Prior

The expected regret weighted by the prior/posterior.
-/

/-- Expected regret over the prior: E_w[Regret]. -/
noncomputable def expectedRegretOverPrior (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (π : Agent) (γ : DiscountFactor) (h : History) (horizon : ℕ) : ℝ :=
  ∑' i, (prior.weight i).toReal * regret (envs i) π γ h horizon

/-- Expected regret is non-negative. -/
theorem expectedRegretOverPrior_nonneg (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (π : Agent) (γ : DiscountFactor) (h : History) (horizon : ℕ) :
    0 ≤ expectedRegretOverPrior O M prior envs π γ h horizon := by
  unfold expectedRegretOverPrior
  apply tsum_nonneg
  intro i
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact regret_nonneg (envs i) π γ h horizon

/-! ## Asymptotic Optimality

A policy π is asymptotically optimal in mean if E[V* - V^π] → 0 as t → ∞.
This is the proper definition, not a placeholder.
-/

/-- Asymptotic optimality in mean: expected regret converges to 0.
    For all ε > 0, there exists t₀ such that for all t ≥ t₀,
    the expected regret is less than ε. -/
def IsAsymptoticallyOptimal (π : Agent) (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (γ : DiscountFactor) : Prop :=
  ∀ ε > 0, ∃ t₀ : ℕ, ∀ t ≥ t₀,
    ∀ h : History, h.wellFormed → h.cycles = t →
      expectedRegretOverPrior O M prior envs π γ h t < ε

/-! ## ε-Best Response

A policy is an ε-best response if regret < ε.
-/

/-- A policy is an ε-best response at history h in environment μ. -/
def IsEpsilonBestResponse (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (ε : ℝ) (h : History) (horizon : ℕ) : Prop :=
  regret μ π γ h horizon < ε

/-- If regret is bounded, we get an ε-best response. -/
theorem regret_bound_gives_best_response (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (ε : ℝ) (h : History) (horizon : ℕ) (hbound : regret μ π γ h horizon < ε) :
    IsEpsilonBestResponse μ π γ ε h horizon :=
  hbound

/-! ## Convergence (measure-theoretic)

The Chapter 7 / Leike-route convergence statements are *on-policy* and are most naturally stated
either almost surely or in probability on the induced trajectory measure.

See the measure-theory pipeline in:

* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/RegretConvergence.lean`
* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/AsymptoticOptimality.lean`
* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/Main.lean`
-/

end Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
