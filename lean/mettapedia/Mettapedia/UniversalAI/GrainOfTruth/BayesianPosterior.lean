import Mettapedia.UniversalAI.GrainOfTruth.Core
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.BayesianAgents.HistoryProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Regret and the Bayesian posterior over a countable class

For a countable family `envs : ℕ → Environment` with a prior on its indices:

* `regret`: the gap `V*_μ(h) - V^π_μ(h)` between the optimal value and the value
  of a policy, with `regret_nonneg` and `regret_le_optimalValue`;
* `mixtureProbability`: `ξ(h) = Σ_ν w(ν) · ν(h)`;
* `bayesianPosteriorWeight`: `w(ν | h) = w(ν) · ν(h) / ξ(h)`, equal to the prior
  weight when `ξ(h) = 0`;
* `bayesianPosterior_sum_one`: the posterior weights sum to one when `ξ(h) > 0`.

The values `value`, `qValue` and `optimalValue` and the inequality
`optimalValue_ge_value` come from `BayesianAgents.lean`.

## References

- Leike (2016). PhD Thesis, Chapters 5 and 7
- Hutter (2005). "Universal Artificial Intelligence"
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
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

/-- The mixture probability ξ(h) = Σ_ν w(ν) · ν(h). -/
noncomputable def mixtureProbability (prior : PriorOverClass) (envs : ℕ → Environment)
    (h : History) : ℝ≥0∞ :=
  ∑' i, prior.weight i * historyProbability (envs i) h

/-- Bayesian posterior weight: w(ν | h) = w(ν) · ν(h) / ξ(h). -/
noncomputable def bayesianPosteriorWeight (prior : PriorOverClass) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (h : History) : ℝ≥0∞ :=
  let numerator := prior.weight ν_idx * historyProbability (envs ν_idx) h
  let denominator := mixtureProbability prior envs h
  if denominator = 0 then prior.weight ν_idx  -- Fallback to prior if ξ(h) = 0
  else numerator / denominator

/-- Posterior weights sum to 1 when ξ(h) > 0:
    Σ_ν w(ν|h) = Σ_ν w(ν)·ν(h) / ξ(h) = ξ(h)/ξ(h) = 1. -/
theorem bayesianPosterior_sum_one (prior : PriorOverClass) (envs : ℕ → Environment) (h : History)
    (h_mix_pos : mixtureProbability prior envs h > 0) :
    ∑' i, bayesianPosteriorWeight prior envs i h = 1 := by
  classical
  set denom : ℝ≥0∞ := mixtureProbability prior envs h
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
    (∑' i, bayesianPosteriorWeight prior envs i h)
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

end Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
