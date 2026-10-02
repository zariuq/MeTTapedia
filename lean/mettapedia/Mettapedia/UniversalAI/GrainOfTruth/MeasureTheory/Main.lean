import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorExpectedRegret

/-!
# Posterior concentration and the posterior-expected regret

For a countable class with a prior that gives the true environment positive
weight, and a policy that has no regret in the true environment: if every
other environment of the class is told apart from the true one along almost
every trajectory, the posterior weight of the true environment tends to one,
and the regret averaged over the posterior tends to zero.

The four theorems differ in how "told apart" is stated:

* `posteriorExpectedRegretVanishes_of_identifiableWithPolicy`: the
  log-likelihood ratio tends to `-∞`;
* `posteriorExpectedRegretVanishes_of_likelihoodRatio_tendsto_zero`: the
  likelihood ratio tends to `0`;
* `posteriorExpectedRegretVanishes_of_eventually_stepLikelihoodRatio_le`: each
  step eventually shrinks the likelihood ratio by a factor below one;
* `posteriorExpectedRegretVanishes_of_refutableWithPolicy`: some finite prefix
  has probability zero under the wrong environment.

Each also assumes that the weighted likelihood ratios are dominated by a
summable sequence (`DominatedLikelihoodRatioSeries`).

These are consistency statements for the posterior. The policy is assumed
optimal in the true environment, so they say nothing about a policy that has to
learn. In particular none of them is the theorem that Thompson sampling is
asymptotically optimal in mean (Leike, Lattimore, Orseau and Hutter 2016), and
none is the convergence to equilibrium of Leike, Taylor and Fallenstein 2016.

## References

- Leike (2016). PhD Thesis, Chapter 5
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.Main

open ProbabilityTheory Real
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorExpectedRegret
open scoped ENNReal NNReal

/-- If every wrong environment has log-likelihood ratio tending to `-∞` under
the true environment and the policy, the posterior-expected regret vanishes. -/
theorem posteriorExpectedRegretVanishes_of_identifiableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    /- the true environment has positive prior weight -/
    (h_grain : 0 < prior.weight ν_star_idx)
    /- Stochasticity: true environment is stochastic -/
    (h_stoch : isStochastic (envs ν_star_idx))
    /- Agent is optimal for true environment -/
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    /- Identifiability: every wrong environment has log-likelihood ratio → -∞ under ν*^π. -/
    (h_ident : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      IdentifiableWithPolicy (envs i) (envs ν_star_idx) agent h_stoch)
    /- Dominated-convergence hypothesis for swapping `t → ∞` with `∑' i` in the denominator. -/
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    PosteriorExpectedRegretVanishes prior envs agent γ horizon ν_star_idx h_stoch :=
by
  have h_consistency :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto
          (fun t => (PosteriorConcentration.posteriorWeight prior envs ν_star_idx t traj).toReal)
          Filter.atTop (nhds 1) :=
    posteriorWeight_true_ae_tendsto_one_of_identifiableWithPolicy
      (prior := prior) (envs := envs) (pi := agent) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      h_ident h_dom
  exact posteriorExpectedRegretVanishes_of_consistency prior envs agent γ horizon ν_star_idx
    h_grain h_stoch h_agent_optimal h_consistency

/-- The same with the hypothesis `ν(h_t)/ν*(h_t) → 0` for every wrong
environment, which needs no logarithm. -/
theorem posteriorExpectedRegretVanishes_of_likelihoodRatio_tendsto_zero
    (prior : PriorOverClass) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_lr_tendsto : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
          Filter.atTop (nhds 0))
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    PosteriorExpectedRegretVanishes prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_consistency :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto
          (fun t => (PosteriorConcentration.posteriorWeight prior envs ν_star_idx t traj).toReal)
          Filter.atTop (nhds 1) :=
    posteriorWeight_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
      (prior := prior) (envs := envs) (pi := agent) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      (h_lr := h_lr_tendsto) (h_dom := h_dom)
  exact posteriorExpectedRegretVanishes_of_consistency prior envs agent γ horizon ν_star_idx
    h_grain h_stoch h_agent_optimal h_consistency

/-- The same when each step eventually shrinks the likelihood ratio of every
wrong environment by a factor below one. -/
theorem posteriorExpectedRegretVanishes_of_eventually_stepLikelihoodRatio_le
    (prior : PriorOverClass) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_step : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∃ r : ℝ≥0∞, r < 1 ∧
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          ∀ᶠ t in Filter.atTop, stepLikelihoodRatio (envs i) (envs ν_star_idx) t traj ≤ r)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    PosteriorExpectedRegretVanishes prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_lr_tendsto :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
            Filter.atTop (nhds 0) := by
    intro i hi
    rcases h_step i hi with ⟨r, hr, h_step_i⟩
    simpa using
      (likelihoodRatio_converges_to_zero_of_eventually_stepLikelihoodRatio_le
        (ν := envs i) (ν_star := envs ν_star_idx) (pi := agent) (h_stoch := h_stoch) hr h_step_i)
  exact posteriorExpectedRegretVanishes_of_likelihoodRatio_tendsto_zero
    (prior := prior) (envs := envs)
    (agent := agent) (γ := γ) (horizon := horizon) (ν_star_idx := ν_star_idx)
    h_grain h_stoch h_agent_optimal (h_lr_tendsto := h_lr_tendsto) (h_dom := h_dom)

/-- The same when every wrong environment is refuted by a finite prefix almost
surely: some observed prefix has probability zero under it. -/
theorem posteriorExpectedRegretVanishes_of_refutableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_ref : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      RefutableWithPolicy (envs i) (envs ν_star_idx) agent h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    PosteriorExpectedRegretVanishes prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_lr_tendsto :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
            Filter.atTop (nhds 0) := by
    intro i hi
    simpa using
      (likelihoodRatio_converges_to_zero_of_refutableWithPolicy (ν := envs i) (ν_star := envs ν_star_idx)
        (pi := agent) (h_stoch := h_stoch) (h_ref := h_ref i hi))
  exact posteriorExpectedRegretVanishes_of_likelihoodRatio_tendsto_zero
    (prior := prior) (envs := envs)
    (agent := agent) (γ := γ) (horizon := horizon) (ν_star_idx := ν_star_idx)
    h_grain h_stoch h_agent_optimal (h_lr_tendsto := h_lr_tendsto) (h_dom := h_dom)

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.Main
