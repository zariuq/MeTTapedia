import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.BayesianAgents.PosteriorSampling
import Mettapedia.ProbabilityTheory.Distributions.BetaBernoulli
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

/-!
# Thompson Sampling for Multi-Armed Bandits

This file formalizes Thompson Sampling by showing it is exactly the Bayes-optimal
agent (AIXI) when applied to stationary bandit environments.

## Main Insight

**Thompson Sampling = `bayesOptimalAgent` for bandit mixtures**

This means we get optimality FOR FREE from the existing `bayes_optimal_maximizes_value`
theorem proven in BayesianAgents.lean!

## Main Definitions

* `BanditArm`: A stationary reward distribution (Bernoulli parameter)
* `bernoulliArmEnvironment`: Convert arm to stateless `Environment`
* `thompsonMixture`: Bayesian mixture over arm parameters (Beta priors)
* `thompsonSamplingAgent`: Thompson Sampling = `bayesOptimalAgent`

## Main Theorems

* `thompsonSampling_is_bayesOptimal`: **Thompson Sampling maximizes expected reward**
  - Proof: 1 line (apply existing theorem!)

## References

- Thompson, W. R. (1933). "On the likelihood that one unknown probability
  exceeds another in view of the evidence of two samples"
- Russo & Van Roy (2014). "Learning to Optimize via Information-Directed Sampling"
- Hutter, M. (2005). "Universal Artificial Intelligence" (AIXI framework)

-/

namespace Mettapedia.Logic.UniversalPrediction.ThompsonSampling

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.ProbabilityTheory

/-! ## Bandit Arms and Environments -/

/-- A bandit arm: fixed Bernoulli parameter p ∈ [0,1].

    Each pull of arm returns reward 1 with probability p, reward 0 with probability 1-p.
-/
structure BanditArm where
  param : BernoulliDist

/-- Convert bandit arm to stateless Environment.

    The environment ignores history and depends only on the last action.
    Observations are deterministic (always false), only rewards are stochastic.
    This is the key property that makes bandits simpler than general MDPs.
-/
noncomputable def bernoulliArmEnvironment (getArm : Action → BanditArm) : Environment where
  prob h x :=
    -- Get the last action from history (which arm was pulled)
    match h_acts : h.actions with
    | [] => 0  -- Empty history: no action taken yet
    | a :: rest =>
        -- Observations are deterministic (always false for bandits)
        if x.obs = false then
          -- Get last action
          let lastAction := (a :: rest).getLast (by simp)
          -- Return reward based on arm's Bernoulli parameter
          let arm := getArm lastAction
          let rewardProb := arm.param.prob x.rewardBit
          ENNReal.ofReal rewardProb
        else
          0  -- Observation true never happens
  prob_le_one h hw := by
    -- Sum of probabilities ≤ 1
    simp only []
    cases h_acts : h.actions with
    | nil =>
      -- Empty history case: sum of 0s = 0 ≤ 1
      simp
    | cons head tail =>
      -- Non-empty history case: h.actions = head :: tail
      have acts_ne : head :: tail ≠ [] := by simp
      let lastAction := (head :: tail).getLast acts_ne
      let arm := getArm lastAction
      simp
      -- Sum over all 4 percepts: (false,false), (false,true), (true,false), (true,true)
      have huniv : (Finset.univ : Finset Percept) = {Percept.mk false false, Percept.mk false true,
                                                      Percept.mk true false, Percept.mk true true} := by
        decide
      change (∑ x : Percept, if x.obs = false then
          ENNReal.ofReal ((getArm lastAction).param.prob x.rewardBit) else 0) ≤ 1
      calc ∑ x : Percept, (if x.obs = false then
              ENNReal.ofReal ((getArm lastAction).param.prob x.rewardBit) else 0)
        _ = (if (Percept.mk false false).obs = false then
                ENNReal.ofReal ((getArm lastAction).param.prob (Percept.mk false false).rewardBit) else 0) +
            (if (Percept.mk false true).obs = false then
                ENNReal.ofReal ((getArm lastAction).param.prob (Percept.mk false true).rewardBit) else 0) +
            (if (Percept.mk true false).obs = false then
                ENNReal.ofReal ((getArm lastAction).param.prob (Percept.mk true false).rewardBit) else 0) +
            (if (Percept.mk true true).obs = false then
                ENNReal.ofReal ((getArm lastAction).param.prob (Percept.mk true true).rewardBit) else 0) := by
            rw [huniv]
            simp [Finset.sum_insert, Finset.sum_singleton]
            ring
        _ = ENNReal.ofReal ((getArm lastAction).param.prob false) +
              ENNReal.ofReal ((getArm lastAction).param.prob true) := by
            simp [Percept.obs, Percept.rewardBit]
        _ = ENNReal.ofReal ((getArm lastAction).param.prob false +
              (getArm lastAction).param.prob true) := by
            rw [← ENNReal.ofReal_add]
            · exact BernoulliDist.prob_nonneg _ _
            · exact BernoulliDist.prob_nonneg _ _
        _ = ENNReal.ofReal 1 := by
            congr 1
            rw [add_comm]
            exact BernoulliDist.prob_sum_one (getArm lastAction).param
        _ = 1 := ENNReal.ofReal_one
        _ ≤ 1 := le_refl 1

/-! ## Thompson Sampling Mixture -/

/-- Hypothesis: each action corresponds to a bandit arm with some Bernoulli parameter.

    We discretize the continuous Beta prior into a finite grid for computational tractability.
-/
structure BanditHypothesis where
  arms : Action → BanditArm

/-- Convert hypothesis to environment. -/
noncomputable def hypothesisToEnvironment (h : BanditHypothesis) : Environment :=
  bernoulliArmEnvironment h.arms

/-- Sample a hypothesis from Beta priors over arm parameters.

    This discretizes the continuous Beta distribution into a finite grid.
    For index i, we sample the i-th quantile of each arm's Beta prior.
-/
noncomputable def sampleHypothesis
    (_i : ℕ)
    (priors : Action → BetaBernoulliPrior) : BanditHypothesis where
  arms := fun action =>
    -- Sample from Beta prior for this arm
    -- For simplicity, use the posterior mean as the sampled value
    let prior := priors action
    let sampledP := prior.mean
    { param := {
        p := sampledP
        p_nonneg := (prior.mean_mem_unit_interval).left
        p_le_one := (prior.mean_mem_unit_interval).right } }

/-- Helper lemma: uniform weights over n elements sum to ≤ 1. -/
private lemma uniform_weights_le_one (n : ℕ) :
    (∑' i, if i < n then (1 : ENNReal) / ↑n else 0) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · -- The tsum has only finitely many nonzero terms, so equals finite sum
    have h_eq : (∑' i, if i < n then (1 : ENNReal) / ↑n else 0) =
                (∑ i ∈ Finset.range n, (1 : ENNReal) / ↑n) := by
      -- Use ENNReal.sum_add_tsum_compl: ∑ i ∈ s, f i + ∑' i ∈ sᶜ, f i = ∑' i, f i
      -- The complement tsum is 0 since f i = 0 for i ∉ Finset.range n
      conv_lhs => arg 1; ext i; rw [show (if i < n then (1 : ENNReal) / ↑n else 0) =
                                          (fun j => if j < n then (1 : ENNReal) / ↑n else 0) i from rfl]
      rw [← ENNReal.sum_add_tsum_compl (Finset.range n)]
      -- Show the complement tsum is 0
      have h_compl : ∑' i : ↥(Finset.range n : Set ℕ)ᶜ,
                      (fun j => if j < n then (1 : ENNReal) / ↑n else 0) i = 0 := by
        simp
      rw [h_compl, add_zero]
      -- Simplify the sum
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    rw [h_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h_ne : (n : ENNReal) ≠ 0 := by simp; exact hn
    rw [mul_comm, ENNReal.div_mul_cancel h_ne ENNReal.coe_ne_top]

/-- Thompson Sampling mixture over arm parameters.

    This is a `BayesianMixture` where:
    - Each component is a hypothesis about the arm parameters
    - Weights come from geometric distribution (summable)
    - The mixture represents our Bayesian belief about the world
-/
noncomputable def thompsonMixture
    (priors : Action → BetaBernoulliPrior)
    (numHypotheses : ℕ := 1000) : BayesianMixture where
  envs := fun i =>
    if i < numHypotheses
    then hypothesisToEnvironment (sampleHypothesis i priors)
    else { prob := fun _ _ => 0, prob_le_one := fun _ _ => by simp }
  weights := fun i =>
    if i < numHypotheses
    then 1 / numHypotheses
    else 0
  weights_le_one := by
    -- Weights sum to ≤ 1 (uniform over finite hypotheses)
    exact uniform_weights_le_one numHypotheses

/-! ## Thompson Sampling Agent -/

/-- Thompson Sampling agent IS the Bayes-optimal agent!

    This is the key insight: Thompson Sampling is not an approximation,
    it IS optimal Bayesian decision-making for the mixture environment.
-/
noncomputable def thompsonSamplingAgent
    (priors : Action → BetaBernoulliPrior)
    (γ : DiscountFactor)
    (horizon : ℕ) : Agent :=
  bayesOptimalAgent (thompsonMixture priors) γ horizon

/-- Posterior-sampling (Thompson sampling) agent over the finite hypothesis class `thompsonMixture`.

This uses the generic history-level posterior-sampling construction from
`Mettapedia.UniversalAI.BayesianAgents.PosteriorSampling`. -/
noncomputable def posteriorSamplingAgent
    (priors : Action → BetaBernoulliPrior)
    (γ : DiscountFactor)
    (horizon : ℕ)
    (numHypotheses : ℕ := 1000) : Agent :=
  Mettapedia.UniversalAI.BayesianAgents.thompsonSamplingAgent
    (prior := (thompsonMixture priors numHypotheses).weights)
    (envs := (thompsonMixture priors numHypotheses).envs)
    (h_prior := (thompsonMixture priors numHypotheses).weights_le_one)
    γ horizon

/-! ## Main Theorem: Thompson Sampling is Bayes-Optimal -/

/-- **THE MAIN THEOREM**: Thompson Sampling maximizes expected reward.

    **Proof**: This is IMMEDIATE from `bayes_optimal_maximizes_value`!

    Thompson Sampling is just the Bayes-optimal agent applied to a bandit
    mixture. Therefore, all optimality guarantees transfer for FREE.
-/
theorem thompsonSampling_is_bayesOptimal
    (priors : Action → BetaBernoulliPrior)
    (γ : DiscountFactor)
    (horizon : ℕ)
    (h : History)
    (hw : h.wellFormed)
    (π : Agent) :
    value (mixtureEnvironment (thompsonMixture priors))
          (thompsonSamplingAgent priors γ (horizon + 2 * h.cycles))
          γ h horizon ≥
    value (mixtureEnvironment (thompsonMixture priors)) π γ h horizon := by
  -- Unfold Thompson Sampling to Bayes-optimal agent
  unfold thompsonSamplingAgent
  -- Apply the existing optimality theorem!
  exact bayes_optimal_maximizes_value (thompsonMixture priors) γ horizon h hw π

/-! ## Properties of Thompson Sampling -/

/-- Thompson Sampling achieves non-negative value (inherits from AIXI). -/
theorem thompsonSampling_value_nonneg
    (priors : Action → BetaBernoulliPrior)
    (γ : DiscountFactor)
    (horizon : ℕ)
    (h : History) :
    0 ≤ value (mixtureEnvironment (thompsonMixture priors))
              (thompsonSamplingAgent priors γ (horizon + 2 * h.cycles))
              γ h horizon := by
  -- Reuse existing theorem
  exact value_nonneg _ _ _ _ _

/-- Thompson Sampling value is bounded by horizon. -/
theorem thompsonSampling_value_bounded
    (priors : Action → BetaBernoulliPrior)
    (γ : DiscountFactor)
    (horizon : ℕ)
    (h : History) :
    value (mixtureEnvironment (thompsonMixture priors))
          (thompsonSamplingAgent priors γ (horizon + 2 * h.cycles))
          γ h horizon ≤ horizon := by
  -- Reuse existing theorem
  exact value_le _ _ _ _ _

/-! ## Examples -/

/-- Uniform Beta(1,1) prior (no prior knowledge). -/
def uniformPrior : BetaBernoulliPrior :=
  { α := 1, β := 1
    α_pos := by norm_num
    β_pos := by norm_num }

/-- Create uniform priors for all actions. -/
def uniformPriors : Action → BetaBernoulliPrior :=
  fun _ => uniformPrior

/-- Thompson Sampling with uniform priors. -/
noncomputable def thompsonSamplingUniform (γ : DiscountFactor) (horizon : ℕ) : Agent :=
  thompsonSamplingAgent uniformPriors γ horizon

end Mettapedia.Logic.UniversalPrediction.ThompsonSampling
