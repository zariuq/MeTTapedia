import Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Bayes Mixture Environment (Posterior-Predictive)

This file defines the **posterior-predictive** Bayesian mixture environment:

`ξ(x | h a) = ∑ᵢ w(i | h a) · νᵢ(x | h a)`

where `w(i | h)` is the Bayesian posterior weight from `FixedPoint.lean`.

This is the “right” object for Leike/Hutter-style *learning as prediction* results:
the posterior weights are history-dependent (they are not a fixed convex combination).
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.FixedPoint

open scoped ENNReal
open Mettapedia.UniversalAI.BayesianAgents

/-! ## Posterior Weight Summability -/

/-- Posterior weights always sum to at most `1` (and sum to `1` when `ξ(h) > 0`). -/
theorem bayesianPosterior_tsum_le_one (O : Mettapedia.Computability.Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (h : History) :
    (∑' i, bayesianPosteriorWeight O M prior envs i h) ≤ 1 := by
  classical
  set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
  by_cases hden : denom = 0
  · -- fallback posterior = prior
    simpa [bayesianPosteriorWeight, denom, hden] using prior.tsum_le_one
  · -- proper posterior sums to 1
    have hden_pos : denom > 0 :=
      lt_of_le_of_ne zero_le (Ne.symm hden)
    have hsum : (∑' i, bayesianPosteriorWeight O M prior envs i h) = 1 :=
      bayesianPosterior_sum_one O M prior envs h hden_pos
    exact le_of_eq hsum

/-! ## The Posterior-Predictive Bayes Mixture Environment -/

-- This lives in `FixedPoint` because it is defined purely from `mixtureProbability` and
-- `bayesianPosteriorWeight`.

/-- The Bayesian mixture environment corresponding to the posterior-predictive distribution. -/
noncomputable def bayesMixtureEnvironment (O : Mettapedia.Computability.Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) : Environment where
  prob h x := ∑' i, bayesianPosteriorWeight O M prior envs i h * (envs i).prob h x
  prob_le_one h hw := by
    classical
    let w : ℕ → ℝ≥0∞ := fun i => bayesianPosteriorWeight O M prior envs i h
    calc
      (∑' x : Percept, ∑' i : ℕ, w i * (envs i).prob h x)
          = ∑' i : ℕ, ∑' x : Percept, w i * (envs i).prob h x := by
              exact ENNReal.tsum_comm
      _ = ∑' i : ℕ, w i * (∑' x : Percept, (envs i).prob h x) := by
            congr 1
            ext i
            rw [← ENNReal.tsum_mul_left]
      _ ≤ ∑' i : ℕ, w i * 1 := by
            gcongr with i
            exact (envs i).prob_le_one h hw
      _ = ∑' i : ℕ, w i := by simp
      _ ≤ 1 := by
            simpa [w] using bayesianPosterior_tsum_le_one O M prior envs h

/-! ## Basic Dominance Facts (for the unnormalized mixture semimeasure) -/

/-- Each component contributes to the mixture semimeasure. -/
theorem le_mixtureProbability (O : Mettapedia.Computability.Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (ν_idx : EnvironmentIndex) (h : History) :
    prior.weight ν_idx * historyProbability (envs ν_idx) h ≤ mixtureProbability O M prior envs h := by
  simpa [mixtureProbability] using (ENNReal.le_tsum ν_idx)

/-- If one component assigns positive probability, then so does the mixture. -/
theorem mixtureProbability_pos_of_component_pos (O : Mettapedia.Computability.Oracle)
    (M : ReflectiveEnvironmentClass O) (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (h : History)
    (hw : 0 < prior.weight ν_idx) (hprob : 0 < historyProbability (envs ν_idx) h) :
    0 < mixtureProbability O M prior envs h := by
  have hpos_ne : prior.weight ν_idx * historyProbability (envs ν_idx) h ≠ 0 := by
    exact mul_ne_zero (ne_of_gt hw) (ne_of_gt hprob)
  have hpos : 0 < prior.weight ν_idx * historyProbability (envs ν_idx) h :=
    lt_of_le_of_ne zero_le (Ne.symm hpos_ne)
  exact lt_of_lt_of_le hpos (le_mixtureProbability O M prior envs ν_idx h)

end Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
