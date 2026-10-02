import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# On-Policy Bayes Mixture Measure on Trajectories

Leike-style Chapter 7 arguments (and the Blackwell–Dubins route) work with the *on-policy*
trajectory measures `μ^π` and the corresponding Bayes mixture `ξ^π`.

This module defines `ξ^π` as a (sub-)probability measure on `Trajectory` and records the basic
absolute-continuity fact `μ^π ≪ ξ^π` whenever the prior assigns positive weight to `μ`.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure

open ProbabilityTheory
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open scoped ENNReal NNReal

/-! ## Mixture Measure -/

/-- The on-policy Bayes mixture measure `ξ^π` on trajectories.

We assume `h_stoch` for every environment in the (countable) class, so that each component
`environmentMeasureWithPolicy (envs i) π` is a probability measure.

The resulting mixture has total mass `∑' i, prior.weight i ≤ 1`, so `ξ^π` is a finite measure. -/
noncomputable def mixtureMeasureWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) : MeasureTheory.Measure Trajectory :=
  MeasureTheory.Measure.sum fun i : EnvironmentIndex =>
    (prior.weight i) • environmentMeasureWithPolicy (envs i) π (h_stoch i)

theorem mixtureMeasureWithPolicy_univ (prior : PriorOverClass) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) :
    mixtureMeasureWithPolicy prior envs π h_stoch Set.univ = ∑' i, prior.weight i := by
  classical
  -- Unfold the `Measure.sum` and use that each component is a probability measure.
  simp [mixtureMeasureWithPolicy, environmentMeasureWithPolicy_univ_eq_one,
    MeasureTheory.Measure.smul_apply, smul_eq_mul, mul_one]

instance mixtureMeasureWithPolicy_isFinite
    (prior : PriorOverClass) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) :
    MeasureTheory.IsFiniteMeasure (mixtureMeasureWithPolicy prior envs π h_stoch) := by
  constructor
  have hle : mixtureMeasureWithPolicy prior envs π h_stoch Set.univ ≤ (1 : ℝ≥0∞) := by
    simpa [mixtureMeasureWithPolicy_univ] using prior.tsum_le_one
  exact lt_of_le_of_lt hle ENNReal.one_lt_top

/-! ## Absolute Continuity of Components -/

theorem environmentMeasureWithPolicy_absolutelyContinuous_mixture
    (prior : PriorOverClass) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (i : EnvironmentIndex) :
    MeasureTheory.Measure.AbsolutelyContinuous
        (environmentMeasureWithPolicy (envs i) π (h_stoch i))
        (mixtureMeasureWithPolicy prior envs π h_stoch) := by
  -- `μ ≪ c • μ` for `c ≠ 0`, and `c • μ` is a summand of the mixture.
  have h0 :
      MeasureTheory.Measure.AbsolutelyContinuous
        (environmentMeasureWithPolicy (envs i) π (h_stoch i))
        ((prior.weight i) • environmentMeasureWithPolicy (envs i) π (h_stoch i)) :=
    MeasureTheory.Measure.absolutelyContinuous_smul (prior.positive i).ne'
  -- Now lift to the `Measure.sum` over all indices.
  have h1 :
      MeasureTheory.Measure.AbsolutelyContinuous
        ((prior.weight i) • environmentMeasureWithPolicy (envs i) π (h_stoch i))
        (mixtureMeasureWithPolicy prior envs π h_stoch) := by
    -- `ν ≪ μs i` implies `ν ≪ Measure.sum μs`.
    simpa [mixtureMeasureWithPolicy] using
      (MeasureTheory.Measure.absolutelyContinuous_sum_right (μs := fun j : EnvironmentIndex =>
        (prior.weight j) • environmentMeasureWithPolicy (envs j) π (h_stoch j)) i
        (MeasureTheory.Measure.absolutelyContinuous_rfl))
  exact h0.trans h1

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
