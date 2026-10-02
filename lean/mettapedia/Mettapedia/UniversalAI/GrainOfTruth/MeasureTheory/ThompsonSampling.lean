import Mettapedia.UniversalAI.BayesianAgents.PosteriorSampling
import Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior

/-!
# Posterior sampling over a countable class

The posterior-sampling agent of `BayesianAgents/PosteriorSampling.lean`,
specialized to a countable family `envs : ℕ → Environment` with a
`PriorOverClass`, and the comparison of its posterior with the posterior used
by the learning theory of this directory.

At every history the agent draws an environment from the posterior and takes
the action that is optimal for it over the remaining finite horizon. This is
not the policy of Leike, Lattimore, Orseau and Hutter (2016): their Thompson
sampling policy (Algorithm 2 of Leike's thesis) keeps the drawn environment for
an effective horizon before drawing again, and that is the policy their
Theorem 4 (Theorem 5.25 of the thesis) is about. No optimality statement is
proved here for either policy.

## Main statements

* `mixtureProbability_eq_unnormalizedPosteriorTotal`: the two normalizing
  constants are the same sum.
* `bayesianPosteriorWeight_eq_posteriorWeightNormalized`: the two posteriors
  agree whenever the history has positive mixture probability. They differ
  when it has probability zero: one returns the prior, the other a point mass.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ThompsonSampling

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
open scoped ENNReal NNReal

/-- Posterior-sampling agent over a countable family `envs : ℕ → Environment`:
draw an environment from the posterior at every step and act optimally for it. -/
noncomputable def thompsonSamplingAgent (prior : PriorOverClass) (envs : ℕ → Environment)
    (γ : DiscountFactor) (horizon : ℕ) : Agent :=
  Mettapedia.UniversalAI.BayesianAgents.thompsonSamplingAgent
    (prior := prior.weight) (envs := envs) (h_prior := prior.tsum_le_one) γ horizon

/-- The mixture probability of a history is the normalizing constant of the
posterior of `BayesianAgents/PosteriorSampling.lean`. -/
theorem mixtureProbability_eq_unnormalizedPosteriorTotal (prior : PriorOverClass)
    (envs : ℕ → Environment) (h : History) :
    mixtureProbability prior envs h = unnormalizedPosteriorTotal prior.weight envs h := rfl

/-- On a history of positive mixture probability the two posteriors agree. -/
theorem bayesianPosteriorWeight_eq_posteriorWeightNormalized (prior : PriorOverClass)
    (envs : ℕ → Environment) (h : History) (positive : mixtureProbability prior envs h ≠ 0)
    (index : EnvironmentIndex) :
    bayesianPosteriorWeight prior envs index h =
      posteriorWeightNormalized prior.weight envs h index := by
  have total : unnormalizedPosteriorTotal prior.weight envs h ≠ 0 := positive
  simp [bayesianPosteriorWeight, posteriorWeightNormalized, total,
    mixtureProbability_eq_unnormalizedPosteriorTotal, unnormalizedPosteriorWeight]

/-- On a history of mixture probability zero they differ at every index other
than `0`: the prior weight there is positive, and the point mass at `0` gives
it weight zero. -/
theorem bayesianPosteriorWeight_ne_posteriorWeightNormalized (prior : PriorOverClass)
    (envs : ℕ → Environment) (h : History) (null : mixtureProbability prior envs h = 0)
    (index : EnvironmentIndex) (other : index ≠ 0) :
    bayesianPosteriorWeight prior envs index h ≠
      posteriorWeightNormalized prior.weight envs h index := by
  have total : unnormalizedPosteriorTotal prior.weight envs h = 0 := null
  have left : bayesianPosteriorWeight prior envs index h = prior.weight index := by
    simp [bayesianPosteriorWeight, null]
  have right : posteriorWeightNormalized prior.weight envs h index = 0 := by
    simpa [posteriorWeightNormalized, total] using other
  rw [left, right]
  exact (prior.positive index).ne'

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ThompsonSampling
