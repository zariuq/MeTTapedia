import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence

/-!
# When the posterior-expected regret vanishes

`expectedRegretOnTrajectory` is the regret of a policy averaged over the
posterior: `Σ_ν w(ν | h_t) · (V*_ν(h_t) - V^π_ν(h_t))`. This file names the
property that it tends to zero along almost every trajectory of the true
environment.

This is a statement about the posterior. It is not asymptotic optimality of
the policy in the true environment, which concerns `V*_μ - V^π_μ` for the true
`μ` alone (see `LeikeStyle.AsymptoticallyOptimalInMean` in `Setup.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorExpectedRegret

open ProbabilityTheory Filter
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence
open scoped ENNReal NNReal

/-- Along almost every trajectory of the true environment, the regret averaged
over the posterior tends to `0`. -/
def PosteriorExpectedRegretVanishes (prior : PriorOverClass) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx)) : Prop :=
  ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
    Filter.Tendsto (fun t => expectedRegretOnTrajectory prior envs agent γ t horizon traj)
      Filter.atTop (nhds 0)

/-- If the policy has no regret in the true environment and the posterior
weight of the true environment tends to one, the posterior-expected regret
vanishes. -/
theorem posteriorExpectedRegretVanishes_of_consistency (prior : PriorOverClass)
    (envs : ℕ → Environment) (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_π_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_consistency : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      Filter.Tendsto
        (fun t => (PosteriorConcentration.posteriorWeight prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 1)) :
    PosteriorExpectedRegretVanishes prior envs agent γ horizon ν_star_idx h_stoch := by
  simpa [PosteriorExpectedRegretVanishes] using
    (consistency_implies_expected_regret_convergence prior envs agent γ horizon
      ν_star_idx h_grain h_stoch h_π_optimal h_consistency)

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorExpectedRegret
