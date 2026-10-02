import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio

/-!
# Phase 3a: Posterior Process (Definitions + Algebra)

This file defines the Bayesian posterior process on trajectories and provides the basic algebraic
rewrite connecting it to likelihood ratios.

It is intentionally “lightweight”: it does **not** prove convergence yet. That is handled in
`PosteriorConcentration.lean`, which imports martingale convergence results and avoids import cycles.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess

open ProbabilityTheory Real
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open scoped ENNReal NNReal

/-! ## Posterior Weight on Trajectories -/

/-- The posterior weight on environment `ν_idx` after observing trajectory up to time `t`.
This is `w(ν | h_t) = w(ν) · ν(h_t) / ξ(h_t)`. -/
noncomputable def posteriorWeight (prior : PriorOverClass) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (t : ℕ) : Trajectory → ℝ≥0∞ :=
  fun traj =>
    let h := trajectoryToHistory traj t
    bayesianPosteriorWeight prior envs ν_idx h

/-- The posterior weight depends only on the first `t` steps. -/
theorem posteriorWeight_adapted (prior : PriorOverClass) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (t : ℕ) :
    ∀ traj₁ traj₂, (∀ i < t, traj₁ i = traj₂ i) →
      posteriorWeight prior envs ν_idx t traj₁ = posteriorWeight prior envs ν_idx t traj₂ := by
  intro traj₁ traj₂ heq
  simp only [posteriorWeight]
  rw [trajectoryToHistory_depends_on_prefix traj₁ traj₂ t heq]

/-! ## Relating Posterior to Likelihood Ratio -/

/-- The posterior weight on `ν_idx` can be expressed via likelihood ratio relative to `ν_star_idx`:

`w(ν | h_t) = w(ν) · (ν(h_t)/ν*(h_t)) / (Σ_μ w(μ) · (μ(h_t)/ν*(h_t)))`.
-/
theorem posteriorWeight_via_likelihoodRatio (prior : PriorOverClass) (envs : ℕ → Environment)
    (ν_star_idx : EnvironmentIndex) (ν_idx : EnvironmentIndex) (t : ℕ) (traj : Trajectory)
    (hξ : mixtureProbability prior envs (trajectoryToHistory traj t) > 0)
    (h_star : historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0) :
    posteriorWeight prior envs ν_idx t traj =
      prior.weight ν_idx * likelihoodRatio (envs ν_idx) (envs ν_star_idx) t traj /
        (∑' μ_idx, prior.weight μ_idx * likelihoodRatio (envs μ_idx) (envs ν_star_idx) t traj) := by
  classical
  set h : History := trajectoryToHistory traj t
  set ν_star : Environment := envs ν_star_idx
  have hξ0 : mixtureProbability prior envs h ≠ 0 := ne_of_gt (by simpa [h] using hξ)
  have h_star_top : historyProbability ν_star h ≠ ∞ :=
    (lt_of_le_of_lt (historyProbability_le_one ν_star h) ENNReal.one_lt_top).ne

  have h_denom :
      mixtureProbability prior envs h / historyProbability ν_star h =
        ∑' μ_idx, prior.weight μ_idx * likelihoodRatio (envs μ_idx) ν_star t traj := by
    simp only [likelihoodRatio, h, ν_star]
    -- Factor out the common division by `ν_star(h)`.
    have :
        (∑' μ_idx, prior.weight μ_idx * historyProbability (envs μ_idx) h) *
            (historyProbability ν_star h)⁻¹ =
          ∑' μ_idx, (prior.weight μ_idx * historyProbability (envs μ_idx) h) *
            (historyProbability ν_star h)⁻¹ := by
          simpa using
            (ENNReal.tsum_mul_right
              (f := fun μ_idx => prior.weight μ_idx * historyProbability (envs μ_idx) h)
              (a := (historyProbability ν_star h)⁻¹)).symm
    calc
      mixtureProbability prior envs h / historyProbability ν_star h
          = (∑' μ_idx, prior.weight μ_idx * historyProbability (envs μ_idx) h) *
              (historyProbability ν_star h)⁻¹ := by
              simp [mixtureProbability, h, div_eq_mul_inv]
      _ = ∑' μ_idx, (prior.weight μ_idx * historyProbability (envs μ_idx) h) *
            (historyProbability ν_star h)⁻¹ := this
      _ = ∑' μ_idx, prior.weight μ_idx * (historyProbability (envs μ_idx) h / historyProbability ν_star h) := by
            refine tsum_congr ?_
            intro μ_idx
            simp [div_eq_mul_inv, mul_assoc]

  have h_cancel :
      (prior.weight ν_idx * likelihoodRatio (envs ν_idx) ν_star t traj) /
          (mixtureProbability prior envs h / historyProbability ν_star h) =
        (prior.weight ν_idx * historyProbability (envs ν_idx) h) /
          mixtureProbability prior envs h := by
    have h_star_inv0 : (historyProbability ν_star h)⁻¹ ≠ 0 :=
      (ENNReal.inv_ne_zero.2 h_star_top)
    have h_star_inv_top : (historyProbability ν_star h)⁻¹ ≠ ∞ :=
      (ENNReal.inv_ne_top.2 h_star)
    calc
      (prior.weight ν_idx * likelihoodRatio (envs ν_idx) ν_star t traj) /
            (mixtureProbability prior envs h / historyProbability ν_star h)
          = ((prior.weight ν_idx * historyProbability (envs ν_idx) h) *
                (historyProbability ν_star h)⁻¹) /
              (mixtureProbability prior envs h * (historyProbability ν_star h)⁻¹) := by
              simp [likelihoodRatio, h, ν_star, div_eq_mul_inv, mul_assoc]
      _ = (prior.weight ν_idx * historyProbability (envs ν_idx) h) /
            mixtureProbability prior envs h := by
            simpa using
              (ENNReal.mul_div_mul_right
                (a := prior.weight ν_idx * historyProbability (envs ν_idx) h)
                (b := mixtureProbability prior envs h)
                (c := (historyProbability ν_star h)⁻¹) h_star_inv0 h_star_inv_top)

  have h_post :
      posteriorWeight prior envs ν_idx t traj =
        (prior.weight ν_idx * historyProbability (envs ν_idx) h) /
          mixtureProbability prior envs h := by
    simp [posteriorWeight, bayesianPosteriorWeight, h, hξ0]

  calc
    posteriorWeight prior envs ν_idx t traj
        = (prior.weight ν_idx * historyProbability (envs ν_idx) h) /
            mixtureProbability prior envs h := h_post
    _ = (prior.weight ν_idx * likelihoodRatio (envs ν_idx) ν_star t traj) /
          (mixtureProbability prior envs h / historyProbability ν_star h) := by
          simpa using h_cancel.symm
    _ = prior.weight ν_idx * likelihoodRatio (envs ν_idx) ν_star t traj /
          (∑' μ_idx, prior.weight μ_idx * likelihoodRatio (envs μ_idx) ν_star t traj) := by
          simp [h_denom]

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess
