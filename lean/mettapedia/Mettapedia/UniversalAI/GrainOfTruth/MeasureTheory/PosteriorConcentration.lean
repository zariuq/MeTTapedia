import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Phase 3b: Posterior Concentration (Convergence Layer)

`PosteriorProcess.lean` defines the posterior process on trajectories and proves basic algebraic
rewrites (e.g. posterior weight via likelihood ratios).

This module re-exports those definitions under the historical namespace
`...PosteriorConcentration` so downstream files don’t need to be updated, and is the intended home
for the *convergence* lemmas (martingale convergence / Blackwell–Dubins-style merging).
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration

open ProbabilityTheory Real Filter
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.BayesianPosterior
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorMartingale
open scoped ENNReal NNReal

export Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorProcess
  (posteriorWeight posteriorWeight_adapted posteriorWeight_via_likelihoodRatio)

/-! ## Martingale convergence for posterior weights -/

/-- The posterior process `t ↦ posteriorReal ... t` converges almost surely under the on-policy
mixture measure `ξ^π`.

This is the “bounded martingale convergence” backbone used in Leike-style arguments. -/
theorem posteriorReal_ae_tendsto_limitProcess
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ν_idx : EnvironmentIndex) :
    ∀ᵐ traj ∂(ξ prior envs pi h_stoch),
      Tendsto (fun t => posteriorReal prior envs ν_idx t traj) atTop
        (nhds (trajectoryFiltration.limitProcess (posteriorReal prior envs ν_idx)
          (ξ prior envs pi h_stoch) traj)) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := ξ prior envs pi h_stoch
  have : MeasureTheory.IsFiniteMeasure μ := inferInstance

  have hM :
      MeasureTheory.Martingale (posteriorReal prior envs ν_idx) trajectoryFiltration μ := by
    simpa [μ] using
      (posteriorReal_martingale (prior := prior) (envs := envs) pi h_stoch ν_idx)
  have hSub : MeasureTheory.Submartingale (posteriorReal prior envs ν_idx) trajectoryFiltration μ :=
    hM.submartingale

  have hbdd : ∀ t, MeasureTheory.eLpNorm (posteriorReal prior envs ν_idx t) 1 μ ≤ (1 : ENNReal) := by
    intro t
    have hbound :
        ∀ᵐ traj ∂μ, ‖posteriorReal prior envs ν_idx t traj‖ ≤ (1 : ℝ) := by
      refine Eventually.of_forall (fun traj => ?_)
      have h0 : 0 ≤ posteriorReal prior envs ν_idx t traj := ENNReal.toReal_nonneg
      have h1 : posteriorReal prior envs ν_idx t traj ≤ 1 :=
        posteriorReal_le_one (prior := prior) (envs := envs) (ν_idx := ν_idx) t traj
      simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
    have hLp :
        MeasureTheory.eLpNorm (posteriorReal prior envs ν_idx t) 1 μ ≤ μ Set.univ := by
      -- `eLpNorm_le_of_ae_bound` specializes to an `L¹` bound by the mass of the space.
      simpa using
        (MeasureTheory.eLpNorm_le_of_ae_bound (μ := μ) (p := (1 : ℝ≥0∞))
          (f := posteriorReal prior envs ν_idx t) (C := (1 : ℝ)) hbound)
    have hμ : μ Set.univ ≤ (1 : ℝ≥0∞) := by
      -- The mixture has total mass `∑' i, prior.weight i ≤ 1`.
      simpa [μ, ξ, mixtureMeasureWithPolicy_univ] using prior.tsum_le_one
    exact le_trans hLp hμ

  simpa [μ] using (hSub.ae_tendsto_limitProcess (R := (1 : NNReal)) hbdd)

/-- A dominated-convergence hypothesis ensuring that we can swap `t → ∞` with the countable sum
over environment indices for the weighted likelihood ratios along a fixed trajectory. -/
def DominatedLikelihoodRatioSeries
    (prior : PriorOverClass) (envs : ℕ → Environment) (ν_star_idx : EnvironmentIndex)
    (traj : Trajectory) : Prop :=
  ∃ bound : EnvironmentIndex → ℝ,
    Summable bound ∧
      (∀ᶠ t in atTop, ∀ i : EnvironmentIndex,
        ‖(prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal‖ ≤ bound i)

/-! ## Posterior concentration on the true environment -/

/-- **Posterior concentration**: if every wrong environment is identifiable (log-likelihood ratio
tends to `-∞`) under the on-policy trajectory measure, and the weighted likelihood-ratio series is
dominated in the sense of `DominatedLikelihoodRatioSeries`, then the posterior weight on the true
environment tends to `1` almost surely under the true environment measure. -/
theorem posteriorWeight_true_ae_tendsto_one_of_identifiableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_ident : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      IdentifiableWithPolicy (envs i) (envs ν_star_idx) pi h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t =>
        (posteriorWeight prior envs ν_star_idx t traj).toReal) atTop (nhds 1) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch

  have h_eventually_trueHistPos :
      ∀ᵐ traj ∂μ, ∀ᶠ t in atTop,
        (historyProbability (envs ν_star_idx) (trajectoryToHistory traj t)).toReal > 0 := by
    -- This holds without identifiability: probability-0 transitions occur with probability 0.
    have h_all :
        ∀ᵐ traj ∂μ, ∀ t : ℕ,
          (historyProbability (envs ν_star_idx) (trajectoryToHistory traj t)).toReal > 0 := by
      simpa [μ] using
        (ae_forall_historyProbability_toReal_pos (μ := envs ν_star_idx) (pi := pi) (h_stoch := h_stoch))
    filter_upwards [h_all] with traj htraj
    -- Strengthen `∀ t` to `∀ᶠ t`.
    exact Filter.Eventually.of_forall (fun t => htraj t)

  have h_lr_wrong :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂μ,
          Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) := by
    intro i hi
    exact likelihoodRatio_converges_to_zero_of_identifiableWithPolicy (ν := envs i) (ν_star := envs ν_star_idx)
      (pi := pi) h_stoch (h_ident i hi)

  -- Assemble the “for all i” version using `ae_all_iff` (countable intersection).
  have h_lr_wrong_all :
      ∀ᵐ traj ∂μ, ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) := by
    -- First package the per-index statements as a predicate `p traj i`.
    have h_each : ∀ i : EnvironmentIndex, ∀ᵐ traj ∂μ,
        (i ≠ ν_star_idx →
          Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0)) := by
      intro i
      by_cases hi : i = ν_star_idx
      · subst hi
        refine MeasureTheory.ae_of_all μ (fun traj => ?_)
        intro h
        exact (h rfl).elim
      · have h_lr : ∀ᵐ traj ∂μ,
            Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) :=
          h_lr_wrong i hi
        -- Strengthen to an implication; the antecedent is always true here.
        filter_upwards [h_lr] with traj htraj
        intro _
        exact htraj
    -- Now interchange `∀ i` and `∀ᵐ traj`.
    have h_all : ∀ᵐ traj ∂μ, ∀ i : EnvironmentIndex,
        (i ≠ ν_star_idx →
          Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0)) := by
      exact (MeasureTheory.ae_all_iff).2 h_each
    simpa using h_all

  -- Main argument: on a trajectory satisfying the pointwise limits, domination, and eventual
  -- positivity of the true history-probability, we can use Tannery + algebra to show posterior→1.
  filter_upwards [h_dom, h_eventually_trueHistPos, h_lr_wrong_all] with traj hDom hPos hLrAll

  rcases hDom with ⟨bound, hBoundSummable, hBound⟩

  -- Define the real-valued weighted likelihood-ratio family.
  let f : ℕ → EnvironmentIndex → ℝ := fun t i =>
    (prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal
  let g : EnvironmentIndex → ℝ := fun i =>
    if i = ν_star_idx then (prior.weight ν_star_idx).toReal else 0

  have h_tsum_f_tendsto :
      Tendsto (fun t => ∑' i, f t i) atTop (nhds (∑' i, g i)) := by
    refine tendsto_tsum_of_dominated_convergence (β := EnvironmentIndex) (G := ℝ)
      (f := f) (g := g) (bound := bound) hBoundSummable ?_ ?_
    · intro i
      by_cases hi : i = ν_star_idx
      · subst i
        -- Eventually, the true history-probability is positive, so likelihoodRatio = 1.
        have h_eventually_lr_one : ∀ᶠ t in atTop,
            (likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal = 1 := by
          filter_upwards [hPos] with t ht
          have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
            (ENNReal.toReal_pos_iff).1 ht |>.1
          have h_hist_ne0 :
              historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
            ne_of_gt h_hist_posENN
          have h_hist_ne_top :
              historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ ∞ :=
            (lt_of_le_of_lt (historyProbability_le_one (envs ν_star_idx) (trajectoryToHistory traj t))
              ENNReal.one_lt_top).ne
          have h_lr : likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj = 1 := by
            -- `p/p = 1` since the prefix probability is positive (hence not 0 and not ∞).
            dsimp [likelihoodRatio]
            exact ENNReal.div_self h_hist_ne0 h_hist_ne_top
          simp [h_lr]

        -- Thus `f t ν*` is eventually constant `prior.weight ν*.toReal`.
        have h_eventually_f :
            (fun t => f t ν_star_idx) =ᶠ[atTop] fun _ => (prior.weight ν_star_idx).toReal := by
          filter_upwards [h_eventually_lr_one] with t ht
          simp [f, ht]
        -- Conclude by eventual equality to a constant.
        have h_const :
            Tendsto (fun _ : ℕ => (prior.weight ν_star_idx).toReal) atTop (nhds (g ν_star_idx)) := by
          simp [g]
        exact h_const.congr' h_eventually_f.symm
      · -- Wrong environments: likelihoodRatio.toReal → 0, hence weighted version → 0.
        have h_lr : Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) :=
          hLrAll i hi
        have h_mul :
            Tendsto (fun t => (prior.weight i).toReal * (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
              atTop (nhds ((prior.weight i).toReal * 0)) :=
          (tendsto_const_nhds.mul h_lr)
        -- Rewrite `f` via `toReal_mul` and finish.
        have : Tendsto (fun t => f t i) atTop (nhds ((prior.weight i).toReal * 0)) := by
          simpa [f, ENNReal.toReal_mul, mul_assoc] using h_mul
        simpa [g, hi] using this
    · -- Domination hypothesis.
      simpa [f] using hBound

  have h_tsum_g : (∑' i, g i) = (prior.weight ν_star_idx).toReal := by
    -- Only one nonzero term in the series.
    simp [g]

  have h_denom_toReal_tendsto :
      Tendsto (fun t =>
        (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
        atTop (nhds (prior.weight ν_star_idx).toReal) := by
    -- For large t, the true history-probability is positive, so no likelihood ratio is `∞`,
    -- allowing us to rewrite toReal(tsum) as tsum(toReal).
    have h_eventually_terms_ne_top :
        ∀ᶠ t in atTop, ∀ i : EnvironmentIndex,
          prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj ≠ ∞ := by
      filter_upwards [hPos] with t ht i
      have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.toReal_pos_iff).1 ht |>.1
      have h_hist_ne0 :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
        ne_of_gt h_hist_posENN
      -- Numerator is ≤ 1, so it is not `∞`.
      have h_num_ne_top :
          historyProbability (envs i) (trajectoryToHistory traj t) ≠ ∞ :=
        (lt_of_le_of_lt (historyProbability_le_one (envs i) (trajectoryToHistory traj t)) ENNReal.one_lt_top).ne
      have h_lr_ne_top :
          likelihoodRatio (envs i) (envs ν_star_idx) t traj ≠ ∞ := by
        -- `a / b ≠ ∞` if `a ≠ ∞` and `b ≠ 0`.
        simpa [likelihoodRatio] using
          (ENNReal.div_ne_top h_num_ne_top (by simpa [trajectoryToHistory] using h_hist_ne0))
      have h_w_ne_top : prior.weight i ≠ ∞ := by
        have hle : prior.weight i ≤ (1 : ℝ≥0∞) := by
          exact le_trans (ENNReal.le_tsum i) prior.tsum_le_one
        exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne
      exact ENNReal.mul_ne_top h_w_ne_top h_lr_ne_top

    have h_eventually_denom_eq :
        (fun t =>
          (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
          =ᶠ[atTop]
        (fun t => ∑' i, f t i) := by
      filter_upwards [h_eventually_terms_ne_top] with t ht
      have : (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal =
          ∑' i, (prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal :=
        ENNReal.tsum_toReal_eq (f := fun i =>
          prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj) (by simpa using ht)
      simpa [f] using this

    -- Apply the Tannery convergence result via the eventual equality.
    have h_tendsto_real :
        Tendsto (fun t => ∑' i, f t i) atTop (nhds (prior.weight ν_star_idx).toReal) := by
      simpa [h_tsum_g] using h_tsum_f_tendsto
    exact h_tendsto_real.congr' h_eventually_denom_eq.symm

  -- Numerator is eventually constant.
  have h_num_toReal_tendsto :
      Tendsto (fun t =>
        (prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal)
        atTop (nhds (prior.weight ν_star_idx).toReal) := by
    have h_eventually_lr_one : ∀ᶠ t in atTop,
        (likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal = 1 := by
      filter_upwards [hPos] with t ht
      have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.toReal_pos_iff).1 ht |>.1
      have h_hist_ne0 :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
        ne_of_gt h_hist_posENN
      have h_hist_ne_top :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ ∞ :=
        (lt_of_le_of_lt (historyProbability_le_one (envs ν_star_idx) (trajectoryToHistory traj t))
          ENNReal.one_lt_top).ne
      have h_lr : likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj = 1 := by
        dsimp [likelihoodRatio]
        exact ENNReal.div_self h_hist_ne0 h_hist_ne_top
      simp [h_lr]

    have h_eventually_num :
        (fun t =>
          (prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal)
          =ᶠ[atTop] fun _ => (prior.weight ν_star_idx).toReal := by
      filter_upwards [h_eventually_lr_one] with t ht
      simp [ENNReal.toReal_mul, ht]

    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (prior.weight ν_star_idx).toReal) atTop
      (nhds (prior.weight ν_star_idx).toReal)).congr' h_eventually_num.symm

  have h_wtrue_toReal_pos : 0 < (prior.weight ν_star_idx).toReal := by
    have h_lt_top : prior.weight ν_star_idx < ∞ := by
      have hle : prior.weight ν_star_idx ≤ (1 : ℝ≥0∞) := le_trans (ENNReal.le_tsum ν_star_idx) prior.tsum_le_one
      exact lt_of_le_of_lt hle ENNReal.one_lt_top
    exact (ENNReal.toReal_pos_iff).2 ⟨prior.positive ν_star_idx, h_lt_top⟩

  -- Finally, rewrite posteriorWeight via likelihood ratios and take limits.
  have h_eventually_posterior_eq :
      (fun t => (posteriorWeight prior envs ν_star_idx t traj).toReal)
        =ᶠ[atTop] fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
              (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal := by
    filter_upwards [hPos] with t ht
    have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
      (ENNReal.toReal_pos_iff).1 ht |>.1
    have h_hist_ne0 :
        historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
      ne_of_gt h_hist_posENN
    have h_mix_pos : mixtureProbability prior envs (trajectoryToHistory traj t) > 0 := by
      have h_term_pos : 0 < prior.weight ν_star_idx * historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.mul_pos_iff).2 ⟨prior.positive ν_star_idx, h_hist_posENN⟩
      have h_term_le :
          prior.weight ν_star_idx * historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≤
            mixtureProbability prior envs (trajectoryToHistory traj t) := by
        simpa [mixtureProbability] using (ENNReal.le_tsum ν_star_idx)
      exact lt_of_lt_of_le h_term_pos h_term_le
    -- Convert the ENNReal equality to its `toReal` version.
    exact congrArg ENNReal.toReal
      (posteriorWeight_via_likelihoodRatio (prior := prior) (envs := envs)
        (ν_star_idx := ν_star_idx) (ν_idx := ν_star_idx) (t := t) (traj := traj) h_mix_pos h_hist_ne0)

  have h_posterior_toReal_tendsto :
      Tendsto (fun t =>
        ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
            (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal)
        atTop (nhds 1) := by
    -- Use `toReal_div` to reduce to a real division.
    have h_posterior_div :
        (fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
              (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal)
          = fun t =>
            ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal) /
              ((∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) := by
      funext t
      simp [ENNReal.toReal_div]

    -- Apply `tendsto.div`.
    have h_div :
        Tendsto (fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal) /
            ((∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal))
          atTop (nhds ((prior.weight ν_star_idx).toReal / (prior.weight ν_star_idx).toReal)) :=
      (h_num_toReal_tendsto.div h_denom_toReal_tendsto (ne_of_gt h_wtrue_toReal_pos))

    simpa [h_posterior_div] using (by
      simpa [div_self (ne_of_gt h_wtrue_toReal_pos)] using h_div)

  -- Transfer from the eventual equality to the desired statement.
  exact h_posterior_toReal_tendsto.congr' h_eventually_posterior_eq.symm

/-- `posteriorReal` is just `(posteriorWeight ...).toReal`, so posterior concentration can also be
stated as `posteriorReal → 1`. -/
theorem posteriorReal_true_ae_tendsto_one_of_identifiableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_ident : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      IdentifiableWithPolicy (envs i) (envs ν_star_idx) pi h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t => posteriorReal prior envs ν_star_idx t traj) atTop (nhds 1) := by
  simpa [posteriorReal] using
    (posteriorWeight_true_ae_tendsto_one_of_identifiableWithPolicy
      (prior := prior) (envs := envs) (pi := pi) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      h_ident h_dom)

/-- Variant of `posteriorWeight_true_ae_tendsto_one_of_identifiableWithPolicy` that takes the
likelihood-ratio limits for wrong environments as a direct hypothesis, avoiding the log-likelihood
packaging. -/
theorem posteriorWeight_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_lr : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
        Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0))
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t =>
        (posteriorWeight prior envs ν_star_idx t traj).toReal) atTop (nhds 1) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch

  have h_eventually_trueHistPos :
      ∀ᵐ traj ∂μ, ∀ᶠ t in atTop,
        (historyProbability (envs ν_star_idx) (trajectoryToHistory traj t)).toReal > 0 := by
    have h_all :
        ∀ᵐ traj ∂μ, ∀ t : ℕ,
          (historyProbability (envs ν_star_idx) (trajectoryToHistory traj t)).toReal > 0 := by
      simpa [μ] using
        (ae_forall_historyProbability_toReal_pos (μ := envs ν_star_idx) (pi := pi) (h_stoch := h_stoch))
    filter_upwards [h_all] with traj htraj
    exact Filter.Eventually.of_forall (fun t => htraj t)

  -- Assemble the “for all i” version using `ae_all_iff` (countable intersection).
  have h_lr_wrong_all :
      ∀ᵐ traj ∂μ, ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) := by
    have h_each : ∀ i : EnvironmentIndex, ∀ᵐ traj ∂μ,
        (i ≠ ν_star_idx →
          Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0)) := by
      intro i
      by_cases hi : i = ν_star_idx
      · subst hi
        refine MeasureTheory.ae_of_all μ (fun traj => ?_)
        intro h
        exact (h rfl).elim
      · have h_lr_i : ∀ᵐ traj ∂μ,
            Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) :=
          h_lr i hi
        filter_upwards [h_lr_i] with traj htraj
        intro _
        exact htraj
    exact (MeasureTheory.ae_all_iff).2 h_each

  -- Main argument: on a trajectory satisfying the pointwise limits, domination, and eventual
  -- positivity of the true history-probability, we can use Tannery + algebra to show posterior→1.
  filter_upwards [h_dom, h_eventually_trueHistPos, h_lr_wrong_all] with traj hDom hPos hLrAll

  rcases hDom with ⟨bound, hBoundSummable, hBound⟩

  -- Define the real-valued weighted likelihood-ratio family.
  let f : ℕ → EnvironmentIndex → ℝ := fun t i =>
    (prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal
  let g : EnvironmentIndex → ℝ := fun i =>
    if i = ν_star_idx then (prior.weight ν_star_idx).toReal else 0

  have h_tsum_f_tendsto :
      Tendsto (fun t => ∑' i, f t i) atTop (nhds (∑' i, g i)) := by
    refine tendsto_tsum_of_dominated_convergence (β := EnvironmentIndex) (G := ℝ)
      (f := f) (g := g) (bound := bound) hBoundSummable ?_ ?_
    · intro i
      by_cases hi : i = ν_star_idx
      · subst i
        -- Eventually, the true history-probability is positive, so likelihoodRatio = 1.
        have h_eventually_lr_one : ∀ᶠ t in atTop,
            (likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal = 1 := by
          filter_upwards [hPos] with t ht
          have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
            (ENNReal.toReal_pos_iff).1 ht |>.1
          have h_hist_ne0 :
              historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
            ne_of_gt h_hist_posENN
          have h_hist_ne_top :
              historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ ∞ :=
            (lt_of_le_of_lt (historyProbability_le_one (envs ν_star_idx) (trajectoryToHistory traj t))
              ENNReal.one_lt_top).ne
          have h_lr : likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj = 1 := by
            -- `p/p = 1` since the prefix probability is positive (hence not 0 and not ∞).
            dsimp [likelihoodRatio]
            exact ENNReal.div_self h_hist_ne0 h_hist_ne_top
          simp [h_lr]

        -- Thus `f t ν*` is eventually constant `prior.weight ν*.toReal`.
        have h_eventually_f :
            (fun t => f t ν_star_idx) =ᶠ[atTop] fun _ => (prior.weight ν_star_idx).toReal := by
          filter_upwards [h_eventually_lr_one] with t ht
          simp [f, ht]
        -- Conclude by eventual equality to a constant.
        have h_const :
            Tendsto (fun _ : ℕ => (prior.weight ν_star_idx).toReal) atTop (nhds (g ν_star_idx)) := by
          simp [g]
        exact h_const.congr' h_eventually_f.symm
      · -- Wrong environments: likelihoodRatio.toReal → 0, hence weighted version → 0.
        have h_lr_i :
            Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) :=
          hLrAll i hi
        have h_mul :
            Tendsto (fun t => (prior.weight i).toReal * (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
              atTop (nhds ((prior.weight i).toReal * 0)) :=
          (tendsto_const_nhds.mul h_lr_i)
        -- Rewrite `f` via `toReal_mul` and finish.
        have : Tendsto (fun t => f t i) atTop (nhds ((prior.weight i).toReal * 0)) := by
          simpa [f, ENNReal.toReal_mul, mul_assoc] using h_mul
        simpa [g, hi] using this
    · -- Domination hypothesis.
      simpa [f] using hBound

  have h_tsum_g : (∑' i, g i) = (prior.weight ν_star_idx).toReal := by
    -- Only one nonzero term in the series.
    simp [g]

  have h_denom_toReal_tendsto :
      Tendsto (fun t =>
        (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
        atTop (nhds (prior.weight ν_star_idx).toReal) := by
    -- For large t, the true history-probability is positive, so no likelihood ratio is `∞`,
    -- allowing us to rewrite toReal(tsum) as tsum(toReal).
    have h_eventually_terms_ne_top :
        ∀ᶠ t in atTop, ∀ i : EnvironmentIndex,
          prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj ≠ ∞ := by
      filter_upwards [hPos] with t ht i
      have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.toReal_pos_iff).1 ht |>.1
      have h_hist_ne0 :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
        ne_of_gt h_hist_posENN
      -- Numerator is ≤ 1, so it is not `∞`.
      have h_num_ne_top :
          historyProbability (envs i) (trajectoryToHistory traj t) ≠ ∞ :=
        (lt_of_le_of_lt (historyProbability_le_one (envs i) (trajectoryToHistory traj t)) ENNReal.one_lt_top).ne
      have h_lr_ne_top :
          likelihoodRatio (envs i) (envs ν_star_idx) t traj ≠ ∞ := by
        -- `a / b ≠ ∞` if `a ≠ ∞` and `b ≠ 0`.
        simpa [likelihoodRatio] using
          (ENNReal.div_ne_top h_num_ne_top (by simpa [trajectoryToHistory] using h_hist_ne0))
      have h_w_ne_top : prior.weight i ≠ ∞ := by
        have hle : prior.weight i ≤ (1 : ℝ≥0∞) := by
          exact le_trans (ENNReal.le_tsum i) prior.tsum_le_one
        exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top
      exact ENNReal.mul_ne_top h_w_ne_top h_lr_ne_top

    have h_eventually_denom_eq :
        (fun t =>
          (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
          =ᶠ[atTop]
        (fun t => ∑' i, f t i) := by
      filter_upwards [h_eventually_terms_ne_top] with t ht
      have : (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal =
          ∑' i, (prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal :=
        ENNReal.tsum_toReal_eq (f := fun i =>
          prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj) (by simpa using ht)
      simpa [f] using this

    -- Apply the Tannery convergence result via the eventual equality.
    have h_tendsto_real :
        Tendsto (fun t => ∑' i, f t i) atTop (nhds (prior.weight ν_star_idx).toReal) := by
      simpa [h_tsum_g] using h_tsum_f_tendsto
    exact h_tendsto_real.congr' h_eventually_denom_eq.symm

  -- Numerator is eventually constant.
  have h_num_toReal_tendsto :
      Tendsto (fun t =>
        (prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal)
        atTop (nhds (prior.weight ν_star_idx).toReal) := by
    have h_eventually_lr_one : ∀ᶠ t in atTop,
        (likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal = 1 := by
      filter_upwards [hPos] with t ht
      have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.toReal_pos_iff).1 ht |>.1
      have h_hist_ne0 :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
        ne_of_gt h_hist_posENN
      have h_hist_ne_top :
          historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ ∞ :=
        (lt_of_le_of_lt (historyProbability_le_one (envs ν_star_idx) (trajectoryToHistory traj t))
          ENNReal.one_lt_top).ne
      have h_lr : likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj = 1 := by
        dsimp [likelihoodRatio]
        exact ENNReal.div_self h_hist_ne0 h_hist_ne_top
      simp [h_lr]

    have h_eventually_num :
        (fun t =>
          (prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal)
          =ᶠ[atTop] fun _ => (prior.weight ν_star_idx).toReal := by
      filter_upwards [h_eventually_lr_one] with t ht
      simp [ENNReal.toReal_mul, ht]

    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (prior.weight ν_star_idx).toReal) atTop
      (nhds (prior.weight ν_star_idx).toReal)).congr' h_eventually_num.symm

  have h_wtrue_toReal_pos : 0 < (prior.weight ν_star_idx).toReal := by
    have h_lt_top : prior.weight ν_star_idx < ∞ := by
      have hle : prior.weight ν_star_idx ≤ (1 : ℝ≥0∞) := le_trans (ENNReal.le_tsum ν_star_idx) prior.tsum_le_one
      exact lt_of_le_of_lt hle ENNReal.one_lt_top
    exact (ENNReal.toReal_pos_iff).2 ⟨prior.positive ν_star_idx, h_lt_top⟩

  -- Finally, rewrite posteriorWeight via likelihood ratios and take limits.
  have h_eventually_posterior_eq :
      (fun t => (posteriorWeight prior envs ν_star_idx t traj).toReal)
        =ᶠ[atTop] fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
              (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal := by
    filter_upwards [hPos] with t ht
    have h_hist_posENN : 0 < historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
      (ENNReal.toReal_pos_iff).1 ht |>.1
    have h_hist_ne0 :
        historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≠ 0 :=
      ne_of_gt h_hist_posENN
    have h_mix_pos : mixtureProbability prior envs (trajectoryToHistory traj t) > 0 := by
      have h_term_pos : 0 < prior.weight ν_star_idx * historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) :=
        (ENNReal.mul_pos_iff).2 ⟨prior.positive ν_star_idx, h_hist_posENN⟩
      have h_term_le :
          prior.weight ν_star_idx * historyProbability (envs ν_star_idx) (trajectoryToHistory traj t) ≤
            mixtureProbability prior envs (trajectoryToHistory traj t) := by
        simpa [mixtureProbability] using (ENNReal.le_tsum ν_star_idx)
      exact lt_of_lt_of_le h_term_pos h_term_le
    -- Convert the ENNReal equality to its `toReal` version.
    exact congrArg ENNReal.toReal
      (posteriorWeight_via_likelihoodRatio (prior := prior) (envs := envs)
        (ν_star_idx := ν_star_idx) (ν_idx := ν_star_idx) (t := t) (traj := traj) h_mix_pos h_hist_ne0)

  have h_posterior_toReal_tendsto :
      Tendsto (fun t =>
        ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
            (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal)
        atTop (nhds 1) := by
    -- Use `toReal_div` to reduce to a real division.
    have h_posterior_div :
        (fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj) /
              (∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj)).toReal)
          = fun t =>
            ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal) /
              ((∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) := by
      funext t
      simp [ENNReal.toReal_div]

    -- Apply `tendsto.div`.
    have h_div :
        Tendsto (fun t =>
          ((prior.weight ν_star_idx * likelihoodRatio (envs ν_star_idx) (envs ν_star_idx) t traj).toReal) /
            ((∑' i, prior.weight i * likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal))
          atTop (nhds ((prior.weight ν_star_idx).toReal / (prior.weight ν_star_idx).toReal)) :=
      (h_num_toReal_tendsto.div h_denom_toReal_tendsto (ne_of_gt h_wtrue_toReal_pos))

    simpa [h_posterior_div] using (by
      simpa [div_self (ne_of_gt h_wtrue_toReal_pos)] using h_div)

  -- Transfer from the eventual equality to the desired statement.
  exact h_posterior_toReal_tendsto.congr' h_eventually_posterior_eq.symm

/-- Likelihood-ratio variant of `posteriorReal_true_ae_tendsto_one_of_identifiableWithPolicy`. -/
theorem posteriorReal_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_lr : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
        Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0))
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t => posteriorReal prior envs ν_star_idx t traj) atTop (nhds 1) := by
  simpa [posteriorReal] using
    (posteriorWeight_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
      (prior := prior) (envs := envs) (pi := pi) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      (h_lr := h_lr) (h_dom := h_dom))

/-- A convenient Leike-style sufficient condition for posterior concentration:
if every wrong environment has a uniform geometric bound `stepLR ≤ r < 1` eventually along true
on-policy trajectories, then the posterior on the true environment tends to `1`. -/
theorem posteriorReal_true_ae_tendsto_one_of_eventually_stepLikelihoodRatio_le
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_step : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∃ r : ℝ≥0∞, r < 1 ∧
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
          ∀ᶠ t in atTop, stepLikelihoodRatio (envs i) (envs ν_star_idx) t traj ≤ r)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t => posteriorReal prior envs ν_star_idx t traj) atTop (nhds 1) := by
  have h_lr : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
        Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) := by
    intro i hi
    rcases h_step i hi with ⟨r, hr, h_step_i⟩
    simpa using
      (likelihoodRatio_converges_to_zero_of_eventually_stepLikelihoodRatio_le
        (ν := envs i) (ν_star := envs ν_star_idx) (pi := pi) (h_stoch := h_stoch) hr h_step_i)
  exact posteriorReal_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
    (prior := prior) (envs := envs) (pi := pi) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
    (h_lr := h_lr) (h_dom := h_dom)

/-- A convenient sufficient condition for posterior concentration: every wrong environment is
refutable by a finite prefix on almost every true on-policy trajectory. -/
theorem posteriorWeight_true_ae_tendsto_one_of_refutableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_ref : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      RefutableWithPolicy (envs i) (envs ν_star_idx) pi h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t =>
        (posteriorWeight prior envs ν_star_idx t traj).toReal) atTop (nhds 1) := by
  have h_lr :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
          Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal) atTop (nhds 0) := by
    intro i hi
    simpa using
      (likelihoodRatio_converges_to_zero_of_refutableWithPolicy (ν := envs i) (ν_star := envs ν_star_idx) (pi := pi)
        (h_stoch := h_stoch) (h_ref := h_ref i hi))
  exact posteriorWeight_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero
    (prior := prior) (envs := envs) (pi := pi) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
    (h_lr := h_lr) (h_dom := h_dom)

/-- `posteriorReal` version of `posteriorWeight_true_ae_tendsto_one_of_refutableWithPolicy`. -/
theorem posteriorReal_true_ae_tendsto_one_of_refutableWithPolicy
    (prior : PriorOverClass) (envs : ℕ → Environment) (pi : Agent)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx))
    (h_ref : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      RefutableWithPolicy (envs i) (envs ν_star_idx) pi h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      DominatedLikelihoodRatioSeries prior envs ν_star_idx traj) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) pi h_stoch),
      Tendsto (fun t => posteriorReal prior envs ν_star_idx t traj) atTop (nhds 1) := by
  simpa [posteriorReal] using
    (posteriorWeight_true_ae_tendsto_one_of_refutableWithPolicy (prior := prior)
      (envs := envs) (pi := pi) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      (h_ref := h_ref) (h_dom := h_dom))

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
