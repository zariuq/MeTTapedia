import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Phase 4: From Consistency to Regret Convergence

This file shows that Bayesian consistency implies regret convergence:
if the posterior concentrates on the true environment, then expected
regret over the prior converges to zero.

## Main Results

* `consistency_implies_expected_regret_convergence` - Posterior concentration → regret → 0
* `expected_to_epsilon_best_response` - Expected regret → ε-best response

## Mathematical Background

The expected regret over the prior is:
  E_π[Regret] = Σ_ν π(ν | h) · Regret(ν, π)

If the agentagent is optimal for the true environment ν*, then:
  Regret(ν*, π) = 0

As the posterior concentrates on ν*, we get:
  E_π[Regret] = π(ν* | h) · 0 + Σ_{ν ≠ ν*} π(ν | h) · Regret(ν)
              → 0 + 0 = 0

because π(ν | h) → 0 for all ν ≠ ν* and regrets are bounded.

## References

- Leike (2016). PhD Thesis, Chapter 7
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence

open MeasureTheory ProbabilityTheory Real
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal MeasureTheory

/-! ## Expected Regret on Trajectories

We define expected regret as a function on trajectories.
-/

/-- Expected regret over the posterior at time t.
    This is Σ_ν π(ν | h_t) · Regret(ν, agent). -/
noncomputable def expectedRegretOnTrajectory (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (t : ℕ) (horizon : ℕ) : Trajectory → ℝ :=
  fun traj =>
    let h := trajectoryToHistory traj t
    ∑' ν_idx, (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
              regret (envs ν_idx) agent γ h horizon

/-- Expected regret is non-negative. -/
theorem expectedRegretOnTrajectory_nonneg (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (t : ℕ) (horizon : ℕ) (traj : Trajectory) :
    0 ≤ expectedRegretOnTrajectory O M prior envs agent γ t horizon traj := by
  apply tsum_nonneg
  intro ν_idx
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact regret_nonneg (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon

/-! ## Regret Bound

Regret is bounded by the maximum possible value, which is the horizon.
-/

/-- Regret is bounded by the horizon (crude bound). -/
theorem regret_bounded (μ : Environment) (agent : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) :
    regret μ agent γ h horizon ≤ horizon := by
  -- Regret = V* - V^π ≤ V* ≤ horizon (since rewards ≤ 1 per step)
  have h1 := regret_le_optimalValue μ agent γ h horizon
  have h2 : optimalValue μ γ h horizon ≤ horizon := optimalValue_le μ γ h horizon
  linarith

/-! ## From Consistency to Regret Convergence

The main theorem: posterior concentration implies regret goes to zero.
-/

/-- **REGRET CONVERGENCE FROM CONSISTENCY**:

    If the posterior concentrates on the true environment ν*, and the agent π
    is optimal for ν*, then expected regret over the prior converges to 0.

    More precisely: a.s. under ν*, E_π[Regret | h_t] → 0 as t → ∞.

    Proof sketch:
    1. Write E[Regret] = π(ν*|h) · Regret(ν*, π) + Σ_{ν ≠ ν*} π(ν|h) · Regret(ν)
    2. First term = 0 sinceagent is optimal for ν*
    3. Second term → 0 since π(ν|h) → 0 for all ν ≠ ν* and regrets are bounded
    4. By dominated convergence: sum → 0 -/
theorem consistency_implies_expected_regret_convergence (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_π_optimal : ∀ h : History, h.wellFormed →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_consistency : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      Filter.Tendsto
        (fun t => (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 1)) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      Filter.Tendsto
        (fun t => expectedRegretOnTrajectory O M prior envs agent γ t horizon traj)
        Filter.atTop (nhds 0) := by
  filter_upwards [h_consistency] with traj htraj
  -- Squeeze: 0 ≤ expectedRegret ≤ horizon * (1 - posterior_true)
  have h_nonneg : ∀ t, 0 ≤ expectedRegretOnTrajectory O M prior envs agent γ t horizon traj := by
    intro t
    exact expectedRegretOnTrajectory_nonneg O M prior envs agent γ t horizon traj

  have h_upper :
      ∀ t,
        expectedRegretOnTrajectory O M prior envs agent γ t horizon traj ≤
          (horizon : ℝ) *
            (1 - (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal) := by
    classical
    intro t
    set h : History := trajectoryToHistory traj t
    have h_wf : h.wellFormed := trajectoryToHistory_wellFormed traj t
    have h_star0 : regret (envs ν_star_idx) agent γ h horizon = 0 :=
      h_π_optimal h h_wf

    -- Notation for posterior weights at this `(t, traj)`.
    let wENN : EnvironmentIndex → ℝ≥0∞ :=
      fun ν_idx => PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj
    let w : EnvironmentIndex → ℝ :=
      fun ν_idx => (wENN ν_idx).toReal
    let u : EnvironmentIndex → ℝ :=
      fun ν_idx => ite (ν_idx = ν_star_idx) 0 (w ν_idx)

    have hw_nonneg : ∀ ν_idx, 0 ≤ w ν_idx := by
      intro ν_idx
      exact ENNReal.toReal_nonneg

    -- Sum of posterior weights is ≤ 1 in ENNReal (it is 1 when `mixtureProbability > 0`,
    -- and ≤ 1 when `mixtureProbability = 0` due to the fallback to the prior).
    have hsumENN_le_one : (∑' ν_idx, wENN ν_idx) ≤ 1 := by
      classical
      set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
      by_cases hden : denom = 0
      · -- posterior falls back to the prior
        have h_eq : (∑' ν_idx, wENN ν_idx) = ∑' ν_idx, prior.weight ν_idx := by
          refine tsum_congr fun ν_idx => ?_
          -- unfold `posteriorWeight` → `bayesianPosteriorWeight`
          simp [wENN, PosteriorConcentration.posteriorWeight, bayesianPosteriorWeight, denom, h, hden]
        simpa [h_eq] using prior.tsum_le_one
      · -- proper posterior: sums to 1
        have hden_pos : denom > 0 := by
          exact lt_of_le_of_ne zero_le (Ne.symm hden)
        have h_sum_one :
            (∑' ν_idx, bayesianPosteriorWeight O M prior envs ν_idx h) = 1 :=
          bayesianPosterior_sum_one O M prior envs h hden_pos
        -- rewrite `wENN` as `bayesianPosteriorWeight`
        have h_eq : (∑' ν_idx, wENN ν_idx) = ∑' ν_idx, bayesianPosteriorWeight O M prior envs ν_idx h := by
          simp [wENN, PosteriorConcentration.posteriorWeight, h]
        simp [h_eq, h_sum_one]

    have hsumENN_ne_top : (∑' ν_idx, wENN ν_idx) ≠ ∞ :=
      (lt_of_le_of_lt hsumENN_le_one ENNReal.one_lt_top).ne

    have hwENN_ne_top : ∀ ν_idx, wENN ν_idx ≠ ∞ :=
      fun ν_idx => ENNReal.ne_top_of_tsum_ne_top hsumENN_ne_top ν_idx

    have hsum_w_le_one : (∑' ν_idx, w ν_idx) ≤ 1 := by
      -- Convert the ENNReal bound to a Real bound via `toReal`.
      have hsum_w :
          (∑' ν_idx, w ν_idx) = (∑' ν_idx, wENN ν_idx).toReal := by
        -- `ENNReal.tsum_toReal_eq` gives `toReal (tsum wENN) = tsum (toReal ∘ wENN)`
        symm
        simpa [w] using (ENNReal.tsum_toReal_eq (f := fun ν_idx => wENN ν_idx) hwENN_ne_top)
      -- Now use monotonicity of `toReal`.
      have : (∑' ν_idx, wENN ν_idx).toReal ≤ 1 := by
        simpa using (ENNReal.toReal_mono ENNReal.one_ne_top hsumENN_le_one)
      simpa [hsum_w] using this

    have hSummable_w : Summable w := ENNReal.summable_toReal hsumENN_ne_top

    have hSummable_u : Summable u := by
      refine Summable.of_nonneg_of_le ?_ ?_ hSummable_w
      · intro ν_idx
        by_cases hν : ν_idx = ν_star_idx
        · simp [u, hν]
        · simp [u, hν, hw_nonneg]
      · intro ν_idx
        by_cases hν : ν_idx = ν_star_idx
        · simp [u, hν, hw_nonneg]
        · simp [u, hν]

    have h_tsum_u_le :
        (∑' ν_idx, u ν_idx) ≤
          1 - w ν_star_idx := by
      -- Decompose `tsum w = w ν_star_idx + tsum u`
      have h_decomp : (∑' ν_idx, w ν_idx) = w ν_star_idx + ∑' ν_idx, u ν_idx := by
        -- `tsum_eq_add_tsum_ite` in the `Summable` namespace.
        simpa [u, add_comm, add_left_comm, add_assoc] using
          (hSummable_w.tsum_eq_add_tsum_ite ν_star_idx)
      have h_u :
          (∑' ν_idx, w ν_idx) - w ν_star_idx = (∑' ν_idx, u ν_idx) := by
        linarith [h_decomp]
      have h_sub :
          (∑' ν_idx, w ν_idx) - w ν_star_idx ≤ 1 - w ν_star_idx :=
        sub_le_sub_right hsum_w_le_one (w ν_star_idx)
      simpa [h_u] using h_sub

    -- Bound expected regret by replacing each regret term by its (crude) horizon bound.
    have h_termwise :
        ∀ ν_idx,
          w ν_idx * regret (envs ν_idx) agent γ h horizon ≤
            w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ) := by
      intro ν_idx
      by_cases hν : ν_idx = ν_star_idx
      · subst hν
        simp [h_star0]
      · have hwt : 0 ≤ w ν_idx := hw_nonneg ν_idx
        have hregle : regret (envs ν_idx) agent γ h horizon ≤ horizon :=
          regret_bounded (envs ν_idx) agent γ h horizon
        -- For ν ≠ ν*, bound by `horizon`.
        simpa [hν] using (mul_le_mul_of_nonneg_left hregle hwt)

    have hSummable_rhs :
        Summable (fun ν_idx => w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ)) := by
      -- Compare to `w * horizon`.
      have hMajor : Summable fun ν_idx => w ν_idx * (horizon : ℝ) :=
        hSummable_w.mul_right (horizon : ℝ)
      refine Summable.of_nonneg_of_le ?_ ?_ hMajor
      · intro ν_idx
        have hwt : 0 ≤ w ν_idx := hw_nonneg ν_idx
        by_cases hν : ν_idx = ν_star_idx
        · simp [hν]
        ·
          have hhz : 0 ≤ (horizon : ℝ) := by exact_mod_cast (Nat.zero_le horizon)
          have : 0 ≤ w ν_idx * (horizon : ℝ) := mul_nonneg hwt hhz
          simpa [hν] using this
      · intro ν_idx
        have hwt : 0 ≤ w ν_idx := hw_nonneg ν_idx
        by_cases hν : ν_idx = ν_star_idx
        ·
          have hhz : 0 ≤ (horizon : ℝ) := by exact_mod_cast (Nat.zero_le horizon)
          have : 0 ≤ w ν_idx * (horizon : ℝ) := mul_nonneg (hw_nonneg ν_idx) hhz
          simpa [hν] using this
        · simp [hν]

    have hSummable_lhs :
        Summable (fun ν_idx => w ν_idx * regret (envs ν_idx) agent γ h horizon) := by
      -- Compare to the same RHS majorant using `regret_bounded`.
      have hMajor : Summable fun ν_idx => w ν_idx * (horizon : ℝ) :=
        hSummable_w.mul_right (horizon : ℝ)
      refine Summable.of_nonneg_of_le ?_ ?_ hMajor
      · intro ν_idx
        exact mul_nonneg (hw_nonneg ν_idx) (regret_nonneg (envs ν_idx) agent γ h horizon)
      · intro ν_idx
        have hwt : 0 ≤ w ν_idx := hw_nonneg ν_idx
        have hregle : regret (envs ν_idx) agent γ h horizon ≤ horizon :=
          regret_bounded (envs ν_idx) agent γ h horizon
        exact mul_le_mul_of_nonneg_left hregle hwt

    have h_tsum_le :
        (∑' ν_idx, w ν_idx * regret (envs ν_idx) agent γ h horizon) ≤
          ∑' ν_idx, w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ) :=
      hSummable_lhs.tsum_le_tsum (fun ν_idx => h_termwise ν_idx) hSummable_rhs

    -- Evaluate the RHS: it is `horizon * tsum u`.
    have h_rhs :
        (∑' ν_idx, w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ)) =
          (∑' ν_idx, u ν_idx) * (horizon : ℝ) := by
      -- rewrite the ite inside as `u`
      have h_eq :
          (fun ν_idx => w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ)) =
            fun ν_idx => u ν_idx * (horizon : ℝ) := by
        funext ν_idx
        by_cases hν : ν_idx = ν_star_idx <;> simp [u, hν]
      calc
        (∑' ν_idx, w ν_idx * ite (ν_idx = ν_star_idx) 0 (horizon : ℝ)) =
            ∑' ν_idx, u ν_idx * (horizon : ℝ) := by
              simpa using (congrArg (fun f => ∑' ν_idx, f ν_idx) h_eq)
        _ = (∑' ν_idx, u ν_idx) * (horizon : ℝ) := by
              simpa using (tsum_mul_right (f := fun ν_idx => u ν_idx) (a := (horizon : ℝ)))

    -- Put everything together.
    have : expectedRegretOnTrajectory O M prior envs agent γ t horizon traj ≤
          (∑' ν_idx, u ν_idx) * (horizon : ℝ) := by
      -- unfold expectedRegretOnTrajectory and use `h_tsum_le`
      simpa [expectedRegretOnTrajectory, PosteriorConcentration.posteriorWeight, h, wENN, w] using
        (h_tsum_le.trans_eq h_rhs)

    -- Finally, use `tsum u ≤ 1 - w_star`.
    have h_horizon_nonneg : 0 ≤ (horizon : ℝ) := by exact_mod_cast (Nat.zero_le horizon)
    have h_mul :
        (∑' ν_idx, u ν_idx) * (horizon : ℝ) ≤
          (1 - w ν_star_idx) * (horizon : ℝ) :=
      mul_le_mul_of_nonneg_right h_tsum_u_le h_horizon_nonneg
    -- Rearrange to the final bound
    simpa [mul_comm, mul_left_comm, mul_assoc, w, wENN] using this.trans h_mul

  -- The upper bound tends to `0` because the posterior weight tends to `1`.
  have h_upper_tendsto :
      Filter.Tendsto
        (fun t =>
          (horizon : ℝ) *
            (1 - (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal))
        Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t =>
        (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 1) := htraj
    have hsub : Filter.Tendsto (fun t =>
        1 - (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds (1 - 1)) :=
      (tendsto_const_nhds.sub h1)
    have hsub0 : Filter.Tendsto (fun t =>
        1 - (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 0) := by simpa using hsub
    simpa [mul_comm, mul_left_comm, mul_assoc] using (tendsto_const_nhds.mul hsub0)

  exact squeeze_zero h_nonneg h_upper h_upper_tendsto

/-! ## From Expected Regret to ε-Best Response

Convert the convergence result to the ε-best response form.
-/

/-- From a.s. expected regret convergence to ε-best response.

    If expected regret → 0 a.s., then for all ε > 0, eventually
    the expected regret is less than ε. -/
theorem expected_regret_to_epsilon_bound (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_regret_convergence : ∀ᵐ traj ∂(environmentMeasure (envs ν_star_idx) h_stoch),
      Filter.Tendsto
        (fun t => expectedRegretOnTrajectory O M prior envs agent γ t horizon traj)
        Filter.atTop (nhds 0))
    (ε : ℝ) (hε : ε > 0) :
    ∀ᵐ traj ∂(environmentMeasure (envs ν_star_idx) h_stoch),
      ∃ t₀ : ℕ, ∀ t ≥ t₀,
        expectedRegretOnTrajectory O M prior envs agent γ t horizon traj < ε := by
  -- Follows directly from the definition of Filter.Tendsto and Metric.tendsto_atTop
  filter_upwards [h_regret_convergence] with traj htraj
  -- Use Metric.tendsto_atTop: Tendsto f atTop (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (f n) a < ε
  rw [Metric.tendsto_atTop] at htraj
  obtain ⟨t₀, ht₀⟩ := htraj ε hε
  use t₀
  intro t ht
  specialize ht₀ t ht
  -- dist (f t) 0 < ε means |f t - 0| < ε, which means |f t| < ε
  simp only [Real.dist_0_eq_abs] at ht₀
  -- Since expected regret is non-negative, |f t| = f t
  have h_nonneg := expectedRegretOnTrajectory_nonneg O M prior envs agent γ t horizon traj
  rwa [abs_of_nonneg h_nonneg] at ht₀

/-- Expected regret less than ε implies ε-best response (on average). -/
theorem small_expectedRegretOnTrajectory_implies_exists_small_regret
    (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (ε : ℝ) (t horizon : ℕ) (traj : Trajectory)
    (_hε : 0 < ε)
    (h_mix_pos : mixtureProbability O M prior envs (trajectoryToHistory traj t) > 0)
    (h_small : expectedRegretOnTrajectory O M prior envs agent γ t horizon traj < ε) :
    ∃ ν_idx : EnvironmentIndex,
      regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon < ε := by
  classical
  have hsum : ∑' i, PosteriorConcentration.posteriorWeight O M prior envs i t traj = 1 := by
    simpa [PosteriorConcentration.posteriorWeight] using
      (bayesianPosterior_sum_one O M prior envs (trajectoryToHistory traj t) h_mix_pos)

  have hsum_toReal :
      ∑' i, (PosteriorConcentration.posteriorWeight O M prior envs i t traj).toReal = 1 := by
    have hsum_ne_top :
        (∑' i, PosteriorConcentration.posteriorWeight O M prior envs i t traj) ≠ ∞ := by
      simp [hsum]
    have h_ne_top :
        ∀ i, PosteriorConcentration.posteriorWeight O M prior envs i t traj ≠ ∞ :=
      fun i => ENNReal.ne_top_of_tsum_ne_top hsum_ne_top i
    calc
      (∑' i, (PosteriorConcentration.posteriorWeight O M prior envs i t traj).toReal)
          = (∑' i, PosteriorConcentration.posteriorWeight O M prior envs i t traj).toReal := by
              symm
              simpa using
                (ENNReal.tsum_toReal_eq (f := fun i =>
                  PosteriorConcentration.posteriorWeight O M prior envs i t traj) h_ne_top)
      _ = 1 := by simp [hsum]

  by_contra hno
  have hge : ∀ ν_idx : EnvironmentIndex,
      ε ≤ regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon := by
    intro ν_idx
    have : ¬ regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon < ε := by
      intro hlt
      exact hno ⟨ν_idx, hlt⟩
    exact le_of_not_gt this

  have hnonneg : ∀ ν_idx : EnvironmentIndex,
      0 ≤ regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon := by
    intro ν_idx
    exact regret_nonneg (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon

  have h_lower : ε ≤ expectedRegretOnTrajectory O M prior envs agent γ t horizon traj := by
    have h_termwise :
        ∀ ν_idx,
          (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal * ε ≤
            (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
              regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon := by
      intro ν_idx
      have hwt : 0 ≤ (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal :=
        ENNReal.toReal_nonneg
      exact mul_le_mul_of_nonneg_left (hge ν_idx) hwt

    have hsum_mul :
        (∑' ν_idx, (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal * ε) =
          (∑' ν_idx, (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal) *
            ε := by
      -- `tsum_mul_right` is in the root namespace for rings.
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (tsum_mul_right (f := fun ν_idx =>
          (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal) (a := ε))

    calc
      ε = 1 * ε := by simp
      _ = (∑' ν_idx, (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal) *
              ε := by simp [hsum_toReal]
      _ = (∑' ν_idx, (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
              ε) := by simp [hsum_mul]
      _ ≤ (∑' ν_idx,
            (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
              regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon) := by
            -- Use the order lemma for `tsum` (requires summability of both sides).
            have hsum_ne_top :
                (∑' i, PosteriorConcentration.posteriorWeight O M prior envs i t traj) ≠ ∞ := by
              simp [hsum]
            have hSummable_w :
                Summable (fun ν_idx =>
                  (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal) :=
              ENNReal.summable_toReal hsum_ne_top
            have hSummable_f :
                Summable (fun ν_idx =>
                  (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal * ε) :=
              hSummable_w.mul_right ε
            have hSummable_major :
                Summable (fun ν_idx =>
                  (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
                    (horizon : ℝ)) :=
              hSummable_w.mul_right (horizon : ℝ)
            have hSummable_g :
                Summable (fun ν_idx =>
                  (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal *
                    regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon) := by
              refine Summable.of_nonneg_of_le ?_ ?_ hSummable_major
              · intro ν_idx
                exact mul_nonneg ENNReal.toReal_nonneg (hnonneg ν_idx)
              · intro ν_idx
                have hwt :
                    0 ≤ (PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj).toReal :=
                  ENNReal.toReal_nonneg
                have hregle :
                    regret (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon ≤ horizon :=
                  regret_bounded (envs ν_idx) agent γ (trajectoryToHistory traj t) horizon
                exact mul_le_mul_of_nonneg_left hregle hwt
            exact hSummable_f.tsum_le_tsum (fun ν_idx => h_termwise ν_idx) hSummable_g
      _ = expectedRegretOnTrajectory O M prior envs agent γ t horizon traj := by
            simp [expectedRegretOnTrajectory]

  exact (not_lt_of_ge h_lower) h_small

/-! ## Summary of Phase 4

We have established the connection between Bayesian consistency and regret:

1. `expectedRegretOnTrajectory` - Expected regret as function on trajectories
2. `expectedRegretOnTrajectory_nonneg` - Non-negativity
3. `regret_bounded` - Regret is bounded
4. `consistency_implies_expected_regret_convergence` - THE KEY IMPLICATION
5. `expected_regret_to_epsilon_bound` - Conversion to ε form

**Remaining sorries**:
- `consistency_implies_expected_regret_convergence` - Dominated convergence argument
- `small_expectedRegretOnTrajectory_implies_exists_small_regret` - Markov inequality

**Key insight**: The posterior concentration from Phase 3 directly implies
that expected regret vanishes, completing the chain:
  Supermartingale → Posterior concentration → Regret → 0
-/

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence
