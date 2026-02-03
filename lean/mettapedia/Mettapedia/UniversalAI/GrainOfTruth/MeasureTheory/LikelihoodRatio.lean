import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Phase 2: Likelihood Ratio as Supermartingale

This file proves the central result for Bayesian consistency: the log-likelihood ratio
between any wrong environment ν and the true environment ν* is a supermartingale.

## Main Definitions

* `likelihoodRatio` - The likelihood ratio ν(h_t) / ν*(h_t)
* `logLikelihoodRatio` - The log-likelihood ratio log(ν(h_t) / ν*(h_t))

## Main Results

* `logLikelihoodRatio_supermartingale` - Under ν*, the log-likelihood ratio is a supermartingale
* `logLikelihoodRatio_ae_tendsto_limitProcess_of_eLpNorm_bdd` - Under a uniform L¹ bound, the
  log-likelihood ratio converges a.s. to a limit process
* `likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges` - If the log-likelihood ratio
  diverges to `-∞`, then the likelihood ratio converges to `0`

## Mathematical Background

The key insight is that for any two probability measures P and Q, the log-likelihood ratio
L_t = log(dP_t/dQ_t) satisfies:

  E_Q[L_{t+1} - L_t | F_t] = -KL(Q_{t+1|F_t} || P_{t+1|F_t}) ≤ 0

where KL is the Kullback-Leibler divergence (always non-negative).

This is the "information gain" interpretation: under Q, observing more data can only
decrease our belief in P (on average), never increase it.

## References

- Cover & Thomas (2006). "Elements of Information Theory", Chapter 11
- Williams (1991). "Probability with Martingales"
- Leike (2016). PhD Thesis, Chapter 7
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio

open MeasureTheory ProbabilityTheory Real
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization
open scoped ENNReal NNReal MeasureTheory

/-! ## Support Condition

Our log-likelihood development works in `ℝ`, so we need to avoid the case where `ν` assigns
probability `0` to an observation that has positive probability under `ν_star` (which would
produce a true log-likelihood of `-∞`).

We capture this as a *support* (domination) condition: `ν` has support containing `ν_star`'s
support at every one-step conditional distribution.
-/

/-- `SupportCondition ν ν_star` means: whenever `ν_star` assigns positive probability to a percept
after an action, `ν` also assigns positive probability to that percept. -/
def SupportCondition (ν ν_star : Environment) : Prop :=
  ∀ (h : History) (a : Action) (x : Percept),
    ν_star.prob (h ++ [HistElem.act a]) x > 0 → ν.prob (h ++ [HistElem.act a]) x > 0

/-! ## Likelihood Ratio

The likelihood ratio at time t compares two environments' probabilities of
generating the same history.
-/

/-- The likelihood ratio ν(h_t) / ν*(h_t) as a function on trajectories.
    Returns the ratio of probabilities that ν and ν* assign to the observed history. -/
noncomputable def likelihoodRatio (ν ν_star : Environment) (t : ℕ) : Trajectory → ℝ≥0∞ :=
  fun traj =>
    let h := trajectoryToHistory traj t
    historyProbability ν h / historyProbability ν_star h

/-- The *one-step* likelihood ratio along a trajectory:
`ν(x_t | h_t, a_t) / ν*(x_t | h_t, a_t)`. -/
noncomputable def stepLikelihoodRatio (ν ν_star : Environment) (t : ℕ) : Trajectory → ℝ≥0∞ :=
  fun traj =>
    let h := trajectoryToHistory traj t
    ν.prob (h ++ [HistElem.act (traj t).action]) (traj t).percept /
      ν_star.prob (h ++ [HistElem.act (traj t).action]) (traj t).percept

/-- The log-likelihood ratio: log(ν(h_t) / ν*(h_t)).
    This is the quantity that forms a supermartingale. -/
noncomputable def logLikelihoodRatio (ν ν_star : Environment) (t : ℕ) : Trajectory → ℝ :=
  fun traj =>
    let h := trajectoryToHistory traj t
    let p_ν := (historyProbability ν h).toReal
    let p_star := (historyProbability ν_star h).toReal
    if p_star = 0 then 0  -- Convention: 0/0 = 0 in log
    else Real.log (p_ν / p_star)

/-! ## Properties of Likelihood Ratio -/

/-- Likelihood ratio at time 0 is 1 (both environments assign probability 1 to empty history). -/
theorem likelihoodRatio_zero (ν ν_star : Environment) (traj : Trajectory) :
    likelihoodRatio ν ν_star 0 traj = 1 := by
  simp only [likelihoodRatio, trajectoryToHistory_zero, historyProbability, historyProbabilityAux]
  rw [ENNReal.div_self]
  · exact one_ne_zero
  · exact ENNReal.one_ne_top

/-- Log-likelihood ratio at time 0 is 0. -/
theorem logLikelihoodRatio_zero (ν ν_star : Environment) (traj : Trajectory) :
    logLikelihoodRatio ν ν_star 0 traj = 0 := by
  simp only [logLikelihoodRatio, trajectoryToHistory_zero, historyProbability, historyProbabilityAux]
  simp only [ENNReal.toReal_one, div_one, Real.log_one, ite_self]

/-- Chain rule for likelihood ratios (pointwise): the full ratio factors into the previous ratio
times the one-step ratio. -/
theorem likelihoodRatio_succ_eq_mul_stepLikelihoodRatio (ν ν_star : Environment) (t : ℕ) (traj : Trajectory) :
    likelihoodRatio ν ν_star t.succ traj =
      likelihoodRatio ν ν_star t traj * stepLikelihoodRatio ν ν_star t traj := by
  classical
  let h : History := trajectoryToHistory traj t
  let a : Action := (traj t).action
  let x : Percept := (traj t).percept
  have hw : h.wellFormed := trajectoryToHistory_wellFormed traj t
  have he : Even h.length := trajectoryToHistory_even traj t
  have h_chain_star :
      historyProbability ν_star (trajectoryToHistory traj t.succ) =
        historyProbability ν_star h * ν_star.prob (h ++ [HistElem.act a]) x := by
    simpa [h, a, x, Nat.succ_eq_add_one, trajectoryToHistory_succ] using
      (historyProbability_append_step ν_star h hw he a x)
  have h_chain_nu :
      historyProbability ν (trajectoryToHistory traj t.succ) =
        historyProbability ν h * ν.prob (h ++ [HistElem.act a]) x := by
    simpa [h, a, x, Nat.succ_eq_add_one, trajectoryToHistory_succ] using
      (historyProbability_append_step ν h hw he a x)
  have h_c_ne_top : historyProbability ν_star h ≠ ∞ := by
    have hle : historyProbability ν_star h ≤ 1 := historyProbability_le_one ν_star h
    exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top
  have h_d_ne_top : ν_star.prob (h ++ [HistElem.act a]) x ≠ ∞ := by
    have ha_wf : (h ++ [HistElem.act a]).wellFormed := wellFormed_append_act h hw he a
    have htsum : (∑' y : Percept, ν_star.prob (h ++ [HistElem.act a]) y) ≤ 1 :=
      ν_star.prob_le_one (h ++ [HistElem.act a]) ha_wf
    have hle : ν_star.prob (h ++ [HistElem.act a]) x ≤ 1 :=
      le_trans (ENNReal.le_tsum x) htsum
    exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top
  simp [likelihoodRatio, stepLikelihoodRatio, h_chain_star, h_chain_nu, h, a, x,
    ENNReal.mul_div_mul_comm (hc := Or.inr h_d_ne_top) (hd := Or.inl h_c_ne_top)]

/-- Likelihood ratio depends only on the first t steps. -/
theorem likelihoodRatio_adapted (ν ν_star : Environment) (t : ℕ) :
    ∀ traj₁ traj₂, (∀ i < t, traj₁ i = traj₂ i) →
      likelihoodRatio ν ν_star t traj₁ = likelihoodRatio ν ν_star t traj₂ := by
  intro traj₁ traj₂ heq
  simp only [likelihoodRatio]
  rw [trajectoryToHistory_depends_on_prefix traj₁ traj₂ t heq]

/-- Log-likelihood ratio depends only on the first t steps. -/
theorem logLikelihoodRatio_adapted (ν ν_star : Environment) (t : ℕ) :
    ∀ traj₁ traj₂, (∀ i < t, traj₁ i = traj₂ i) →
      logLikelihoodRatio ν ν_star t traj₁ = logLikelihoodRatio ν ν_star t traj₂ := by
  intro traj₁ traj₂ heq
  simp only [logLikelihoodRatio]
  rw [trajectoryToHistory_depends_on_prefix traj₁ traj₂ t heq]

/-! ## Increments of Log-Likelihood Ratio

The key to showing the supermartingale property is understanding how the
log-likelihood ratio changes from step t to step t+1.
-/

/-- The conditional log-likelihood for a single step.
    This is log(ν(x_t | h_{<t}) / ν*(x_t | h_{<t})) where x_t is the t-th observation.

    Returns 0 when:
    - ν_star gives 0 probability to the history prefix, OR
    - ν_star gives 0 probability to the step

    NOTE: The decomposition theorem currently has sorries for measure-zero cases
    where ν assigns 0 probability. These cases prevent pointwise equality for
    all trajectories. The theorem should be restated as almost-everywhere equality
    under ν_star for a complete proof. -/
noncomputable def stepLogLikelihood (ν ν_star : Environment) (h : History) (step : Step) : ℝ :=
  let a := step.action
  let x := step.percept
  let p_star_h := (historyProbability ν_star h).toReal
  let p_ν := (ν.prob (h ++ [HistElem.act a]) x).toReal
  let p_star := (ν_star.prob (h ++ [HistElem.act a]) x).toReal
  if p_star_h = 0 then 0  -- History has 0 prob under ν_star
  else if p_star = 0 then 0  -- Step has 0 prob under ν_star
  else Real.log (p_ν / p_star)

/-- Log of ratio equals log numerator minus log denominator (when both are positive). -/
theorem log_div_eq_sub' (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div (ne_of_gt ha) (ne_of_gt hb)

/-- When all factors are positive, the log-ratio decomposition holds.
    log((ab)/(cd)) = log(a/c) + log(b/d) for positive a, b, c, d. -/
theorem log_ratio_mul_eq_add (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.log ((a * b) / (c * d)) = Real.log (a / c) + Real.log (b / d) := by
  rw [mul_div_mul_comm]
  exact Real.log_mul (div_ne_zero (ne_of_gt ha) (ne_of_gt hc))
                      (div_ne_zero (ne_of_gt hb) (ne_of_gt hd))

-- Note: A previous version had log_ratio_mul_eq_add' allowing zero numerators,
-- but this was incorrect. The case where numerators can be 0 is handled separately
-- in the decomposition proof using the measure-zero exceptional set argument.
-- Use log_ratio_mul_eq_add directly when all factors are positive.

/-- If all steps up to time t have positive ν_star conditional probability,
    then the history probability is also positive.

    TODO: Complete proof using ENNReal properties.
    The idea is correct: product of positive probabilities is positive.
    Need to use the right ENNReal lemmas for multiplication and zero. -/
lemma historyProbability_pos_of_steps_pos (ν_star : Environment) (traj : Trajectory) (t : ℕ)
    (h_pos : ∀ s < t, (ν_star.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action])
                                     (traj s).percept) > 0) :
    historyProbability ν_star (trajectoryToHistory traj t) > 0 := by
  induction t with
  | zero =>
    simp [trajectoryToHistory_zero, historyProbability, historyProbabilityAux]
  | succ t ih =>
    have ih_pos :
        historyProbability ν_star (trajectoryToHistory traj t) > 0 :=
      ih (fun s hs => h_pos s (Nat.lt_succ_of_lt hs))
    have h_step_pos :
        ν_star.prob (trajectoryToHistory traj t ++ [HistElem.act (traj t).action]) (traj t).percept > 0 :=
      h_pos t (Nat.lt_succ_self t)
    have hw : (trajectoryToHistory traj t).wellFormed :=
      trajectoryToHistory_wellFormed traj t
    have he : Even (trajectoryToHistory traj t).length :=
      trajectoryToHistory_even traj t
    have h_chain :
        historyProbability ν_star (trajectoryToHistory traj t.succ) =
          historyProbability ν_star (trajectoryToHistory traj t) *
            ν_star.prob (trajectoryToHistory traj t ++ [HistElem.act (traj t).action]) (traj t).percept := by
      -- Use the chain rule and the `trajectoryToHistory_succ` decomposition.
      simpa [Nat.succ_eq_add_one, trajectoryToHistory_succ] using
        (historyProbability_append_step ν_star (trajectoryToHistory traj t) hw he (traj t).action (traj t).percept)
    -- Positivity follows from positivity of each factor.
    rw [h_chain]
    exact ENNReal.mul_pos ih_pos.ne' h_step_pos.ne'

/-- Appending [act a] to a wellFormed history with even length preserves wellFormedness.
    This is because even-length wellFormed histories end with a percept (or are empty),
    and appending [act a] gives a valid [act, per, ..., act, per, act] pattern. -/
theorem wellFormed_append_act (h : History) (hw : h.wellFormed) (he : Even h.length) (a : Action) :
    (h ++ [HistElem.act a]).wellFormed := by
  -- Induction on the length of h, generalized over h
  induction h using List.twoStepInduction with
  | nil =>
    -- [] ++ [act a] = [act a], wellFormed by definition
    rfl
  | singleton e =>
    -- [e] has length 1 (odd), but he says Even 1, which is false
    simp only [List.length_singleton] at he
    -- Even 1 is false, so this case is vacuously true
    exact (Nat.not_even_one he).elim
  | cons_cons e1 e2 rest ih =>
    -- h = e1 :: e2 :: rest
    -- For h to be wellFormed with pattern [act, per, rest], we need:
    match e1, e2 with
    | HistElem.act _, HistElem.per _ =>
      -- [act a', per p, rest] is wellFormed iff rest is wellFormed
      simp only [List.cons_append, History.wellFormed] at hw ⊢
      -- rest has even length since h has even length
      have he' : Even rest.length := by
        simp only [List.length_cons] at he
        -- he : Even (rest.length + 1 + 1) = Even (rest.length + 2)
        -- rest.length is even iff rest.length + 2 is even
        obtain ⟨k, hk⟩ := he
        use k - 1
        omega
      exact ih hw he'
    | HistElem.act _, HistElem.act _ =>
      -- [act, act, ...] is not wellFormed, hw : false = true, contradiction
      simp only [History.wellFormed] at hw
      cases hw
    | HistElem.per _, _ =>
      -- [per, ...] is not wellFormed (must start with action), hw : false = true
      simp only [History.wellFormed] at hw
      cases hw

/-- The log-likelihood ratio decomposes as a sum of step log-likelihoods
    almost surely under the true environment ν*.

    L_t = Σ_{s<t} stepLL_s

    This holds almost everywhere under ν_star because:
    - When ν_star assigns 0 probability to a trajectory, the equality holds trivially
    - When ν assigns 0 probability but ν_star assigns positive probability,
      this is a measure-zero set under ν_star, so we only need a.e. equality

    The a.e. qualifier is essential: pointwise equality fails when ν and ν_star
    disagree on measure-zero sets. -/
theorem logLikelihoodRatio_decomposition_ae (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star)
    (h_support : SupportCondition ν ν_star) :
    ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
      logLikelihoodRatio ν ν_star t traj =
        ∑ s ∈ Finset.range t,
          stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch

  -- We prove by induction on `t`, working almost-everywhere under `μ`.
  induction t with
  | zero =>
    apply Filter.Eventually.of_forall
    intro traj
    -- RHS is an empty sum.
    simp [Finset.range_zero]
    simpa using logLikelihoodRatio_zero ν ν_star traj
  | succ t ih =>
    -- Define the "bad" event at time `s`: the realized step has zero probability under `ν_star`.
    let badStep (s : ℕ) : Set Trajectory :=
      {traj |
        ν_star.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action]) (traj s).percept = 0}

    have h_badStep_zero : ∀ s : ℕ, μ (badStep s) = 0 := by
      intro s
      -- Partition by the `(s+1)`-step prefix; whenever the last percept has zero conditional
      -- probability under `ν_star`, the corresponding cylinder has measure `0`.
      let extendPrefix (pfx : Fin (s + 1) → Step) : Trajectory :=
        fun n => if h : n < s + 1 then pfx ⟨n, h⟩ else default
      let last : Fin (s + 1) := ⟨s, Nat.lt_succ_self s⟩
      let badPrefix (pfx : Fin (s + 1) → Step) : Set Trajectory :=
        if ν_star.prob
              (trajectoryToHistory (extendPrefix pfx) s ++ [HistElem.act (pfx last).action])
              (pfx last).percept = 0
        then cylinderSet (trajectoryToHistory (extendPrefix pfx) (s + 1))
        else ∅
      -- Every trajectory in `badStep s` is contained in one of the `badPrefix pfx`.
      have h_cover : badStep s ⊆ ⋃ pfx : (Fin (s + 1) → Step), badPrefix pfx := by
        intro traj htraj
        refine Set.mem_iUnion.2 ?_
        refine ⟨truncate (s + 1) traj, ?_⟩
        -- Show we are in the `then` branch.
        have h_then :
            ν_star.prob
                  (trajectoryToHistory (extendPrefix (truncate (s + 1) traj)) s ++
                    [HistElem.act ((truncate (s + 1) traj) last).action])
                  ((truncate (s + 1) traj) last).percept = 0 := by
          -- Prefix agreement gives equality of the conditioning history and the realized step.
          have h_hist :
              trajectoryToHistory (extendPrefix (truncate (s + 1) traj)) s =
                trajectoryToHistory traj s := by
            refine trajectoryToHistory_depends_on_prefix _ _ s ?_
            intro i hi
            -- `simp` reduces this to the (impossible) `s < i` branch.
            simp [extendPrefix, truncate]
            intro hsi
            exfalso
            exact Nat.lt_asymm hi hsi
          have h_step :
              (extendPrefix (truncate (s + 1) traj) s) = traj s := by
            simp [extendPrefix, truncate]
          simpa [badStep, h_hist, h_step] using htraj
        have h_mem : traj ∈ cylinderSet (trajectoryToHistory (extendPrefix (truncate (s + 1) traj)) (s + 1)) := by
          refine ⟨s + 1, ?_⟩
          refine trajectoryToHistory_depends_on_prefix traj (extendPrefix (truncate (s + 1) traj)) (s + 1) ?_
          intro i hi
          -- `simp` reduces this to the (impossible) `s < i` branch.
          simp [extendPrefix, truncate]
          intro hsi
          exfalso
          exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ hi)) hsi
        simp [badPrefix, h_then, h_mem]

      -- Now `badStep s` is a countable union of null sets, hence null.
      have h_le :
          μ (badStep s) ≤ ∑' pfx : (Fin (s + 1) → Step), μ (badPrefix pfx) := by
        -- First bound by the measure of the (countable) union using `h_cover`,
        -- then use the union bound `measure_iUnion_le`.
        have hmono : μ (badStep s) ≤ μ (⋃ pfx : (Fin (s + 1) → Step), badPrefix pfx) :=
          MeasureTheory.measure_mono h_cover
        exact hmono.trans (MeasureTheory.measure_iUnion_le (μ := μ) badPrefix)
      have h_each : ∀ pfx : (Fin (s + 1) → Step), μ (badPrefix pfx) = 0 := by
        intro pfx
        by_cases h0 :
            ν_star.prob
                  (trajectoryToHistory (extendPrefix pfx) s ++ [HistElem.act (pfx last).action])
                  (pfx last).percept = 0
        · -- Use the cylinder factorization lemma.
          have hw : (trajectoryToHistory (extendPrefix pfx) s).wellFormed :=
            trajectoryToHistory_wellFormed (extendPrefix pfx) s
          have he : Even (trajectoryToHistory (extendPrefix pfx) s).length :=
            trajectoryToHistory_even (extendPrefix pfx) s
          have h_succ :
              trajectoryToHistory (extendPrefix pfx) (s + 1) =
                trajectoryToHistory (extendPrefix pfx) s ++
                  [HistElem.act (pfx last).action, HistElem.per (pfx last).percept] := by
            -- `extendPrefix pfx s = pfx last`.
            have : (extendPrefix pfx s) = pfx last := by
              simp [extendPrefix, last]
            simp [trajectoryToHistory_succ, this]
          -- Rewrite `badPrefix` into the `append` form and apply `cylinderSet_append_single_step`.
          have h_meas :
              μ (cylinderSet (trajectoryToHistory (extendPrefix pfx) (s + 1))) =
                μ (cylinderSet (trajectoryToHistory (extendPrefix pfx) s)) *
                  uniformActionProb *
                    ν_star.prob
                      (trajectoryToHistory (extendPrefix pfx) s ++ [HistElem.act (pfx last).action])
                      (pfx last).percept := by
            -- Expand `μ`.
            simp [μ, h_succ] at *
            -- `cylinderSet_append_single_step` is stated for `environmentMeasure`.
            simpa [μ, h_succ] using
              (cylinderSet_append_single_step (μ := ν_star) (h_stoch := h_stoch)
                (pfx := trajectoryToHistory (extendPrefix pfx) s)
                (a := (pfx last).action) (x := (pfx last).percept) hw he)
          -- Since the last factor is `0`, the measure is `0`.
          have : μ (cylinderSet (trajectoryToHistory (extendPrefix pfx) (s + 1))) = 0 := by
            -- Use the factorization equality and the hypothesis `h0`.
            -- Convert the last factor to `0` directly.
            simp [h_meas, h0]
          simpa [badPrefix, h0, μ] using this
        · simp [badPrefix, h0]
      have h_sum : (∑' pfx : (Fin (s + 1) → Step), μ (badPrefix pfx)) = 0 := by
        simp [h_each]
      have h0 : μ (badStep s) ≤ 0 := by
        simpa [h_sum] using h_le.trans_eq h_sum
      exact le_antisymm h0 (zero_le _)

    -- Hence almost surely, all `ν_star` one-step probabilities along the first `t+1` steps are positive.
    have h_good :
        ∀ᵐ traj ∂μ, ∀ s < t.succ,
          ν_star.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action]) (traj s).percept > 0 := by
      -- The complement is a finite union of `badStep s`, each of which has measure `0`.
      have h_union0 :
          μ (⋃ s ∈ Finset.range t.succ, badStep s) = 0 := by
        apply le_antisymm
        · calc
          μ (⋃ s ∈ Finset.range t.succ, badStep s)
              ≤ ∑ s ∈ Finset.range t.succ, μ (badStep s) :=
                  MeasureTheory.measure_biUnion_finset_le (μ := μ) (Finset.range t.succ) badStep
          _ = 0 := by simp [h_badStep_zero]
        · exact zero_le _
      -- Convert to an a.e. statement.
      have h_ae_not :
          ∀ᵐ traj ∂μ, traj ∉ ⋃ s ∈ Finset.range t.succ, badStep s :=
        (MeasureTheory.measure_eq_zero_iff_ae_notMem).1 h_union0
      filter_upwards [h_ae_not] with traj hnot
      intro s hs
      have hs_mem : s ∈ Finset.range t.succ := by simpa [Finset.mem_range] using hs
      have : traj ∉ badStep s := by
        intro hmem
        exact hnot (by exact Set.mem_iUnion₂.2 ⟨s, hs_mem, hmem⟩)
      -- For `ℝ≥0∞`, `p ≠ 0` is equivalent to `0 < p`.
      have : ν_star.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action]) (traj s).percept ≠ 0 := by
        simpa [badStep] using this
      simpa [pos_iff_ne_zero] using this

    -- Now prove the decomposition pointwise on the good set, using the induction hypothesis.
    filter_upwards [ih, h_good] with traj hIH hGood
    -- Unfold the `Finset.range` sum at `t+1`.
    have h_sum :
        (∑ s ∈ Finset.range t.succ,
            stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s)) =
          (∑ s ∈ Finset.range t,
            stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s)) +
            stepLogLikelihood ν ν_star (trajectoryToHistory traj t) (traj t) := by
      simp [Finset.sum_range_succ]

    -- Reduce the goal to the one-step increment identity.
    rw [h_sum]
    -- Rewrite the `t`-prefix sum using the induction hypothesis.
    rw [← hIH]

    -- Abbreviations for the `t`-prefix and the current step.
    let h : History := trajectoryToHistory traj t
    let a : Action := (traj t).action
    let x : Percept := (traj t).percept

    -- Positivity of all `ν_star` step probabilities up to time `t+1` gives positivity of the
    -- history probabilities for the relevant prefixes.
    have h_star_steps_pos : ∀ s < t.succ,
        ν_star.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action]) (traj s).percept > 0 := by
      intro s hs; exact hGood s hs

    have h_star_hist_pos : historyProbability ν_star (trajectoryToHistory traj t.succ) > 0 :=
      historyProbability_pos_of_steps_pos ν_star traj t.succ h_star_steps_pos
    have h_star_hist_pos_t : historyProbability ν_star h > 0 := by
      -- Restrict to the first `t` steps.
      refine historyProbability_pos_of_steps_pos ν_star traj t ?_
      intro s hs
      exact hGood s (Nat.lt_succ_of_lt hs)
    have h_star_step_pos :
        ν_star.prob (h ++ [HistElem.act a]) x > 0 := by
      -- This is exactly the `s = t` instance of `hGood`.
      simpa [h, a, x] using hGood t (Nat.lt_succ_self t)

    -- Use the support condition to get the corresponding `ν`-positivity.
    have h_nu_step_pos :
        ν.prob (h ++ [HistElem.act a]) x > 0 :=
      h_support h a x h_star_step_pos
    have h_nu_steps_pos : ∀ s < t.succ,
        ν.prob (trajectoryToHistory traj s ++ [HistElem.act (traj s).action]) (traj s).percept > 0 := by
      intro s hs
      exact h_support _ _ _ (hGood s hs)
    have h_nu_hist_pos : historyProbability ν (trajectoryToHistory traj t.succ) > 0 :=
      historyProbability_pos_of_steps_pos ν traj t.succ h_nu_steps_pos
    have h_nu_hist_pos_t : historyProbability ν h > 0 := by
      refine historyProbability_pos_of_steps_pos ν traj t ?_
      intro s hs
      exact h_support _ _ _ (hGood s (Nat.lt_succ_of_lt hs))

    -- Convert the relevant ENNReal-positivity statements to positivity in `ℝ`.
    have h_star_hist_toReal_pos :
        0 < (historyProbability ν_star (trajectoryToHistory traj t.succ)).toReal := by
      have hlt : historyProbability ν_star (trajectoryToHistory traj t.succ) < ∞ := by
        have hle : historyProbability ν_star (trajectoryToHistory traj t.succ) ≤ 1 :=
          historyProbability_le_one ν_star (trajectoryToHistory traj t.succ)
        exact lt_of_le_of_lt hle ENNReal.one_lt_top
      exact ENNReal.toReal_pos h_star_hist_pos.ne' hlt.ne_top

    have h_star_hist_toReal_pos_t :
        0 < (historyProbability ν_star h).toReal := by
      have hlt : historyProbability ν_star h < ∞ := by
        have hle : historyProbability ν_star h ≤ 1 := historyProbability_le_one ν_star h
        exact lt_of_le_of_lt hle ENNReal.one_lt_top
      exact ENNReal.toReal_pos h_star_hist_pos_t.ne' hlt.ne_top

    have h_nu_hist_toReal_pos_t :
        0 < (historyProbability ν h).toReal := by
      have hlt : historyProbability ν h < ∞ := by
        have hle : historyProbability ν h ≤ 1 := historyProbability_le_one ν h
        exact lt_of_le_of_lt hle ENNReal.one_lt_top
      exact ENNReal.toReal_pos h_nu_hist_pos_t.ne' hlt.ne_top

    have h_star_step_toReal_pos :
        0 < (ν_star.prob (h ++ [HistElem.act a]) x).toReal := by
      have hlt : ν_star.prob (h ++ [HistElem.act a]) x < ∞ := by
        have hle : ν_star.prob (h ++ [HistElem.act a]) x ≤ 1 := by
          have hw : (h ++ [HistElem.act a]).wellFormed := by
            have hw' : h.wellFormed := trajectoryToHistory_wellFormed traj t
            have he' : Even h.length := trajectoryToHistory_even traj t
            exact wellFormed_append_act h hw' he' a
          calc
            ν_star.prob (h ++ [HistElem.act a]) x
                ≤ ∑' y : Percept, ν_star.prob (h ++ [HistElem.act a]) y := ENNReal.le_tsum x
            _ = 1 := h_stoch _ hw
        exact lt_of_le_of_lt hle ENNReal.one_lt_top
      exact ENNReal.toReal_pos h_star_step_pos.ne' hlt.ne_top

    have h_nu_step_toReal_pos :
        0 < (ν.prob (h ++ [HistElem.act a]) x).toReal := by
      have hlt : ν.prob (h ++ [HistElem.act a]) x < ∞ := by
        have hle : ν.prob (h ++ [HistElem.act a]) x ≤ 1 := by
          have hw : (h ++ [HistElem.act a]).wellFormed := by
            have hw' : h.wellFormed := trajectoryToHistory_wellFormed traj t
            have he' : Even h.length := trajectoryToHistory_even traj t
            exact wellFormed_append_act h hw' he' a
          calc
            ν.prob (h ++ [HistElem.act a]) x
                ≤ ∑' y : Percept, ν.prob (h ++ [HistElem.act a]) y := ENNReal.le_tsum x
            _ ≤ 1 := ν.prob_le_one _ hw
        exact lt_of_le_of_lt hle ENNReal.one_lt_top
      exact ENNReal.toReal_pos h_nu_step_pos.ne' hlt.ne_top

    -- Chain rule for `historyProbability` along the trajectory prefix.
    have h_chain_star :
        historyProbability ν_star (trajectoryToHistory traj t.succ) =
          historyProbability ν_star h * ν_star.prob (h ++ [HistElem.act a]) x := by
      have hw : h.wellFormed := trajectoryToHistory_wellFormed traj t
      have he : Even h.length := trajectoryToHistory_even traj t
      -- Use `trajectoryToHistory_succ` to expose the appended step.
      simpa [h, a, x, Nat.succ_eq_add_one, trajectoryToHistory_succ] using
        (historyProbability_append_step ν_star h hw he a x)
    have h_chain_nu :
        historyProbability ν (trajectoryToHistory traj t.succ) =
          historyProbability ν h * ν.prob (h ++ [HistElem.act a]) x := by
      have hw : h.wellFormed := trajectoryToHistory_wellFormed traj t
      have he : Even h.length := trajectoryToHistory_even traj t
      simpa [h, a, x, Nat.succ_eq_add_one, trajectoryToHistory_succ] using
        (historyProbability_append_step ν h hw he a x)

    -- Now compute `logLikelihoodRatio (t+1)` and simplify to the desired log-add form.
    have h_log_succ :
        logLikelihoodRatio ν ν_star t.succ traj =
          logLikelihoodRatio ν ν_star t traj + stepLogLikelihood ν ν_star h (traj t) := by
      -- Unfold definitions (allowing `simp` to reduce the internal `let`-bindings).
      simp [logLikelihoodRatio, stepLogLikelihood, h]
      -- First, show we are in the `else` branch for the `(t+1)` history under `ν_star`.
      have h_star_toReal_ne0 :
          (historyProbability ν_star (trajectoryToHistory traj t.succ)).toReal ≠ 0 :=
        ne_of_gt h_star_hist_toReal_pos
      simp [if_neg h_star_toReal_ne0]
      -- Replace the full-history probabilities using the chain rule and `ENNReal.toReal_mul`.
      simp [h_chain_star, h_chain_nu, ENNReal.toReal_mul]
      -- At this point, `simp` has already reduced the `if`-branches in `stepLogLikelihood`
      -- using the positivity facts established above.
      -- Apply the log product decomposition.
      have h_log :=
        log_ratio_mul_eq_add
          ((historyProbability ν h).toReal)
          ((ν.prob (h ++ [HistElem.act a]) x).toReal)
          ((historyProbability ν_star h).toReal)
          ((ν_star.prob (h ++ [HistElem.act a]) x).toReal)
          h_nu_hist_toReal_pos_t h_nu_step_toReal_pos h_star_hist_toReal_pos_t h_star_step_toReal_pos
      -- Rewrite the remaining `if`-branches on the RHS using positivity of the `ν_star` factors.
      have h_star_toReal_ne0_t : (historyProbability ν_star h).toReal ≠ 0 :=
        ne_of_gt h_star_hist_toReal_pos_t
      have h_star_step_toReal_ne0 : (ν_star.prob (h ++ [HistElem.act a]) x).toReal ≠ 0 :=
        ne_of_gt h_star_step_toReal_pos
      -- After these rewrites, the RHS matches `h_log`.
      simpa [logLikelihoodRatio, stepLogLikelihood, h, a, x,
        if_neg h_star_toReal_ne0_t, if_neg h_star_step_toReal_ne0,
        mul_assoc, add_assoc, add_left_comm, add_comm] using h_log

    -- Finish by rewriting with the one-step increment identity.
    simp [h_log_succ, h]

/-! ## The Supermartingale Property

This is the central result: the log-likelihood ratio is a supermartingale
under the true environment ν*.
-/

/-- The conditional expectation of the step log-likelihood is the negative KL divergence.

    E_{ν*}[stepLogLikelihood ν ν* h X | h] = -KL(ν* || ν | h)

    where KL(P || Q) = Σ_x P(x) log(P(x)/Q(x)) ≥ 0 is the KL divergence.

    This is the key information-theoretic inequality that makes the supermartingale work.

    NOTE: The history h is the history BEFORE taking the step. stepLogLikelihood ν ν* h ⟨a, x⟩
    computes log(ν.prob(h ++ [act a]) x / ν_star.prob(h ++ [act a]) x). -/
theorem conditional_stepLogLikelihood (ν ν_star : Environment) (h : History) (a : Action)
    (hw : h.wellFormed) (he : Even h.length) (h_stoch : isStochastic ν_star)
    (h_support : ∀ x : Percept, (ν_star.prob (h ++ [HistElem.act a]) x).toReal > 0 →
                                 (ν.prob (h ++ [HistElem.act a]) x).toReal > 0) :
    -- Under ν*, the expected step log-likelihood is ≤ 0
    ∑ x : Percept, (ν_star.prob (h ++ [HistElem.act a]) x).toReal *
      stepLogLikelihood ν ν_star h ⟨a, x⟩ ≤ 0 := by
  /-
  This is Gibbs' inequality: E_P[log(Q/P)] ≤ 0

  The proof uses Jensen's inequality for the concave log function:
  - log is concave on (0, ∞)
  - For weights P(x) ≥ 0 and points Q(x)/P(x) > 0:
    ∑_x P(x) * log(Q(x)/P(x)) ≤ log(∑_x P(x) * Q(x)/P(x)) = log(∑_x Q(x))
  - Since ∑_x Q(x) ≤ 1: log(∑_x Q(x)) ≤ log(1) = 0
  -/
  -- Abbreviate the history prefix with action
  set ha := h ++ [HistElem.act a]
  have ha_wf : ha.wellFormed := wellFormed_append_act h hw he a
  -- Abbreviate the probabilities with explicit types
  let P : Percept → ℝ := fun x => (ν_star.prob ha x).toReal
  let Q : Percept → ℝ := fun x => (ν.prob ha x).toReal
  -- First, handle the stepLogLikelihood definition
  -- stepLogLikelihood ν ν_star h ⟨a, x⟩ = if p_star_h = 0 then 0 else if P(x) = 0 then 0 else log(Q(x)/P(x))
  -- Since we're summing over all x with weights P(x), terms with P(x) = 0 contribute 0
  -- Also, if historyProbability ν_star h = 0, then all terms are 0 (from first if-branch)
  -- So we focus on the case where both conditions are false
  by_cases h_hist : (historyProbability ν_star h).toReal = 0
  · -- If history has 0 probability, all stepLogLikelihood terms are 0
    have h_all_zero : ∀ x, stepLogLikelihood ν ν_star h ⟨a, x⟩ = 0 := by
      intro x
      simp only [stepLogLikelihood]
      rw [if_pos h_hist]
    simp only [h_all_zero, mul_zero, Finset.sum_const_zero, le_refl]
  · -- History has positive probability
    -- Rewrite stepLogLikelihood using its definition
    have h_step_eq : ∀ x, stepLogLikelihood ν ν_star h ⟨a, x⟩ =
        if P x = 0 then 0 else Real.log (Q x / P x) := by
      intro x
      simp only [stepLogLikelihood]
      rw [if_neg h_hist]

    -- Terms with P(x) = 0 contribute 0 to the sum
    have h_sum_eq : ∑ x : Percept, P x * stepLogLikelihood ν ν_star h ⟨a, x⟩ =
                     ∑ x : Percept, if P x = 0 then 0 else P x * Real.log (Q x / P x) := by
      congr 1
      ext x
      rw [h_step_eq]
      by_cases h : P x = 0
      · simp [h]
      · simp [h]

    rw [h_sum_eq]

    -- Goal: ∑_x (if P(x) = 0 then 0 else P(x) * log(Q(x)/P(x))) ≤ 0
    -- The key insight: for x with P(x) > 0, we have:
    -- P(x) * log(Q(x)/P(x)) = P(x) * (log(Q(x)) - log(P(x)))

    -- Upper bound: use that ∑ Q(x) ≤ 1
    have h_Q_sum_le : ∑ x : Percept, Q x ≤ 1 := by
      -- For finite types, finset sum ≤ tsum ≤ 1
      have hsum : ∑' x : Percept, ν.prob ha x ≤ 1 := ν.prob_le_one ha ha_wf
      have hsum_fin : ∑ x : Percept, ν.prob ha x ≤ 1 := by
        calc ∑ x : Percept, ν.prob ha x
            ≤ ∑' x : Percept, ν.prob ha x := ENNReal.sum_le_tsum Finset.univ
          _ ≤ 1 := hsum
      -- All probabilities are finite (≤ 1 < ⊤)
      have h_fin : ∀ x : Percept, ν.prob ha x ≠ ∞ := by
        intro x
        have h_le : ν.prob ha x ≤ 1 := by
          have h_tsum : ∑' y : Percept, ν.prob ha y ≤ 1 := ν.prob_le_one ha ha_wf
          apply le_trans (ENNReal.le_tsum x)
          exact h_tsum
        have h_lt : ν.prob ha x < ⊤ := lt_of_le_of_lt h_le ENNReal.one_lt_top
        exact h_lt.ne_top
      -- Convert to reals using toReal_sum
      calc ∑ x : Percept, Q x
          = ∑ x : Percept, (ν.prob ha x).toReal := rfl
        _ = (∑ x : Percept, ν.prob ha x).toReal := by
            rw [← ENNReal.toReal_sum]
            intro x _
            exact h_fin x
        _ ≤ 1 := by
            have : (∑ x : Percept, ν.prob ha x).toReal ≤ (1 : ℝ≥0∞).toReal := by
              apply ENNReal.toReal_mono ENNReal.one_ne_top
              exact hsum_fin
            simp only [ENNReal.toReal_one] at this
            exact this

    -- Prove ∑ P(x) = 1 using isStochastic
    have h_P_sum_one : ∑ x : Percept, P x = 1 := by
      have h_stoch_ha := h_stoch ha ha_wf
      -- All P(x) are finite (≤ 1 < ⊤)
      have h_P_fin : ∀ x : Percept, ν_star.prob ha x ≠ ∞ := by
        intro x
        have : ν_star.prob ha x ≤ 1 := by
          calc ν_star.prob ha x
              ≤ ∑' y : Percept, ν_star.prob ha y := ENNReal.le_tsum x
            _ = 1 := h_stoch_ha
        have h_lt : ν_star.prob ha x < ⊤ := lt_of_le_of_lt this ENNReal.one_lt_top
        exact h_lt.ne_top
      -- Convert finset sum to tsum, which equals 1
      calc ∑ x : Percept, P x
          = ∑ x : Percept, (ν_star.prob ha x).toReal := rfl
        _ = (∑ x : Percept, ν_star.prob ha x).toReal := by
            rw [← ENNReal.toReal_sum]
            intro x _
            exact h_P_fin x
        _ = 1 := by
            have hsum : (∑ x : Percept, ν_star.prob ha x) = 1 := by
              simpa [tsum_fintype] using h_stoch_ha
            simp [hsum]

    -- Use log(t) ≤ t - 1 to bound each term
    have h_term_bound : ∀ x : Percept,
        (if P x = 0 then 0 else P x * Real.log (Q x / P x)) ≤ Q x - P x := by
      intro x
      by_cases h : P x = 0
      · simp [h]
        exact ENNReal.toReal_nonneg
      · simp [h]
        have h_pos : 0 < P x := by
          have : ¬(P x ≤ 0) := by
            intro h_le
            have : P x = 0 := le_antisymm h_le ENNReal.toReal_nonneg
            exact h this
          push_neg at this
          exact this
        by_cases h_Q_zero : Q x = 0
        · -- Q x = 0 case: By the support condition, P x > 0 implies Q x > 0
          -- So Q x = 0 implies P x = 0, contradicting our assumption P x > 0
          exfalso
          have h_Q_pos : Q x > 0 := h_support x h_pos
          linarith [h_Q_pos]
        · -- Q x > 0 case
          have h_Q_pos : 0 < Q x := by
            have : ¬(Q x ≤ 0) := by
              intro h_le
              have : Q x = 0 := le_antisymm h_le ENNReal.toReal_nonneg
              exact h_Q_zero this
            push_neg at this
            exact this
          have h_ratio_pos : 0 < Q x / P x := div_pos h_Q_pos h_pos
          have h_log_ineq := Real.log_le_sub_one_of_pos h_ratio_pos
          have h_algebra : P x * (Q x / P x - 1) = Q x - P x := by
            have h_pos_ne : P x ≠ 0 := ne_of_gt h_pos
            field_simp
          calc P x * Real.log (Q x / P x)
              ≤ P x * (Q x / P x - 1) :=
                mul_le_mul_of_nonneg_left h_log_ineq (le_of_lt h_pos)
            _ = Q x - P x := h_algebra

    -- Sum the bounds: ∑ term ≤ ∑ (Q-P) = ∑Q - ∑P = ∑Q - 1 ≤ 0
    have h_sum_bound : (∑ x : Percept, if P x = 0 then 0 else P x * Real.log (Q x / P x) : ℝ) ≤
                       ∑ x : Percept, (Q x - P x) :=
      Finset.sum_le_sum fun x _ => h_term_bound x

    have h_sub : ∑ x : Percept, (Q x - P x) = ∑ x : Percept, Q x - ∑ x : Percept, P x := by
      simp_rw [← Finset.sum_sub_distrib]

    -- Break down the calc chain with explicit intermediate steps
    have h_step1 : (∑ x : Percept, if P x = 0 then 0 else P x * Real.log (Q x / P x) : ℝ) ≤
                   ∑ x : Percept, (Q x - P x) := h_sum_bound
    have h_step2 : ∑ x : Percept, (Q x - P x) = ∑ x : Percept, Q x - ∑ x : Percept, P x := h_sub
    have h_step3 : ∑ x : Percept, Q x - ∑ x : Percept, P x = ∑ x : Percept, Q x - 1 := by
      rw [h_P_sum_one]
    have h_step4 : ∑ x : Percept, Q x - 1 ≤ 1 - 1 := by
      linarith [h_Q_sum_le]
    have h_step5 : (1 : ℝ) - 1 = 0 := sub_self 1

    calc (∑ x : Percept, if P x = 0 then 0 else P x * Real.log (Q x / P x) : ℝ)
        ≤ ∑ x : Percept, (Q x - P x) := h_step1
      _ = ∑ x : Percept, Q x - ∑ x : Percept, P x := h_step2
      _ = ∑ x : Percept, Q x - 1 := h_step3
      _ ≤ 1 - 1 := h_step4
      _ = 0 := h_step5

/-- Log-likelihood ratio is strongly measurable with respect to the filtration.
    This is a technical requirement for the supermartingale definition. -/
theorem logLikelihoodRatio_stronglyMeasurable (ν ν_star : Environment) (t : ℕ) :
    @Measurable Trajectory ℝ (sigmaAlgebraUpTo t) _ (logLikelihoodRatio ν ν_star t) := by
  -- Use measurable_wrt_filtration_iff: measurable iff depends only on first t steps
  rw [measurable_wrt_filtration_iff]
  -- This is exactly logLikelihoodRatio_adapted
  exact logLikelihoodRatio_adapted ν ν_star t

/-- Log-likelihood ratio is integrable under the true environment.
    This is needed to define conditional expectations. -/
theorem logLikelihoodRatio_integrable (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star) :
    MeasureTheory.Integrable (logLikelihoodRatio ν ν_star t) (environmentMeasure ν_star h_stoch) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance

  -- `logLikelihoodRatio ν ν_star t` depends only on the first `t` steps, hence has finite range and
  -- is bounded, therefore integrable on a finite measure space.
  have h_meas_sigma :
      @Measurable Trajectory ℝ (sigmaAlgebraUpTo t) _ (logLikelihoodRatio ν ν_star t) :=
    logLikelihoodRatio_stronglyMeasurable ν ν_star t
  have h_meas : Measurable (logLikelihoodRatio ν ν_star t) := by
    -- Lift measurability from `sigmaAlgebraUpTo t` to the full product σ-algebra.
    exact (Measurable.mono h_meas_sigma (sigmaAlgebraUpTo_le t) le_rfl)
  have h_aesm : MeasureTheory.AEStronglyMeasurable (logLikelihoodRatio ν ν_star t) μ :=
    h_meas.aestronglyMeasurable

  -- Extend a finite prefix to a full trajectory by padding with `default`.
  let extendPrefix (pfx : Fin t → Step) : Trajectory :=
    fun n => if h : n < t then pfx ⟨n, h⟩ else default

  -- A uniform bound for `‖logLikelihoodRatio‖`, obtained from finiteness of the prefix space.
  let g : (Fin t → Step) → ℝ := fun pfx => ‖logLikelihoodRatio ν ν_star t (extendPrefix pfx)‖
  have hfin : (Set.range g).Finite := Set.finite_range g
  rcases hfin.bddAbove with ⟨C, hC⟩

  have h_bound : ∀ traj : Trajectory, ‖logLikelihoodRatio ν ν_star t traj‖ ≤ C := by
    intro traj
    have h_eq :
        logLikelihoodRatio ν ν_star t traj =
          logLikelihoodRatio ν ν_star t (extendPrefix (truncate t traj)) := by
      refine logLikelihoodRatio_adapted ν ν_star t traj (extendPrefix (truncate t traj)) ?_
      intro i hi
      simp [extendPrefix, truncate, hi]
    -- Use the bound on the (finite) range of `g`.
    have h_in : g (truncate t traj) ∈ Set.range g := ⟨truncate t traj, rfl⟩
    calc
      ‖logLikelihoodRatio ν ν_star t traj‖
          = ‖logLikelihoodRatio ν ν_star t (extendPrefix (truncate t traj))‖ := by simp [h_eq]
      _ = g (truncate t traj) := rfl
      _ ≤ C := hC h_in

  exact MeasureTheory.Integrable.of_bound (μ := μ) h_aesm C
    (Filter.Eventually.of_forall h_bound)

/-- `prefixToHistory t pfx` has length `2t`. -/
theorem prefixToHistory_length (t : ℕ) (pfx : Fin t → Step) :
    (prefixToHistory t pfx).length = 2 * t := by
  induction t with
  | zero =>
    simp [prefixToHistory]
  | succ t ih =>
    -- Peel one step using `prefixToHistory_succ` and apply the IH.
    simp [prefixToHistory_succ, ih]
    omega

/-- `prefixToHistory t pfx` is well-formed. -/
theorem prefixToHistory_wellFormed (t : ℕ) (pfx : Fin t → Step) :
    (prefixToHistory t pfx).wellFormed := by
  induction t with
  | zero =>
    simp [prefixToHistory, History.wellFormed]
  | succ t ih =>
    -- `prefixToHistory (t+1) pfx = [act, per] ++ ...`, and `wellFormed` reduces to the tail.
    simpa [prefixToHistory_succ, History.wellFormed] using ih (fun i => pfx i.succ)

/-- `historySteps` of a `prefixToHistory` is the original length. -/
theorem historySteps_prefixToHistory (t : ℕ) (pfx : Fin t → Step) :
    historySteps (prefixToHistory t pfx) = t := by
  simp only [historySteps, prefixToHistory_length, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]

/-- Recover the `truncate` prefix from `trajectoryToHistory`. -/
theorem historyToFinPrefix_trajectoryToHistory (t : ℕ) (traj : Trajectory) :
    historyToFinPrefix t (trajectoryToHistory traj t) = truncate t traj := by
  induction t generalizing traj with
  | zero =>
    funext i
    exact (nomatch i)
  | succ t ih =>
    funext i
    -- Use the front-decomposition lemma matching the recursive structure of `historyToFinPrefix`.
    have h_decomp :
        trajectoryToHistory traj (t + 1) =
          [HistElem.act (traj 0).action, HistElem.per (traj 0).percept] ++
            trajectoryToHistory (shiftTrajectory traj) t := by
      simpa [Nat.succ_eq_add_one] using trajectoryToHistory_succ_eq traj t
    -- Peel the `Fin (t+1)` index.
    cases i using Fin.cases with
    | zero =>
      cases h0 : traj 0 with
      | mk a x =>
        simp [h_decomp, truncate, h0]
    | succ j =>
      have h_tail := congrArg (fun f => f j) (ih (traj := shiftTrajectory traj))
      -- Reduce to the IH and unwind `truncate`/`shiftTrajectory`.
      simpa [historyToFinPrefix, h_decomp, truncate, shiftTrajectory] using h_tail

/-- The atom `{traj | truncate t traj = pfx}` equals the corresponding cylinder at time `t`. -/
theorem truncate_preimage_singleton_eq_cylinderSetAt (t : ℕ) (pfx : Fin t → Step) :
    (truncate t) ⁻¹' ({pfx} : Set (Fin t → Step)) = cylinderSetAt t (prefixToHistory t pfx) := by
  ext traj
  constructor
  · intro htraj
    -- Use `prefixToHistory_eq_trajectoryToHistory`.
    have : prefixToHistory t (truncate t traj) = trajectoryToHistory traj t :=
      prefixToHistory_eq_trajectoryToHistory t traj
    have ht : truncate t traj = pfx := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using htraj
    -- Now rewrite.
    simpa [cylinderSetAt, ht] using this.symm
  · intro htraj
    -- Apply `historyToFinPrefix` to recover the truncation.
    have ht : trajectoryToHistory traj t = prefixToHistory t pfx := by
      simpa [cylinderSetAt, Set.mem_setOf_eq] using htraj
    have ht' := congrArg (fun h => historyToFinPrefix t h) ht
    have : truncate t traj = pfx := by
      simpa [historyToFinPrefix_trajectoryToHistory, historyToFinPrefix_prefixToHistory] using ht'
    simp [Set.mem_preimage, Set.mem_singleton_iff, this]

/-- The per-step log-likelihood increment as a function on trajectories. -/
noncomputable def stepLogLikelihoodProcess (ν ν_star : Environment) (t : ℕ) : Trajectory → ℝ :=
  fun traj => stepLogLikelihood ν ν_star (trajectoryToHistory traj t) (traj t)

/-- `stepLogLikelihoodProcess` depends only on the first `t+1` steps. -/
theorem stepLogLikelihoodProcess_adapted (ν ν_star : Environment) (t : ℕ) :
    ∀ traj₁ traj₂, (∀ i < t.succ, traj₁ i = traj₂ i) →
      stepLogLikelihoodProcess ν ν_star t traj₁ = stepLogLikelihoodProcess ν ν_star t traj₂ := by
  intro traj₁ traj₂ h
  simp [stepLogLikelihoodProcess, stepLogLikelihood]
  -- The conditioning history depends only on the first `t` steps.
  have h_hist :
      trajectoryToHistory traj₁ t = trajectoryToHistory traj₂ t := by
    refine trajectoryToHistory_depends_on_prefix traj₁ traj₂ t ?_
    intro i hi
    exact h i (Nat.lt_trans hi (Nat.lt_succ_self t))
  -- The realized step at time `t` is part of the first `t+1` steps.
  have h_step : traj₁ t = traj₂ t := h t (Nat.lt_succ_self t)
  simp [h_hist, h_step]

/-- `stepLogLikelihoodProcess` is measurable with respect to `sigmaAlgebraUpTo (t+1)`. -/
theorem stepLogLikelihoodProcess_measurable (ν ν_star : Environment) (t : ℕ) :
    @Measurable Trajectory ℝ (sigmaAlgebraUpTo t.succ) _ (stepLogLikelihoodProcess ν ν_star t) := by
  -- Use `measurable_wrt_filtration_iff`: measurability iff the function depends only on a prefix.
  rw [measurable_wrt_filtration_iff]
  exact stepLogLikelihoodProcess_adapted ν ν_star t

/-- `stepLogLikelihoodProcess` is integrable under the true environment for each fixed `t`. -/
theorem stepLogLikelihoodProcess_integrable (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star) :
    MeasureTheory.Integrable (stepLogLikelihoodProcess ν ν_star t)
      (environmentMeasure ν_star h_stoch) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance

  -- Measurability: `stepLogLikelihoodProcess` is measurable w.r.t. `sigmaAlgebraUpTo (t+1)`.
  have h_meas_sigma :
      @Measurable Trajectory ℝ (sigmaAlgebraUpTo t.succ) _ (stepLogLikelihoodProcess ν ν_star t) :=
    stepLogLikelihoodProcess_measurable ν ν_star t
  have h_meas : Measurable (stepLogLikelihoodProcess ν ν_star t) := by
    exact (Measurable.mono h_meas_sigma (sigmaAlgebraUpTo_le t.succ) le_rfl)
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable (stepLogLikelihoodProcess ν ν_star t) μ :=
    h_meas.aestronglyMeasurable

  -- Extend a finite prefix to a full trajectory by padding with `default`.
  let extendPrefix (pfx : Fin t.succ → Step) : Trajectory :=
    fun n => if h : n < t.succ then pfx ⟨n, h⟩ else default

  -- A uniform bound, obtained from finiteness of the `(t+1)`-prefix space.
  let g : (Fin t.succ → Step) → ℝ :=
    fun pfx => ‖stepLogLikelihoodProcess ν ν_star t (extendPrefix pfx)‖
  have hfin : (Set.range g).Finite := Set.finite_range g
  rcases hfin.bddAbove with ⟨C, hC⟩

  have h_bound : ∀ traj : Trajectory, ‖stepLogLikelihoodProcess ν ν_star t traj‖ ≤ C := by
    intro traj
    have h_eq :
        stepLogLikelihoodProcess ν ν_star t traj =
          stepLogLikelihoodProcess ν ν_star t (extendPrefix (truncate t.succ traj)) := by
      refine stepLogLikelihoodProcess_adapted ν ν_star t traj (extendPrefix (truncate t.succ traj)) ?_
      intro i hi
      -- `simp` reduces this to the (impossible) `t < i` branch.
      simp [extendPrefix, truncate]
      intro hti
      exfalso
      exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ hi)) hti
    have h_in : g (truncate t.succ traj) ∈ Set.range g := ⟨truncate t.succ traj, rfl⟩
    calc
      ‖stepLogLikelihoodProcess ν ν_star t traj‖
          = ‖stepLogLikelihoodProcess ν ν_star t (extendPrefix (truncate t.succ traj))‖ := by
              simp [h_eq]
      _ = g (truncate t.succ traj) := rfl
      _ ≤ C := hC h_in

  exact MeasureTheory.Integrable.of_bound (μ := μ) h_aesm C
    (Filter.Eventually.of_forall h_bound)

/-- The one-step increment identity for the log-likelihood ratio, almost surely under `ν_star`. -/
theorem logLikelihoodRatio_succ_eq_add_stepLogLikelihoodProcess_ae (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star) (h_support : SupportCondition ν ν_star) :
    ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
      logLikelihoodRatio ν ν_star t.succ traj =
        logLikelihoodRatio ν ν_star t traj + stepLogLikelihoodProcess ν ν_star t traj := by
  have h_t :=
    logLikelihoodRatio_decomposition_ae ν ν_star t h_stoch h_support
  have h_succ :=
    logLikelihoodRatio_decomposition_ae ν ν_star t.succ h_stoch h_support
  filter_upwards [h_t, h_succ] with traj ht ht_succ
  -- Rewrite the decomposition at `t+1` as the decomposition at `t` plus the last term.
  have h_sum :
      (∑ s ∈ Finset.range t.succ,
        stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s)) =
      (∑ s ∈ Finset.range t,
        stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s)) +
        stepLogLikelihood ν ν_star (trajectoryToHistory traj t) (traj t) := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.sum_range_succ (fun s =>
        stepLogLikelihood ν ν_star (trajectoryToHistory traj s) (traj s)) t)
  -- Combine.
  simp [stepLogLikelihoodProcess, ht, ht_succ, h_sum]

/-- On a fixed `t`-prefix atom, the step log-likelihood has non-positive set integral. -/
theorem setIntegral_stepLogLikelihoodProcess_atom_le_zero (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star) (h_support : SupportCondition ν ν_star)
    (pfx : Fin t → Step) :
    (∫ traj in (truncate t) ⁻¹' ({pfx} : Set (Fin t → Step)),
        stepLogLikelihoodProcess ν ν_star t traj ∂(environmentMeasure ν_star h_stoch)) ≤ 0 := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance

  -- Rewrite the atom as a time-`t` cylinder.
  have h_atom :
      (truncate t) ⁻¹' ({pfx} : Set (Fin t → Step)) = cylinderSetAt t (prefixToHistory t pfx) :=
    truncate_preimage_singleton_eq_cylinderSetAt t pfx
  let h : History := prefixToHistory t pfx
  have hw : h.wellFormed := prefixToHistory_wellFormed t pfx
  have he : Even h.length := by
    rw [prefixToHistory_length t pfx]
    exact even_two_mul t
  have h_steps : historySteps h = t := by
    simpa [h] using historySteps_prefixToHistory t pfx

  -- Partition the cylinder by the next step.
  let stepSet : Step → Set Trajectory :=
    fun st => cylinderSetAt t h ∩ {traj | traj t = st}

  have h_cover : (⋃ st : Step, stepSet st) = cylinderSetAt t h := by
    ext traj
    constructor
    · intro hU
      rcases Set.mem_iUnion.1 hU with ⟨st, hst⟩
      exact hst.1
    · intro ht
      refine Set.mem_iUnion.2 ?_
      refine ⟨traj t, ?_⟩
      exact ⟨ht, rfl⟩

  have h_stepSet_meas : ∀ st : Step, MeasurableSet (stepSet st) := by
    intro st
    have h_cyl : MeasurableSet (cylinderSetAt t h) := cylinderSetAt_measurable t h
    have h_single : MeasurableSet ({st} : Set Step) := measurableSet_singleton st
    have h_eval : Measurable fun traj : Trajectory => traj t := measurable_pi_apply t
    have h_evt : MeasurableSet ({traj : Trajectory | traj t = st}) := by
      simpa [Set.preimage, Set.mem_setOf_eq] using h_eval h_single
    exact h_cyl.inter h_evt

  have h_stepSet_pairwise : Pairwise fun st₁ st₂ => Disjoint (stepSet st₁) (stepSet st₂) := by
    intro st₁ st₂ hne
    refine Set.disjoint_left.2 ?_
    intro traj h1 h2
    have ht1 : traj t = st₁ := h1.2
    have ht2 : traj t = st₂ := h2.2
    exact hne (ht1.symm.trans ht2)

  have h_stepSet_int : ∀ st : Step, MeasureTheory.IntegrableOn
      (stepLogLikelihoodProcess ν ν_star t) (stepSet st) μ := by
    intro _
    exact (stepLogLikelihoodProcess_integrable ν ν_star t h_stoch).integrableOn

  have h_int_decomp :
      (∫ traj in cylinderSetAt t h, stepLogLikelihoodProcess ν ν_star t traj ∂μ) =
        ∑ st : Step, (∫ traj in stepSet st, stepLogLikelihoodProcess ν ν_star t traj ∂μ) := by
    rw [← h_cover]
    simpa [stepSet] using
      (MeasureTheory.integral_iUnion_fintype (μ := μ)
        (f := stepLogLikelihoodProcess ν ν_star t) (s := stepSet)
        h_stepSet_meas h_stepSet_pairwise h_stepSet_int)

  have h_int_piece :
      ∀ st : Step,
        (∫ traj in stepSet st, stepLogLikelihoodProcess ν ν_star t traj ∂μ) =
          μ.real (stepSet st) * stepLogLikelihood ν ν_star h st := by
    intro st
    have h_eqOn : Set.EqOn (stepLogLikelihoodProcess ν ν_star t)
        (fun _ => stepLogLikelihood ν ν_star h st) (stepSet st) := by
      intro traj htraj
      have ht_hist : trajectoryToHistory traj t = h := htraj.1
      have ht_step : traj t = st := htraj.2
      simp [stepLogLikelihoodProcess, ht_hist, ht_step]
    rw [MeasureTheory.setIntegral_congr_fun (h_stepSet_meas st) h_eqOn]
    simp [smul_eq_mul]

  have h_stepSet_real :
      ∀ st : Step,
        μ.real (stepSet st) =
          μ.real (cylinderSet h) * uniformActionProb.toReal *
            (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal := by
    intro st
    -- Switch from `cylinderSetAt` to `cylinderSet`.
    have h_cyl : cylinderSetAt t h = cylinderSet h := by
      have hc := (cylinderSet_eq_cylinderSetAt' h hw)
      simpa [h_steps] using hc.symm
    have h_stepSet_eq :
        stepSet st = cylinderSet h ∩ {traj | traj (historySteps h) = st} := by
      ext traj
      simp [stepSet, h_cyl, h_steps]
    have h_fact :=
      IT_product_factorization ν_star h_stoch h hw he st
    -- Convert to real-valued measure; `ENNReal.toReal_mul` handles all cases.
    simp [μ, MeasureTheory.measureReal_def, h_stepSet_eq, h_fact, mul_left_comm, mul_comm]

  have h_inner_nonpos :
      (∑ st : Step,
          (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
            stepLogLikelihood ν ν_star h st) ≤ 0 := by
    classical
    -- Rewrite the sum over steps as an iterated sum over actions and percepts.
    have h_step_to_prod :
        (∑ st : Step,
            (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
              stepLogLikelihood ν ν_star h st) =
          ∑ p : Action × Percept,
            (ν_star.prob (h ++ [HistElem.act p.1]) p.2).toReal *
              stepLogLikelihood ν ν_star h (Step.mk p.1 p.2) := by
      refine Fintype.sum_equiv Step.equiv
        (fun st =>
          (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
            stepLogLikelihood ν ν_star h st)
        (fun p =>
          (ν_star.prob (h ++ [HistElem.act p.1]) p.2).toReal *
            stepLogLikelihood ν ν_star h (Step.mk p.1 p.2))
        (fun st => by
          -- `Step.equiv st = (st.action, st.percept)`.
          simp [Step.equiv])
    have h_prod_to_double :
        (∑ p : Action × Percept,
            (ν_star.prob (h ++ [HistElem.act p.1]) p.2).toReal *
              stepLogLikelihood ν ν_star h (Step.mk p.1 p.2)) =
          ∑ a : Action, ∑ x : Percept,
            (ν_star.prob (h ++ [HistElem.act a]) x).toReal *
              stepLogLikelihood ν ν_star h ⟨a, x⟩ := by
      -- This is exactly `Fintype.sum_prod_type`.
      simp [Fintype.sum_prod_type]
    rw [h_step_to_prod, h_prod_to_double]
    -- Bound each action-slice by Gibbs' inequality.
    have h_each_action :
        ∀ a : Action,
          (∑ x : Percept,
              (ν_star.prob (h ++ [HistElem.act a]) x).toReal *
                stepLogLikelihood ν ν_star h ⟨a, x⟩) ≤ 0 := by
      intro a
      have h_support_toReal :
          ∀ x : Percept,
            (ν_star.prob (h ++ [HistElem.act a]) x).toReal > 0 →
              (ν.prob (h ++ [HistElem.act a]) x).toReal > 0 := by
        intro x hx
        have hx' : 0 < (ν_star.prob (h ++ [HistElem.act a]) x).toReal := by
          simpa [gt_iff_lt] using hx
        have hx_pos : 0 < ν_star.prob (h ++ [HistElem.act a]) x :=
          (ENNReal.toReal_pos_iff).1 hx' |>.1
        have hx_pos_nu : 0 < ν.prob (h ++ [HistElem.act a]) x :=
          h_support h a x hx_pos
        have hx_lt_top : ν.prob (h ++ [HistElem.act a]) x < ∞ := by
          have ha_wf : (h ++ [HistElem.act a]).wellFormed := wellFormed_append_act h hw he a
          have h_le : ν.prob (h ++ [HistElem.act a]) x ≤ 1 := by
            have hsum : (∑' y : Percept, ν.prob (h ++ [HistElem.act a]) y) ≤ 1 :=
              ν.prob_le_one (h ++ [HistElem.act a]) ha_wf
            exact le_trans (ENNReal.le_tsum x) hsum
          exact lt_of_le_of_lt h_le ENNReal.one_lt_top
        exact ENNReal.toReal_pos hx_pos_nu.ne' hx_lt_top.ne_top
      simpa using
        conditional_stepLogLikelihood ν ν_star h a hw he h_stoch h_support_toReal
    classical
    simpa using
      (Finset.sum_nonpos (s := (Finset.univ : Finset Action)) fun a _ => h_each_action a)

  have h_nonneg_const :
      0 ≤ μ.real (cylinderSet h) * uniformActionProb.toReal := by
    have h₁ : 0 ≤ μ.real (cylinderSet h) := by
      simp [MeasureTheory.measureReal_def]
    have h₂ : 0 ≤ uniformActionProb.toReal := ENNReal.toReal_nonneg
    exact mul_nonneg h₁ h₂

  have h_main :
      (∫ traj in cylinderSetAt t h, stepLogLikelihoodProcess ν ν_star t traj ∂μ) ≤ 0 := by
    -- Expand using the partition, then factor out the nonnegative constant.
    classical
    rw [h_int_decomp]
    simp_rw [h_int_piece, h_stepSet_real]
    -- Factor out `μ.real (cylinderSet h) * uniformActionProb.toReal`.
    have h_sum :
        (∑ st : Step,
            (μ.real (cylinderSet h) * uniformActionProb.toReal) *
              ((ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st)) =
          (μ.real (cylinderSet h) * uniformActionProb.toReal) *
            (∑ st : Step,
              (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st) := by
      -- This is `Finset.mul_sum` for the universal finset, used backwards.
      classical
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset Step))
          (a := μ.real (cylinderSet h) * uniformActionProb.toReal)
          (f := fun st : Step =>
            (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
              stepLogLikelihood ν ν_star h st)).symm
    -- Apply the non-positive inner sum bound.
    have :
        (μ.real (cylinderSet h) * uniformActionProb.toReal) *
            (∑ st : Step,
              (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h_nonneg_const h_inner_nonpos
    -- Rewrite back to the original sum form (with commutativity/associativity normalization).
    have h_goal_eq :
        (μ.real (cylinderSet h) * uniformActionProb.toReal) *
            (∑ st : Step,
              (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st) =
          ∑ st : Step,
            uniformActionProb.toReal *
              (stepLogLikelihood ν ν_star h st *
                ((ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                  μ.real (cylinderSet h))) := by
      classical
      -- First, expand the product into a sum of products.
      -- Then normalize each term using commutativity/associativity in `ℝ`.
      calc
        (μ.real (cylinderSet h) * uniformActionProb.toReal) *
            (∑ st : Step,
              (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st)
            =
          ∑ st : Step,
            (μ.real (cylinderSet h) * uniformActionProb.toReal) *
              ((ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                stepLogLikelihood ν ν_star h st) := by
          -- `Finset.mul_sum` for the universal finset.
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset Step))
              (a := μ.real (cylinderSet h) * uniformActionProb.toReal)
              (f := fun st : Step =>
                (ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                  stepLogLikelihood ν ν_star h st))
        _ = _ := by
          -- Normalize each summand into the target arrangement.
          refine Finset.sum_congr rfl ?_
          intro st _
          ring_nf
    -- Now rewrite the goal using `h_goal_eq` and conclude from `this`.
    have : (∑ st : Step,
            uniformActionProb.toReal *
              (stepLogLikelihood ν ν_star h st *
                ((ν_star.prob (h ++ [HistElem.act st.action]) st.percept).toReal *
                  μ.real (cylinderSet h)))) ≤ 0 := by
      simpa [h_goal_eq] using this
    -- The current goal is the same sum, but expressed via the partitioning lemma `h_sum`.
    -- Use `h_sum` to rewrite it into the above form.
    simpa [h_sum, mul_assoc, mul_left_comm, mul_comm] using this

  -- Translate back to the original atom set.
  simpa [μ, h_atom, h] using h_main

/-- For any ℱₜ-measurable event, the step log-likelihood has non-positive set integral. -/
theorem setIntegral_stepLogLikelihoodProcess_le_zero (ν ν_star : Environment) (t : ℕ)
    (h_stoch : isStochastic ν_star) (h_support : SupportCondition ν ν_star)
    (s : Set Trajectory) (hs : @MeasurableSet Trajectory (sigmaAlgebraUpTo t) s) :
    (∫ traj in s, stepLogLikelihoodProcess ν ν_star t traj ∂(environmentMeasure ν_star h_stoch)) ≤ 0 := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance

  -- Represent `s` as a preimage under `truncate`.
  rcases (by
      simpa [sigmaAlgebraUpTo, MeasurableSpace.measurableSet_comap] using hs) with ⟨A, _hA, rfl⟩

  let atom : (Fin t → Step) → Set Trajectory :=
    fun pfx => (truncate t) ⁻¹' ({pfx} : Set (Fin t → Step))
  let atom' : (Fin t → Step) → Set Trajectory :=
    fun pfx => if pfx ∈ A then atom pfx else ∅

  have h_set : (truncate t) ⁻¹' A = ⋃ pfx : (Fin t → Step), atom' pfx := by
    ext traj
    constructor
    · intro hA_traj
      refine Set.mem_iUnion.2 ?_
      refine ⟨truncate t traj, ?_⟩
      have : truncate t traj ∈ A := hA_traj
      simp [atom', atom, this, Set.mem_preimage, Set.mem_singleton_iff]
    · intro hU
      rcases Set.mem_iUnion.1 hU with ⟨pfx, hpfx⟩
      by_cases hp : pfx ∈ A
      · have h_atom : traj ∈ atom pfx := by simpa [atom', hp] using hpfx
        have ht : truncate t traj = pfx := by
          simpa [atom, Set.mem_preimage, Set.mem_singleton_iff] using h_atom
        simpa [ht] using hp
      · simp [atom', hp] at hpfx

  have h_atom_meas : ∀ pfx : (Fin t → Step), MeasurableSet (atom' pfx) := by
    intro pfx
    by_cases hp : pfx ∈ A
    · have h_trunc_meas : Measurable (truncate t) := truncate_measurable t
      have h_single : MeasurableSet ({pfx} : Set (Fin t → Step)) := measurableSet_singleton pfx
      simpa [atom', atom, hp] using h_trunc_meas h_single
    · simp [atom', hp]

  have h_pairwise : Pairwise fun pfx₁ pfx₂ => Disjoint (atom' pfx₁) (atom' pfx₂) := by
    intro pfx₁ pfx₂ hne
    by_cases h1 : pfx₁ ∈ A <;> by_cases h2 : pfx₂ ∈ A
    · refine Set.disjoint_left.2 ?_
      intro traj htraj₁ htraj₂
      have h₁ : truncate t traj = pfx₁ := by
        simpa [atom', atom, h1, Set.mem_preimage, Set.mem_singleton_iff] using htraj₁
      have h₂ : truncate t traj = pfx₂ := by
        simpa [atom', atom, h2, Set.mem_preimage, Set.mem_singleton_iff] using htraj₂
      exact hne (h₁.symm.trans h₂)
    · simp [atom', h1, h2]
    · simp [atom', h1, h2]
    · simp [atom', h1, h2]

  have h_int : ∀ pfx : (Fin t → Step), MeasureTheory.IntegrableOn
      (stepLogLikelihoodProcess ν ν_star t) (atom' pfx) μ := by
    intro _
    exact (stepLogLikelihoodProcess_integrable ν ν_star t h_stoch).integrableOn

  have h_atom_nonpos :
      ∀ pfx : (Fin t → Step),
        (∫ traj in atom' pfx, stepLogLikelihoodProcess ν ν_star t traj ∂μ) ≤ 0 := by
    intro pfx
    by_cases hp : pfx ∈ A
    · have : (∫ traj in atom pfx, stepLogLikelihoodProcess ν ν_star t traj ∂μ) ≤ 0 := by
        simpa [μ] using
          setIntegral_stepLogLikelihoodProcess_atom_le_zero ν ν_star t h_stoch h_support pfx
      simpa [atom', hp, atom] using this
    · simp [atom', hp]

  rw [h_set]
  have h_sum :
      (∫ traj in ⋃ pfx : (Fin t → Step), atom' pfx,
          stepLogLikelihoodProcess ν ν_star t traj ∂μ) =
        ∑ pfx : (Fin t → Step),
          (∫ traj in atom' pfx, stepLogLikelihoodProcess ν ν_star t traj ∂μ) := by
    simpa using
      (MeasureTheory.integral_iUnion_fintype (μ := μ)
        (f := stepLogLikelihoodProcess ν ν_star t) (s := atom')
        h_atom_meas h_pairwise h_int)
  rw [h_sum]
  classical
  simpa using
    (Finset.sum_nonpos (s := (Finset.univ : Finset (Fin t → Step))) fun pfx _ =>
      h_atom_nonpos pfx)

/-- **THE KEY THEOREM**: Log-likelihood ratio is a supermartingale.

    Under the true environment ν*, the process (L_t)_{t≥0} where
    L_t = log(ν(h_t) / ν*(h_t)) is a supermartingale with respect to
    the canonical filtration.

    This means: E_{ν*}[L_{t+1} | F_t] ≤ L_t

    Proof idea:
    E[L_{t+1} | F_t] = E[L_t + stepLL | F_t]
                     = L_t + E[stepLL | F_t]  (L_t is F_t-measurable)
                     ≤ L_t + 0               (by conditional_stepLogLikelihood)
                     = L_t

    where stepLL = stepLogLikelihood ν ν* h_{t} (X_t). -/
theorem logLikelihoodRatio_supermartingale (ν ν_star : Environment)
    (_h_ne : ν ≠ ν_star) (h_stoch : isStochastic ν_star)
    (h_support : SupportCondition ν ν_star) :
    MeasureTheory.Supermartingale
      (fun t => logLikelihoodRatio ν ν_star t)
      trajectoryFiltration
      (environmentMeasure ν_star h_stoch) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance
  -- Prove the supermartingale property via the set integral characterization.
  refine MeasureTheory.supermartingale_of_setIntegral_succ_le (𝒢 := trajectoryFiltration) (μ := μ) ?_ ?_ ?_
  · -- Adapted
    intro t
    apply Measurable.stronglyMeasurable
    simpa [trajectoryFiltration] using logLikelihoodRatio_stronglyMeasurable ν ν_star t
  · -- Integrable
    intro t
    simpa [μ] using logLikelihoodRatio_integrable ν ν_star t h_stoch
  · -- One-step set integral inequality
    intro t s hs
    have hs_sigma : @MeasurableSet Trajectory (sigmaAlgebraUpTo t) s := by
      simpa [trajectoryFiltration, μ] using hs
    have hs_meas : MeasurableSet s := (trajectoryFiltration.le t) s hs
    have h_decomp :
        ∀ᵐ traj ∂μ,
          traj ∈ s →
            logLikelihoodRatio ν ν_star t.succ traj =
              logLikelihoodRatio ν ν_star t traj + stepLogLikelihoodProcess ν ν_star t traj := by
      have h :=
        logLikelihoodRatio_succ_eq_add_stepLogLikelihoodProcess_ae ν ν_star t h_stoch h_support
      filter_upwards [h] with traj htraj
      intro _
      exact htraj
    have h_eq :
        (∫ traj in s, logLikelihoodRatio ν ν_star t.succ traj ∂μ) =
          ∫ traj in s,
            (logLikelihoodRatio ν ν_star t traj + stepLogLikelihoodProcess ν ν_star t traj) ∂μ := by
      exact MeasureTheory.setIntegral_congr_ae hs_meas h_decomp
    have h_add :
        (∫ traj in s,
            (logLikelihoodRatio ν ν_star t traj + stepLogLikelihoodProcess ν ν_star t traj) ∂μ) =
          (∫ traj in s, logLikelihoodRatio ν ν_star t traj ∂μ) +
            (∫ traj in s, stepLogLikelihoodProcess ν ν_star t traj ∂μ) := by
      have h_int_log :
          MeasureTheory.Integrable (logLikelihoodRatio ν ν_star t) (μ.restrict s) :=
        (logLikelihoodRatio_integrable ν ν_star t h_stoch).integrableOn
      have h_int_step :
          MeasureTheory.Integrable (stepLogLikelihoodProcess ν ν_star t) (μ.restrict s) :=
        (stepLogLikelihoodProcess_integrable ν ν_star t h_stoch).integrableOn
      simpa using MeasureTheory.integral_add (μ := μ.restrict s) h_int_log h_int_step
    have h_step_le :
        (∫ traj in s, stepLogLikelihoodProcess ν ν_star t traj ∂μ) ≤ 0 := by
      simpa [μ] using setIntegral_stepLogLikelihoodProcess_le_zero ν ν_star t h_stoch h_support s hs_sigma
    calc
      (∫ traj in s, logLikelihoodRatio ν ν_star t.succ traj ∂μ)
          = ∫ traj in s,
              (logLikelihoodRatio ν ν_star t traj + stepLogLikelihoodProcess ν ν_star t traj) ∂μ := h_eq
      _ = (∫ traj in s, logLikelihoodRatio ν ν_star t traj ∂μ) +
            (∫ traj in s, stepLogLikelihoodProcess ν ν_star t traj ∂μ) := h_add
      _ ≤ (∫ traj in s, logLikelihoodRatio ν ν_star t traj ∂μ) + 0 := by
            exact add_le_add_right h_step_le _
      _ = (∫ traj in s, logLikelihoodRatio ν ν_star t traj ∂μ) := by simp

/-! ## Consequences of the Supermartingale Property

The supermartingale property implies that under the true environment,
the log-likelihood ratio for wrong environments tends to -∞.
-/

/-- **Almost sure convergence** of the log-likelihood ratio under an explicit L¹ bound.

    In full generality (for arbitrary semimeasures), `ν ≠ ν*` does *not* imply
    `logLikelihoodRatio ν ν* t → -∞` a.s.: e.g. mixtures `ν := c • ν* + (1-c) • ν'` can keep a
    nonzero limiting likelihood ratio along `ν*`-typical trajectories.

    What we can prove from Mathlib's martingale convergence theorem is: if the process is
    uniformly L¹-bounded, then it converges a.s. to a limit process. -/
theorem logLikelihoodRatio_ae_tendsto_limitProcess_of_eLpNorm_bdd (ν ν_star : Environment)
    (h_ne : ν ≠ ν_star) (h_stoch : isStochastic ν_star)
    (h_support : SupportCondition ν ν_star)
    {R : NNReal}
    (hbdd :
      ∀ t,
        MeasureTheory.eLpNorm (logLikelihoodRatio ν ν_star t) 1
            (environmentMeasure ν_star h_stoch) ≤ (R : ENNReal)) :
    ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
      Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop
        (nhds
          (-trajectoryFiltration.limitProcess (fun t traj => -logLikelihoodRatio ν ν_star t traj)
            (environmentMeasure ν_star h_stoch) traj)) := by
  classical
  let μ : MeasureTheory.Measure Trajectory := environmentMeasure ν_star h_stoch
  haveI : MeasureTheory.IsProbabilityMeasure μ := environmentMeasure_isProbability ν_star h_stoch
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance

  let f : ℕ → Trajectory → ℝ := fun t traj => -logLikelihoodRatio ν ν_star t traj

  have h_sup :
      MeasureTheory.Supermartingale (fun t => logLikelihoodRatio ν ν_star t) trajectoryFiltration μ :=
    logLikelihoodRatio_supermartingale ν ν_star h_ne h_stoch h_support
  have h_sub : MeasureTheory.Submartingale f trajectoryFiltration μ := by
    simpa [f] using h_sup.neg

  have hbdd' : ∀ t, MeasureTheory.eLpNorm (f t) 1 μ ≤ (R : ENNReal) := by
    intro t
    have hnorm :
        MeasureTheory.eLpNorm (f t) 1 μ =
          MeasureTheory.eLpNorm (logLikelihoodRatio ν ν_star t) 1 μ := by
      dsimp [f]
      exact MeasureTheory.eLpNorm_neg (logLikelihoodRatio ν ν_star t) 1 μ
    calc
      MeasureTheory.eLpNorm (f t) 1 μ
          = MeasureTheory.eLpNorm (logLikelihoodRatio ν ν_star t) 1 μ := hnorm
      _ ≤ (R : ENNReal) := by
          simpa [μ] using hbdd t

  have h_tendsto_neg :
      ∀ᵐ traj ∂μ,
        Filter.Tendsto (fun t => f t traj) Filter.atTop
          (nhds (trajectoryFiltration.limitProcess f μ traj)) :=
    h_sub.ae_tendsto_limitProcess hbdd'

  filter_upwards [h_tendsto_neg] with traj htraj
  -- Convert convergence of `-L_t` to convergence of `L_t`.
  have := Filter.Tendsto.neg htraj
  simpa [f] using this

/-- If `logLikelihoodRatio` tends to `-∞` almost surely (with respect to an arbitrary measure),
then the likelihood ratio tends to `0` (`exp` transfer). -/
theorem likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges' (ν ν_star : Environment)
    (μ : MeasureTheory.Measure Trajectory)
    (h_diverges :
      ∀ᵐ traj ∂μ,
        Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot) :
    ∀ᵐ traj ∂μ,
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal)
        Filter.atTop (nhds 0) := by
  filter_upwards [h_diverges] with traj htraj

  -- Step 0: Extract the key fact from htraj
  have htraj_atBot : Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot := htraj
  rw [Filter.tendsto_atBot] at htraj
  have h_eventually_le : ∀ᶠ t in Filter.atTop, logLikelihoodRatio ν ν_star t traj ≤ -1 := htraj (-1)

  -- Step 1: Eventually, we're not in the "p_star = 0" case
  -- because logLikelihoodRatio → -∞ can't happen if it's stuck at 0
  have h_eventually_pos : ∀ᶠ t in Filter.atTop,
      (historyProbability ν_star (trajectoryToHistory traj t)).toReal > 0 := by
    filter_upwards [h_eventually_le] with t ht
    by_contra h_not_pos
    push_neg at h_not_pos
    -- p_star ≤ 0, but p_star ≥ 0 always, so p_star = 0
    have h_zero : (historyProbability ν_star (trajectoryToHistory traj t)).toReal = 0 :=
      le_antisymm h_not_pos ENNReal.toReal_nonneg
    -- But then logLikelihoodRatio = 0 by definition
    have : logLikelihoodRatio ν ν_star t traj = 0 := by
      simp only [logLikelihoodRatio, h_zero, ite_true]
    -- This contradicts ht which says logLikelihoodRatio ≤ -1
    linarith

  -- Step 2: Eventually, exp(logLikelihoodRatio) = likelihoodRatio.toReal
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      Real.exp (logLikelihoodRatio ν ν_star t traj) =
      (likelihoodRatio ν ν_star t traj).toReal := by
    filter_upwards [h_eventually_pos, h_eventually_le] with t ht ht_le
    simp only [logLikelihoodRatio, likelihoodRatio]
    -- Since p_star > 0, we're in the else branch
    have h_p_star_ne : (historyProbability ν_star (trajectoryToHistory traj t)).toReal ≠ 0 :=
      ne_of_gt ht
    simp only [if_neg h_p_star_ne]
    -- Now we have exp(log(p_ν / p_star))
    -- Need to show this equals (p_ν_ENNReal / p_star_ENNReal).toReal
    rw [ENNReal.toReal_div]
    -- Need to apply exp_log, which requires showing p_ν / p_star > 0
    -- We have p_star > 0, so we just need p_ν > 0
    have h_p_nu_pos : (historyProbability ν (trajectoryToHistory traj t)).toReal > 0 := by
      by_contra h_not_pos
      push_neg at h_not_pos
      -- p_ν ≤ 0, but p_ν ≥ 0 always, so p_ν = 0
      have h_p_nu_zero : (historyProbability ν (trajectoryToHistory traj t)).toReal = 0 :=
        le_antisymm h_not_pos ENNReal.toReal_nonneg
      -- Then p_ν / p_star = 0 / p_star = 0
      have h_div_zero : (historyProbability ν (trajectoryToHistory traj t)).toReal /
                         (historyProbability ν_star (trajectoryToHistory traj t)).toReal = 0 := by
        rw [h_p_nu_zero, zero_div]
      -- So log(0) = 0
      have h_log_zero : Real.log ((historyProbability ν (trajectoryToHistory traj t)).toReal /
                       (historyProbability ν_star (trajectoryToHistory traj t)).toReal) = 0 := by
        rw [h_div_zero, Real.log_zero]
      -- Since p_star ≠ 0, logLikelihoodRatio = log(p_ν / p_star)
      have h_llr_eq : logLikelihoodRatio ν ν_star t traj =
                      Real.log ((historyProbability ν (trajectoryToHistory traj t)).toReal /
                                (historyProbability ν_star (trajectoryToHistory traj t)).toReal) := by
        simp only [logLikelihoodRatio, if_neg h_p_star_ne]
      -- So logLikelihoodRatio = 0
      rw [h_llr_eq, h_log_zero] at ht_le
      -- But ht_le says 0 ≤ -1, contradiction
      linarith
    exact Real.exp_log (div_pos h_p_nu_pos ht)

  -- Step 3: Compose with exp tendsto
  have h_exp_tendsto : Filter.Tendsto (fun t => Real.exp (logLikelihoodRatio ν ν_star t traj))
      Filter.atTop (nhds 0) := by
    have : Filter.Tendsto Real.exp Filter.atBot (nhds 0) := Real.tendsto_exp_atBot
    exact this.comp htraj_atBot

  -- Step 4: Transfer via the eventual equality
  exact Filter.Tendsto.congr' h_eventually_eq h_exp_tendsto

/-- Pointwise `log` transfer: if the likelihood ratio tends to `0` through positive values, then the
log-likelihood ratio tends to `-∞`. This is the converse direction to the `exp` transfer lemma. -/
theorem logLikelihoodRatio_tendsto_atBot_of_likelihoodRatio_toReal_tendsto_zero
    (ν ν_star : Environment) (traj : Trajectory)
    (h_pos : ∀ᶠ t in Filter.atTop, 0 < (likelihoodRatio ν ν_star t traj).toReal)
    (h_tendsto :
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot := by
  -- Upgrade `f → 0` to a `nhdsWithin` statement on `(0, ∞)` so we can apply `log → -∞`.
  have h_tendsto' :
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_tendsto (by
      simpa [Set.mem_Ioi] using h_pos)
  have h_log :
      Filter.Tendsto (fun t => Real.log ((likelihoodRatio ν ν_star t traj).toReal))
        Filter.atTop Filter.atBot :=
    (by
      have hlog0 : Filter.Tendsto Real.log (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot := by
        simpa using Real.tendsto_log_nhdsGT_zero
      exact hlog0.comp h_tendsto')
  -- Since the likelihood ratio is eventually strictly positive, we are eventually not in the
  -- `p_star = 0` branch of the `logLikelihoodRatio` definition.
  have h_star_ne0 :
      ∀ᶠ t in Filter.atTop, (historyProbability ν_star (trajectoryToHistory traj t)).toReal ≠ 0 := by
    filter_upwards [h_pos] with t ht
    have : (historyProbability ν_star (trajectoryToHistory traj t)).toReal ≠ 0 := by
      intro hzero
      -- If `p_star = 0`, then by Lean's `0`-conventions `likelihoodRatio.toReal = 0`, contradicting `ht`.
      have h_lr_zero : (likelihoodRatio ν ν_star t traj).toReal = 0 := by
        simp [likelihoodRatio, hzero]
      have ht' := ht
      simp [h_lr_zero] at ht'
    exact this

  -- Transfer the `log` limit along the eventual definitional equality.
  have h_eventually_eq :
      (fun t => logLikelihoodRatio ν ν_star t traj) =ᶠ[Filter.atTop]
        fun t => Real.log ((likelihoodRatio ν ν_star t traj).toReal) := by
    filter_upwards [h_star_ne0] with t ht
    simp [logLikelihoodRatio, likelihoodRatio, ht, ENNReal.toReal_div]

  exact Filter.Tendsto.congr' h_eventually_eq.symm h_log

/-- If `logLikelihoodRatio ν ν* t traj → -∞`, then eventually the `ν*`-history probability along
that trajectory is strictly positive (so we are not stuck in the `p_star = 0` convention). -/
theorem eventually_historyProbability_toReal_pos_of_logLikelihoodRatio_tendsto_atBot
    (ν ν_star : Environment) (traj : Trajectory)
    (h :
      Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot) :
    ∀ᶠ t in Filter.atTop,
      (historyProbability ν_star (trajectoryToHistory traj t)).toReal > 0 := by
  -- If `historyProbability ν_star ...` were `0`, then `logLikelihoodRatio` would be `0` by definition,
  -- contradicting the eventual bound `≤ -1`.
  rw [Filter.tendsto_atBot] at h
  have h_eventually_le : ∀ᶠ t in Filter.atTop, logLikelihoodRatio ν ν_star t traj ≤ -1 := h (-1)
  filter_upwards [h_eventually_le] with t ht
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero :
      (historyProbability ν_star (trajectoryToHistory traj t)).toReal = 0 :=
    le_antisymm h_not_pos ENNReal.toReal_nonneg
  have h_llr_zero : logLikelihoodRatio ν ν_star t traj = 0 := by
    simp [logLikelihoodRatio, h_zero]
  -- contradiction: `0 ≤ -1`
  have : (0 : ℝ) ≤ -1 := by simpa [h_llr_zero] using ht
  linarith

/-- Corollary: Likelihood ratio converges to 0 for wrong environments.

    If `logLikelihoodRatio` tends to `-∞` almost surely under the true environment measure `ν*`,
    then `ν(h_t)/ν*(h_t)` tends to `0`. -/
theorem likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges (ν ν_star : Environment)
    (h_stoch : isStochastic ν_star)
    (h_diverges :
      ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
        Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot) :
    ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal)
        Filter.atTop (nhds 0) :=
  likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges' ν ν_star
    (environmentMeasure ν_star h_stoch) h_diverges

/-! ## Basic support fact: true prefix probabilities are positive a.s. -/

/-- Under the on-policy trajectory measure of a stochastic environment, the realized finite-prefix
history probability is strictly positive at every time, almost surely.

This eliminates the need to derive “true prefix probability eventually positive” from an
identifiability hypothesis. -/
theorem ae_forall_historyProbability_toReal_pos (μ : Environment) (pi : Agent) (h_stoch : isStochastic μ) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy μ pi h_stoch),
      ∀ t : ℕ, (historyProbability μ (trajectoryToHistory traj t)).toReal > 0 := by
  classical
  let μT : MeasureTheory.Measure Trajectory := environmentMeasureWithPolicy μ pi h_stoch

  -- First show the per-time statement: the bad event `{historyProbability = 0}` has μT-measure 0.
  have h_each : ∀ t : ℕ, μT {traj | historyProbability μ (trajectoryToHistory traj t) = 0} = 0 := by
    intro t
    -- For each prefix `p : Fin t → Step`, its preimage under `truncate t` is the corresponding cylinder.
    let badPrefix : (Fin t → Step) → Set Trajectory :=
      fun p =>
        if historyProbability μ (prefixToHistory t p) = 0
        then truncate t ⁻¹' ({p} : Set (Fin t → Step))
        else ∅

    have h_cover :
        {traj | historyProbability μ (trajectoryToHistory traj t) = 0} ⊆
          ⋃ p : (Fin t → Step), badPrefix p := by
      intro traj htraj
      refine Set.mem_iUnion.2 ?_
      refine ⟨truncate t traj, ?_⟩
      have h_then :
          historyProbability μ (prefixToHistory t (truncate t traj)) = 0 := by
        simpa [prefixToHistory_eq_trajectoryToHistory] using htraj
      have : traj ∈ badPrefix (truncate t traj) := by
        simp [badPrefix, h_then]
      exact this

    have h_null : ∀ p : (Fin t → Step), μT (badPrefix p) = 0 := by
      intro p
      by_cases hp : historyProbability μ (prefixToHistory t p) = 0
      · have h_pre_at :
            truncate t ⁻¹' ({p} : Set (Fin t → Step)) =
              cylinderSetAt t (prefixToHistory t p) := by
          simpa using truncate_preimage_singleton_eq_cylinderSetAt t p
        have hw : (prefixToHistory t p).wellFormed :=
          prefixToHistory_wellFormed t p
        have hc : Even (prefixToHistory t p).length := by
          rw [prefixToHistory_length]
          exact even_two_mul t
        have h_steps : historySteps (prefixToHistory t p) = t :=
          historySteps_prefixToHistory t p
        have h_pre :
            truncate t ⁻¹' ({p} : Set (Fin t → Step)) =
              cylinderSet (prefixToHistory t p) := by
          have h_cyl :
              cylinderSetAt t (prefixToHistory t p) = cylinderSet (prefixToHistory t p) := by
            simpa [h_steps] using (cylinderSet_eq_cylinderSetAt (h := prefixToHistory t p) hw).symm
          simpa [h_cyl] using h_pre_at
        have h_cyl :
            μT (cylinderSet (prefixToHistory t p)) =
              policyProbability pi (prefixToHistory t p) *
                historyProbability μ (prefixToHistory t p) := by
          simpa [μT] using
            (environmentMeasureWithPolicy_cylinderSet_eq μ pi h_stoch (h := prefixToHistory t p) hw hc)
        calc
          μT (badPrefix p) = μT (cylinderSet (prefixToHistory t p)) := by
            simp [badPrefix, hp, h_pre]
          _ = policyProbability pi (prefixToHistory t p) *
                historyProbability μ (prefixToHistory t p) := by
            simpa using h_cyl
          _ = 0 := by simp [hp]
      · simp [badPrefix, hp]

    -- Conclude by bounding the bad set by a countable union of null sets.
    have h_le : μT {traj | historyProbability μ (trajectoryToHistory traj t) = 0} ≤
        μT (⋃ p : (Fin t → Step), badPrefix p) :=
      MeasureTheory.measure_mono h_cover
    have h_union : μT (⋃ p : (Fin t → Step), badPrefix p) ≤
        ∑' p : (Fin t → Step), μT (badPrefix p) :=
      MeasureTheory.measure_iUnion_le (μ := μT) badPrefix
    have h_tsum : (∑' p : (Fin t → Step), μT (badPrefix p)) = 0 := by
      classical
      have h_fun : (fun p : (Fin t → Step) => μT (badPrefix p)) = fun _ => (0 : ℝ≥0∞) := by
        funext p
        exact h_null p
      simp [h_fun]
    exact le_antisymm (le_trans h_le (h_union.trans_eq h_tsum)) (zero_le _)

  -- Upgrade from `historyProbability = 0` being a null event to `toReal > 0` a.s. for all times.
  have h_each_pos : ∀ t : ℕ, ∀ᵐ traj ∂μT,
      (historyProbability μ (trajectoryToHistory traj t)).toReal > 0 := by
    intro t
    have h_ne0 : ∀ᵐ traj ∂μT, historyProbability μ (trajectoryToHistory traj t) ≠ 0 := by
      have : ({traj | historyProbability μ (trajectoryToHistory traj t) ≠ 0} : Set Trajectory) ∈
          MeasureTheory.ae μT := by
        refine (MeasureTheory.mem_ae_iff).2 ?_
        simpa [Set.compl_setOf, not_not] using h_each t
      simpa using (show ∀ᵐ traj ∂μT, historyProbability μ (trajectoryToHistory traj t) ≠ 0 from this)
    filter_upwards [h_ne0] with traj htraj_ne0
    have h_ne_top :
        historyProbability μ (trajectoryToHistory traj t) ≠ ∞ := by
      have hle : historyProbability μ (trajectoryToHistory traj t) ≤ 1 :=
        historyProbability_le_one μ (trajectoryToHistory traj t)
      exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top
    exact ENNReal.toReal_pos htraj_ne0 h_ne_top

  -- Swap `∀ t` and `∀ᵐ traj` (countable intersection over ℕ).
  have h_all : ∀ᵐ traj ∂μT, ∀ t : ℕ,
      (historyProbability μ (trajectoryToHistory traj t)).toReal > 0 :=
    (MeasureTheory.ae_all_iff).2 h_each_pos
  simpa [μT] using h_all

/-! ## Identifiability Hypothesis (packaging)

Leike-style arguments typically assume (or prove under additional structural assumptions) that
every wrong environment `ν` is *identifiable* from the true one `ν*` along `ν*`-typical
trajectories, i.e. the log-likelihood ratio tends to `-∞`.

This file supplies the basic wrapper lemmas that turn such an identifiability statement into the
likelihood-ratio convergence needed for posterior concentration. -/

/-- `Identifiable ν ν*` means: under the true environment measure, the log-likelihood ratio of `ν`
against `ν*` tends to `-∞`. -/
def Identifiable (ν ν_star : Environment) (h_stoch : isStochastic ν_star) : Prop :=
  ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
    Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot

/-- Policy-driven variant: identifiability under the on-policy trajectory measure `ν*^π`. -/
def IdentifiableWithPolicy (ν ν_star : Environment) (pi : Agent) (h_stoch : isStochastic ν_star) : Prop :=
  ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
    Filter.Tendsto (fun t => logLikelihoodRatio ν ν_star t traj) Filter.atTop Filter.atBot

/-! ## Leike-style identifiability via likelihood ratios

Leike often phrases “identifiability” (for Bayesian consistency over a countable model class) as:

`ν(h_t) / ν*(h_t) → 0` almost surely under the true on-policy measure `ν*^π`.

This avoids any `log 0` corner-cases and is exactly the hypothesis used by the posterior
concentration proof (see `PosteriorConcentration.lean`). -/

/-- `LRIdentifiableWithPolicy ν ν* π` means: under the true on-policy measure `ν*^π`, the likelihood
ratio `ν(h_t)/ν*(h_t)` tends to `0`. -/
def LRIdentifiableWithPolicy (ν ν_star : Environment) (pi : Agent) (h_stoch : isStochastic ν_star) : Prop :=
  ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
    Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop (nhds 0)

/-! ## Identifiability via uniform per-step likelihood-ratio shrinkage

This is a strong but simple sufficient condition that matches the spirit of Leike’s “relative
entropy / likelihood ratio” arguments: if the wrong environment is penalized by a fixed constant
factor on each step along `ν*^π`-typical trajectories, then the full likelihood ratio decays
geometrically. -/

/-- If the one-step likelihood ratio is eventually bounded by `r < 1` along `ν*^π`-typical
trajectories, then the full likelihood ratio converges to `0`. -/
theorem likelihoodRatio_converges_to_zero_of_eventually_stepLikelihoodRatio_le
    (ν ν_star : Environment) (pi : Agent) (h_stoch : isStochastic ν_star)
    {r : ℝ≥0∞} (hr : r < 1)
    (h_step :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
        ∀ᶠ t in Filter.atTop, stepLikelihoodRatio ν ν_star t traj ≤ r) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop (nhds 0) := by
  classical
  let μT : MeasureTheory.Measure Trajectory := environmentMeasureWithPolicy ν_star pi h_stoch
  have h_pos :
      ∀ᵐ traj ∂μT, ∀ t : ℕ, (historyProbability ν_star (trajectoryToHistory traj t)).toReal > 0 := by
    simpa [μT] using (ae_forall_historyProbability_toReal_pos (μ := ν_star) (pi := pi) (h_stoch := h_stoch))
  filter_upwards [h_step, h_pos] with traj h_step_traj h_pos_traj
  rcases (Filter.eventually_atTop.1 h_step_traj) with ⟨t0, ht0⟩

  -- The geometric comparison sequence.
  let C : ℝ≥0∞ := likelihoodRatio ν ν_star t0 traj
  have hC_ne_top : C ≠ ∞ := by
    -- `C = ν(h_t0)/ν*(h_t0)` is finite since both numerator and denominator are finite and the
    -- denominator is nonzero (a.s.).
    have hden_toReal_pos :
        (historyProbability ν_star (trajectoryToHistory traj t0)).toReal > 0 :=
      h_pos_traj t0
    have hden_ne0 : historyProbability ν_star (trajectoryToHistory traj t0) ≠ 0 := by
      intro h0
      have : (historyProbability ν_star (trajectoryToHistory traj t0)).toReal = 0 := by simp [h0]
      exact (lt_irrefl 0) (this ▸ hden_toReal_pos)
    have hnum_ne_top : historyProbability ν (trajectoryToHistory traj t0) ≠ ∞ := by
      have hle : historyProbability ν (trajectoryToHistory traj t0) ≤ 1 :=
        historyProbability_le_one ν (trajectoryToHistory traj t0)
      exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top
    simpa [C, likelihoodRatio] using (ENNReal.div_ne_top hnum_ne_top hden_ne0)

  have h_bound : ∀ n : ℕ, likelihoodRatio ν ν_star (t0 + n) traj ≤ C * r ^ n := by
    intro n
    induction n with
    | zero =>
      simp [C]
    | succ n ih =>
      have h_step' : stepLikelihoodRatio ν ν_star (t0 + n) traj ≤ r :=
        ht0 (t0 + n) (Nat.le_add_right t0 n)
      have hrec :
          likelihoodRatio ν ν_star (t0 + n).succ traj =
            likelihoodRatio ν ν_star (t0 + n) traj *
              stepLikelihoodRatio ν ν_star (t0 + n) traj := by
        simpa using likelihoodRatio_succ_eq_mul_stepLikelihoodRatio (ν := ν) (ν_star := ν_star) (t := t0 + n)
          (traj := traj)
      calc
        likelihoodRatio ν ν_star (t0 + n.succ) traj
            = likelihoodRatio ν ν_star (t0 + n).succ traj := by
                simp [Nat.succ_eq_add_one, Nat.add_assoc]
        _ = likelihoodRatio ν ν_star (t0 + n) traj *
              stepLikelihoodRatio ν ν_star (t0 + n) traj := hrec
        _ ≤ (C * r ^ n) * r := by
              -- monotonicity of multiplication in `ℝ≥0∞`
              exact mul_le_mul ih h_step' (by simp) (by simp)
        _ = C * r ^ n.succ := by
              simp [pow_succ, mul_assoc, mul_comm]

  have h_geom : Filter.Tendsto (fun n : ℕ => C * r ^ n) Filter.atTop (nhds 0) := by
    -- `r ^ n → 0` for `r < 1`, then multiply by the finite constant `C`.
    have hpow : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
    have := ENNReal.Tendsto.const_mul (a := C) hpow (Or.inr hC_ne_top)
    simpa using this

  -- Squeeze: `0 ≤ f_n ≤ C*r^n`, hence `f_n → 0`.
  have h_shift :
      Filter.Tendsto (fun n : ℕ => likelihoodRatio ν ν_star (t0 + n) traj) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) _ _)
      h_geom (fun _ => by simp) h_bound
  have h_full :
      Filter.Tendsto (fun t : ℕ => likelihoodRatio ν ν_star t traj) Filter.atTop (nhds 0) := by
    -- Shift-invariance of `atTop`.
    have h_shift' :
        Filter.Tendsto (fun n : ℕ => likelihoodRatio ν ν_star (n + t0) traj) Filter.atTop (nhds 0) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_shift
    exact (Filter.tendsto_add_atTop_iff_nat t0).1 h_shift'
  -- Convert to `toReal`.
  have h_toReal : Filter.Tendsto ENNReal.toReal (nhds (0 : ℝ≥0∞)) (nhds (0 : ℝ)) :=
    ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)
  exact h_toReal.comp h_full

theorem lrIdentifiableWithPolicy_of_eventually_stepLikelihoodRatio_le (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star) {r : ℝ≥0∞} (hr : r < 1)
    (h_step :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
        ∀ᶠ t in Filter.atTop, stepLikelihoodRatio ν ν_star t traj ≤ r) :
    LRIdentifiableWithPolicy ν ν_star pi h_stoch := by
  simpa [LRIdentifiableWithPolicy] using
    (likelihoodRatio_converges_to_zero_of_eventually_stepLikelihoodRatio_le
      (ν := ν) (ν_star := ν_star) (pi := pi) h_stoch hr h_step)

theorem lrIdentifiableWithPolicy_of_identifiableWithPolicy (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star) (h_ident : IdentifiableWithPolicy ν ν_star pi h_stoch) :
    LRIdentifiableWithPolicy ν ν_star pi h_stoch := by
  simpa [LRIdentifiableWithPolicy] using
    (likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges' (ν := ν) (ν_star := ν_star)
      (μ := environmentMeasureWithPolicy ν_star pi h_stoch) h_ident)

/-! ## Easy identifiability via finite refutation (support mismatch)

If the wrong environment assigns probability `0` to some finite prefix that occurs almost surely
under the true on-policy measure, then the likelihood ratio is eventually `0`, hence tends to `0`.

This is a strong but very easy-to-use sufficient condition, capturing the case where `ν` is ruled
out by a finite counterexample on almost every trajectory.
-/

/-- `RefutableWithPolicy ν ν* π` means: under `ν*^π`, almost surely there exists a time `t`
such that `ν` assigns probability `0` to the observed prefix history of length `t`. -/
def RefutableWithPolicy (ν ν_star : Environment) (pi : Agent) (h_stoch : isStochastic ν_star) : Prop :=
  ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
    ∃ t : ℕ, historyProbability ν (trajectoryToHistory traj t) = 0

/-- A finite refutation implies likelihood ratio → 0 under the on-policy true measure. -/
theorem likelihoodRatio_converges_to_zero_of_refutableWithPolicy (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star) (h_ref : RefutableWithPolicy ν ν_star pi h_stoch) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop (nhds 0) := by
  classical
  filter_upwards [h_ref] with traj htraj
  rcases htraj with ⟨t0, ht0⟩

  have h_zero_mono : ∀ t : ℕ, t0 ≤ t → historyProbability ν (trajectoryToHistory traj t) = 0 := by
    intro t ht
    refine Nat.le_induction (m := t0)
      (P := fun t _ => historyProbability ν (trajectoryToHistory traj t) = 0)
      ?_ (fun t ht ih => ?_) t ht
    · simpa using ht0
    · have hw : (trajectoryToHistory traj t).wellFormed := trajectoryToHistory_wellFormed traj t
      have he : Even (trajectoryToHistory traj t).length := trajectoryToHistory_even traj t
      have h_chain :
          historyProbability ν (trajectoryToHistory traj t.succ) =
            historyProbability ν (trajectoryToHistory traj t) *
              ν.prob (trajectoryToHistory traj t ++ [HistElem.act (traj t).action]) (traj t).percept := by
        -- Use the chain rule and the `trajectoryToHistory_succ` decomposition.
        simpa [Nat.succ_eq_add_one, trajectoryToHistory_succ] using
          (historyProbability_append_step ν (trajectoryToHistory traj t) hw he (traj t).action (traj t).percept)
      -- If the prefix probability is 0 at time `t`, it stays 0 at time `t+1`.
      simp [h_chain, ih]

  have h_eventually_zero : ∀ᶠ t in Filter.atTop, (likelihoodRatio ν ν_star t traj).toReal = 0 := by
    refine (Filter.eventually_atTop.mpr ⟨t0, ?_⟩)
    intro t ht
    have h_num : historyProbability ν (trajectoryToHistory traj t) = 0 :=
      h_zero_mono t ht
    simp [likelihoodRatio, h_num]

  -- Conclude via eventual equality to the constant `0`.
  have h_tendsto_const :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have h_eventuallyEq :
      (fun t => (likelihoodRatio ν ν_star t traj).toReal) =ᶠ[Filter.atTop] fun _ => (0 : ℝ) := by
    filter_upwards [h_eventually_zero] with t ht
    simpa using ht
  exact h_tendsto_const.congr' h_eventuallyEq.symm

theorem lrIdentifiableWithPolicy_of_refutableWithPolicy (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star) (h_ref : RefutableWithPolicy ν ν_star pi h_stoch) :
    LRIdentifiableWithPolicy ν ν_star pi h_stoch := by
  simpa [LRIdentifiableWithPolicy] using
    (likelihoodRatio_converges_to_zero_of_refutableWithPolicy (ν := ν) (ν_star := ν_star) (pi := pi)
      h_stoch h_ref)

/-- A sufficient condition for `IdentifiableWithPolicy`: likelihood ratio tends to `0` through
positive values. This packages `logLikelihoodRatio_tendsto_atBot_of_likelihoodRatio_toReal_tendsto_zero`. -/
theorem identifiableWithPolicy_of_likelihoodRatio_toReal_tendsto_zero (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star)
    (h_pos : ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
      ∀ᶠ t in Filter.atTop, 0 < (likelihoodRatio ν ν_star t traj).toReal)
    (h_tendsto :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
        Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal) Filter.atTop (nhds 0)) :
    IdentifiableWithPolicy ν ν_star pi h_stoch := by
  filter_upwards [h_pos, h_tendsto] with traj hpos htend
  exact logLikelihoodRatio_tendsto_atBot_of_likelihoodRatio_toReal_tendsto_zero
    (ν := ν) (ν_star := ν_star) traj hpos htend

/-- Identifiability implies likelihood ratio → 0 (the `exp` transfer lemma). -/
theorem likelihoodRatio_converges_to_zero_of_identifiable (ν ν_star : Environment)
    (h_stoch : isStochastic ν_star) (h_ident : Identifiable ν ν_star h_stoch) :
    ∀ᵐ traj ∂(environmentMeasure ν_star h_stoch),
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal)
        Filter.atTop (nhds 0) :=
  likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges ν ν_star h_stoch h_ident

/-- Policy-driven variant of `likelihoodRatio_converges_to_zero_of_identifiable`. -/
theorem likelihoodRatio_converges_to_zero_of_identifiableWithPolicy (ν ν_star : Environment) (pi : Agent)
    (h_stoch : isStochastic ν_star) (h_ident : IdentifiableWithPolicy ν ν_star pi h_stoch) :
    ∀ᵐ traj ∂(environmentMeasureWithPolicy ν_star pi h_stoch),
      Filter.Tendsto (fun t => (likelihoodRatio ν ν_star t traj).toReal)
        Filter.atTop (nhds 0) :=
  likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges' ν ν_star
    (environmentMeasureWithPolicy ν_star pi h_stoch) h_ident

/-! ## Summary of Phase 2

We have established the core martingale theory:

1. `likelihoodRatio` and `logLikelihoodRatio` - The key processes
2. `logLikelihoodRatio_supermartingale` - The supermartingale property (KEY THEOREM)
3. `logLikelihoodRatio_ae_tendsto_limitProcess_of_eLpNorm_bdd` - A.s. convergence under an explicit
   L¹-boundedness hypothesis
4. `likelihoodRatio_converges_to_zero_of_logLikelihoodRatio_diverges` - `exp` transfer: `L_t → -∞`
   implies likelihood ratio → 0

This file has **0 sorries**. The remaining work for full Bayesian consistency is to supply the
missing hypothesis that yields `ν(h_t)/ν*(h_t) → 0` for wrong environments (e.g. finite refutation,
singularity, KL-divergence conditions) and then wire that into `PosteriorConcentration.lean`.
-/

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
