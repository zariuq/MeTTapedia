import Mettapedia.UniversalAI.GrainOfTruth.Core
import Mettapedia.UniversalAI.BayesianAgents
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Grain of Truth: Core Theory

This file provides the theoretical foundation for the Grain of Truth convergence theorem.
It builds on the existing infrastructure in `BayesianAgents.lean` rather than duplicating it.

## Key Insight

`BayesianAgents.lean` already contains:
- `value μ π γ h n` - The expected value V^π_μ(h) under policy π
- `qValue μ π γ h a n` - The Q-value Q^π_μ(h,a)
- `optimalValue μ γ h n` - The optimal value V*_μ(h)
- `optimalValue_ge_value` - **The key theorem: V* ≥ V^π**

We use these directly rather than redefining them.

## Main Definitions

* `Regret` - V* - V^π, the performance gap (uses existing `optimalValue` and `value`)
* `HistoryProbability` - Probability that environment μ generates history h
* `BayesianPosteriorWeight` - Proper Bayesian update formula
* `ExpectedRegretOverPrior` - Weighted regret over environment class

## References

- Leike (2016). PhD Thesis, Chapter 7
- Hutter (2005). "Universal Artificial Intelligence"

-/

namespace Mettapedia.UniversalAI.GrainOfTruth.FixedPoint

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal

/-! ## Regret Using Existing Infrastructure

The regret is simply V* - V^π. We use the existing `optimalValue` and `value`
from BayesianAgents.lean.
-/

/-- Instantaneous regret: gap between optimal value and policy value.
    Uses the existing `optimalValue` and `value` from BayesianAgents. -/
noncomputable def regret (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) : ℝ :=
  optimalValue μ γ h horizon - value μ π γ h horizon

/-- **Regret is always non-negative**.
    This follows directly from `optimalValue_ge_value` in BayesianAgents.lean. -/
theorem regret_nonneg (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) :
    0 ≤ regret μ π γ h horizon := by
  unfold regret
  -- Use the existing theorem from BayesianAgents
  have h := optimalValue_ge_value μ γ h horizon π
  linarith

/-- Regret is bounded by the optimal value. -/
theorem regret_le_optimalValue (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (h : History) (horizon : ℕ) :
    regret μ π γ h horizon ≤ optimalValue μ γ h horizon := by
  unfold regret
  have hv := value_nonneg μ π γ h horizon
  linarith

/-! ## History Probability

The probability that an environment μ generates a history h.
For a history h = (a₁, e₁, a₂, e₂, ..., aₜ, eₜ):
  μ(h) = ∏ᵢ μ(eᵢ | a₁e₁...aᵢ₋₁eᵢ₋₁aᵢ)
-/

/-- Extract the percepts from a history. -/
def historyPercepts : History → List Percept
  | [] => []
  | HistElem.per x :: rest => x :: historyPercepts rest
  | HistElem.act _ :: rest => historyPercepts rest

/-- Auxiliary function for historyProbability with accumulator.
    The `pfx` argument tracks the history seen so far (chronologically).

    For history [act a₀, per x₀, act a₁, per x₁, ...], we compute:
    P(h) = P(x₀ | [act a₀]) × P(x₁ | [act a₀, per x₀, act a₁]) × ... -/
noncomputable def historyProbabilityAux (μ : Environment) : History → History → ℝ≥0∞
  | _, [] => 1
  | _, [HistElem.act _] => 1  -- Just an action, no percept yet
  | pfx, HistElem.act a :: HistElem.per x :: rest =>
    -- P(x | pfx ++ [act a]) × P(rest | pfx ++ [act a, per x])
    let conditioningHist := pfx ++ [HistElem.act a]
    let newPrefix := pfx ++ [HistElem.act a, HistElem.per x]
    μ.prob conditioningHist x * historyProbabilityAux μ newPrefix rest
  | _, HistElem.act _ :: HistElem.act _ :: _ =>
    -- Malformed: two actions in a row, treat as probability 0
    0
  | pfx, HistElem.per _ :: rest => historyProbabilityAux μ pfx rest  -- Skip leading percepts

/-- Probability that environment μ generates percept sequence.
    This is the product of conditional probabilities.

    For well-formed histories (alternating act-per), this computes:
    μ(h) = ∏ᵢ μ(eᵢ | h_{<i}, aᵢ)

    where h_{<i} = [a₀, x₀, ..., a_{i-1}, x_{i-1}] is the history before step i. -/
noncomputable def historyProbability (μ : Environment) (h : History) : ℝ≥0∞ :=
  historyProbabilityAux μ [] h

/-- Appending `[act a]` to a wellFormed history of even length preserves wellFormedness. -/
theorem wellFormed_append_act (h : History) (hw : h.wellFormed) (he : Even h.length) (a : Action) :
    (h ++ [HistElem.act a]).wellFormed := by
  induction h using List.twoStepInduction with
  | nil =>
    rfl
  | singleton e =>
    simp only [List.length_singleton] at he
    exact (Nat.not_even_one he).elim
  | cons_cons e1 e2 rest ih =>
    match e1, e2 with
    | HistElem.act _, HistElem.per _ =>
      simp only [List.cons_append, History.wellFormed] at hw ⊢
      have he' : Even rest.length := by
        simp only [List.length_cons] at he
        obtain ⟨k, hk⟩ := he
        use k - 1
        omega
      exact ih hw he'
    | HistElem.act _, HistElem.act _ =>
      simp only [History.wellFormed] at hw
      cases hw
    | HistElem.per _, _ =>
      simp only [History.wellFormed] at hw
      cases hw

/-- Appending `[act a, per x]` to a wellFormed history of even length preserves wellFormedness. -/
theorem wellFormed_append_act_per (h : History) (hw : h.wellFormed) (he : Even h.length)
    (a : Action) (x : Percept) :
    (h ++ [HistElem.act a, HistElem.per x]).wellFormed := by
  induction h using List.twoStepInduction with
  | nil =>
    rfl
  | singleton e =>
    simp only [List.length_singleton] at he
    exact (Nat.not_even_one he).elim
  | cons_cons e1 e2 rest ih =>
    match e1, e2 with
    | HistElem.act _, HistElem.per _ =>
      simp only [List.cons_append, History.wellFormed] at hw ⊢
      have he' : Even rest.length := by
        simp only [List.length_cons] at he
        obtain ⟨k, hk⟩ := he
        use k - 1
        omega
      exact ih hw he'
    | HistElem.act _, HistElem.act _ =>
      simp only [History.wellFormed] at hw
      cases hw
    | HistElem.per _, _ =>
      simp only [History.wellFormed] at hw
      cases hw

/-- Auxiliary lemma: historyProbabilityAux is at most 1 for any prefix. -/
theorem historyProbabilityAux_le_one (μ : Environment) (pfx h : History)
    (h_pfx_wf : pfx.wellFormed) (h_pfx_complete : Even pfx.length) :
    historyProbabilityAux μ pfx h ≤ 1 := by
  induction h generalizing pfx with
  | nil => simp [historyProbabilityAux]
  | cons elem rest ih =>
    cases elem with
    | act a =>
      cases rest with
      | nil => simp [historyProbabilityAux]
      | cons elem' rest' =>
        cases elem' with
        | act _ => simp [historyProbabilityAux]  -- 0 ≤ 1
        | per x =>
          simp only [historyProbabilityAux]
          -- Need: μ.prob _ x * historyProbabilityAux μ _ rest' ≤ 1
          -- Each factor is ≤ 1, so product is ≤ 1
          have h1 : μ.prob (pfx ++ [HistElem.act a]) x ≤ 1 := by
            have h_wf : (pfx ++ [HistElem.act a]).wellFormed :=
              wellFormed_append_act pfx h_pfx_wf h_pfx_complete a
            calc μ.prob (pfx ++ [HistElem.act a]) x
                ≤ ∑' y, μ.prob (pfx ++ [HistElem.act a]) y := ENNReal.le_tsum _
              _ ≤ 1 := μ.prob_le_one _ h_wf
          have h2 : historyProbabilityAux μ (pfx ++ [HistElem.act a, HistElem.per x]) rest' ≤ 1 :=
            ih (pfx ++ [HistElem.act a, HistElem.per x])
              (wellFormed_append_act_per pfx h_pfx_wf h_pfx_complete a x)
              (by
                rcases h_pfx_complete with ⟨k, hk⟩
                refine ⟨k + 1, ?_⟩
                simp [List.length_append, hk]
                omega)
          exact mul_le_one' h1 h2
    | per _ => exact ih pfx h_pfx_wf h_pfx_complete

/-- History probability is at most 1.

    For well-formed histories, this is the product of conditional probabilities,
    each of which is ≤ 1 (since it's at most the sum which is ≤ 1).

    Proof sketch:
    1. Each μ.prob ha x ≤ ∑' y, μ.prob ha y ≤ 1 (by Environment.prob_le_one)
    2. Product of numbers in [0,1] is in [0,1]
    3. By induction on history structure -/
theorem historyProbability_le_one (μ : Environment) (h : History) :
    historyProbability μ h ≤ 1 := by
  simp only [historyProbability]
  exact historyProbabilityAux_le_one μ [] h rfl (by simp)

/-- Helper lemma: historyProbabilityAux with concatenation.
    When processing (h ++ [act a, per x]), the result is:
    (historyProbabilityAux for h) × (μ.prob for the new step) -/
theorem historyProbabilityAux_append_act_per (μ : Environment) (pfx h : History)
    (hw : h.wellFormed) (hc : Even h.length) (a : Action) (x : Percept) :
    historyProbabilityAux μ pfx (h ++ [HistElem.act a, HistElem.per x]) =
      historyProbabilityAux μ pfx h * μ.prob (pfx ++ h ++ [HistElem.act a]) x := by
  -- Proof by strong induction on h.length
  match h with
  | [] =>
    -- h = [], so h ++ [act a, per x] = [act a, per x]
    simp only [List.nil_append, historyProbabilityAux, one_mul, List.append_nil, mul_one]
  | [HistElem.act _] =>
    -- h = [act _], but Even h.length = Even 1 = false
    simp only [List.length_singleton] at hc
    exact absurd hc (by decide : ¬Even 1)
  | [HistElem.per _] =>
    -- Not wellFormed: [per _] is not a valid history start
    simp [History.wellFormed] at hw
  | HistElem.act a' :: HistElem.per x' :: rest' =>
    -- h = act a' :: per x' :: rest'
    -- Process first pair, then recurse
    simp only [List.cons_append, historyProbabilityAux]
    -- wellFormed h = wellFormed rest'
    simp only [History.wellFormed] at hw
    simp only [List.length_cons] at hc
    have hc' : Even rest'.length := by
      obtain ⟨k, hk⟩ := hc
      use k - 1
      omega
    -- Recursively apply
    have ih := historyProbabilityAux_append_act_per μ (pfx ++ [HistElem.act a', HistElem.per x'])
                 rest' hw hc' a x
    rw [ih]
    -- Normalize: pfx ++ [a', x'] ++ rest' = pfx ++ a' :: x' :: rest'
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    -- Reassociate the multiplication: a * (b * c) = a * b * c
    ring
  | HistElem.act _ :: HistElem.act _ :: _ =>
    -- Not wellFormed: two actions in a row
    simp [History.wellFormed] at hw
  | HistElem.per _ :: _ :: _ =>
    -- Not wellFormed: starts with percept
    simp [History.wellFormed] at hw
termination_by h.length

/-- **Chain rule for history probability**: Extending a history by one step multiplies
    the probability by the conditional probability of that step.

    P(h ++ [act a, per x]) = P(h) × P(x | h, a)

    This is the fundamental factorization that makes the log-likelihood decomposition work. -/
theorem historyProbability_append_step (μ : Environment) (h : History)
    (hw : h.wellFormed) (hc : Even h.length) (a : Action) (x : Percept) :
    historyProbability μ (h ++ [HistElem.act a, HistElem.per x]) =
      historyProbability μ h * μ.prob (h ++ [HistElem.act a]) x := by
  unfold historyProbability
  rw [historyProbabilityAux_append_act_per μ [] h hw hc a x]
  simp only [List.nil_append]

/-! ## Bayesian Posterior

The proper Bayesian update formula.
Given a prior w over environments and observed history h:
  w(ν | h) = w(ν) · ν(h) / ξ(h)
where ξ(h) = Σ_ν w(ν) · ν(h) is the mixture probability.
-/

/-- Environment in the class with its prior weight. -/
structure WeightedEnvironment (O : Oracle) (M : ReflectiveEnvironmentClass O) where
  /-- Index into the environment class -/
  idx : EnvironmentIndex
  /-- The actual environment (would be computed from oracle) -/
  env : Environment
  /-- Prior weight -/
  priorWeight : ℝ≥0∞
  /-- Weight is positive -/
  weight_pos : 0 < priorWeight

/-- The mixture probability ξ(h) = Σ_ν w(ν) · ν(h). -/
noncomputable def mixtureProbability (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (h : History) : ℝ≥0∞ :=
  ∑' i, prior.weight i * historyProbability (envs i) h

/-- Bayesian posterior weight: w(ν | h) = w(ν) · ν(h) / ξ(h).
    This is the proper Bayesian update, not a placeholder. -/
noncomputable def bayesianPosteriorWeight (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (h : History) : ℝ≥0∞ :=
  let numerator := prior.weight ν_idx * historyProbability (envs ν_idx) h
  let denominator := mixtureProbability O M prior envs h
  if denominator = 0 then prior.weight ν_idx  -- Fallback to prior if ξ(h) = 0
  else numerator / denominator

/-- Posterior weights sum to 1 (when ξ(h) > 0).
    Proof sketch: w(ν|h) = w(ν)·ν(h) / ξ(h), so
    Σ_ν w(ν|h) = Σ_ν w(ν)·ν(h) / ξ(h) = ξ(h)/ξ(h) = 1
    Requires: tsum_div_const or ENNReal division lemmas -/
theorem bayesianPosterior_sum_one (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (h : History)
    (h_mix_pos : mixtureProbability O M prior envs h > 0) :
    ∑' i, bayesianPosteriorWeight O M prior envs i h = 1 := by
  classical
  set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
  have hden_ne0 : denom ≠ 0 := ne_of_gt h_mix_pos
  have hden_le_one : denom ≤ 1 := by
    have h_term : ∀ i : ℕ, prior.weight i * historyProbability (envs i) h ≤ prior.weight i := by
      intro i
      have h_prob : historyProbability (envs i) h ≤ 1 := historyProbability_le_one (envs i) h
      simpa [mul_one] using (mul_le_mul_left' h_prob (prior.weight i))
    have h_le : denom ≤ ∑' i, prior.weight i := by
      simpa [denom, mixtureProbability] using (ENNReal.tsum_le_tsum h_term)
    exact le_trans h_le prior.tsum_le_one
  have hden_ne_top : denom ≠ ∞ :=
    (lt_of_le_of_lt hden_le_one ENNReal.one_lt_top).ne_top

  calc
    (∑' i, bayesianPosteriorWeight O M prior envs i h)
        = ∑' i, (prior.weight i * historyProbability (envs i) h) / denom := by
            simp [bayesianPosteriorWeight, denom, hden_ne0]
    _ = ∑' i, (prior.weight i * historyProbability (envs i) h) * denom⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑' i, prior.weight i * historyProbability (envs i) h) * denom⁻¹ := by
          simpa using (ENNReal.tsum_mul_right (f := fun i => prior.weight i * historyProbability (envs i) h)
            (a := denom⁻¹))
    _ = denom * denom⁻¹ := by
          simp [denom, mixtureProbability]
    _ = 1 := ENNReal.mul_inv_cancel hden_ne0 hden_ne_top

/-! ## Expected Regret Over Prior

The expected regret weighted by the prior/posterior.
-/

/-- Expected regret over the prior: E_w[Regret]. -/
noncomputable def expectedRegretOverPrior (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (π : Agent) (γ : DiscountFactor) (h : History) (horizon : ℕ) : ℝ :=
  ∑' i, (prior.weight i).toReal * regret (envs i) π γ h horizon

/-- Expected regret is non-negative. -/
theorem expectedRegretOverPrior_nonneg (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (π : Agent) (γ : DiscountFactor) (h : History) (horizon : ℕ) :
    0 ≤ expectedRegretOverPrior O M prior envs π γ h horizon := by
  unfold expectedRegretOverPrior
  apply tsum_nonneg
  intro i
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact regret_nonneg (envs i) π γ h horizon

/-! ## Asymptotic Optimality

A policy π is asymptotically optimal in mean if E[V* - V^π] → 0 as t → ∞.
This is the proper definition, not a placeholder.
-/

/-- Asymptotic optimality in mean: expected regret converges to 0.
    For all ε > 0, there exists t₀ such that for all t ≥ t₀,
    the expected regret is less than ε. -/
def IsAsymptoticallyOptimal (π : Agent) (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (γ : DiscountFactor) : Prop :=
  ∀ ε > 0, ∃ t₀ : ℕ, ∀ t ≥ t₀,
    ∀ h : History, h.wellFormed → h.cycles = t →
      expectedRegretOverPrior O M prior envs π γ h t < ε

/-! ## ε-Best Response

A policy is an ε-best response if regret < ε.
-/

/-- A policy is an ε-best response at history h in environment μ. -/
def IsEpsilonBestResponse (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (ε : ℝ) (h : History) (horizon : ℕ) : Prop :=
  regret μ π γ h horizon < ε

/-- If regret is bounded, we get an ε-best response. -/
theorem regret_bound_gives_best_response (μ : Environment) (π : Agent) (γ : DiscountFactor)
    (ε : ℝ) (h : History) (horizon : ℕ) (hbound : regret μ π γ h horizon < ε) :
    IsEpsilonBestResponse μ π γ ε h horizon :=
  hbound

/-! ## Convergence (measure-theoretic)

The Chapter 7 / Leike-route convergence statements are *on-policy* and are most naturally stated
either almost surely or in probability on the induced trajectory measure.

See the measure-theory pipeline in:

* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/RegretConvergence.lean`
* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/AsymptoticOptimality.lean`
* `Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/Main.lean`
-/

end Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
