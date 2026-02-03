import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# On-Policy Cylinder Factorization

This file records the simple but crucial factorization lemma for the on-policy trajectory measure
`environmentMeasureWithPolicy`:

`μ^π(cyl(h)) = π(h) * μ(h)`,

where `μ(h)` is the usual history probability from `FixedPoint.lean`, and `π(h)` is the product of
the agent's action probabilities along `h`.

It also gives the corresponding factorization for the on-policy Bayes mixture measure `ξ^π`.

These lemmas are the main algebraic input for the “posterior is a martingale under ξ^π” proof.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization

open MeasureTheory ProbabilityTheory
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.MixtureMeasure
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal MeasureTheory

/-! ## Action-Probability Along a History -/

/-- Auxiliary: product of the agent's action probabilities along the *remaining* history `h`,
starting from the already-realized prefix `pfx`.

For well-formed, complete histories this computes:
`π(pfx, a₀) * π(pfx ++ a₀x₀, a₁) * ...`. -/
noncomputable def policyProbabilityAux (π : Agent) : History → History → ℝ≥0∞
  | _, [] => 1
  | _, [HistElem.act _] => 1
  | pfx, HistElem.act a :: HistElem.per x :: rest =>
      π.policy pfx a * policyProbabilityAux π (pfx ++ [HistElem.act a, HistElem.per x]) rest
  | _, HistElem.act _ :: HistElem.act _ :: _ => 0
  | pfx, HistElem.per _ :: rest => policyProbabilityAux π pfx rest

@[simp] theorem policyProbabilityAux_nil (π : Agent) (pfx : History) :
    policyProbabilityAux π pfx [] = 1 := rfl

@[simp] theorem policyProbabilityAux_singleton_act (π : Agent) (pfx : History) (a : Action) :
    policyProbabilityAux π pfx [HistElem.act a] = 1 := rfl

@[simp] theorem policyProbabilityAux_cons_cons (π : Agent) (pfx : History)
    (a : Action) (x : Percept) (rest : History) :
    policyProbabilityAux π pfx (HistElem.act a :: HistElem.per x :: rest) =
      π.policy pfx a * policyProbabilityAux π (pfx ++ [HistElem.act a, HistElem.per x]) rest := by
  simp [policyProbabilityAux]

/-- Product of action probabilities along a history (starting from the empty prefix). -/
noncomputable def policyProbability (π : Agent) (h : History) : ℝ≥0∞ :=
  policyProbabilityAux π [] h

/-! ## Cylinder Factorization for `μ^π` -/

/-- Chain rule for cylinder measures under a policy-driven trajectory measure. -/
theorem cylinderSet_append_measureWithPolicy (μ : Environment) (π : Agent) (h_stoch : isStochastic μ)
    (pfx h : History) (h_pfx_wf : pfx.wellFormed) (h_wf : h.wellFormed)
    (h_pfx_complete : Even pfx.length) (h_complete : Even h.length) :
    environmentMeasureWithPolicy μ π h_stoch (cylinderSet (pfx ++ h)) =
      environmentMeasureWithPolicy μ π h_stoch (cylinderSet pfx) *
        policyProbabilityAux π pfx h * historyProbabilityAux μ pfx h := by
  -- Strong induction on `historySteps h`, following `HistoryFiltration.cylinderSet_append_measure`.
  generalize hn : historySteps h = n
  induction n using Nat.strong_induction_on generalizing pfx h with
  | _ n ih =>
    cases h with
    | nil =>
      simp only [historySteps, List.length_nil, Nat.zero_div] at hn
      subst hn
      simp [policyProbabilityAux, historyProbabilityAux]
    | cons elem rest =>
      cases elem with
      | act a =>
        cases rest with
        | nil =>
          simp only [List.length_singleton] at h_complete
          exact absurd h_complete (by decide : ¬Even 1)
        | cons elem' rest' =>
          cases elem' with
          | act _ =>
            exact absurd h_wf (by simp [History.wellFormed])
          | per x =>
            have h_wf_rest' : History.wellFormed rest' := h_wf
            have h_complete_rest' : Even rest'.length := by
              -- `Even (2 + rest'.length)` implies `Even rest'.length`.
              simp only [List.length_cons] at h_complete
              have heq : rest'.length + 1 + 1 = rest'.length + 2 := by ring
              rw [heq, Nat.even_add] at h_complete
              exact h_complete.mpr (by decide : Even 2)

            have hn_decomp : n = 1 + historySteps rest' := by
              rw [← hn, historySteps_cons_cons]
            have h_steps_lt : historySteps rest' < n := by
              rw [hn_decomp]; omega

            have h_pfx'_wf : (pfx ++ [HistElem.act a, HistElem.per x]).wellFormed :=
              wellFormed_append_pair pfx a x h_pfx_wf h_pfx_complete
            have h_pfx'_complete : Even (pfx ++ [HistElem.act a, HistElem.per x]).length := by
              rcases h_pfx_complete with ⟨k, hk⟩
              refine ⟨k + 1, ?_⟩
              simp [List.length_append, hk]
              omega

            have h_append_assoc :
                pfx ++ (HistElem.act a :: HistElem.per x :: rest') =
                  (pfx ++ [HistElem.act a, HistElem.per x]) ++ rest' := by
              simp [List.append_assoc]
            rw [h_append_assoc]

            have ih_rest' :=
              ih (historySteps rest') h_steps_lt
                (pfx ++ [HistElem.act a, HistElem.per x]) rest'
                h_pfx'_wf h_wf_rest' h_pfx'_complete h_complete_rest' rfl
            rw [ih_rest']

            -- One-step factorization for the prefix extension.
            rw [cylinderSet_append_single_stepWithPolicy μ π h_stoch pfx a x h_pfx_wf h_pfx_complete]

            -- Unfold the auxiliary products.
            rw [policyProbabilityAux_cons_cons, historyProbabilityAux_cons_cons]
            -- Rearrange products.
            ring
      | per _ =>
        exact absurd h_wf (by simp [History.wellFormed])

/-- Cylinder probability under `μ^π` factors as action-probability × history-probability. -/
theorem environmentMeasureWithPolicy_cylinderSet_eq (μ : Environment) (π : Agent) (h_stoch : isStochastic μ)
    (h : History) (h_wf : h.wellFormed) (h_complete : Even h.length) :
    environmentMeasureWithPolicy μ π h_stoch (cylinderSet h) =
      policyProbability π h * historyProbability μ h := by
  have h_chain :=
    cylinderSet_append_measureWithPolicy (μ := μ) (π := π) (h_stoch := h_stoch)
      (pfx := []) (h := h) (h_pfx_wf := by simp [History.wellFormed])
      (h_wf := h_wf) (h_pfx_complete := by simp) (h_complete := h_complete)
  -- Simplify the `pfx := []` specialization.
  simpa [policyProbability, cylinderSet_empty, environmentMeasureWithPolicy_univ_eq_one,
    historyProbability, policyProbabilityAux] using h_chain

/-! ## Cylinder Factorization for `ξ^π` -/

/-- Cylinder probability under the on-policy Bayes mixture `ξ^π` factors as
`π(h) * ξ(h)`, where `ξ(h)` is the discrete mixture probability from `FixedPoint.lean`. -/
theorem mixtureMeasureWithPolicy_cylinderSet_eq (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i))
    (h : History) (h_wf : h.wellFormed) (h_complete : Even h.length) :
    mixtureMeasureWithPolicy O M prior envs π h_stoch (cylinderSet h) =
      policyProbability π h * mixtureProbability O M prior envs h := by
  classical
  -- Expand the mixture measure as a countable sum of scaled component measures.
  simp [mixtureMeasureWithPolicy, MeasureTheory.Measure.sum_apply_of_countable,
    MeasureTheory.Measure.smul_apply, smul_eq_mul]
  -- Rewrite each component cylinder mass as `π(h) * ν(h)`.
  have hcomp :
      ∀ i : EnvironmentIndex,
        environmentMeasureWithPolicy (envs i) π (h_stoch i) (cylinderSet h) =
          policyProbability π h * historyProbability (envs i) h := by
    intro i
    simpa using
      (environmentMeasureWithPolicy_cylinderSet_eq (μ := envs i) (π := π) (h_stoch := h_stoch i)
        (h := h) (h_wf := h_wf) (h_complete := h_complete))
  -- Factor out the common `policyProbability π h`.
  calc
    (∑' i : EnvironmentIndex,
          prior.weight i * environmentMeasureWithPolicy (envs i) π (h_stoch i) (cylinderSet h)) =
        ∑' i : EnvironmentIndex, policyProbability π h * (prior.weight i * historyProbability (envs i) h) := by
          refine tsum_congr fun i => ?_
          simp [hcomp i, mul_assoc, mul_left_comm, mul_comm]
    _ = policyProbability π h * ∑' i : EnvironmentIndex, prior.weight i * historyProbability (envs i) h := by
          simpa using (ENNReal.tsum_mul_left (f := fun i : EnvironmentIndex =>
            prior.weight i * historyProbability (envs i) h) (a := policyProbability π h))
    _ = policyProbability π h * mixtureProbability O M prior envs h := by
          simp [mixtureProbability]

/-! ## Posterior Weight × Cylinder Mass -/

/-- On a cylinder event, the posterior weight cancels the mixture probability, leaving the
corresponding component mass. This is the key algebraic step behind the posterior martingale. -/
theorem bayesianPosteriorWeight_mul_mixtureMeasureWithPolicy_cylinderSet (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment) (π : Agent)
    (h_stoch : ∀ i : EnvironmentIndex, isStochastic (envs i)) (ν_idx : EnvironmentIndex)
    (h : History) (h_wf : h.wellFormed) (h_complete : Even h.length) :
    bayesianPosteriorWeight O M prior envs ν_idx h *
        mixtureMeasureWithPolicy O M prior envs π h_stoch (cylinderSet h) =
      prior.weight ν_idx *
        environmentMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx) (cylinderSet h) := by
  classical
  set denom : ℝ≥0∞ := mixtureProbability O M prior envs h
  by_cases hden : denom = 0
  · -- If the mixture probability is 0, then the cylinder has 0 mixture mass, and also the
    -- ν-component mass in the mixture is 0.
    have hterm0 : prior.weight ν_idx * historyProbability (envs ν_idx) h = 0 := by
      have hle : prior.weight ν_idx * historyProbability (envs ν_idx) h ≤ denom := by
        simpa [denom, mixtureProbability] using ENNReal.le_tsum ν_idx
      exact le_antisymm (le_trans hle (by simp [hden])) (zero_le _)
    have hmix0 : mixtureMeasureWithPolicy O M prior envs π h_stoch (cylinderSet h) = 0 := by
      simp [mixtureMeasureWithPolicy_cylinderSet_eq (O := O) (M := M) (prior := prior) (envs := envs)
        (π := π) (h_stoch := h_stoch) (h := h) (h_wf := h_wf) (h_complete := h_complete), denom, hden]
    have hcomp0 :
        environmentMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx) (cylinderSet h) = 0 := by
      -- The component cylinder mass is `π(h) * ν(h)`, and `prior.weight ν_idx * ν(h) = 0`.
      have : historyProbability (envs ν_idx) h = 0 := by
        -- From `prior.weight ν_idx * historyProbability ... = 0`.
        exact (mul_eq_zero.mp hterm0).resolve_left (prior.positive ν_idx).ne'
      simp [environmentMeasureWithPolicy_cylinderSet_eq (μ := envs ν_idx) (π := π) (h_stoch := h_stoch ν_idx)
        (h := h) (h_wf := h_wf) (h_complete := h_complete), this]
    simp [bayesianPosteriorWeight, denom, hden, hmix0, hcomp0]
  · have hden_pos : denom ≠ 0 := hden
    -- Use the cylinder factorization of the mixture and component measures.
    have hmix :
        mixtureMeasureWithPolicy O M prior envs π h_stoch (cylinderSet h) =
          policyProbability π h * denom := by
      simpa [denom] using
        (mixtureMeasureWithPolicy_cylinderSet_eq (O := O) (M := M) (prior := prior) (envs := envs) (π := π)
          (h_stoch := h_stoch) (h := h) (h_wf := h_wf) (h_complete := h_complete))
    have hcomp :
        environmentMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx) (cylinderSet h) =
          policyProbability π h * historyProbability (envs ν_idx) h := by
      simpa using
        (environmentMeasureWithPolicy_cylinderSet_eq (μ := envs ν_idx) (π := π) (h_stoch := h_stoch ν_idx)
          (h := h) (h_wf := h_wf) (h_complete := h_complete))

    -- Now compute and cancel the common `denom`.
    have hden_le_one : denom ≤ 1 := by
      have h_term : ∀ i : EnvironmentIndex,
          prior.weight i * historyProbability (envs i) h ≤ prior.weight i := by
        intro i
        have h_prob : historyProbability (envs i) h ≤ 1 := historyProbability_le_one (envs i) h
        simpa [mul_one] using (mul_le_mul_right h_prob (prior.weight i))
      have h_le : denom ≤ ∑' i, prior.weight i := by
        simpa [denom, mixtureProbability] using (ENNReal.tsum_le_tsum h_term)
      exact le_trans h_le prior.tsum_le_one
    have hden_ne_top : denom ≠ ∞ := (lt_of_le_of_lt hden_le_one ENNReal.one_lt_top).ne_top

    -- Expand everything and cancel `denom`.
    have h_cancel :
        (historyProbability (envs ν_idx) h * prior.weight ν_idx / denom) * denom =
          historyProbability (envs ν_idx) h * prior.weight ν_idx := by
      -- `((a / b) * b) = a` for `b ≠ 0, b ≠ ∞`.
      simpa using
        (ENNReal.div_mul_cancel (a := denom) (b := historyProbability (envs ν_idx) h * prior.weight ν_idx)
          hden_pos hden_ne_top)

    calc
      bayesianPosteriorWeight O M prior envs ν_idx h *
            mixtureMeasureWithPolicy O M prior envs π h_stoch (cylinderSet h)
          = (historyProbability (envs ν_idx) h * prior.weight ν_idx / denom) *
              (policyProbability π h * denom) := by
                simp [bayesianPosteriorWeight, denom, hden_pos, hmix, mul_assoc, mul_comm]
      _ = policyProbability π h *
            ((historyProbability (envs ν_idx) h * prior.weight ν_idx / denom) * denom) := by
            ring
      _ = policyProbability π h * (historyProbability (envs ν_idx) h * prior.weight ν_idx) := by
            simp [h_cancel]
      _ = prior.weight ν_idx * (policyProbability π h * historyProbability (envs ν_idx) h) := by
            ring
      _ = prior.weight ν_idx *
            environmentMeasureWithPolicy (envs ν_idx) π (h_stoch ν_idx) (cylinderSet h) := by
            simp [hcomp]

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PolicyFactorization
