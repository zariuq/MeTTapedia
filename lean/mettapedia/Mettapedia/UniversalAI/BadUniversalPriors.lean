import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Bad Universal Priors and Notions of Optimality

This file formalizes the negative results from Leike & Hutter (2015):
"Bad Universal Priors and Notions of Optimality"

## Main Results

These results show fundamental limitations of AIXI and Bayesian RL:

* **Theorem 7 (Dogmatic Prior)**: For any computable policy π, there exists a
  universal mixture ξ' that makes AIXI follow π (as long as V^π > ε)

* **Theorem 18 (Pareto Optimality is Trivial)**: Every policy is Pareto optimal
  in the class of all computable environments

* **Corollary 13**: Some AIXIs are stupid - AIXI can score arbitrarily close
  to minimum intelligence

* **Corollary 14**: Any computable policy can score arbitrarily close to
  maximum intelligence

## Philosophical Implications

These results show that AIXI is a *relative* theory of intelligence,
dependent on the choice of the Universal Turing Machine (UTM).
There can be no invariance theorem for AIXI as there is for Kolmogorov complexity.

## References

- Leike, J. & Hutter, M. (2015). "Bad Universal Priors and Notions of Optimality"
  JMLR Workshop and Conference Proceedings vol 40:1-16
- arXiv:1510.05572
-/

namespace Mettapedia.UniversalAI.BadUniversalPriors

open BayesianAgents

private def perceptEquiv : Percept ≃ Bool × Bool :=
  ⟨fun p => match p with | Percept.mk a b => (a, b),
    fun ⟨a, b⟩ => Percept.mk a b,
    by intro p; cases p; rfl,
    by intro p; cases p; rfl⟩

private lemma sum_rewardBit_half (b : Bool) :
    (∑ x : Percept, (if x.rewardBit = b then (1 : ENNReal) / 2 else 0)) = 1 := by
  classical
  have h1 :
      (∑ x : Percept, (if x.rewardBit = b then (1 : ENNReal) / 2 else 0)) =
        ∑ x : Bool × Bool, (if x.2 = b then (1 : ENNReal) / 2 else 0) := by
    refine Fintype.sum_equiv perceptEquiv
        (f := fun x : Percept => if x.rewardBit = b then (1 : ENNReal) / 2 else 0)
        (g := fun x : Bool × Bool => if x.2 = b then (1 : ENNReal) / 2 else 0) ?_
    intro x
    cases x with
    | mk o r => rfl
  rw [h1]
  cases b <;> simp [Fintype.sum_prod_type] <;>
    simpa using
      (ENNReal.mul_inv_cancel two_ne_zero (by
        simp [ENNReal.ofNat_ne_top]))

private lemma sum_const_quarter :
    (∑ _x : Percept, (1 : ENNReal) / 4) = 1 := by
  classical
  have h1 :
      (∑ _x : Percept, (1 : ENNReal) / 4) =
        ∑ _x : Bool × Bool, (1 : ENNReal) / 4 := by
    refine Fintype.sum_equiv perceptEquiv (f := fun _x : Percept => (1 : ENNReal) / 4)
        (g := fun _x : Bool × Bool => (1 : ENNReal) / 4) ?_
    intro x
    cases x with
    | mk o r => rfl
  rw [h1]
  simp
  simpa using
    (ENNReal.mul_inv_cancel (by norm_num : (4 : ENNReal) ≠ 0) (by
      simp [ENNReal.ofNat_ne_top]))

theorem policy_sum_toReal_eq_one (π : Agent) (h : History) (hw : h.wellFormed) :
    (π.policy h Action.left).toReal
      + (π.policy h Action.right).toReal
      + (π.policy h Action.stay).toReal = 1 := by
  have hsum_tsum : (∑' a : Action, π.policy h a) = 1 := π.policy_sum_one h hw
  have hsum : (∑ a : Action, π.policy h a) = 1 := by
    simpa [tsum_fintype] using hsum_tsum
  have hterm_ne_top : ∀ a : Action, π.policy h a ≠ (⊤ : ENNReal) := by
    intro a
    have ha_le_sum : π.policy h a ≤ ∑ b : Action, π.policy h b := by
      classical
      have : π.policy h a ≤ ∑ b ∈ (Finset.univ : Finset Action), π.policy h b := by
        refine Finset.single_le_sum ?_ (by simp)
        intro b _hb
        exact zero_le _
      simpa using this
    have ha_le_one : π.policy h a ≤ 1 := by
      simpa [hsum] using ha_le_sum
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ha_le_one
  have htoReal_sum :
      (∑ a ∈ (Finset.univ : Finset Action), π.policy h a).toReal =
        ∑ a ∈ (Finset.univ : Finset Action), (π.policy h a).toReal :=
    ENNReal.toReal_sum (s := (Finset.univ : Finset Action)) (f := fun a : Action => π.policy h a) (by
      intro a ha
      exact hterm_ne_top a)
  have htoReal_eq : (∑ a : Action, (π.policy h a).toReal) = 1 := by
    have h := congrArg ENNReal.toReal hsum
    simpa [htoReal_sum] using h
  have hexp :
      (∑ a : Action, (π.policy h a).toReal) =
        (π.policy h Action.left).toReal + (π.policy h Action.right).toReal +
          (π.policy h Action.stay).toReal := by
    classical
    rw [univ_Action]
    simp [Finset.sum_insert, Finset.sum_singleton, add_assoc]
  simpa [hexp, add_assoc] using htoReal_eq

/-! ## Hell and Heaven Environments

The key construction uses "hell" (reward 0 forever) and "heaven" (reward 1 forever)
environments to manipulate AIXI's behavior.
-/

/-- The Hell environment: always returns reward 0.
    Used to punish agents that deviate from a prescribed policy. -/
noncomputable def hellEnvironment : Environment where
  prob := fun h x =>
    -- Probability 1/2 for each of 2 percepts with rewardBit = false
    if h.wellFormed ∧ x.rewardBit = false then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h _ => by
    rw [tsum_fintype]
    by_cases hw : h.wellFormed
    · -- Well-formed: sum over 4 percepts = 1/2 + 0 + 1/2 + 0 = 1
      have hsum :
          (∑ x : Percept, (if x.rewardBit = false then (1 : ENNReal) / 2 else 0)) = 1 :=
        sum_rewardBit_half false
      exact (le_of_eq <| by simpa [hw, true_and] using hsum)
    · -- Not well-formed: all probabilities are 0
      simp [hw]

/-- The Heaven environment: always returns reward 1.
    Used to reward agents that follow a prescribed policy. -/
noncomputable def heavenEnvironment : Environment where
  prob := fun h x =>
    -- Probability 1/2 for percepts with rewardBit = true
    if h.wellFormed ∧ x.rewardBit = true then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h _ => by
    rw [tsum_fintype]
    by_cases hw : h.wellFormed
    · -- Well-formed: sum over 4 percepts = 0 + 1/2 + 0 + 1/2 = 1
      have hsum :
          (∑ x : Percept, (if x.rewardBit = true then (1 : ENNReal) / 2 else 0)) = 1 :=
        sum_rewardBit_half true
      exact (le_of_eq <| by simpa [hw, true_and] using hsum)
    · -- Not well-formed: all probabilities are 0
      simp [hw]

/-- Value in hell environment is 0 (no rewards ever). -/
theorem value_in_hell (π : Agent) (γ : DiscountFactor) (h : History) :
    value hellEnvironment π γ h 0 = 0 := by
  simp only [value_zero]

/-- In this model `horizon` counts *half-steps* (agent move / environment move).
So a single interaction cycle needs `horizon = 2`. In heaven, the value is `1`. -/
theorem value_in_heaven_eq_one (π : Agent) (γ : DiscountFactor) :
    value heavenEnvironment π γ [] 2 = 1 := by
  -- Expand the 2-step value: one action choice (value) and one percept step (qValue).
  -- All percepts with rewardBit=true have prob 1/2 and reward 1, others 0
  -- So we get: sum over actions of (policy(a) * sum over percepts of (prob * reward))
  -- = sum over actions of (policy(a) * (1/2 * 1 + 1/2 * 1)) = sum of policy(a) = 1
  have hw : History.wellFormed ([] : History) := by simp [History.wellFormed]
  have hhalf : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by
    simpa [one_div] using (add_halves (1 : ℝ))
  -- Reduce to the sum of the action probabilities (as reals).
  simp [value, qValue, heavenEnvironment, History.wellFormed, Percept.rewardBit, Percept.reward,
    List.foldl, hhalf, add_assoc]
  simpa [add_assoc] using (policy_sum_toReal_eq_one (π := π) (h := []) (hw := hw))

theorem value_in_heaven_positive (π : Agent) (γ : DiscountFactor) :
    0 < value heavenEnvironment π γ [] 2 := by
  simp [value_in_heaven_eq_one (π := π) (γ := γ)]

/-! ## The Dogmatic Prior (Theorem 7)

The key construction: given any computable policy π, we create an environment ν
that mimics the universal mixture ξ while following π, but sends the agent to
hell (reward 0 forever) if it deviates from π.
-/

/-- A deterministic policy: selects a single action with probability 1.
    Used to define the "prescribed" behavior in the dogmatic prior. -/
noncomputable def deterministicPolicy (actionFn : History → Action) : Agent where
  policy := fun h a => if a = actionFn h then 1 else 0
  policy_sum_one := fun h _ => by
    classical
    rw [tsum_fintype]
    cases hact : actionFn h <;> simp [univ_Action]

/-- Create an environment that punishes deviation from a prescribed action function.

    ν(e_{1:t} | a_{1:t}) =
      - ξ(e_{1:t} | a_{1:t})  if a_k = π(æ_{<k}) for all k ≤ t
      - Goes to hell (reward 0) if agent deviates

    For simplicity, we condition on whether the FIRST action matches. -/
noncomputable def dogmaticEnv (ξ : Environment) (targetAction : Action) : Environment where
  prob := fun h x =>
    -- Check if first action (if any) matches target
    let firstAction := h.actions.head?
    match firstAction with
    | none => ξ.prob h x  -- No actions yet, behave like ξ
    | some a =>
      if a = targetAction then
        ξ.prob h x  -- Followed policy, behave like ξ
      else
        -- Deviated: go to hell (only reward 0 percepts)
        if x.rewardBit = false then ξ.prob h x else 0
  prob_le_one := fun h hw => by
    cases hfirst : h.actions.head? with
    | none => exact ξ.prob_le_one h hw
    | some a =>
      -- Need to handle the match case for `some a`
      by_cases ha : a = targetAction
      · simp only [ha, ↓reduceIte]
        exact ξ.prob_le_one h hw
      · simp only [ha, ↓reduceIte]
        -- Sum is ≤ sum over ξ which is ≤ 1
        calc ∑' x, (if x.rewardBit = false then ξ.prob h x else 0)
            ≤ ∑' x, ξ.prob h x := by
              apply ENNReal.tsum_le_tsum
              intro x; split_ifs <;> simp
          _ ≤ 1 := ξ.prob_le_one h hw

/-- Key property: The dogmatic environment equals the base environment
    for histories where the agent follows the target action. -/
theorem dogmatic_equals_base_on_policy (ξ : Environment) (targetAction : Action)
    (h : History) (x : Percept)
    (hfirst : h.actions.head? = some targetAction) :
    (dogmaticEnv ξ targetAction).prob h x = ξ.prob h x := by
  simp only [dogmaticEnv, hfirst, ↓reduceIte]

/-! ## Theorem 7: The Dogmatic Prior

For any computable policy π, any universal mixture ξ, and ε > 0,
there exists a universal mixture ξ' such that for any history h
consistent with π with V^π_ξ(h) > ε, the action π(h) is the
unique ξ'-optimal action.
-/

/-- The dogmatic prior mixture: ξ' = (1/2)ν + (ε/2)ξ
    where ν is the dogmatic environment for the target action. -/
noncomputable def dogmaticMixture (ξ : Environment) (targetAction : Action)
    (ε : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1) : Environment where
  prob := fun h x =>
    (1/2 : ENNReal) * (dogmaticEnv ξ targetAction).prob h x +
    (ENNReal.ofReal (ε/2)) * ξ.prob h x
  prob_le_one := fun h hw => by
    have h1 : ∑' x, ((1/2 : ENNReal) * (dogmaticEnv ξ targetAction).prob h x +
               ENNReal.ofReal (ε/2) * ξ.prob h x) =
        (1/2) * ∑' x, (dogmaticEnv ξ targetAction).prob h x +
        ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x := by
      rw [ENNReal.tsum_add]
      congr 1 <;> rw [ENNReal.tsum_mul_left]
    rw [h1]
    have hdog_le : ∑' x, (dogmaticEnv ξ targetAction).prob h x ≤ 1 :=
      (dogmaticEnv ξ targetAction).prob_le_one h hw
    have hξ_le : ∑' x, ξ.prob h x ≤ 1 := ξ.prob_le_one h hw
    have hε2_le : ENNReal.ofReal (ε/2) ≤ 1/2 := by
      have h1 : ε / 2 ≤ 1 / 2 := by linarith
      calc ENNReal.ofReal (ε/2) ≤ ENNReal.ofReal (1/2) := ENNReal.ofReal_le_ofReal h1
        _ = 1/2 := by simp only [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
            ENNReal.ofReal_ofNat]
    calc (1/2 : ENNReal) * ∑' x, (dogmaticEnv ξ targetAction).prob h x +
         ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x
        ≤ (1/2) * 1 + (1/2) * 1 := by
          apply add_le_add
          · exact mul_le_mul_left' hdog_le _
          · calc ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x
                ≤ (1/2) * ∑' x, ξ.prob h x := mul_le_mul_right' hε2_le _
              _ ≤ (1/2) * 1 := mul_le_mul_left' hξ_le _
      _ = 1 := by simpa using ENNReal.inv_two_add_inv_two

/-! ### Main Theorem Statement

**Theorem 7** (Leike & Hutter 2015):
Let π be any computable policy, let ξ be any universal mixture,
and let ε > 0. There is a universal mixture ξ' such that for any
history h consistent with π and V^π_ξ(h) > ε, the action π(h) is
the unique ξ'-optimal action.

**Proof idea**:
1. Construct ν that mimics ξ while following π, but goes to hell on deviation
2. Set ξ' = (1/2)ν + (ε/2)ξ
3. Since ν equals ξ on policy π, posterior weight of ν stays at 2/(1+ε)
4. Deviating gives V* ≤ ε/(1+ε) < ε < V^π_ξ(h), so deviation is suboptimal
-/

theorem optimalQValue_horizon1_eq (μ : Environment) (γ : DiscountFactor) (h : History) (a : Action) :
    optimalQValue μ γ h a 1 =
      let ha := h ++ [HistElem.act a]
      if ¬ha.wellFormed then 0
      else (μ.prob ha (Percept.mk false true)).toReal + (μ.prob ha (Percept.mk true true)).toReal := by
  classical
  -- Expand the 1-step optimal Q-value: only rewardBit=true percepts contribute.
  simp [optimalQValue, optimalValue, Percept.reward, List.foldl]

theorem optimalQValue_horizon1_le_one (μ : Environment) (γ : DiscountFactor) (h : History) (a : Action) :
    optimalQValue μ γ h a 1 ≤ 1 := by
  classical
  set ha : History := h ++ [HistElem.act a]
  cases hwa : ha.wellFormed with
  | false =>
      simp [optimalQValue, ha, hwa]
  | true =>
      have hwa' : ha.wellFormed := by simp [hwa]
      have hprob_le_one_tsum : (∑' x : Percept, μ.prob ha x) ≤ 1 := μ.prob_le_one ha hwa'
      have hprob_le_one : (∑ x : Percept, μ.prob ha x) ≤ 1 := by
        simpa [tsum_fintype] using hprob_le_one_tsum
      have hsum_ne_top : (∑ x : Percept, μ.prob ha x) ≠ (⊤ : ENNReal) :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hprob_le_one
      have hprob_ne_top : ∀ x : Percept, μ.prob ha x ≠ (⊤ : ENNReal) := by
        intro x
        have hx_le_sum : μ.prob ha x ≤ ∑ y : Percept, μ.prob ha y := by
          classical
          have : μ.prob ha x ≤ ∑ y ∈ (Finset.univ : Finset Percept), μ.prob ha y := by
            refine Finset.single_le_sum ?_ (by simp)
            intro y _hy
            exact zero_le _
          simpa using this
        have hx_le_one : μ.prob ha x ≤ 1 := hx_le_sum.trans hprob_le_one
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hx_le_one
      have htoReal_sum :
          (∑ x ∈ (Finset.univ : Finset Percept), μ.prob ha x).toReal =
            ∑ x ∈ (Finset.univ : Finset Percept), (μ.prob ha x).toReal :=
        ENNReal.toReal_sum
          (s := (Finset.univ : Finset Percept))
          (f := fun x : Percept => μ.prob ha x)
          (by
            intro x _hx
            exact hprob_ne_top x)
      have hsum_toReal_le : (∑ x : Percept, (μ.prob ha x).toReal) ≤ 1 := by
        have hle : (∑ x : Percept, μ.prob ha x).toReal ≤ (1 : ENNReal).toReal :=
          (ENNReal.toReal_le_toReal hsum_ne_top ENNReal.one_ne_top).2 hprob_le_one
        simpa [htoReal_sum] using hle
      -- Only the two rewardBit=true percepts contribute, so this is ≤ the full probability mass.
      have htwo_le_sum :
          (μ.prob ha (Percept.mk false true)).toReal + (μ.prob ha (Percept.mk true true)).toReal ≤
            ∑ x : Percept, (μ.prob ha x).toReal := by
        -- Expand the finite sum to 4 terms and drop the nonnegative ones.
        have hnonneg_ff : 0 ≤ (μ.prob ha (Percept.mk false false)).toReal := ENNReal.toReal_nonneg
        have hnonneg_tf : 0 ≤ (μ.prob ha (Percept.mk true false)).toReal := ENNReal.toReal_nonneg
        have hexp :
            (∑ x : Percept, (μ.prob ha x).toReal) =
              (μ.prob ha (Percept.mk false false)).toReal +
                ((μ.prob ha (Percept.mk false true)).toReal +
                  ((μ.prob ha (Percept.mk true false)).toReal +
                    (μ.prob ha (Percept.mk true true)).toReal)) := by
          classical
          rw [univ_Percept]
          simp [Finset.sum_insert, Finset.sum_singleton]
        -- Now `linarith` with the expanded form.
        linarith [hexp, hnonneg_ff, hnonneg_tf]
      -- Put it together.
      have hQ :
          optimalQValue μ γ h a 1 ≤
            (μ.prob ha (Percept.mk false true)).toReal + (μ.prob ha (Percept.mk true true)).toReal := by
        -- This is actually equality when `ha` is well-formed.
        have := optimalQValue_horizon1_eq (μ := μ) (γ := γ) (h := h) (a := a)
        -- Rewrite the `if` using `hwa`.
        simpa [ha, hwa] using this.le
      exact (hQ.trans (htwo_le_sum.trans hsum_toReal_le))

theorem dogmaticMixture_prefers_target_horizon1 (ξ : Environment) (γ : DiscountFactor)
    (targetAction : Action) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hQ : optimalQValue ξ γ [] targetAction 1 > ε) :
    ∀ a, a ≠ targetAction →
      optimalQValue (dogmaticMixture ξ targetAction ε hε hε1) γ [] a 1 <
        optimalQValue (dogmaticMixture ξ targetAction ε hε hε1) γ [] targetAction 1 := by
  classical
  intro a ha
  have hε0 : 0 ≤ ε / 2 := by linarith
  set w : ENNReal := ENNReal.ofReal (ε / 2)

  have hOtherEq :
      optimalQValue (dogmaticMixture ξ targetAction ε hε hε1) γ [] a 1 =
        w.toReal * optimalQValue ξ γ [] a 1 := by
    cases a <;> cases targetAction <;> try cases ha rfl
    all_goals
      (simp [w, optimalQValue, optimalValue, dogmaticMixture, dogmaticEnv, Percept.rewardBit,
        Percept.reward, History.actions, History.wellFormed, List.foldl, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hε0]; ring)

  have hOtherLe : optimalQValue (dogmaticMixture ξ targetAction ε hε hε1) γ [] a 1 ≤ ε / 2 := by
    have hξ_le_one : optimalQValue ξ γ [] a 1 ≤ 1 :=
      optimalQValue_horizon1_le_one (μ := ξ) (γ := γ) (h := []) (a := a)
    have hw_nonneg : 0 ≤ w.toReal := by
      simpa [w, ENNReal.toReal_ofReal hε0] using hε0
    have : w.toReal * optimalQValue ξ γ [] a 1 ≤ w.toReal * 1 :=
      mul_le_mul_of_nonneg_left hξ_le_one hw_nonneg
    have hw_toReal : w.toReal = ε / 2 := by simp [w, ENNReal.toReal_ofReal hε0]
    simpa [hOtherEq, hw_toReal] using this

  have hTargetGt : optimalQValue (dogmaticMixture ξ targetAction ε hε hε1) γ [] targetAction 1 > ε / 2 := by
    -- The target action gets at least the `1/2 · ξ` contribution (the extra `ε/2 · ξ` only helps).
    set μm : Environment := dogmaticMixture ξ targetAction ε hε hε1
    set ha : History := [HistElem.act targetAction]
    have hwa : ha.wellFormed := by
      cases targetAction <;> simp [ha, History.wellFormed]
    have hwa_eq : ha.wellFormed = true := by
      cases targetAction <;> simp [ha, History.wellFormed]
    -- Rewrite both Q-values to the rewardBit=true terms.
    have hQm :
        optimalQValue μm γ [] targetAction 1 =
          (μm.prob ha (Percept.mk false true)).toReal + (μm.prob ha (Percept.mk true true)).toReal := by
      simpa [μm, ha, History.wellFormed] using
        (optimalQValue_horizon1_eq (μ := μm) (γ := γ) (h := []) (a := targetAction))
    have hQξ :
        optimalQValue ξ γ [] targetAction 1 =
          (ξ.prob ha (Percept.mk false true)).toReal + (ξ.prob ha (Percept.mk true true)).toReal := by
      simpa [ha, History.wellFormed] using
        (optimalQValue_horizon1_eq (μ := ξ) (γ := γ) (h := []) (a := targetAction))
    -- Each rewardBit=true term in μm dominates the `1/2 · ξ` part.
    have hprob_le_one_tsum : (∑' x : Percept, μm.prob ha x) ≤ 1 := μm.prob_le_one ha hwa
    have hprob_le_one : (∑ x : Percept, μm.prob ha x) ≤ 1 := by
      simpa [tsum_fintype] using hprob_le_one_tsum
    have hprob_le_one_x : ∀ x : Percept, μm.prob ha x ≤ 1 := by
      intro x
      have hx_le_sum : μm.prob ha x ≤ ∑ y : Percept, μm.prob ha y := by
        classical
        have : μm.prob ha x ≤ ∑ y ∈ (Finset.univ : Finset Percept), μm.prob ha y := by
          refine Finset.single_le_sum ?_ (by simp)
          intro y _hy
          exact zero_le _
        simpa using this
      exact hx_le_sum.trans hprob_le_one
    have hprob_ne_top : ∀ x : Percept, μm.prob ha x ≠ (⊤ : ENNReal) := by
      intro x
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hprob_le_one_x x)

    have hterm_le (x : Percept) :
        ((1/2 : ENNReal) * ξ.prob ha x).toReal ≤ (μm.prob ha x).toReal := by
      -- In the matching-first-action case, `μm.prob ha x = 1/2·ξ + w·ξ`.
      have hdog : (dogmaticEnv ξ targetAction).prob ha x = ξ.prob ha x := by
        -- First action matches `targetAction`.
        have hhead : ha.actions.head? = some targetAction := by
          cases targetAction <;> simp [ha, History.actions]
        exact
          dogmatic_equals_base_on_policy (ξ := ξ) (targetAction := targetAction) (h := ha) (x := x)
            hhead
      have hprob :
          μm.prob ha x =
            (1/2 : ENNReal) * ξ.prob ha x + w * ξ.prob ha x := by
        -- Expand `μm` and use `hdog` to replace the dogmatic environment.
        simp [μm, dogmaticMixture, hdog, w, ha]
      -- Use monotonicity of `ENNReal.toReal` on finite values.
      have hle : (1/2 : ENNReal) * ξ.prob ha x ≤ μm.prob ha x := by
        -- `a ≤ a + b` with `b ≥ 0`.
        have hnonneg : 0 ≤ w * ξ.prob ha x := mul_nonneg (zero_le _) (zero_le _)
        rw [hprob]
        exact le_add_of_nonneg_right hnonneg
      exact ENNReal.toReal_mono (hprob_ne_top x) hle

    have hLowerBound :
        (1/2 : ℝ) * optimalQValue ξ γ [] targetAction 1 ≤ optimalQValue μm γ [] targetAction 1 := by
      -- Rewrite to the two percept terms and apply `hterm_le` to each.
      have hhalf_toReal : ((1/2 : ENNReal).toReal : ℝ) = (1/2 : ℝ) := by norm_num
      -- Convert `((1/2)*p).toReal` into `(1/2)*p.toReal`.
      have hft :
          (1/2 : ℝ) * (ξ.prob ha (Percept.mk false true)).toReal ≤
            (μm.prob ha (Percept.mk false true)).toReal := by
        simpa [ENNReal.toReal_mul, hhalf_toReal] using hterm_le (Percept.mk false true)
      have htt :
          (1/2 : ℝ) * (ξ.prob ha (Percept.mk true true)).toReal ≤
            (μm.prob ha (Percept.mk true true)).toReal := by
        simpa [ENNReal.toReal_mul, hhalf_toReal] using hterm_le (Percept.mk true true)
      -- Now combine.
      -- Expand the Q-values and use `linarith`.
      have hξeq := hQξ
      have hmeq := hQm
      -- `linarith` understands linear arithmetic once the equalities are inlined.
      linarith [hft, htt, hξeq, hmeq]

    have : (1/2 : ℝ) * optimalQValue ξ γ [] targetAction 1 > ε / 2 := by
      nlinarith [hQ]
    exact lt_of_lt_of_le this hLowerBound

  exact lt_of_le_of_lt hOtherLe hTargetGt

/-! ## Theorem 18: Pareto Optimality is Trivial

Every policy is Pareto optimal in the class of all computable environments.
This completely undermines Pareto optimality as an optimality criterion.
-/

/-- Definition of Pareto optimality.

    A policy π is Pareto optimal in environment class M iff there is no
    policy π̃ that does at least as well in all environments and
    strictly better in at least one. -/
def ParetoOptimal (π : Agent) (M : Set Environment) (γ : DiscountFactor) (m : ℕ) : Prop :=
  ¬∃ π' : Agent,
    (∀ ν ∈ M, value ν π' γ [] m ≥ value ν π γ [] m) ∧
    (∃ ρ ∈ M, value ρ π' γ [] m > value ρ π γ [] m)

/-- A history where it is the agent’s turn to act: well‑formed and ending in a percept (or empty). -/
def History.agentTurn (h : History) : Prop :=
  h.wellFormed = true ∧ h.actions.length = h.percepts.length

/-- Full-history Pareto optimality: quantify dominance and strict improvement over all agent-turn histories. -/
def ParetoOptimalAllHistories (π : Agent) (M : Set Environment) (γ : DiscountFactor) (m : ℕ) : Prop :=
  ¬∃ π' : Agent,
    (∀ ν ∈ M, ∀ h, History.agentTurn h → value ν π' γ h m ≥ value ν π γ h m) ∧
    (∃ ρ ∈ M, ∃ h, History.agentTurn h ∧ value ρ π' γ h m > value ρ π γ h m)

/-- A "buddy environment" for a specific action that rewards that action
    and punishes all others.

    - If agent takes targetAction at first step, go to heaven (reward 1 forever)
    - If agent takes any other action, go to hell (reward 0 forever)

    This environment is computable and demonstrates that every policy
    is Pareto optimal. -/
noncomputable def buddyEnvironment (targetAction : Action) : Environment where
  prob := fun h x =>
    match h.actions.head? with
    | none =>
      -- No action yet: uniform distribution
      if h.wellFormed then (1 : ENNReal) / 4 else 0
    | some a =>
      if a = targetAction then
        -- Went to heaven: reward 1
        if h.wellFormed ∧ x.rewardBit = true then (1 : ENNReal) / 2 else 0
      else
        -- Went to hell: reward 0
        if h.wellFormed ∧ x.rewardBit = false then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h hw => by
    cases hfirst : h.actions.head? with
    | none =>
      rw [tsum_fintype]
      have hw' : h.wellFormed = true := by simpa using hw
      have hsum : (∑ _x : Percept, (1 : ENNReal) / 4) = 1 := sum_const_quarter
      have hle : (∑ _x : Percept, (1 : ENNReal) / 4) ≤ 1 := le_of_eq hsum
      simpa [hfirst, hw'] using hle
    | some a =>
      rw [tsum_fintype]
      have hw' : h.wellFormed = true := by simpa using hw
      by_cases ha : a = targetAction
      · have hsum :
            (∑ x : Percept, (if x.rewardBit = true then (1 : ENNReal) / 2 else 0)) = 1 :=
          sum_rewardBit_half true
        have hle : (∑ x : Percept, (if x.rewardBit = true then (1 : ENNReal) / 2 else 0)) ≤ 1 :=
          le_of_eq hsum
        simpa [hfirst, ha, hw', true_and] using hle
      · have hsum :
            (∑ x : Percept, (if x.rewardBit = false then (1 : ENNReal) / 2 else 0)) = 1 :=
          sum_rewardBit_half false
        have hle : (∑ x : Percept, (if x.rewardBit = false then (1 : ENNReal) / 2 else 0)) ≤ 1 :=
          le_of_eq hsum
        simpa [hfirst, ha, hw', true_and] using hle

/-- A "buddy environment" that rewards the most recent action.

Used for the full-history Pareto optimality result: at any agent-turn history `h`,
the horizon-2 value equals the policy's probability mass on the defended action. -/
noncomputable def buddyEnvironmentNow (targetAction : Action) : Environment where
  prob := fun h x =>
    match h.reverse with
    | HistElem.act a :: _ =>
        if a = targetAction then
          if h.wellFormed ∧ x.rewardBit = true then (1 : ENNReal) / 2 else 0
        else
          if h.wellFormed ∧ x.rewardBit = false then (1 : ENNReal) / 2 else 0
    | _ =>
        if h.wellFormed then (1 : ENNReal) / 4 else 0
  prob_le_one := fun h hw => by
    -- All cases are explicit finite sums over Percept.
    rw [tsum_fintype]
    have hw' : h.wellFormed = true := by simpa using hw
    cases hrev : h.reverse with
    | nil =>
        have hsum : (∑ _x : Percept, (1 : ENNReal) / 4) = 1 := sum_const_quarter
        exact (le_of_eq <| by simpa [hrev, hw'] using hsum)
    | cons e tail =>
        cases e with
        | per _x =>
            have hsum : (∑ _x : Percept, (1 : ENNReal) / 4) = 1 := sum_const_quarter
            exact (le_of_eq <| by simpa [hrev, hw'] using hsum)
        | act a =>
            by_cases ha : a = targetAction
            · have hsum :
                  (∑ x : Percept, (if x.rewardBit = true then (1 : ENNReal) / 2 else 0)) = 1 :=
                sum_rewardBit_half true
              exact (le_of_eq <| by simpa [hrev, ha, hw', true_and] using hsum)
            · have hsum :
                  (∑ x : Percept, (if x.rewardBit = false then (1 : ENNReal) / 2 else 0)) = 1 :=
                sum_rewardBit_half false
              exact (le_of_eq <| by simpa [hrev, ha, hw', true_and] using hsum)

theorem History.agentTurn_append_act_wellFormed (h : History) (a : Action)
    (hturn : History.agentTurn h) : (h ++ [HistElem.act a]).wellFormed = true := by
  classical
  -- Prove by strong induction on the list length.
  have P :
      ∀ n : ℕ, ∀ h : History, h.length = n → History.agentTurn h →
        (h ++ [HistElem.act a]).wellFormed = true := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih h hlen hturn
    rcases hturn with ⟨hw, hacts_eq⟩
    cases h with
    | nil =>
        simp [History.wellFormed]
    | cons e rest =>
        cases e with
        | per =>
            simp [History.wellFormed] at hw
        | act a0 =>
            cases rest with
            | nil =>
                simp [History.actions, History.percepts] at hacts_eq
            | cons e2 rest2 =>
                cases e2 with
                | act =>
                    simp [History.wellFormed] at hw
                | per x =>
                    have hw2 : History.wellFormed rest2 = true := by
                      simpa [History.wellFormed] using hw
                    have hacts_eq2 :
                        (History.actions rest2).length = (History.percepts rest2).length := by
                      simpa [History.actions, History.percepts] using hacts_eq
                    have hturn2 : History.agentTurn rest2 := ⟨hw2, hacts_eq2⟩
                    have hlt : rest2.length < n := by
                      have hn : n = rest2.length + 2 := by
                        simpa using hlen.symm
                      have hlt' : rest2.length < rest2.length + 2 :=
                        Nat.lt_add_of_pos_right (n := rest2.length) (k := 2) (by decide)
                      rw [hn]
                      exact hlt'
                    have hrec :
                        History.wellFormed (rest2 ++ [HistElem.act a]) = true :=
                      ih rest2.length hlt rest2 rfl hturn2
                    simpa [History.wellFormed] using hrec
  exact P h.length h rfl hturn

theorem value_buddyEnvironmentNow_horizon2 (targetAction : Action) (π : Agent) (γ : DiscountFactor)
    (h : History) (hturn : History.agentTurn h) :
    value (buddyEnvironmentNow targetAction) π γ h 2 = (π.policy h targetAction).toReal := by
  have hw : h.wellFormed = true := hturn.1
  have hw_left : (h ++ [HistElem.act Action.left]).wellFormed = true :=
    History.agentTurn_append_act_wellFormed (h := h) (a := Action.left) hturn
  have hw_right : (h ++ [HistElem.act Action.right]).wellFormed = true :=
    History.agentTurn_append_act_wellFormed (h := h) (a := Action.right) hturn
  have hw_stay : (h ++ [HistElem.act Action.stay]).wellFormed = true :=
    History.agentTurn_append_act_wellFormed (h := h) (a := Action.stay) hturn
  have hhalf : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by
    simpa [one_div] using (add_halves (1 : ℝ))
  cases targetAction <;>
    simp [value, qValue, buddyEnvironmentNow, hw, hw_left, hw_right, hw_stay, List.foldl,
      List.reverse_append, Percept.rewardBit, Percept.reward, hhalf]

/-- **Theorem 18**: Every policy is Pareto optimal.

    **Proof**: For any policy π, we construct "buddy environments" that
    defend π against any challenger π̃. For each history h where π and π̃
    first disagree, there's an environment that rewards π's action and
    punishes π̃'s action. Together, these environments ensure no π̃ can
    dominate π.

    This is a devastating result: Pareto optimality is meaningless because
    every policy, no matter how bad, is Pareto optimal! -/
theorem pareto_optimality_trivial_horizon2 (π : Agent) (γ : DiscountFactor)
    (M : Set Environment) (hM : ∀ ν, ν ∈ M) :
    ParetoOptimal π M γ 2 := by
  classical
  unfold ParetoOptimal
  intro hcontra
  rcases hcontra with ⟨π', hdomAll, ρ, hρM, hstrict⟩
  -- Use the buddy environments for each first action to force agreement of first-step action
  -- distributions; then horizon-2 value is identical in every environment, contradicting `hstrict`.
  have hwell : History.wellFormed [] := by simp only [History.wellFormed]
  -- Helper: value in a buddy environment at horizon 2 equals the policy mass on the defended action.
  have hbuddy :
      ∀ a : Action, value (buddyEnvironment a) π γ [] 2 = (π.policy [] a).toReal ∧
        value (buddyEnvironment a) π' γ [] 2 = (π'.policy [] a).toReal := by
    intro a
    constructor
    · -- Value for π
      have hhalf : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by
        simpa [one_div] using (add_halves (1 : ℝ))
      cases a <;>
        simp [value, qValue, buddyEnvironment, History.wellFormed, History.actions, Percept.rewardBit,
          Percept.reward, List.foldl, hhalf]
    · -- Value for π'
      have hhalf : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by
        simpa [one_div] using (add_halves (1 : ℝ))
      cases a <;>
        simp [value, qValue, buddyEnvironment, History.wellFormed, History.actions, Percept.rewardBit,
          Percept.reward, List.foldl, hhalf]

  have hprob_ge : ∀ a : Action, (π'.policy [] a).toReal ≥ (π.policy [] a).toReal := by
    intro a
    have haM : buddyEnvironment a ∈ M := hM (buddyEnvironment a)
    have hdom := hdomAll (buddyEnvironment a) haM
    -- Rewrite both sides using `hbuddy`.
    have hπ : value (buddyEnvironment a) π γ [] 2 = (π.policy [] a).toReal := (hbuddy a).1
    have hπ' : value (buddyEnvironment a) π' γ [] 2 = (π'.policy [] a).toReal := (hbuddy a).2
    -- Use the dominance inequality.
    simp only [hπ, hπ'] at hdom
    exact hdom

  -- Convert the ENNReal "sum to 1" property into a real sum over the 3 actions.
  have hsumπ : (π.policy [] Action.left).toReal
      + (π.policy [] Action.right).toReal
      + (π.policy [] Action.stay).toReal = 1 := by
    simpa using (policy_sum_toReal_eq_one (π := π) (h := []) (hw := hwell))

  have hsumπ' : (π'.policy [] Action.left).toReal
      + (π'.policy [] Action.right).toReal
      + (π'.policy [] Action.stay).toReal = 1 := by
    simpa using (policy_sum_toReal_eq_one (π := π') (h := []) (hw := hwell))

  -- From componentwise ≥ and equal sums, all three components are equal.
  have hleft : (π'.policy [] Action.left).toReal = (π.policy [] Action.left).toReal := by
    have hge := hprob_ge Action.left
    have hge_rest :
        (π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal ≥
          (π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal := by
      linarith [hprob_ge Action.right, hprob_ge Action.stay]
    -- Use sums to get the reverse inequality for the left component.
    have hle : (π'.policy [] Action.left).toReal ≤ (π.policy [] Action.left).toReal := by
      -- Rearrange via `hsumπ` and `hsumπ'`.
      have : (π'.policy [] Action.left).toReal =
          1 - ((π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal) := by
        linarith [hsumπ']
      have : (π'.policy [] Action.left).toReal ≤
          1 - ((π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal) := by
        have hsub : 1 - ((π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal) ≤
            1 - ((π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal) := by
          exact sub_le_sub_left hge_rest _
        -- replace the left side with the expression from `hsumπ'`
        linarith [hsumπ', hsub]
      -- The right-hand side is exactly the left component of π by `hsumπ`.
      linarith [hsumπ, this]
    exact le_antisymm hle hge

  have hright : (π'.policy [] Action.right).toReal = (π.policy [] Action.right).toReal := by
    have hge := hprob_ge Action.right
    have hge_rest :
        (π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal ≥
          (π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal := by
      linarith [hprob_ge Action.left, hprob_ge Action.stay]
    have hle : (π'.policy [] Action.right).toReal ≤ (π.policy [] Action.right).toReal := by
      have hsub : 1 - ((π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal) ≤
          1 - ((π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal) := by
        exact sub_le_sub_left hge_rest _
      have hπ'expr : (π'.policy [] Action.right).toReal =
          1 - ((π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal) := by
        linarith [hsumπ']
      have hπexpr : (π.policy [] Action.right).toReal =
          1 - ((π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal) := by
        linarith [hsumπ]
      linarith [hπ'expr, hπexpr, hsub]
    exact le_antisymm hle hge

  have hstay : (π'.policy [] Action.stay).toReal = (π.policy [] Action.stay).toReal := by
    -- Obtain from sum equality once left/right agree.
    linarith [hsumπ, hsumπ', hleft, hright]

  -- With identical first-step action probabilities, horizon-2 values coincide in every environment.
  have hEqVal : value ρ π' γ [] 2 = value ρ π γ [] 2 := by
    -- Expand both values and rewrite using the probability equalities.
    simp [value, qValue, History.wellFormed, List.foldl, hleft, hright, hstay]

  -- Contradiction with the assumed strict improvement in some environment ρ.
  have : ¬ value ρ π' γ [] 2 > value ρ π γ [] 2 := by
    simp only [hEqVal, lt_self_iff_false, not_false_eq_true]
  exact this hstrict

theorem pareto_optimality_trivial_allHistories_horizon2 (π : Agent) (γ : DiscountFactor)
    (M : Set Environment) (hM : ∀ ν, ν ∈ M) :
    ParetoOptimalAllHistories π M γ 2 := by
  classical
  unfold ParetoOptimalAllHistories
  intro hcontra
  rcases hcontra with ⟨π', hdomAll, ρ, hρM, h, hturn, hstrict⟩
  have hprob_ge : ∀ a : Action, (π'.policy h a).toReal ≥ (π.policy h a).toReal := by
    intro a
    have haM : buddyEnvironmentNow a ∈ M := hM (buddyEnvironmentNow a)
    have hdom := hdomAll (buddyEnvironmentNow a) haM h hturn
    have hπ : value (buddyEnvironmentNow a) π γ h 2 = (π.policy h a).toReal :=
      value_buddyEnvironmentNow_horizon2 (targetAction := a) (π := π) (γ := γ) (h := h) hturn
    have hπ' : value (buddyEnvironmentNow a) π' γ h 2 = (π'.policy h a).toReal :=
      value_buddyEnvironmentNow_horizon2 (targetAction := a) (π := π') (γ := γ) (h := h) hturn
    simpa [hπ, hπ'] using hdom

  have hw : h.wellFormed := by simpa using hturn.1
  have hsumπ :
      (π.policy h Action.left).toReal
        + (π.policy h Action.right).toReal
        + (π.policy h Action.stay).toReal = 1 := by
    simpa using (policy_sum_toReal_eq_one (π := π) (h := h) (hw := hw))
  have hsumπ' :
      (π'.policy h Action.left).toReal
        + (π'.policy h Action.right).toReal
        + (π'.policy h Action.stay).toReal = 1 := by
    simpa using (policy_sum_toReal_eq_one (π := π') (h := h) (hw := hw))

  have hleft : (π'.policy h Action.left).toReal = (π.policy h Action.left).toReal := by
    have hge := hprob_ge Action.left
    have hle : (π'.policy h Action.left).toReal ≤ (π.policy h Action.left).toReal := by
      have hge_rest :
          (π'.policy h Action.right).toReal + (π'.policy h Action.stay).toReal ≥
            (π.policy h Action.right).toReal + (π.policy h Action.stay).toReal := by
        linarith [hprob_ge Action.right, hprob_ge Action.stay]
      linarith [hsumπ, hsumπ', hge_rest]
    exact le_antisymm hle hge

  have hright : (π'.policy h Action.right).toReal = (π.policy h Action.right).toReal := by
    have hge := hprob_ge Action.right
    have hle : (π'.policy h Action.right).toReal ≤ (π.policy h Action.right).toReal := by
      have hge_rest :
          (π'.policy h Action.left).toReal + (π'.policy h Action.stay).toReal ≥
            (π.policy h Action.left).toReal + (π.policy h Action.stay).toReal := by
        linarith [hprob_ge Action.left, hprob_ge Action.stay]
      linarith [hsumπ, hsumπ', hge_rest]
    exact le_antisymm hle hge

  have hstay : (π'.policy h Action.stay).toReal = (π.policy h Action.stay).toReal := by
    linarith [hsumπ, hsumπ', hleft, hright]

  have hEqVal : value ρ π' γ h 2 = value ρ π γ h 2 := by
    -- Horizon 2 depends only on the one-step action distribution; future values are at horizon 0.
    simp [value, qValue, hturn.1, List.foldl, hleft, hright, hstay, add_assoc]

  have : ¬ value ρ π' γ h 2 > value ρ π γ h 2 := by
    simp [hEqVal]
  exact this hstrict

/-! ## Corollaries: Intelligence is Subjective

These corollaries show that the Legg-Hutter intelligence measure
and balanced Pareto optimality depend entirely on the UTM choice.
-/

/-!
### Corollary 13: Some AIXIs are stupid.

For any universal mixture ξ and every ε > 0, there is a universal
mixture ξ' such that AIXI with ξ' scores near-minimum intelligence
when measured with ξ.

**Proof sketch**: Use the dogmatic prior to make AIXI follow a
near-worst policy.
-/

/-!
### Corollary 14: AIXI is stupid for some intelligence measures.

For any ξ-optimal policy π*_ξ and for every ε > 0, there is a
universal mixture ξ' such that π*_ξ scores near-zero and some
other policy scores near-maximum.

**Proof sketch**: The dogmatic prior for any other policy will
make AIXI score near-maximum.
-/

/-!
### Corollary 15: Computable policies can be smart.

For any computable policy π and any ε > 0, there is a universal
mixture ξ' such that π scores near-maximum intelligence.

**Proof sketch**: Use the dogmatic prior for π.
-/

/-! ## Summary: Implications for AI Safety

These results have profound implications:

1. **No invariance theorem**: Unlike Kolmogorov complexity, AIXI's behavior
   depends fundamentally on the UTM choice. There is no "natural" UTM.

2. **Pareto optimality is meaningless**: Every policy is Pareto optimal,
   so this cannot distinguish good from bad policies.

3. **Intelligence is subjective**: The Legg-Hutter intelligence measure
   can make any computable policy score arbitrarily high or low.

4. **Exploration is crucial**: The underlying problem is that Bayesian
   agents like AIXI don't explore enough. The dogmatic prior exploits
   this by threatening hell for exploration.

5. **Solutions exist**: Adding explicit exploration (BayesExp, knowledge-seeking
   agents, optimism) can restore weak asymptotic optimality.

Table of optimality notions (from paper):
| Notion                        | Status                                    |
|-------------------------------|-------------------------------------------|
| μ-optimal                     | Requires knowing true environment         |
| Pareto optimality             | Trivial (Theorem 18)                      |
| Balanced Pareto optimality    | UTM-dependent (Corollary 13, 14)          |
| Self-optimizing               | Doesn't apply to M^CCS_LSC                |
| Strong asymptotic optimality  | Impossible                                |
| Weak asymptotic optimality    | Achievable (BayesExp), but not by AIXI    |

-/

end Mettapedia.UniversalAI.BadUniversalPriors
