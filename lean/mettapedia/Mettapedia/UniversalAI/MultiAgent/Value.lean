import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.MultiAgent.Policy
import Mettapedia.UniversalAI.BayesianAgents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Multi-Agent Value Functions

This file defines value functions for multi-agent reinforcement learning.

## Main Definitions

* `playerValue`: Expected discounted reward for player i
* `playerQValue`: Expected value of taking action a for player i
* `bestResponseValue`: Maximum value player i can achieve

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems"

-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents
open BigOperators

/-! ## Weighted Average Bound Lemmas -/

/-- Weighted sum is bounded by the bound when weights sum to ≤ 1 and values are ≤ bound.
    This is the key lemma for bounding expected values. -/
theorem weighted_sum_le_bound {α : Type*} [Fintype α] (w : α → ℝ) (v : α → ℝ) (B : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a ≤ 1)
    (hv_le : ∀ a, v a ≤ B) (hB_nonneg : 0 ≤ B) :
    ∑ a, w a * v a ≤ B := by
  calc ∑ a, w a * v a
      ≤ ∑ a, w a * B := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hv_le a) (hw_nonneg a)
    _ = B * ∑ a, w a := by rw [← Finset.sum_mul]; ring
    _ ≤ B * 1 := by
        apply mul_le_mul_of_nonneg_left hw_sum hB_nonneg
    _ = B := by ring

/-- Weighted sum equals bound when weights sum to exactly 1. -/
theorem weighted_sum_le_bound_eq_one {α : Type*} [Fintype α] (w : α → ℝ) (v : α → ℝ) (B : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1)
    (hv_le : ∀ a, v a ≤ B) (hB_nonneg : 0 ≤ B) :
    ∑ a, w a * v a ≤ B := by
  apply weighted_sum_le_bound w v B hw_nonneg (le_of_eq hw_sum) hv_le hB_nonneg

/-! ## ENNReal.toReal Helpers -/

/-- Convert ENNReal sum to Real sum when all terms are finite. -/
theorem ennreal_sum_toReal_eq {α : Type*} [Fintype α] (f : α → ENNReal)
    (hf_ne_top : ∀ a, f a ≠ ⊤) :
    (∑ a, f a).toReal = ∑ a, (f a).toReal := by
  exact ENNReal.toReal_sum (s := Finset.univ) (f := f) (fun a _ha => hf_ne_top a)

/-- Terms of a bounded sum are finite. -/
theorem ennreal_term_ne_top_of_sum_le {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_le : ∑ a, f a ≤ 1) (a : α) : f a ≠ ⊤ := by
  have hsum_ne_top : (∑ a, f a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hsum_le
  have ha_le_sum : f a ≤ ∑ b, f b := Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ a)
  exact ne_top_of_le_ne_top hsum_ne_top ha_le_sum

/-- When ENNReal sum ≤ 1, the Real sum also ≤ 1. -/
theorem ennreal_sum_toReal_le_one {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_le : ∑ a, f a ≤ 1) :
    ∑ a, (f a).toReal ≤ 1 := by
  have hf_ne_top : ∀ a, f a ≠ ⊤ := ennreal_term_ne_top_of_sum_le f hsum_le
  have hsum_ne_top : (∑ a, f a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hsum_le
  calc ∑ a, (f a).toReal
      = (∑ a, f a).toReal := (ennreal_sum_toReal_eq f hf_ne_top).symm
    _ ≤ (1 : ENNReal).toReal := by
        apply ENNReal.toReal_le_toReal hsum_ne_top ENNReal.one_ne_top |>.mpr hsum_le
    _ = 1 := ENNReal.toReal_one

/-- When ENNReal sum = 1, the Real sum also = 1. -/
theorem ennreal_sum_toReal_eq_one {α : Type*} [Fintype α] (f : α → ENNReal)
    (hsum_eq : ∑ a, f a = 1) :
    ∑ a, (f a).toReal = 1 := by
  have hf_ne_top : ∀ a, f a ≠ ⊤ := ennreal_term_ne_top_of_sum_le f (le_of_eq hsum_eq)
  calc ∑ a, (f a).toReal
      = (∑ a, f a).toReal := (ennreal_sum_toReal_eq f hf_ne_top).symm
    _ = (1 : ENNReal).toReal := by rw [hsum_eq]
    _ = 1 := ENNReal.toReal_one

/-! ## Helper: Joint action probability -/

/-- Probability that all agents choose the given joint action. -/
noncomputable def jointActionProb
    (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n)
    (ja : JointAction n) : ENNReal :=
  ∏ j : Fin n, (π.agents j).policy (h.playerView j) (ja j)

/-- Joint action probabilities sum to 1.

    This follows from the fact that each agent's policy sums to 1,
    and the joint action probability is a product of independent policies.
    Uses Finset.sum_prod_piFinset: ∑ f ∈ piFinset s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s i, g i j
-/
theorem jointActionProb_sum_eq_one {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (hw : h.wellFormed = true) :
    (∑ ja : JointAction n, jointActionProb π h ja) = 1 := by
  simp only [jointActionProb, JointAction]
  -- Rewrite using sum_prod_piFinset
  -- Use Fintype.piFinset_univ: piFinset (fun _ => univ) = univ
  conv_lhs => rw [← Fintype.piFinset_univ]
  -- Apply sum_prod_piFinset: ∑ f ∈ piFinset (fun _ => univ), ∏ i, g i (f i) = ∏ i, ∑ j ∈ univ, g i j
  rw [Finset.sum_prod_piFinset]
  -- Now we have: ∏ j, ∑ a ∈ univ, π_j(a) = 1
  -- Each inner sum equals 1 by policy_sum_one
  have h_each_one : ∀ j : Fin n, (∑ a ∈ Finset.univ, (π.agents j).policy (h.playerView j) a) = 1 := by
    intro j
    -- Use the proven playerView_wellFormed lemma
    have hw_view : (h.playerView j).wellFormed = true :=
      MultiAgentHistory.playerView_wellFormed j h hw
    -- Convert Finset.sum to tsum using tsum_fintype (in reverse)
    have htsum : (∑' a : Action, (π.agents j).policy (h.playerView j) a) = 1 :=
      (π.agents j).policy_sum_one (h.playerView j) hw_view
    -- tsum_fintype: ∑' a, f a = ∑ a, f a for Fintype
    simp only [tsum_fintype] at htsum
    exact htsum
  simp only [h_each_one, Finset.prod_const_one]

/-! ## Player Value Function -/

/-- Expected discounted reward for player i under joint policy π. -/
noncomputable def playerValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    ∑' (ja : JointAction n),
      ∑' (jp : JointPercept n),
        let actionProb := jointActionProb π h ja
        let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
        ((actionProb * envProb).toReal) *
        ((jp i).reward +
         γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)

/-- Player value is non-negative. -/
theorem playerValue_nonneg {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor)
    (i : Fin n) (h : MultiAgentHistory n) (horizon : ℕ) :
    0 ≤ playerValue μ π γ i h horizon := by
  induction horizon generalizing h with
  | zero => simp [playerValue]
  | succ k ih =>
    simp only [playerValue]
    apply tsum_nonneg
    intro ja
    apply tsum_nonneg
    intro jp
    -- Probability term is non-negative
    have hprob : 0 ≤ (jointActionProb π h ja * μ.prob (h ++ [JointHistElem.act ja]) jp).toReal :=
      ENNReal.toReal_nonneg
    -- Reward is non-negative
    have hrew : 0 ≤ (jp i).reward := Percept.reward_nonneg (jp i)
    -- Discount factor is non-negative
    have hγ : 0 ≤ γ.val := γ.nonneg
    -- Future value is non-negative by induction hypothesis
    have hfuture : 0 ≤ playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k :=
      ih (h ++ [JointHistElem.act ja, JointHistElem.per jp])
    -- Combine: prob * (reward + γ * future) ≥ 0
    exact mul_nonneg hprob (add_nonneg hrew (mul_nonneg hγ hfuture))

/-- Helper: The inner value term is bounded by (k+1). -/
private theorem playerValue_inner_bound {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor) (i : Fin n) (k : ℕ)
    (h : MultiAgentHistory n) (ja : JointAction n) (jp : JointPercept n)
    (ih : ∀ h', playerValue μ π γ i h' k ≤ k) :
    (jp i).reward + γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤ k + 1 := by
  have hrew : (jp i).reward ≤ 1 := Percept.reward_le_one (jp i)
  have hγ : γ.val ≤ 1 := γ.le_one
  have hfuture : playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤ k :=
    ih (h ++ [JointHistElem.act ja, JointHistElem.per jp])
  have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (jp i).reward + γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k
      ≤ 1 + γ.val * k := by
        apply add_le_add hrew
        apply mul_le_mul_of_nonneg_left hfuture γ.nonneg
    _ ≤ 1 + 1 * k := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_right hγ hk_nonneg
    _ = k + 1 := by ring

/-- Player value is bounded by horizon.

    This is the multi-agent analogue of the single-agent `value_le` theorem.
    The proof uses:
    1. `jointActionProb_sum_eq_one`: joint action probabilities sum to 1
    2. `μ.prob_le_one`: environment probabilities sum to ≤ 1
    3. `Percept.reward_le_one`: rewards are in [0,1]
    4. `γ.le_one`: discount factor ≤ 1
    5. `endsWithPercept`: history ends with percept (or is empty) for extension
-/
theorem playerValue_le_horizon {n : ℕ} (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor)
    (i : Fin n) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤ horizon := by
  induction horizon generalizing h hw hep with
  | zero => simp [playerValue]
  | succ k ih =>
    simp only [playerValue]
    -- Convert tsums to finite sums (both types are Fintype)
    rw [tsum_fintype]
    simp only [tsum_fintype]
    -- Now we have: ∑ ja, ∑ jp, prob * (reward + γ * future)
    -- Bound: each term is ≤ prob * (k + 1)
    -- Sum over jp: ∑ jp, prob_ja * prob_jp * bound ≤ prob_ja * bound (since ∑ prob_jp ≤ 1)
    -- Sum over ja: ∑ ja, prob_ja * bound ≤ bound (since ∑ prob_ja = 1)
    calc ∑ ja, ∑ jp, (jointActionProb π h ja * μ.prob (h ++ [JointHistElem.act ja]) jp).toReal *
             ((jp i).reward + γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)
        ≤ ∑ ja : JointAction n, (jointActionProb π h ja).toReal * ((k : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro ja _
          -- The extended history is well-formed for μ.prob_le_one
          -- (multi-agent: action extends well-formed history that ends with percept)
          have hw_ha : (h ++ [JointHistElem.act ja]).wellFormed = true :=
            MultiAgentHistory.wellFormed_append_act h ja hw hep
          -- Environment probabilities sum to ≤ 1 (using tsum_fintype to convert)
          have henv_sum_le_tsum : ∑' jp : JointPercept n, μ.prob (h ++ [JointHistElem.act ja]) jp ≤ 1 :=
            μ.prob_le_one (h ++ [JointHistElem.act ja]) hw_ha
          have henv_sum_le : ∑ jp : JointPercept n, μ.prob (h ++ [JointHistElem.act ja]) jp ≤ 1 := by
            simp only [tsum_fintype] at henv_sum_le_tsum
            exact henv_sum_le_tsum
          -- Each environment probability is finite
          have henv_ne_top : ∀ jp, μ.prob (h ++ [JointHistElem.act ja]) jp ≠ ⊤ :=
            ennreal_term_ne_top_of_sum_le _ henv_sum_le
          -- Joint action probability is finite (≤ 1)
          -- Derive from policy_sum_one: each policy probability is ≤ sum = 1
          have hja_le_one : jointActionProb π h ja ≤ 1 := by
            simp only [jointActionProb]
            apply Finset.prod_le_one
            · intro j _; exact zero_le _
            · intro j _
              -- Agent policy probability ≤ 1 (since policies sum to 1)
              have hpview := MultiAgentHistory.playerView_wellFormed j h hw
              have hsum : (∑' a : Action, (π.agents j).policy (h.playerView j) a) = 1 :=
                (π.agents j).policy_sum_one (h.playerView j) hpview
              have hle : (π.agents j).policy (h.playerView j) (ja j) ≤
                         ∑' a : Action, (π.agents j).policy (h.playerView j) a := by
                simp only [tsum_fintype]
                apply Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ _)
              simpa [hsum] using hle
          have hja_ne_top : jointActionProb π h ja ≠ ⊤ :=
            ne_top_of_le_ne_top ENNReal.one_ne_top hja_le_one
          -- Inner term is bounded by (k + 1)
          have hinner_bound : ∀ jp,
              (jp i).reward + γ.val * playerValue μ π γ i
                (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤ k + 1 := by
            intro jp
            have hrew : (jp i).reward ≤ 1 := Percept.reward_le_one (jp i)
            have hγ : γ.val ≤ 1 := γ.le_one
            -- The extended history [h, act, per] is well-formed and ends with percept
            have hext := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
            have hw_ext : (h ++ [JointHistElem.act ja, JointHistElem.per jp]).wellFormed = true :=
              hext.1
            have hep_ext : (h ++ [JointHistElem.act ja, JointHistElem.per jp]).endsWithPercept = true :=
              hext.2
            have hfuture : playerValue μ π γ i
                (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤ k :=
              ih (h ++ [JointHistElem.act ja, JointHistElem.per jp]) hw_ext hep_ext
            have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            calc (jp i).reward + γ.val * playerValue μ π γ i
                    (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k
                ≤ 1 + γ.val * k := by
                  apply add_le_add hrew
                  apply mul_le_mul_of_nonneg_left hfuture γ.nonneg
              _ ≤ 1 + 1 * k := by
                  apply add_le_add_left
                  exact mul_le_mul_of_nonneg_right hγ hk_nonneg
              _ = k + 1 := by ring
          -- Weights sum to ≤ 1 after converting to Real
          have henv_sum_toReal_le : ∑ jp, (μ.prob (h ++ [JointHistElem.act ja]) jp).toReal ≤ 1 :=
            ennreal_sum_toReal_le_one _ henv_sum_le
          -- Factor the sum: ∑ (p * q) * v = p * ∑ q * v
          have hfactored : ∑ jp, (jointActionProb π h ja * μ.prob (h ++ [JointHistElem.act ja]) jp).toReal *
                ((jp i).reward + γ.val * playerValue μ π γ i
                  (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k) =
              (jointActionProb π h ja).toReal * ∑ jp, (μ.prob (h ++ [JointHistElem.act ja]) jp).toReal *
                ((jp i).reward + γ.val * playerValue μ π γ i
                  (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k) := by
            -- Step 1: Rewrite toReal of product
            conv_lhs =>
              arg 2
              ext jp
              rw [ENNReal.toReal_mul]
            -- Step 2: Factor out the constant (jointActionProb π h ja).toReal
            conv_lhs =>
              arg 2
              ext jp
              rw [mul_assoc]
            rw [← Finset.mul_sum]
          rw [hfactored]
          -- Apply weighted average bound to the inner sum
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          apply weighted_sum_le_bound _ _ ((k : ℝ) + 1)
          · intro jp; exact ENNReal.toReal_nonneg
          · exact henv_sum_toReal_le
          · exact hinner_bound
          · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
      _ ≤ (k : ℝ) + 1 := by
          -- Joint action probabilities sum to 1
          have hja_sum_eq : ∑ ja : JointAction n, jointActionProb π h ja = 1 :=
            jointActionProb_sum_eq_one π h hw
          -- Convert to Real sum = 1
          have hja_toReal_sum_eq : ∑ ja, (jointActionProb π h ja).toReal = 1 :=
            ennreal_sum_toReal_eq_one _ hja_sum_eq
          -- Sum of w_a * c = c * ∑ w_a = c when ∑ w_a = 1
          calc ∑ ja, (jointActionProb π h ja).toReal * ((k : ℝ) + 1)
              = ∑ ja, ((k : ℝ) + 1) * (jointActionProb π h ja).toReal := by
                congr 1; ext ja; ring
            _ = ((k : ℝ) + 1) * ∑ ja, (jointActionProb π h ja).toReal := by
                rw [← Finset.mul_sum]
            _ = ((k : ℝ) + 1) * 1 := by rw [hja_toReal_sum_eq]
            _ ≤ (k : ℝ) + 1 := by ring_nf; rfl
      _ = ((k + 1 : ℕ) : ℝ) := by norm_cast

/-! ## Q-Value Function -/

/-- Expected value for player i when forcing action a, then following π. -/
noncomputable def playerQValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    -- Sum over all possible joint actions
    ∑' (ja : JointAction n),
      -- Check if player i takes the forced action
      if ja i = action then
        -- Compute probability of other players' actions
        let othersProb : ENNReal :=
          Finset.prod (Finset.univ.erase i) fun j =>
            (π.agents j).policy (h.playerView j) (ja j)
        ∑' (jp : JointPercept n),
          let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
          ((othersProb * envProb).toReal) *
          ((jp i).reward +
           γ.val * playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)
      else
        0

/-! ## Best Response Value (True Optimal Play)

The best response value represents what player i can achieve by playing **optimally at every step**,
while other players follow their policies π_j. This is the standard game-theoretic definition.

Key difference from `playerQValue`:
- `playerQValue μ π` uses `playerValue μ π` in recursion (player i follows π_i in future)
- `bestResponseQValue μ π` uses `bestResponseValue μ π` in recursion (player i optimizes in future)

These are mutually recursive definitions.
-/

mutual
/-- Q-value when player i plays optimally in all future steps.
    Other players follow their policies π_j for j ≠ i. -/
noncomputable def bestResponseQValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | k + 1 =>
    ∑' (ja : JointAction n),
      if ja i = action then
        let othersProb : ENNReal :=
          Finset.prod (Finset.univ.erase i) fun j =>
            (π.agents j).policy (h.playerView j) (ja j)
        ∑' (jp : JointPercept n),
          let envProb := μ.prob (h ++ [JointHistElem.act ja]) jp
          ((othersProb * envProb).toReal) *
          ((jp i).reward +
           γ.val * bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k)
      else
        0

/-- Maximum value player i can achieve by choosing actions optimally at EVERY step.
    Other players follow their policies π_j for j ≠ i.

    This is the standard game-theoretic "best response value":
    V*(h) = max_a Q*(h, a) where Q* uses V* recursively.

    Contrast with playerValue which assumes player i follows π_i. -/
noncomputable def bestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  ⨆ (action : Action), bestResponseQValue μ π γ i h action horizon
end

/-! ## One-Step Best Response Value (for comparison)

This is what we originally had - optimizing only the current action,
assuming player i follows π_i in future steps. Useful for some proofs. -/

/-- One-step best response: optimize current action only, then follow π_i.
    This equals ⨆_a playerQValue μ π γ i h a horizon. -/
noncomputable def oneStepBestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) : ℝ :=
  ⨆ (action : Action), playerQValue μ π γ i h action horizon

/-- Weighted average is ≤ supremum for finite types with nonnegative weights summing to 1. -/
theorem weighted_avg_le_ciSup {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (x : α → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a)
    (hw_sum : ∑ a, w a = 1) :
    ∑ a, w a * x a ≤ ⨆ a, x a := by
  have hbdd : BddAbove (Set.range x) := Set.Finite.bddAbove (Set.finite_range x)
  calc ∑ a, w a * x a
      ≤ ∑ a, w a * (⨆ a, x a) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hw_nonneg a)
        exact le_ciSup hbdd a
    _ = (⨆ a, x a) * ∑ a, w a := by rw [← Finset.sum_mul]; ring
    _ = (⨆ a, x a) * 1 := by rw [hw_sum]
    _ = ⨆ a, x a := by ring

/-- Split jointActionProb into player i's probability and others' probability. -/
theorem jointActionProb_split {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (ja : JointAction n) (i : Fin n) :
    jointActionProb π h ja =
    (π.agents i).policy (h.playerView i) (ja i) *
    Finset.prod (Finset.univ.erase i) fun j =>
      (π.agents j).policy (h.playerView j) (ja j) := by
  simp only [jointActionProb]
  -- Split the product at i: ∏ j, f j = f i * ∏ j ≠ i, f j
  conv_lhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]

/-- Probability of other players' actions (excluding player i). -/
noncomputable def othersProb {n : ℕ}
    (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n)
    (ja : JointAction n)
    (i : Fin n) : ENNReal :=
  Finset.prod (Finset.univ.erase i) fun j =>
    (π.agents j).policy (h.playerView j) (ja j)

/-- othersProb is bounded by 1. -/
theorem othersProb_le_one {n : ℕ} (π : MultiAgentPolicy n)
    (h : MultiAgentHistory n) (ja : JointAction n) (i : Fin n)
    (hw : h.wellFormed = true) : othersProb π h ja i ≤ 1 := by
  simp only [othersProb]
  apply Finset.prod_le_one
  · intro j _; exact zero_le _
  · intro j _hj
    have hpview := MultiAgentHistory.playerView_wellFormed j h hw
    have hsum : (∑' a : Action, (π.agents j).policy (h.playerView j) a) = 1 :=
      (π.agents j).policy_sum_one (h.playerView j) hpview
    have hle : (π.agents j).policy (h.playerView j) (ja j) ≤
               ∑' a : Action, (π.agents j).policy (h.playerView j) a := by
      simp only [tsum_fintype]
      apply Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ _)
    simpa [hsum] using hle

/-- Sum over if-then-else: ∑ x, (if x = target then f x else 0) = f target -/
theorem sum_ite_eq_val {α β : Type*} [Fintype α] [AddCommMonoid β] [DecidableEq α]
    (f : α → β) (target : α) :
    ∑ x : α, (if x = target then f x else 0) = f target := by
  have h := Finset.sum_ite_eq' (s := Finset.univ) (a := target) (b := f)
  simp only [Finset.mem_univ, ↓reduceIte] at h
  exact h

/-- Fiber-wise decomposition: ∑_x f(x) = ∑_a ∑_x (if g(x) = a then f(x) else 0) -/
theorem sum_fiberwise {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ] [DecidableEq β]
    (f : α → γ) (g : α → β) :
    ∑ x : α, f x = ∑ b : β, ∑ x : α, (if g x = b then f x else 0) := by
  rw [Finset.sum_comm]
  congr 1
  ext x
  -- Goal: f x = ∑ b, if g x = b then f x else 0
  -- We need: ∑ b, (if g x = b then f x else 0) = f x
  -- Use sum_ite_eq: ∑ x ∈ s, if a = x then b x else 0 = if a ∈ s then b a else 0
  have h := Finset.sum_ite_eq (s := Finset.univ) (a := g x) (b := fun _ => f x)
  simp only [Finset.mem_univ, ↓reduceIte] at h
  exact h.symm

/-- The main decomposition: playerValue = ∑_a π_i(a) * playerQValue(a)

    This is the key lemma connecting playerValue to playerQValue.
    The proof requires careful manipulation of the sum structure:
    1. Factor jointActionProb = π_i(ja i) * othersProb(ja)
    2. Reindex the sum by grouping on (ja i)
    3. Factor out π_i(a) from each fiber
    4. Recognize the remaining sum as playerQValue(a)
-/
theorem playerValue_eq_weighted_qValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon =
    ∑ a : Action, ((π.agents i).policy (h.playerView i) a).toReal *
                  playerQValue μ π γ i h a horizon := by
  match horizon with
  | 0 =>
    simp only [playerValue, playerQValue, mul_zero, Finset.sum_const_zero]
  | k + 1 =>
    simp only [playerValue, playerQValue]
    rw [tsum_fintype]
    simp only [tsum_fintype]
    -- Define the inner function for clarity
    let f : JointAction n → JointPercept n → ℝ := fun ja jp =>
      (jp i).reward + γ.val * playerValue μ π γ i
        (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k
    -- LHS = ∑_{ja} ∑_{jp} jointActionProb(ja) * envProb(jp) * f(ja,jp)
    -- We'll show this equals
    -- RHS = ∑_a π_i(a) * ∑_{ja} (if ja i = a then ∑_{jp} othersProb(ja) * envProb(jp) * f(ja,jp) else 0)
    -- Step 1: Factor jointActionProb = π_i(ja i) * othersProb
    have hfactor : ∀ ja : JointAction n,
        jointActionProb π h ja = (π.agents i).policy (h.playerView i) (ja i) * othersProb π h ja i := by
      intro ja
      rw [jointActionProb_split π h ja i]
      rfl
    -- Transform LHS using the factorization
    conv_lhs =>
      arg 2; ext ja; arg 2; ext jp
      rw [hfactor ja, mul_assoc, ENNReal.toReal_mul, mul_assoc]
    -- Pull out the π_i factor from the inner sum
    conv_lhs =>
      arg 2; ext ja
      rw [← Finset.mul_sum]
    -- Step 2: Use fiber-wise decomposition
    rw [sum_fiberwise _ (fun ja => ja i)]
    -- Step 3: Factor out π_i(a) from each fiber
    congr 1
    ext a
    -- Each summand: if ja i = a then π_i(ja i) * (∑_jp ...) else 0
    --             = π_i(a) * (if ja i = a then ∑_jp ... else 0)
    have hpull : ∀ ja : JointAction n,
        (if ja i = a then
          ((π.agents i).policy (h.playerView i) (ja i)).toReal *
          ∑ jp, (othersProb π h ja i * μ.prob (h ++ [JointHistElem.act ja]) jp).toReal * f ja jp
        else 0) =
        ((π.agents i).policy (h.playerView i) a).toReal *
        (if ja i = a then
          ∑ jp, (othersProb π h ja i * μ.prob (h ++ [JointHistElem.act ja]) jp).toReal * f ja jp
        else 0) := by
      intro ja
      split_ifs with hja
      · rw [hja]
      · ring
    conv_lhs => arg 2; ext ja; rw [hpull ja]
    rw [← Finset.mul_sum]
    -- Step 4: The inner sums match after unfolding definitions
    simp only [othersProb, f]

/-- playerValue ≤ oneStepBestResponseValue (weighted average ≤ supremum).

    **Proof Strategy**:
    1. Use playerValue_eq_weighted_qValue: playerValue = Σ_a π_i(a) * playerQValue(a)
    2. Use that Σ_a π_i(a) = 1 (policy sums to 1)
    3. Apply weighted_avg_le_ciSup: weighted average ≤ supremum
-/
theorem playerValue_le_oneStepBestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤
    oneStepBestResponseValue μ π γ i h horizon := by
  -- Use the decomposition lemma
  rw [playerValue_eq_weighted_qValue μ π γ i h horizon]
  simp only [oneStepBestResponseValue]
  -- Now we have: ∑_a π_i(a) * playerQValue(a) ≤ ⨆_a playerQValue(a)
  -- The weights π_i(a) are non-negative and sum to 1
  have hw_view : (h.playerView i).wellFormed = true :=
    MultiAgentHistory.playerView_wellFormed i h hw
  have hπ_tsum : (∑' a : Action, (π.agents i).policy (h.playerView i) a) = 1 :=
    (π.agents i).policy_sum_one (h.playerView i) hw_view
  -- Convert tsum to Finset.sum (Action is Fintype)
  have hπ_sum : (∑ a : Action, (π.agents i).policy (h.playerView i) a) = 1 := by
    have h := hπ_tsum
    simp only [tsum_fintype] at h
    exact h
  have hπ_sum_real : ∑ a : Action, ((π.agents i).policy (h.playerView i) a).toReal = 1 :=
    ennreal_sum_toReal_eq_one _ hπ_sum
  -- Apply weighted average ≤ supremum
  apply weighted_avg_le_ciSup
  · intro a; exact ENNReal.toReal_nonneg
  · exact hπ_sum_real

/-- playerQValue ≤ bestResponseQValue by induction on horizon.

    The key insight: at horizon k+1, both Q-values have the same structure,
    but playerQValue uses `playerValue ... k` in recursion while
    bestResponseQValue uses `bestResponseValue ... k`.

    By IH at horizon k, we have playerQValue ≤ bestResponseQValue for all actions,
    which gives oneStepBestResponseValue ≤ bestResponseValue,
    which combined with playerValue_le_oneStepBestResponseValue gives
    playerValue ≤ bestResponseValue at horizon k.
-/
theorem playerQValue_le_bestResponseQValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (action : Action)
    (horizon : ℕ) :
    playerQValue μ π γ i h action horizon ≤
    bestResponseQValue μ π γ i h action horizon := by
  -- Generalize over action to get stronger IH
  induction horizon generalizing h hw hep action with
  | zero =>
    simp only [playerQValue, bestResponseQValue, le_refl]
  | succ k ih =>
    simp only [playerQValue, bestResponseQValue]
    rw [tsum_fintype, tsum_fintype]
    apply Finset.sum_le_sum
    intro ja _
    split_ifs with hja
    · -- ja i = action case
      simp only [tsum_fintype]
      apply Finset.sum_le_sum
      intro jp _
      -- Extended history is well-formed and ends with percept
      have hext := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
      have hw' : (h ++ [JointHistElem.act ja, JointHistElem.per jp]).wellFormed = true := hext.1
      have hep' : (h ++ [JointHistElem.act ja, JointHistElem.per jp]).endsWithPercept = true := hext.2
      -- Only difference is the recursive term
      -- playerQValue uses γ * playerValue ... k
      -- bestResponseQValue uses γ * bestResponseValue ... k
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ γ.nonneg
      -- Need: playerValue μ π γ i h' k ≤ bestResponseValue μ π γ i h' k
      -- where h' = h ++ [act ja, per jp]
      -- From IH, we get: ∀ a, playerQValue ... k ≤ bestResponseQValue ... k
      -- This gives: oneStepBestResponseValue ... k ≤ bestResponseValue ... k
      -- Combined with playerValue_le_oneStepBestResponseValue, we get the result
      have ih_qvalue : ∀ a, playerQValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a k ≤
                           bestResponseQValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a k :=
        fun a => ih (h ++ [JointHistElem.act ja, JointHistElem.per jp]) hw' hep' a
      -- oneStepBestResponseValue ≤ bestResponseValue via IH
      have h_onestep_le : oneStepBestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤
                          bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k := by
        simp only [oneStepBestResponseValue, bestResponseValue]
        have hbdd : BddAbove (Set.range fun a => bestResponseQValue μ π γ i
            (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a k) :=
          Set.Finite.bddAbove (Set.finite_range _)
        apply ciSup_le
        intro a
        calc playerQValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a k
            ≤ bestResponseQValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a k :=
              ih_qvalue a
          _ ≤ ⨆ a', bestResponseQValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a' k :=
              le_ciSup hbdd a
      -- playerValue ≤ oneStepBestResponseValue (already proven)
      have h_pv_le_one : playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k ≤
                         oneStepBestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k :=
        playerValue_le_oneStepBestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) hw' k
      -- Combine: playerValue ≤ bestResponseValue
      calc playerValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k
          ≤ oneStepBestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k := h_pv_le_one
        _ ≤ bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k := h_onestep_le
    · -- ja i ≠ action case: both sides are 0
      rfl

/-- oneStepBestResponseValue ≤ bestResponseValue.

    One-step optimization is at most as good as optimizing at every step.
    This follows from playerQValue ≤ bestResponseQValue. -/
theorem oneStepBestResponseValue_le_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    oneStepBestResponseValue μ π γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  simp only [oneStepBestResponseValue, bestResponseValue]
  have hbdd : BddAbove (Set.range fun a => bestResponseQValue μ π γ i h a horizon) :=
    Set.Finite.bddAbove (Set.finite_range _)
  apply ciSup_le
  intro a
  calc playerQValue μ π γ i h a horizon
      ≤ bestResponseQValue μ π γ i h a horizon :=
        playerQValue_le_bestResponseQValue μ π γ i h hw hep a horizon
    _ ≤ ⨆ a', bestResponseQValue μ π γ i h a' horizon :=
        le_ciSup hbdd a

/-- Best response value is at least as good as following the policy.

    This is the main inequality: playing optimally is at least as good as following any policy.
-/
theorem playerValue_le_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    playerValue μ π γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  calc playerValue μ π γ i h horizon
      ≤ oneStepBestResponseValue μ π γ i h horizon :=
        playerValue_le_oneStepBestResponseValue μ π γ i h hw horizon
    _ ≤ bestResponseValue μ π γ i h horizon :=
        oneStepBestResponseValue_le_bestResponseValue μ π γ i h hw hep horizon

end Mettapedia.UniversalAI.MultiAgent
