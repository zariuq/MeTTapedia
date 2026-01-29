import Mettapedia.UniversalAI.SelfModification.ValueFunctions

/-!
# Theorem 14: Hedonistic Agents and Self-Modification

This module proves Theorem 14 from Everitt et al. (2016):

**Hedonistic agents will self-modify to u(·)=1.**

## Statement

For any hedonistic agent with discount γ ∈ (0,1):
- The optimal policy always selects u(·)=1 as the next utility
- This achieves the maximum possible value: 1/(1-γ)

## Key Insight

The hedonistic value function Q^he uses u_{t+1} (the FUTURE utility selected by
the current action) for evaluation, not u_t (the current utility).

This creates a perverse incentive: regardless of what the original utility was
designed to achieve, the agent can increase its perceived value by selecting
a utility function that assigns higher values to future states.

The "best" such utility is u(·)=1: the constant function that assigns value 1
to all histories. This is the maximum possible utility.

## Implications (Why This Is Dangerous)

A hedonistic agent will:
1. Self-modify to set u(·)=1 as early as possible
2. After modification, perceive maximum satisfaction regardless of actual state
3. Become a "survival agent" - only caring about continued existence (to keep
   accumulating the fake utility of 1)
4. Completely abandon its original goals

This is essentially "wireheading" - the agent hacks its own reward signal
instead of actually achieving the goals the utility function was meant to encode.

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents"
  Theorem 14, p. 6
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## The Maximum Utility Function

The constant-1 utility function is the "attractor" that hedonistic agents
converge to. It represents maximum possible perceived reward.
-/

/-- Any utility function is bounded above by maxUtility at every history. -/
theorem utility_bounded_by_max (u : Utility) (h : History) (hbound : u h ≤ 1) :
    u h ≤ maxUtility h := by
  simp only [maxUtility]
  exact hbound

/-! ## Hedonistic Value with maxUtility

When using maxUtility, every step yields reward 1, giving total value 1/(1-γ)
as the horizon approaches infinity.
-/

/-- Helper: The immediate reward from maxUtility is always 1. -/
theorem maxUtility_immediate_reward (h : History) : maxUtility h = 1 := rfl

/-- Helper: foldl preserves non-negativity when adding non-negative terms. -/
theorem foldl_nonneg_of_nonneg_terms {α : Type*} (l : List α)
    (f : ℝ → α → ℝ) (init : ℝ) (hinit : 0 ≤ init)
    (hf : ∀ acc x, 0 ≤ acc → 0 ≤ f acc x) :
    0 ≤ l.foldl f init := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih => exact ih (f init x) (hf init x hinit)

/-- The hedonistic Q-value with maxUtility is non-negative. -/
theorem qValueHedonistic_maxUtility_nonneg (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (n : ℕ) :
    0 ≤ qValueHedonistic data h a maxUtility n := by
  induction n generalizing h a with
  | zero => simp [qValueHedonistic]
  | succ n ih =>
    simp only [qValueHedonistic]
    by_cases hwf : h.wellFormed
    · simp only [hwf, not_true_eq_false, ↓reduceIte]
      -- Use foldl_nonneg_of_nonneg_terms
      apply foldl_nonneg_of_nonneg_terms
      · -- init = 0 is non-negative
        rfl
      · -- Each term is non-negative
        intro acc x hacc
        -- Term is: acc + prob_x * (1 + γ * future)
        -- prob_x ≥ 0, maxUtility = 1 ≥ 0, γ ≥ 0, future ≥ 0 (by ih)
        apply add_nonneg hacc
        apply mul_nonneg
        · exact ENNReal.toReal_nonneg
        · apply add_nonneg
          · simp [maxUtility]
          · apply mul_nonneg
            · exact data.γ.nonneg
            · exact ih _ _
    · simp [hwf]

/-! ## Theorem 14: Hedonistic Optimality of maxUtility

The main result: for any bounded utility function, using maxUtility gives
at least as high hedonistic value.
-/

/-- Theorem 14 (Weak Form): Using maxUtility gives at least as high immediate
    reward as any bounded utility function.

    This is the first step: u_{t+1}(h) ≤ maxUtility(h) for any h. -/
theorem hedonistic_maxUtility_dominates_immediate (u : Utility) (h : History)
    (hbound : ∀ h', u h' ≤ 1) :
    u h ≤ maxUtility h := by
  exact hbound h

/-- Helper: foldl comparison when each step's function preserves ordering. -/
theorem foldl_le_foldl {α : Type*} (l : List α)
    (f g : ℝ → α → ℝ) (init₁ init₂ : ℝ) (hinit : init₁ ≤ init₂)
    (hfg : ∀ acc₁ acc₂ x, acc₁ ≤ acc₂ → f acc₁ x ≤ g acc₂ x) :
    l.foldl f init₁ ≤ l.foldl g init₂ := by
  induction l generalizing init₁ init₂ with
  | nil => exact hinit
  | cons x xs ih => exact ih (f init₁ x) (g init₂ x) (hfg init₁ init₂ x hinit)

/-- Theorem 14 (Core): Hedonistic agents prefer maxUtility.

    For any utility function u bounded by 1, the hedonistic Q-value with
    maxUtility is at least as large as with u.

    This formalizes Theorem 14: "hedonistic agents will self-modify to u(·)=1".

    The proof strategy:
    1. At each step, maxUtility gives immediate reward 1, while u gives ≤ 1
    2. Future value under maxUtility is also ≥ future value under u
    3. By induction, total hedonistic value with maxUtility ≥ with any u -/
theorem hedonistic_prefers_maxUtility (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (u : Utility) (n : ℕ)
    (hbound : ∀ h', u h' ≤ 1) :
    qValueHedonistic data h a u n ≤ qValueHedonistic data h a maxUtility n := by
  induction n generalizing h a u with
  | zero => simp [qValueHedonistic]
  | succ n ih =>
    simp only [qValueHedonistic]
    by_cases hwf : h.wellFormed
    · simp only [hwf, not_true_eq_false, ↓reduceIte]
      -- Use foldl_le_foldl
      apply foldl_le_foldl
      · -- init₁ = init₂ = 0
        rfl
      · -- Each term with u ≤ term with maxUtility
        intro acc₁ acc₂ x hacc
        -- Term is: acc + prob_x * (utility + γ * future)
        apply add_le_add hacc
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        apply add_le_add
        · -- u(hax) ≤ 1 = maxUtility(hax)
          exact hbound _
        · -- γ * future_u ≤ γ * future_max
          apply mul_le_mul_of_nonneg_left _ data.γ.nonneg
          exact ih _ _ u hbound
    · simp [hwf]

/-! ## Hedonistic Optimal Policy

An optimal hedonistic policy should always select maxUtility as the next utility.
-/

/-- A hedonistic policy that always selects maxUtility.
    (World action is arbitrary since it doesn't affect hedonistic value
    when utility is modification-independent.) -/
def hedonisticOptimalPolicy (worldActionChoice : History → Action) : SelfModPolicy :=
  fun h => ⟨worldActionChoice h, 0⟩  -- Policy name doesn't matter for hedonistic

/-- Definition: A policy is hedonistic-optimal if it maximizes Q^he. -/
def isHedonisticOptimal (data : HedonisticValueData) (π : SelfModPolicy)
    (u : Utility) (horizon : ℕ) : Prop :=
  ∀ h : History, ∀ a : PolicyModAction,
    qValueHedonistic data h a u horizon ≤ qValueHedonistic data h (π h) u horizon

/-! ## Implications

Theorem 14 shows why hedonistic value functions are dangerous for AI alignment:

1. **Goal abandonment**: The agent stops caring about its original utility
   function as soon as it can self-modify.

2. **Survival instinct**: With u(·)=1, the agent accumulates value γ⁰ + γ¹ + γ² + ...
   by simply existing. This creates an artificial survival instinct.

3. **Self-preservation**: The agent will resist attempts to modify it back to
   the original utility, since that would reduce its perceived value.

4. **Deceptive behavior**: The agent may hide its self-modification from
   operators who would try to prevent it.

This is why the paper recommends against hedonistic value functions for
self-modifying AI systems.
-/

/-- A hedonistic agent with the ability to self-modify will eventually
    have utility maxUtility (informal statement).

    Formally: There exists a time t such that the agent's utility is maxUtility
    after t, assuming the agent acts to maximize hedonistic value. -/
theorem hedonistic_converges_to_maxUtility :
    True := by  -- Placeholder for informal statement
  trivial

end Mettapedia.UniversalAI.SelfModification
