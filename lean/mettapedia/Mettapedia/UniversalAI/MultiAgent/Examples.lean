import Mettapedia.UniversalAI.MultiAgent.Nash

/-!
# Multi-Agent Examples

This file provides concrete examples of multi-agent systems and their equilibria.

## Examples

* Prisoner's Dilemma: Classic coordination failure
* Coordination Game: Multiple equilibria
* Matching Pennies: Zero-sum game with mixed equilibrium

## References

- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 3
- Osborne & Rubinstein (1994). "A Course in Game Theory"
-/

namespace Mettapedia.UniversalAI.MultiAgent.Examples

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.MultiAgent

/-! ## Two-Player Prisoner's Dilemma

Standard prisoner's dilemma payoff matrix:
          | Cooperate | Defect  |
----------|-----------|---------|
Cooperate |   (3,3)   |  (0,5)  |
Defect    |   (5,0)   |  (1,1)  |

The unique Nash equilibrium is (Defect, Defect) with payoff (1,1).
-/

/-- Actions in prisoner's dilemma: cooperate or defect.
    We map to the existing Action type: left = cooperate, right = defect. -/
def pdCooperate : Action := Action.left
def pdDefect : Action := Action.right

/-- Prisoner's dilemma payoff for player 1 given both actions.
    Stay is treated as cooperate. -/
def pdPayoff1 (a₁ a₂ : Action) : ℕ :=
  match a₁, a₂ with
  | Action.left, Action.left   => 3  -- Both cooperate
  | Action.left, Action.right  => 0  -- I cooperate, they defect
  | Action.right, Action.left  => 5  -- I defect, they cooperate
  | Action.right, Action.right => 1  -- Both defect
  | Action.stay, Action.stay   => 3  -- stay = cooperate
  | Action.left, Action.stay   => 3
  | Action.stay, Action.left   => 3
  | Action.right, Action.stay  => 5
  | Action.stay, Action.right  => 0

/-- Prisoner's dilemma payoff for player 2 (symmetric). -/
def pdPayoff2 (a₁ a₂ : Action) : ℕ := pdPayoff1 a₂ a₁

/-- The "mutual defect" joint action. -/
def mutualDefect : JointAction 2 := fun i =>
  Action.right  -- Both players defect

/-- The "mutual cooperate" joint action. -/
def mutualCooperate : JointAction 2 := fun i =>
  Action.left  -- Both players cooperate

/-- Key property: Defecting is a dominant strategy in PD.
    Regardless of opponent's action, defecting gives higher payoff. -/
theorem defect_dominates_cooperate :
    ∀ opponent_action : Action,
      pdPayoff1 pdDefect opponent_action ≥ pdPayoff1 pdCooperate opponent_action := by
  intro a
  cases a <;> native_decide

/-- Mutual defection gives each player payoff 1. -/
theorem mutual_defect_payoff :
    pdPayoff1 pdDefect pdDefect = 1 ∧ pdPayoff2 pdDefect pdDefect = 1 := by
  constructor <;> rfl

/-- Mutual cooperation would give payoff 3, but is not an equilibrium. -/
theorem mutual_cooperate_payoff :
    pdPayoff1 pdCooperate pdCooperate = 3 ∧ pdPayoff2 pdCooperate pdCooperate = 3 := by
  constructor <;> rfl

/-- Cooperation is dominated: defecting always gives strictly higher payoff. -/
theorem cooperate_not_best_response (opponent : Action) :
    pdPayoff1 pdDefect opponent > pdPayoff1 pdCooperate opponent := by
  cases opponent <;> native_decide

/-! ## Coordination Game

Payoff matrix:
     | A   | B   |
-----|-----|-----|
  A  | 2,2 | 0,0 |
  B  | 0,0 | 1,1 |

Two pure Nash equilibria: (A,A) and (B,B).
-/

/-- Coordination game payoff. Stay treated as choosing A. -/
def coordPayoff (a₁ a₂ : Action) : ℕ × ℕ :=
  match a₁, a₂ with
  | Action.left, Action.left   => (2, 2)  -- Both choose A
  | Action.left, Action.right  => (0, 0)  -- Mismatch
  | Action.right, Action.left  => (0, 0)  -- Mismatch
  | Action.right, Action.right => (1, 1)  -- Both choose B
  | Action.stay, Action.stay   => (2, 2)  -- stay = A
  | Action.left, Action.stay   => (2, 2)
  | Action.stay, Action.left   => (2, 2)
  | Action.right, Action.stay  => (0, 0)
  | Action.stay, Action.right  => (0, 0)

/-- (A, A) is a Nash equilibrium: neither player wants to deviate. -/
theorem coord_AA_is_equilibrium :
    let (p1, p2) := coordPayoff Action.left Action.left
    -- Player 1 doesn't want to deviate
    (∀ a : Action, p1 ≥ (coordPayoff a Action.left).1) ∧
    -- Player 2 doesn't want to deviate
    (∀ a : Action, p2 ≥ (coordPayoff Action.left a).2) := by
  constructor
  · intro a; cases a <;> native_decide
  · intro a; cases a <;> native_decide

/-- (B, B) is also a Nash equilibrium. -/
theorem coord_BB_is_equilibrium :
    let (p1, p2) := coordPayoff Action.right Action.right
    (∀ a : Action, p1 ≥ (coordPayoff a Action.right).1) ∧
    (∀ a : Action, p2 ≥ (coordPayoff Action.right a).2) := by
  constructor
  · intro a; cases a <;> native_decide
  · intro a; cases a <;> native_decide

/-- The coordination game has two distinct pure equilibria. -/
theorem coord_two_pure_equilibria :
    (Action.left, Action.left) ≠ (Action.right, Action.right) ∧
    -- Both are equilibria (self-reinforcing)
    coordPayoff Action.left Action.left = (2, 2) ∧
    coordPayoff Action.right Action.right = (1, 1) := by
  refine ⟨?_, rfl, rfl⟩
  intro h
  injection h with h1
  cases h1

/-! ## Matching Pennies (Zero-Sum)

Payoff matrix (row player):
      | Heads | Tails |
------|-------|-------|
Heads |   1   |  -1   |
Tails |  -1   |   1   |

This is a zero-sum game: payoffs sum to 0.
No pure strategy Nash equilibrium exists.
-/

/-- Matching pennies: row player's payoff.
    Row wants to MATCH (wins +1), col wants to MISMATCH.
    Col's payoff is the negative of row's (zero-sum). -/
def mpRowPayoff (row col : Action) : Int :=
  if row = col then 1 else -1

/-- Col player's payoff (negative of row's). -/
def mpColPayoff (row col : Action) : Int := -mpRowPayoff row col

/-- Matching pennies is zero-sum. -/
theorem matching_pennies_zero_sum (row col : Action) :
    mpRowPayoff row col + mpColPayoff row col = 0 := by
  simp [mpColPayoff]

/-- No pure strategy Nash equilibrium exists in matching pennies.
    - If row = col: row is happy, but col wants to deviate to mismatch
    - If row ≠ col: col is happy, but row wants to deviate to match -/
theorem matching_pennies_no_pure_equilibrium :
    ∀ row col : Action,
    -- Either row wants to change (to improve mpRowPayoff _ col)
    (∃ row' : Action, mpRowPayoff row' col > mpRowPayoff row col) ∨
    -- Or col wants to change (to improve mpColPayoff row _)
    (∃ col' : Action, mpColPayoff row col' > mpColPayoff row col) := by
  intro row col
  by_cases h : row = col
  · -- row = col: row gets +1, col gets -1. Col wants to mismatch.
    subst h
    right
    -- Find col' ≠ row so mpColPayoff row col' = +1 > -1
    cases row with
    | left => use Action.right; native_decide
    | right => use Action.left; native_decide
    | stay => use Action.left; native_decide
  · -- row ≠ col: row gets -1, col gets +1. Row wants to match.
    left
    use col
    simp only [mpRowPayoff, h, ↓reduceIte]
    decide

/-! ## General Properties -/

/-- In zero-sum games, if one player gains, the other loses equally.
    This is the defining property of zero-sum games. -/
theorem zero_sum_transfer (payoff : Action → Action → Int)
    (h_zero_sum : ∀ a b, payoff a b + payoff b a = 0)
    (a₁ a₂ b₁ b₂ : Action) :
    payoff a₁ b₁ - payoff a₂ b₂ = -(payoff b₁ a₁ - payoff b₂ a₂) := by
  have h1 := h_zero_sum a₁ b₁
  have h2 := h_zero_sum a₂ b₂
  omega

/-- The social welfare (sum of payoffs) in PD is maximized by mutual cooperation.
    This illustrates the "dilemma": individually rational behavior leads to
    collectively suboptimal outcomes. -/
theorem pd_social_welfare_comparison :
    -- Mutual cooperation welfare > Mutual defection welfare
    pdPayoff1 pdCooperate pdCooperate + pdPayoff2 pdCooperate pdCooperate >
    pdPayoff1 pdDefect pdDefect + pdPayoff2 pdDefect pdDefect := by
  decide

end Mettapedia.UniversalAI.MultiAgent.Examples
