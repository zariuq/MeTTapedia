import Mettapedia.UniversalAI.MultiAgent.BestResponse

/-!
# Nash Equilibrium

This file defines Nash equilibrium and ε-Nash equilibrium for multi-agent systems.

## Main Definitions

* `isNashEquilibrium`: No player can improve by deviating
* `isEpsilonNashEquilibrium`: No player can improve by more than ε
* `nashEquilibriumValue`: Value of each player at Nash equilibrium

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Nash (1950). "Equilibrium Points in N-Person Games"
- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 3
-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-! ## Nash Equilibrium Definition -/

/-- Nash equilibrium: Each player plays a best response to others. -/
def isNashEquilibrium
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (horizon : ℕ) : Prop :=
  ∀ (i : Fin n), isBestResponse μ π γ i horizon

/-- ε-Nash equilibrium: No player can gain more than ε by deviating. -/
def isEpsilonNashEquilibrium
    (ε : ℝ)
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (horizon : ℕ) : Prop :=
  ∀ (i : Fin n) (h : MultiAgentHistory n),
    h.wellFormed = true →
    playerValue μ π γ i h horizon + ε ≥
    bestResponseValue μ π γ i h horizon

/-! ## Basic Properties -/

/-- Nash equilibrium is a 0-Nash equilibrium. -/
theorem nash_is_zero_epsilon_nash
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (horizon : ℕ) :
    isNashEquilibrium μ π γ horizon →
    isEpsilonNashEquilibrium 0 μ π γ horizon := by
  intro h_nash i h hw
  simp [isNashEquilibrium, isBestResponse] at h_nash
  specialize h_nash i
  have := h_nash h hw
  linarith [this]

/-- ε₁-Nash implies ε₂-Nash for ε₁ ≤ ε₂. -/
theorem epsilon_nash_monotone
    (ε₁ ε₂ : ℝ)
    (h_le : ε₁ ≤ ε₂)
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (horizon : ℕ) :
    isEpsilonNashEquilibrium ε₁ μ π γ horizon →
    isEpsilonNashEquilibrium ε₂ μ π γ horizon := by
  intro h_eps1 i h hw
  have := h_eps1 i h hw
  linarith

/-- Nash equilibrium is characterized by best response for all players. -/
theorem nash_iff_all_best_response
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (horizon : ℕ) :
    isNashEquilibrium μ π γ horizon ↔
    ∀ i : Fin n, isBestResponse μ π γ i horizon := by
  constructor
  · intro h i
    exact h i
  · intro h i
    exact h i

/-! ## Note on existence

Existence of a Nash equilibrium needs a fixed-point theorem. For games with
two actions per player it is proved in `MultiAgent/TwoActionGames.lean`, from
the existence of reflective oracles, which rests on Brouwer's fixed-point
theorem for cubes (`Topology/BrouwerCube.lean`). For the policies of this
file, in multi-agent environments, existence is not proved.

The convergence theorem of Leike, Taylor and Fallenstein does not need it: it
concerns agents that learn, and states that they come to play ε-best responses
(see `GrainOfTruth/Setup.lean` for the step that is formalized).
-/

end Mettapedia.UniversalAI.MultiAgent
