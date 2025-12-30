import Mettapedia.UniversalAI.MultiAgent.JointActions
import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Multi-Agent Policies

This file defines multi-agent policies and their properties.

## Main Definitions

* `MultiAgentPolicy n`: A policy for each of n agents
* `AgentClass`: A set of agents (for computability)
* `isClosedUnderBayesOptimal`: Policy class closed under best response

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 3

-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-- A multi-agent policy: one policy per agent. -/
structure MultiAgentPolicy (n : ℕ) where
  /-- Policy for each agent. Each agent has a stochastic policy. -/
  agents : Fin n → Agent

/-- Extract agent i's agent from a multi-agent policy. -/
def playerAgent {n : ℕ} (π : MultiAgentPolicy n) (i : Fin n) : Agent :=
  π.agents i

/-- Construct a multi-agent policy from individual agents. -/
def MultiAgentPolicy.mk' {n : ℕ} (agents : Fin n → Agent) : MultiAgentPolicy n :=
  ⟨agents⟩

/-- Two multi-agent policies are equal if all agents are equal. -/
@[ext]
theorem MultiAgentPolicy.ext {n : ℕ} (π₁ π₂ : MultiAgentPolicy n) :
    (∀ i : Fin n, π₁.agents i = π₂.agents i) → π₁ = π₂ := by
  intro h
  cases π₁
  cases π₂
  simp only [mk.injEq]
  funext i
  exact h i

/-- An agent class: a set of agents (stochastic policies). -/
structure AgentClass where
  /-- The set of agents in this class. -/
  agents : Set Agent
  /-- Agent class must be countable (for Δ⁰₂-enumerability). -/
  countable : agents.Countable

/-- An agent class with an explicit enumeration function. -/
structure EnumerableAgentClass extends AgentClass where
  /-- Enumeration function: ℕ → Option Agent -/
  enum : ℕ → Option Agent
  /-- Enumeration is surjective onto the agent class. -/
  enum_surjective : ∀ π ∈ toAgentClass.agents, ∃ n, enum n = some π
  /-- Enumeration only returns agents in the class. -/
  enum_in_class : ∀ n π, enum n = some π → π ∈ toAgentClass.agents

/-- An agent class closed under Bayes-optimal response. -/
structure isClosedUnderBayesOptimal (AgentSet : AgentClass) (br : Type) : Prop where
  closure : True  -- Placeholder until BayesOptimalResponse is defined

/-- The constant agent that always chooses the same action (deterministic). -/
def constantAgent (a : Action) : Agent where
  policy := fun _h a' => if a' = a then 1 else 0
  policy_sum_one := by
    intro h _hw
    rw [tsum_fintype]
    simp [Finset.sum_ite_eq]

/-- Constant agent is in any agent class containing it. -/
theorem constantAgent_in_class {AgentSet : AgentClass} {a : Action} :
    constantAgent a ∈ AgentSet.agents → constantAgent a ∈ AgentSet.agents := id

/-- Example: 2-agent multi-agent policy where both play constant agents. -/
example : MultiAgentPolicy 2 :=
  ⟨fun i =>
    match i with
    | ⟨0, _⟩ => constantAgent Action.left
    | ⟨1, _⟩ => constantAgent Action.right
    | ⟨n+2, h⟩ => by omega⟩

end Mettapedia.UniversalAI.MultiAgent
