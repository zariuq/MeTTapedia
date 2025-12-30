import Mettapedia.UniversalAI.MultiAgent.JointActions
import Mettapedia.UniversalAI.BayesianAgents
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Basic

/-!
# Multi-Agent Environments

This file defines multi-agent environments where n agents act simultaneously
and the environment responds with joint percepts.

## Main Definitions

* `MultiAgentEnvironment n`: Environment with n agents acting jointly

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 2

-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-- A multi-agent environment for n agents.

    The environment takes a multi-agent history and a joint action, and produces
    a probability distribution over joint percepts.
-/
structure MultiAgentEnvironment (n : ℕ) where
  /-- Probability of joint percept given multi-agent history. -/
  prob : MultiAgentHistory n → JointPercept n → ENNReal

  /-- Probabilities sum to at most 1 (semimeasure property). -/
  prob_le_one : ∀ h : MultiAgentHistory n,
    h.wellFormed = true →
    (∑' jp : JointPercept n, prob h jp) ≤ 1

/-- The environment assigns zero probability to ill-formed histories. -/
def MultiAgentEnvironment.prob_wellformed {n : ℕ} (μ : MultiAgentEnvironment n)
    (h : MultiAgentHistory n) (jp : JointPercept n) : ENNReal :=
  if h.wellFormed then μ.prob h jp else 0

/-- If the environment gives probability 0 to all joint percepts, then the
    total probability is 0. -/
theorem prob_zero_of_all_zero {n : ℕ} (μ : MultiAgentEnvironment n)
    (h : MultiAgentHistory n) :
    (∀ jp : JointPercept n, μ.prob h jp = 0) →
    (∑' jp : JointPercept n, μ.prob h jp) = 0 := by
  intro hall
  simp only [hall, tsum_zero]

end Mettapedia.UniversalAI.MultiAgent
