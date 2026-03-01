import Mettapedia.UniversalAI.ProblemClasses
import Mettapedia.UniversalAI.TimeBoundedAIXI.Core

/-!
# Chapter 6 ↔ Chapter 7 bridge (Hutter 2005)

This file instantiates the Chapter 7 (core-generic) AIXItl ε-optimality schema
(`Mettapedia.UniversalAI.TimeBoundedAIXI.Core`) to the Chapter 6 embeddings from
`ProblemClasses.lean`.

Other core-generic instantiations (FM, supervised learning) live in
`Mettapedia.UniversalAI.UniversalAIBridgeCore`.
-/

namespace Mettapedia.UniversalAI.UniversalAIBridge

open scoped Classical

open Mettapedia.UniversalAI.TimeBoundedAIXI.Core

namespace SequencePredictionProblem

open Mettapedia.UniversalAI.ProblemClasses
open Mettapedia.UniversalAI.ProblemClasses.SequencePredictionProblem

/-- Well-formedness of the canonical decision history for an observed bit prefix. -/
theorem spDecisionHistory_wellFormed (bits : List Bool) :
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) (spDecisionHistory bits) := by
  induction bits with
  | nil =>
      simp [spDecisionHistory, BayesianAgents.Core.History.wellFormed]
  | cons b bs ih =>
      simp [spDecisionHistory, BayesianAgents.Core.History.wellFormed, ih]

/-- Chapter 7 convergence schema instantiated to the Chapter 6 sequence-prediction environment. -/
theorem aixitl_cycle_eps_optimal_in_sequencePrediction
    (sp : SequencePredictionProblem) (γ : BayesianAgents.Core.DiscountFactor) (t : ℕ)
    (bits : List Bool) (n : ℕ)
    (assumptions : AIXItlConvergenceAssumptions (μ := spToEnvironment sp) (γ := γ) n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits)
                (BayesianAgents.Core.optimalAction (spToEnvironment sp) γ (spDecisionHistory bits) n) n - ε ≤
            BayesianAgents.Core.optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits)
              (aixitl_cycle
                (aixitlFromProofChecker (spToEnvironment sp) γ (n + 1) assumptions.checker.toProofChecker l l_p t)
                (spDecisionHistory bits)) n := by
  intro ε hε
  exact
    aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := spToEnvironment sp) (γ := γ) (t := t)
      (h := spDecisionHistory bits) (n := n) (ε := ε) (hwf := spDecisionHistory_wellFormed (bits := bits))
      (assumptions := assumptions) hε

end SequencePredictionProblem

namespace StrategicGameProblem

open Mettapedia.UniversalAI.ProblemClasses
open Mettapedia.UniversalAI.ProblemClasses.StrategicGameProblem

variable {Action Opp : Type*} [Fintype Action] [Fintype Opp] [Inhabited Action] [Inhabited Opp]

/-- Chapter 7 convergence schema instantiated to the Chapter 6 strategic-game environment. -/
theorem aixitl_cycle_eps_optimal_in_strategicGame
    (sg : StrategicGameProblem Action Opp) (t : ℕ)
    (position : List (Action × Opp)) (n : ℕ)
    (assumptions : AIXItlConvergenceAssumptions (μ := sgToEnvironment (sg := sg)) (γ := gameDiscount) n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount (sgHistory position)
                (BayesianAgents.Core.optimalAction (sgToEnvironment (sg := sg)) gameDiscount (sgHistory position) n) n -
              ε ≤
            BayesianAgents.Core.optimalQValue (sgToEnvironment (sg := sg)) gameDiscount (sgHistory position)
              (aixitl_cycle
                (aixitlFromProofChecker (sgToEnvironment (sg := sg)) gameDiscount (n + 1)
                  assumptions.checker.toProofChecker l l_p t)
                (sgHistory position)) n := by
  intro ε hε
  have hwf :
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept Opp) (sgHistory position) := by
    simpa using (sgHistory_wellFormed (Action := Action) (Opp := Opp) (pos := position))
  exact
    aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := sgToEnvironment (sg := sg))
      (γ := gameDiscount) (t := t) (h := sgHistory position) (n := n) (ε := ε) (hwf := hwf)
      (assumptions := assumptions) hε

end StrategicGameProblem

end Mettapedia.UniversalAI.UniversalAIBridge
