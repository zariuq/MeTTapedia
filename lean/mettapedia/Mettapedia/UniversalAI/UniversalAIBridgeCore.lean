import Mettapedia.UniversalAI.ProblemClasses
import Mettapedia.UniversalAI.TimeBoundedAIXI.Core

/-!
# Chapter 6 ↔ Chapter 7 bridge (core-generic alphabets)

`ProblemClasses.lean` models several Chapter 6 reductions using the **generic**
`BayesianAgents.Core` API (problem-specific action/percept alphabets).

`TimeBoundedAIXI.Core` provides the Chapter 7 ε-optimality / proof-enumeration convergence schema
over the same core API, so we can state “Chapter 7 implies computable ε-optimality” corollaries
for these Chapter 6 environments.
-/

namespace Mettapedia.UniversalAI.UniversalAIBridgeCore

open scoped Classical

open Mettapedia.UniversalAI.ProblemClasses
open Mettapedia.UniversalAI.TimeBoundedAIXI.Core

namespace FunctionMinimizationProblem

open Mettapedia.UniversalAI.ProblemClasses.FunctionMinimizationProblem

/-- Chapter 7 convergence schema instantiated to the Chapter 6 function-minimization environment. -/
theorem aixitl_cycle_eps_optimal_in_functionMinimization
    (fm : FunctionMinimizationProblem) [Inhabited fm.Action]
    (γ : BayesianAgents.Core.DiscountFactor) (t : ℕ)
    (h : BayesianAgents.Core.History fm.Action (Percept fm)) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := fm.Action) (Percept := Percept fm) h)
    (checker :
      Mettapedia.UniversalAI.TimeBoundedAIXI.CompleteProofChecker
        (ValidValueLowerBound (toEnvironment fm) γ (n + 1)))
    (hex :
      ∀ ε : ℝ,
        0 < ε →
          ∃ p : ExtendedChronologicalProgram fm.Action (Percept fm),
            ValidValueLowerBound (toEnvironment fm) γ (n + 1) p ∧
              BayesianAgents.Core.optimalQValue (toEnvironment fm) γ h
                    (BayesianAgents.Core.optimalAction (toEnvironment fm) γ h n) n - ε ≤
                  (p.compute h).1) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (toEnvironment fm) γ h
                (BayesianAgents.Core.optimalAction (toEnvironment fm) γ h n) n - ε ≤
            BayesianAgents.Core.optimalQValue (toEnvironment fm) γ h
              (aixitl_cycle
                (aixitlFromProofChecker (toEnvironment fm) γ (n + 1) checker.toProofChecker l l_p t) h) n := by
  intro ε hε
  rcases hex ε hε with ⟨p, hpValid, hpClaim⟩
  rcases
      aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program'
        (μ := toEnvironment fm) (γ := γ) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
        (hex := ⟨p, hpValid, hpClaim⟩) with
    ⟨l, N, hN⟩
  exact ⟨l, N, hN⟩

/-- Chapter 7 packaged convergence assumptions instantiated to the Chapter 6 function-minimization environment. -/
theorem aixitl_cycle_eps_optimal_in_functionMinimization_of_convergenceAssumptions
    (fm : FunctionMinimizationProblem) [Inhabited fm.Action]
    (γ : BayesianAgents.Core.DiscountFactor) (t : ℕ)
    (h : BayesianAgents.Core.History fm.Action (Percept fm)) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := fm.Action) (Percept := Percept fm) h)
    (assumptions : AIXItlConvergenceAssumptions (μ := toEnvironment fm) (γ := γ) n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (toEnvironment fm) γ h
                (BayesianAgents.Core.optimalAction (toEnvironment fm) γ h n) n - ε ≤
            BayesianAgents.Core.optimalQValue (toEnvironment fm) γ h
              (aixitl_cycle
                (aixitlFromProofChecker (toEnvironment fm) γ (n + 1) assumptions.checker.toProofChecker l l_p t) h) n := by
  intro ε hε
  exact
    aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := toEnvironment fm) (γ := γ) (t := t)
      (h := h) (n := n) (ε := ε) (hwf := hwf) (assumptions := assumptions) hε

end FunctionMinimizationProblem

namespace SupervisedLearningProblem

open Mettapedia.UniversalAI.ProblemClasses.SupervisedLearningProblem

/-- Chapter 7 convergence schema instantiated to the Chapter 6 supervised-learning environment. -/
theorem aixitl_cycle_eps_optimal_in_supervisedLearning
    (ex : SupervisedLearningProblem) [Inhabited ex.V]
    (γ : BayesianAgents.Core.DiscountFactor) (t : ℕ)
    (h : BayesianAgents.Core.History ex.V (Percept ex)) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := ex.V) (Percept := Percept ex) h)
    (checker :
      Mettapedia.UniversalAI.TimeBoundedAIXI.CompleteProofChecker
        (ValidValueLowerBound (toEnvironment ex) γ (n + 1)))
    (hex :
      ∀ ε : ℝ,
        0 < ε →
          ∃ p : ExtendedChronologicalProgram ex.V (Percept ex),
            ValidValueLowerBound (toEnvironment ex) γ (n + 1) p ∧
              BayesianAgents.Core.optimalQValue (toEnvironment ex) γ h
                    (BayesianAgents.Core.optimalAction (toEnvironment ex) γ h n) n - ε ≤
                  (p.compute h).1) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (toEnvironment ex) γ h
                (BayesianAgents.Core.optimalAction (toEnvironment ex) γ h n) n - ε ≤
            BayesianAgents.Core.optimalQValue (toEnvironment ex) γ h
              (aixitl_cycle
                (aixitlFromProofChecker (toEnvironment ex) γ (n + 1) checker.toProofChecker l l_p t) h) n := by
  intro ε hε
  rcases hex ε hε with ⟨p, hpValid, hpClaim⟩
  rcases
      aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program'
        (μ := toEnvironment ex) (γ := γ) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
        (hex := ⟨p, hpValid, hpClaim⟩) with
    ⟨l, N, hN⟩
  exact ⟨l, N, hN⟩

/-- Chapter 7 packaged convergence assumptions instantiated to the Chapter 6 supervised-learning environment. -/
theorem aixitl_cycle_eps_optimal_in_supervisedLearning_of_convergenceAssumptions
    (ex : SupervisedLearningProblem) [Inhabited ex.V]
    (γ : BayesianAgents.Core.DiscountFactor) (t : ℕ)
    (h : BayesianAgents.Core.History ex.V (Percept ex)) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := ex.V) (Percept := Percept ex) h)
    (assumptions : AIXItlConvergenceAssumptions (μ := toEnvironment ex) (γ := γ) n) :
    ∀ ε : ℝ,
      0 < ε →
        ∃ l N, ∀ l_p ≥ N,
          BayesianAgents.Core.optimalQValue (toEnvironment ex) γ h
                (BayesianAgents.Core.optimalAction (toEnvironment ex) γ h n) n - ε ≤
            BayesianAgents.Core.optimalQValue (toEnvironment ex) γ h
              (aixitl_cycle
                (aixitlFromProofChecker (toEnvironment ex) γ (n + 1) assumptions.checker.toProofChecker l l_p t) h) n := by
  intro ε hε
  exact
    aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually (μ := toEnvironment ex) (γ := γ) (t := t)
      (h := h) (n := n) (ε := ε) (hwf := hwf) (assumptions := assumptions) hε

end SupervisedLearningProblem

end Mettapedia.UniversalAI.UniversalAIBridgeCore
