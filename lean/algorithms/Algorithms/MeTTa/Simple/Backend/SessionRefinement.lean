import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Backend.SessionReference

namespace Algorithms.MeTTa.Simple.Backend.SessionRefinement

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple

abbrev SessionWF : Session → Prop := SessionReference.SessionWF

def DeterministicAcceptedRaw (s : Session) (term : Pattern) : Prop :=
  Session.optimizedBackendInterface.shouldUseDeterministicInStrict term = true ∧
  Session.optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false ∧
  Session.optimizedBackendInterface.hasMultipleRootRuleChoices
    (Session.withCompiledIndexes s false) term = false ∧
  Session.optimizedBackendInterface.isResolvedDeterministicResult
    ((Session.optimizedBackendInterface.evalDeterministicCore s
      (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2) = true ∧
  (((Session.optimizedBackendInterface.evalDeterministicCore s
      (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2 != term) ||
    Session.optimizedBackendInterface.acceptUnchangedDeterministic term) = true

private theorem optimizedCoreEq
    (s : Session) (term : Pattern) :
    Session.optimizedBackendInterface.evalWithStateCore s term =
      SessionReference.evalWithStateCore s term := by
  simpa [SessionReference.evalWithStateCore] using
    Session.optimizedBackendInterface_evalWithStateCore_eq_reference s term

theorem evalWithState_eq_reference_of_deterministic_agreement_raw_guard
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    Session.evalWithState s term = SessionReference.evalWithStateCore s term := by
  have hAgreeRaw' :
      ∀ (s : Session) (term : Pattern),
        Session.optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        Session.optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        Session.optimizedBackendInterface.hasMultipleRootRuleChoices
          (Session.withCompiledIndexes s false) term = false →
        Session.optimizedBackendInterface.isResolvedDeterministicResult
          ((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2 != term) ||
          Session.optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        Session.optimizedBackendInterface.evalWithStateCore s term := by
    intro s term h1 h2 h3 h4 h5
    rw [optimizedCoreEq s term]
    exact hAgreeRaw s term ⟨h1, h2, h3, h4, h5⟩
  have hEq :
      Session.evalWithState s term =
        Session.optimizedBackendInterface.evalWithStateCore s term :=
    Session.evalWithState_eq_reference_of_deterministic_agreement_raw_guard
      (s := s) (term := term) hs hAgreeRaw'
  rw [optimizedCoreEq s term] at hEq
  exact hEq

theorem wf_evalWithState_of_reference_and_deterministic_agreement
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReference.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.evalWithState s term).1 := by
  have hCorePres' :
      ∀ (s : Session) (term : Pattern),
        Session.CompiledConsistent s →
        Session.CompiledConsistent (Session.optimizedBackendInterface.evalWithStateCore s term).1 := by
    intro s term hs
    rw [optimizedCoreEq s term]
    exact hCorePres s term hs
  have hAgreeRaw' :
      ∀ (s : Session) (term : Pattern),
        Session.optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        Session.optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        Session.optimizedBackendInterface.hasMultipleRootRuleChoices
          (Session.withCompiledIndexes s false) term = false →
        Session.optimizedBackendInterface.isResolvedDeterministicResult
          ((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2 != term) ||
          Session.optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        Session.optimizedBackendInterface.evalWithStateCore s term := by
    intro s term h1 h2 h3 h4 h5
    rw [optimizedCoreEq s term]
    exact hAgreeRaw s term ⟨h1, h2, h3, h4, h5⟩
  exact
    Session.compiledConsistent_evalWithState_of_reference_and_deterministic_agreement
      hCorePres' s term hs hAgreeRaw'

theorem wf_applyStmt_eval_of_reference_and_deterministic_agreement
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        SessionWF s →
        SessionWF (SessionReference.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : SessionWF s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        DeterministicAcceptedRaw s term →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        SessionReference.evalWithStateCore s term) :
    SessionWF (Session.applyStmt s (.eval term)).1 := by
  have hCorePres' :
      ∀ (s : Session) (term : Pattern),
        Session.CompiledConsistent s →
        Session.CompiledConsistent (Session.optimizedBackendInterface.evalWithStateCore s term).1 := by
    intro s term hs
    rw [optimizedCoreEq s term]
    exact hCorePres s term hs
  have hAgreeRaw' :
      ∀ (s : Session) (term : Pattern),
        Session.optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        Session.optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        Session.optimizedBackendInterface.hasMultipleRootRuleChoices
          (Session.withCompiledIndexes s false) term = false →
        Session.optimizedBackendInterface.isResolvedDeterministicResult
          ((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((Session.optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (Session.optimizedBackendInterface.maxNodes s)) term).2 != term) ||
          Session.optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          Session.optimizedBackendInterface s term =
        Session.optimizedBackendInterface.evalWithStateCore s term := by
    intro s term h1 h2 h3 h4 h5
    rw [optimizedCoreEq s term]
    exact hAgreeRaw s term ⟨h1, h2, h3, h4, h5⟩
  exact
    Session.compiledConsistent_applyStmt_eval_of_reference_and_deterministic_agreement
      hCorePres' s term hs hAgreeRaw'

end Algorithms.MeTTa.Simple.Backend.SessionRefinement
