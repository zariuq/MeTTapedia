import Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

namespace Algorithms.MeTTa.Simple.Backend.OptimizedRefinement

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.OptimizedEval
open Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

variable {σ : Type}

theorem evalWithState_eq_reference_of_guard_failure
    (I : Interface σ) (s : σ) (term : Pattern)
    (hFail :
      I.shouldUseDeterministicInStrict term = false ∨
      I.hasDeterministicBlockingRewriteBodies s = true ∨
      I.hasMultipleRootRuleChoices s term = true ∨
      I.isResolvedDeterministicResult
        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = false ∨
      (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
        I.acceptUnchangedDeterministic term) = false) :
    evalWithState I s term = I.evalWithStateCore s term := by
  rcases hFail with hStrictFalse | hRest
  · exact evalWithState_fallback_when_not_strict I s term hStrictFalse
  · by_cases hStrictTrue : I.shouldUseDeterministicInStrict term = true
    · have hBlockedEq :
          I.hasDeterministicBlockingRewriteBodies s = true ∨
          I.hasDeterministicBlockingRewriteBodies s = false := by
          cases hB : I.hasDeterministicBlockingRewriteBodies s <;> simp
      rcases hBlockedEq with hBlockedTrue | hBlockedFalse
      · exact evalWithState_fallback_when_blocked I s term hStrictTrue hBlockedTrue
      · have hMultiEq :
            I.hasMultipleRootRuleChoices s term = true ∨
            I.hasMultipleRootRuleChoices s term = false := by
            cases hM : I.hasMultipleRootRuleChoices s term <;> simp
        rcases hMultiEq with hMultiTrue | hMultiFalse
        · exact evalWithState_fallback_when_multi_root I s term hStrictTrue hBlockedFalse hMultiTrue
        · rcases hRest with hBlockedTrue' | hRest2
          · exact evalWithState_fallback_when_blocked I s term hStrictTrue hBlockedTrue'
          · rcases hRest2 with hMultiTrue' | hRest3
            · exact evalWithState_fallback_when_multi_root I s term hStrictTrue hBlockedFalse hMultiTrue'
            · rcases hRest3 with hResolvedFalse | hAcceptFalse
              · exact
                  evalWithState_fallback_when_unresolved
                    I s term hStrictTrue hBlockedFalse hMultiFalse hResolvedFalse
              · have hResolvedEq :
                    I.isResolvedDeterministicResult
                      ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true ∨
                    I.isResolvedDeterministicResult
                      ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = false := by
                    cases hR :
                      I.isResolvedDeterministicResult
                        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) <;> simp
                rcases hResolvedEq with hResolvedTrue | hResolvedFalse
                · exact
                    evalWithState_fallback_when_unchanged_rejected
                      I s term hStrictTrue hBlockedFalse hMultiFalse hResolvedTrue hAcceptFalse
                · exact
                    evalWithState_fallback_when_unresolved
                      I s term hStrictTrue hBlockedFalse hMultiFalse hResolvedFalse
    · have hStrictFalse' : I.shouldUseDeterministicInStrict term = false := by
        cases hS : I.shouldUseDeterministicInStrict term <;> simp [hS] at hStrictTrue ⊢
      exact evalWithState_fallback_when_not_strict I s term hStrictFalse'

theorem evalWithState_eq_reference_of_deterministic_agreement
    (I : Interface σ)
    (hAgree :
      ∀ (s : σ) (term : Pattern),
        I.shouldUseDeterministicInStrict term = true →
        I.hasDeterministicBlockingRewriteBodies s = false →
        I.hasMultipleRootRuleChoices s term = false →
        I.isResolvedDeterministicResult
          ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true →
        (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
          I.acceptUnchangedDeterministic term) = true →
        evalWithState I s term = I.evalWithStateCore s term)
    (s : σ) (term : Pattern) :
    evalWithState I s term = I.evalWithStateCore s term := by
  by_cases hStrict : I.shouldUseDeterministicInStrict term = true
  · by_cases hBlocked : I.hasDeterministicBlockingRewriteBodies s = false
    · by_cases hMulti : I.hasMultipleRootRuleChoices s term = false
      · by_cases hResolved :
          I.isResolvedDeterministicResult
            ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true
        · by_cases hAccept :
            (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
              I.acceptUnchangedDeterministic term) = true
          · exact hAgree s term hStrict hBlocked hMulti hResolved hAccept
          · have hAcceptFalse :
                (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
                  I.acceptUnchangedDeterministic term) = false := by
                cases hA :
                  (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
                    I.acceptUnchangedDeterministic term) <;> simp [hA] at hAccept ⊢
            exact
              evalWithState_fallback_when_unchanged_rejected
                I s term hStrict hBlocked hMulti hResolved hAcceptFalse
        · have hResolvedFalse :
              I.isResolvedDeterministicResult
                ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = false := by
              cases hR :
                I.isResolvedDeterministicResult
                  ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) <;>
                simp [hR] at hResolved ⊢
          exact evalWithState_fallback_when_unresolved I s term hStrict hBlocked hMulti hResolvedFalse
      · have hMultiTrue : I.hasMultipleRootRuleChoices s term = true := by
          cases hM : I.hasMultipleRootRuleChoices s term <;> simp [hM] at hMulti ⊢
        exact evalWithState_fallback_when_multi_root I s term hStrict hBlocked hMultiTrue
    · have hBlockedTrue : I.hasDeterministicBlockingRewriteBodies s = true := by
        cases hB : I.hasDeterministicBlockingRewriteBodies s <;> simp [hB] at hBlocked ⊢
      exact evalWithState_fallback_when_blocked I s term hStrict hBlockedTrue
  · have hStrictFalse : I.shouldUseDeterministicInStrict term = false := by
      cases hS : I.shouldUseDeterministicInStrict term <;> simp [hS] at hStrict ⊢
    exact evalWithState_fallback_when_not_strict I s term hStrictFalse

end Algorithms.MeTTa.Simple.Backend.OptimizedRefinement
