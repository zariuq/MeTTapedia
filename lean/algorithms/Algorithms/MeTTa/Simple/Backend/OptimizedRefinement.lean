import Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

namespace Algorithms.MeTTa.Simple.Backend.OptimizedRefinement

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.OptimizedEval
open Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

variable {σ : Type}

private theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

private theorem bool_eq_true_of_ne_false {b : Bool} (h : ¬(b = false)) : b = true := by
  cases b <;> simp_all

theorem evalWithState_eq_reference_of_guard_failure
    (I : Interface σ) (s : σ) (term : Pattern)
    (hFail :
      I.shouldUseDeterministicInStrict term = false ∨
      I.hasDeterministicBlockingRewriteBodies s = true ∨
      I.hasMultipleRootRuleChoices s term = true ∨
      I.noDeterministicReducerOverlap s = false ∨
      I.noCoreBuiltinOverrides s = false ∨
      I.isResolvedDeterministicResult
        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = false ∨
      (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
        I.acceptUnchangedDeterministic term) = false) :
    evalWithState I s term = I.evalWithStateCore s term := by
  rcases hFail with hStrictFalse | hBlockedTrue | hMultiTrue | hOverlapFalse | hCoreFalse | hResolvedFalse | hAcceptFalse
  · exact evalWithState_fallback_when_not_strict I s term hStrictFalse
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · exact evalWithState_fallback_when_blocked I s term hS hBlockedTrue
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · by_cases hB : I.hasDeterministicBlockingRewriteBodies s = false
      · exact evalWithState_fallback_when_multi_root I s term hS hB hMultiTrue
      · exact evalWithState_fallback_when_blocked I s term hS (bool_eq_true_of_ne_false hB)
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · by_cases hB : I.hasDeterministicBlockingRewriteBodies s = false
      · by_cases hM : I.hasMultipleRootRuleChoices s term = false
        · exact evalWithState_fallback_when_overlap I s term hS hB hM hOverlapFalse
        · exact evalWithState_fallback_when_multi_root I s term hS hB (bool_eq_true_of_ne_false hM)
      · exact evalWithState_fallback_when_blocked I s term hS (bool_eq_true_of_ne_false hB)
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · by_cases hB : I.hasDeterministicBlockingRewriteBodies s = false
      · by_cases hM : I.hasMultipleRootRuleChoices s term = false
        · by_cases hO : I.noDeterministicReducerOverlap s = true
          · exact evalWithState_fallback_when_core_override I s term hS hB hM hO hCoreFalse
          · exact evalWithState_fallback_when_overlap I s term hS hB hM (bool_eq_false_of_ne_true hO)
        · exact evalWithState_fallback_when_multi_root I s term hS hB (bool_eq_true_of_ne_false hM)
      · exact evalWithState_fallback_when_blocked I s term hS (bool_eq_true_of_ne_false hB)
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · by_cases hB : I.hasDeterministicBlockingRewriteBodies s = false
      · by_cases hM : I.hasMultipleRootRuleChoices s term = false
        · by_cases hO : I.noDeterministicReducerOverlap s = true
          · by_cases hC : I.noCoreBuiltinOverrides s = true
            · exact evalWithState_fallback_when_unresolved I s term hS hB hM hO hC hResolvedFalse
            · exact evalWithState_fallback_when_core_override I s term hS hB hM hO
                (bool_eq_false_of_ne_true hC)
          · exact evalWithState_fallback_when_overlap I s term hS hB hM (bool_eq_false_of_ne_true hO)
        · exact evalWithState_fallback_when_multi_root I s term hS hB (bool_eq_true_of_ne_false hM)
      · exact evalWithState_fallback_when_blocked I s term hS (bool_eq_true_of_ne_false hB)
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)
  · by_cases hS : I.shouldUseDeterministicInStrict term = true
    · by_cases hB : I.hasDeterministicBlockingRewriteBodies s = false
      · by_cases hM : I.hasMultipleRootRuleChoices s term = false
        · by_cases hO : I.noDeterministicReducerOverlap s = true
          · by_cases hC : I.noCoreBuiltinOverrides s = true
            · by_cases hR : I.isResolvedDeterministicResult
                  ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true
              · exact evalWithState_fallback_when_unchanged_rejected
                  I s term hS hB hM hO hC hR hAcceptFalse
              · exact evalWithState_fallback_when_unresolved I s term hS hB hM hO hC
                  (bool_eq_false_of_ne_true hR)
            · exact evalWithState_fallback_when_core_override I s term hS hB hM hO
                (bool_eq_false_of_ne_true hC)
          · exact evalWithState_fallback_when_overlap I s term hS hB hM (bool_eq_false_of_ne_true hO)
        · exact evalWithState_fallback_when_multi_root I s term hS hB (bool_eq_true_of_ne_false hM)
      · exact evalWithState_fallback_when_blocked I s term hS (bool_eq_true_of_ne_false hB)
    · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hS)

theorem evalWithState_eq_reference_of_deterministic_agreement
    (I : Interface σ)
    (hAgree :
      ∀ (s : σ) (term : Pattern),
        I.shouldUseDeterministicInStrict term = true →
        I.hasDeterministicBlockingRewriteBodies s = false →
        I.hasMultipleRootRuleChoices s term = false →
        I.noDeterministicReducerOverlap s = true →
        I.noCoreBuiltinOverrides s = true →
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
      · by_cases hOverlap : I.noDeterministicReducerOverlap s = true
        · by_cases hCore : I.noCoreBuiltinOverrides s = true
          · by_cases hResolved :
              I.isResolvedDeterministicResult
                ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true
            · by_cases hAccept :
                (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
                  I.acceptUnchangedDeterministic term) = true
              · exact hAgree s term hStrict hBlocked hMulti hOverlap hCore hResolved hAccept
              · exact evalWithState_fallback_when_unchanged_rejected
                  I s term hStrict hBlocked hMulti hOverlap hCore hResolved
                  (bool_eq_false_of_ne_true hAccept)
            · exact evalWithState_fallback_when_unresolved
                I s term hStrict hBlocked hMulti hOverlap hCore (bool_eq_false_of_ne_true hResolved)
          · exact evalWithState_fallback_when_core_override I s term hStrict hBlocked hMulti hOverlap
              (bool_eq_false_of_ne_true hCore)
        · exact evalWithState_fallback_when_overlap I s term hStrict hBlocked hMulti
            (bool_eq_false_of_ne_true hOverlap)
      · exact evalWithState_fallback_when_multi_root I s term hStrict hBlocked
          (bool_eq_true_of_ne_false hMulti)
    · exact evalWithState_fallback_when_blocked I s term hStrict
        (bool_eq_true_of_ne_false hBlocked)
  · exact evalWithState_fallback_when_not_strict I s term (bool_eq_false_of_ne_true hStrict)

end Algorithms.MeTTa.Simple.Backend.OptimizedRefinement
