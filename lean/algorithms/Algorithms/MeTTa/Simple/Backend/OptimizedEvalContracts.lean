import Algorithms.MeTTa.Simple.Backend.OptimizedEval

namespace Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.OptimizedEval

variable {σ : Type}

theorem evalWithState_fallback_when_not_strict
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = false) :
    evalWithState I s term = I.evalWithStateCore s term := by
  simp [evalWithState, hStrict]

theorem evalWithState_fallback_when_blocked
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = true)
    (hBlocked : I.hasDeterministicBlockingRewriteBodies s = true) :
    evalWithState I s term = I.evalWithStateCore s term := by
  simp [evalWithState, hStrict, hBlocked]

theorem evalWithState_fallback_when_multi_root
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = true)
    (hBlocked : I.hasDeterministicBlockingRewriteBodies s = false)
    (hMulti : I.hasMultipleRootRuleChoices s term = true) :
    evalWithState I s term = I.evalWithStateCore s term := by
  simp [evalWithState, hStrict, hBlocked, hMulti]

theorem evalWithState_fallback_when_unresolved
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = true)
    (hBlocked : I.hasDeterministicBlockingRewriteBodies s = false)
    (hMulti : I.hasMultipleRootRuleChoices s term = false)
    (hResolved :
      I.isResolvedDeterministicResult
        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = false) :
    evalWithState I s term = I.evalWithStateCore s term := by
  simp [evalWithState, hStrict, hBlocked, hMulti, hResolved]

theorem evalWithState_fallback_when_unchanged_rejected
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = true)
    (hBlocked : I.hasDeterministicBlockingRewriteBodies s = false)
    (hMulti : I.hasMultipleRootRuleChoices s term = false)
    (hResolved :
      I.isResolvedDeterministicResult
        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true)
    (hAccept :
      (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
        I.acceptUnchangedDeterministic term) = false) :
    evalWithState I s term = I.evalWithStateCore s term := by
  simp [evalWithState, hStrict, hBlocked, hMulti, hResolved, hAccept]

theorem evalWithState_deterministic_when_gate_and_accept
    (I : Interface σ) (s : σ) (term : Pattern)
    (hStrict : I.shouldUseDeterministicInStrict term = true)
    (hBlocked : I.hasDeterministicBlockingRewriteBodies s = false)
    (hMulti : I.hasMultipleRootRuleChoices s term = false)
    (hResolved :
      I.isResolvedDeterministicResult
        ((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2) = true)
    (hAccept :
      (((I.evalDeterministicCore s (Nat.max 4096 (I.maxNodes s)) term).2 != term) ||
        I.acceptUnchangedDeterministic term) = true) :
    evalWithState I s term =
      let detFuel := Nat.max 4096 (I.maxNodes s)
      let outDet := I.evalDeterministicCore s detFuel term
      (outDet.1, [outDet.2]) := by
  simp [evalWithState, hStrict, hBlocked, hMulti, hResolved, hAccept]

end Algorithms.MeTTa.Simple.Backend.OptimizedEvalContracts

