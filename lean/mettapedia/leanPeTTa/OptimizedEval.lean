import MeTTailCore

namespace Algorithms.MeTTa.Simple.Backend.OptimizedEval

open MeTTailCore.MeTTaIL.Syntax

structure Interface (σ : Type) where
  maxNodes : σ → Nat
  shouldUseDeterministicInStrict : Pattern → Bool
  hasDeterministicBlockingRewriteBodies : σ → Bool
  hasMultipleRootRuleChoices : σ → Pattern → Bool
  noDeterministicReducerOverlap : σ → Bool
  noCoreBuiltinOverrides : σ → Bool
  evalDeterministicCore : σ → Nat → Pattern → σ × Pattern
  evalWithStateCore : σ → Pattern → σ × List Pattern
  isResolvedDeterministicResult : Pattern → Bool
  acceptUnchangedDeterministic : Pattern → Bool

def evalWithState (I : Interface σ) (s : σ) (term : Pattern) : σ × List Pattern :=
  if I.shouldUseDeterministicInStrict term &&
     !I.hasDeterministicBlockingRewriteBodies s &&
     !I.hasMultipleRootRuleChoices s term &&
     I.noDeterministicReducerOverlap s &&
     I.noCoreBuiltinOverrides s then
    let detFuel := Nat.max 4096 (I.maxNodes s)
    let (sDet, outDet) := I.evalDeterministicCore s detFuel term
    if I.isResolvedDeterministicResult outDet &&
       (outDet != term || I.acceptUnchangedDeterministic term) then
      (sDet, [outDet])
    else
      I.evalWithStateCore s term
  else
    I.evalWithStateCore s term

end Algorithms.MeTTa.Simple.Backend.OptimizedEval
