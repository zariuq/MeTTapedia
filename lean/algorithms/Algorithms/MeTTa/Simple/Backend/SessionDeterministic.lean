import MeTTailCore
import Algorithms.MeTTa.Simple.Backend.CompiledBundle
import Algorithms.MeTTa.Simple.Semantics.DeterministicEval

namespace Algorithms.MeTTa.Simple.Backend.SessionDeterministic

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  rewrites : σ → List RewriteRule
  useCompiledIndexes : σ → Bool
  compiledRules : σ → Algorithms.MeTTa.Simple.Backend.CompiledBundle.View
  premiseFreeRulesForHeadArity : σ → String → Nat → List RewriteRule
  normalizePattern : Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  applyBindings : Bindings → Pattern → Pattern
  evalTupleIntrinsic : σ → List Pattern → σ × List Pattern
  translateCall : σ → Pattern → List Pattern
  deterministicPreserveArgs : String → Bool
  intrinsicDirect : σ → String → List Pattern → List Pattern
  rewriteAritiesForHead : σ → String → List Nat
  builtinPartialMinArity : String → Option Nat
  partialPattern : String → List Pattern → Pattern
  memoLimit : σ → Nat

def deterministicBlockedHeads : List String :=
  [ "match", "let", "let*", "case", "foldall", "forall"
  , "superpose", "collapse", "once", "transaction", "with_mutex"
  , "add-atom", "remove-atom", "remove-all-atoms", "get-atoms"
  , "import!", "add-translator-rule!", "remove-translator-rule!"
  ]

partial def patternContainsAnyHead (heads : List String) : Pattern → Bool
  | .fvar _ => false
  | .bvar _ => false
  | .apply ctor args =>
      heads.contains ctor || args.any (patternContainsAnyHead heads)
  | .lambda body => patternContainsAnyHead heads body
  | .multiLambda _ body => patternContainsAnyHead heads body
  | .subst body repl =>
      patternContainsAnyHead heads body || patternContainsAnyHead heads repl
  | .collection _ elems _ =>
      elems.any (patternContainsAnyHead heads)

def hasDeterministicBlockingRewriteBodies (I : Interface σ) (s : σ) : Bool :=
  (I.rewrites s).any (fun r =>
    patternContainsAnyHead deterministicBlockedHeads r.left ||
    patternContainsAnyHead deterministicBlockedHeads r.right)

partial def firstRuleReductionRaw? (I : Interface σ) (s : σ) (term : Pattern) : Option Pattern :=
  (I.rewrites s).findSome? (fun rule =>
    if rule.premises.isEmpty then
      let leftN := I.normalizePattern rule.left
      let rightN := I.normalizePattern rule.right
      match I.matchPattern leftN term with
      | [] => none
      | bs :: _ => some (I.applyBindings bs rightN)
    else
      none)

partial def firstRuleReduction? (I : Interface σ) (s : σ) (term : Pattern) : Option Pattern :=
  if I.useCompiledIndexes s then
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.firstPremiseFreeReduction?
      (I.compiledRules s)
      I.matchPattern
      I.applyBindings
      term
  else
    firstRuleReductionRaw? I s term

def evalDeterministicCore (I : Interface σ) (s : σ) (fuel : Nat)
    (term : Pattern) : σ × Pattern :=
  let iface : Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface σ := {
    evalTupleIntrinsic := I.evalTupleIntrinsic
    translateCall := I.translateCall
    deterministicPreserveArgs := I.deterministicPreserveArgs
    intrinsicDirect := I.intrinsicDirect
    firstRuleReduction? := firstRuleReduction? I
    rewriteAritiesForHead := I.rewriteAritiesForHead
    builtinPartialMinArity := I.builtinPartialMinArity
    partialPattern := I.partialPattern
    memoLimit := I.memoLimit
  }
  Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval iface s fuel term

def hasMultipleRootCandidates (I : Interface σ) (term : Pattern)
    (candidates : List RewriteRule) : Bool :=
  let termN := I.normalizePattern term
  let matchCount :=
    candidates.foldl
      (fun acc rule =>
        let lhsN := I.normalizePattern rule.left
        if (I.matchPattern lhsN termN).isEmpty then
          acc
        else
          acc + 1)
      0
  matchCount > 1

theorem hasMultipleRootCandidates_congr
    (I : Interface σ) (term : Pattern) {candidates₁ candidates₂ : List RewriteRule}
    (h : candidates₁ = candidates₂) :
    hasMultipleRootCandidates I term candidates₁ =
      hasMultipleRootCandidates I term candidates₂ := by
  simp [h]

def hasMultipleRootRuleChoices (I : Interface σ) (s : σ) (term : Pattern) : Bool :=
  match term with
  | .apply ctor args =>
      let candidates := I.premiseFreeRulesForHeadArity s ctor args.length
      hasMultipleRootCandidates I term candidates
  | _ => false

def acceptUnchangedDeterministic : Pattern → Bool
  | .apply "call" _ => true
  | .apply "eval" _ => true
  | .apply "reduce" _ => true
  | .apply "chain" _ => true
  | .apply "quote" _ => true
  | _ => false

end Algorithms.MeTTa.Simple.Backend.SessionDeterministic
