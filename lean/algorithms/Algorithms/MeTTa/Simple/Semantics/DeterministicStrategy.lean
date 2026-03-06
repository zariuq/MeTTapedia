import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy

open MeTTailCore.MeTTaIL.Syntax

private def nonDetOrEffectHeads : List String :=
  [ "match", "let", "let*", "case", "foldall", "forall"
  , "superpose", "collapse", "once", "transaction", "with_mutex"
  , "add-atom", "remove-atom", "remove-all-atoms", "get-atoms"
  , "import!", "add-translator-rule!", "remove-translator-rule!"
  ]

private def nonMemoHeads : List String :=
  [ "if", "Expr", "=", ":", "test", "assertEqual", "assertEqualToResult"
  , "match", "let", "let*", "case", "foldall", "forall"
  , "superpose", "collapse", "once", "transaction", "with_mutex"
  , "add-atom", "remove-atom", "remove-all-atoms", "get-atoms"
  , "import!", "add-translator-rule!", "remove-translator-rule!"
  ]

private def unresolvedResultHeads : List String :=
  [ "if", "let", "let*", "case", "match", "Expr", "empty", "cut"
  , "call", "eval", "reduce", "chain"
  , "repr"
  ]

private partial def hasAnyFVar : Pattern → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .apply _ args => args.any hasAnyFVar
  | .lambda b => hasAnyFVar b
  | .multiLambda _ b => hasAnyFVar b
  | .subst b r => hasAnyFVar b || hasAnyFVar r
  | .collection _ elems _ => elems.any hasAnyFVar

private partial def containsHead (heads : List String) : Pattern → Bool
  | .apply ctor args =>
      heads.contains ctor || args.any (containsHead heads)
  | .lambda b => containsHead heads b
  | .multiLambda _ b => containsHead heads b
  | .subst b r => containsHead heads b || containsHead heads r
  | .collection _ elems _ => elems.any (containsHead heads)
  | _ => false

def shouldUseDeterministicInStrict (term : Pattern) : Bool :=
  !hasAnyFVar term &&
    !containsHead nonDetOrEffectHeads term

def isResolvedDeterministicResult (term : Pattern) : Bool :=
  !hasAnyFVar term &&
    !containsHead unresolvedResultHeads term

def isMemoizableDeterministicCall : Pattern → Bool
  | .apply ctor args =>
      !(nonMemoHeads.contains ctor) &&
      !args.isEmpty &&
      !hasAnyFVar (.apply ctor args)
  | _ => false

end Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy
