import Algorithms.MeTTa.Simple.Backend.CompiledBundle

namespace Algorithms.MeTTa.Simple.Backend.CompiledBundleContracts

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open Algorithms.MeTTa.Simple.Backend.CompiledBundle

theorem build_preserves_rewrites
    (normalizePattern : Pattern → Pattern)
    (rewrites : List RewriteRule) (selfFacts : List Pattern) :
    (build normalizePattern rewrites selfFacts).rewrites = rewrites := rfl

theorem build_ruleIndex_spec
    (normalizePattern : Pattern → Pattern)
    (rewrites : List RewriteRule) (selfFacts : List Pattern) :
    (build normalizePattern rewrites selfFacts).ruleIndex =
      Algorithms.MeTTa.Simple.Backend.RuleIndex.build rewrites := rfl

theorem build_spaceIndex_spec
    (normalizePattern : Pattern → Pattern)
    (rewrites : List RewriteRule) (selfFacts : List Pattern) :
    (build normalizePattern rewrites selfFacts).spaceIndex =
      Algorithms.MeTTa.Simple.Backend.SpaceIndex.build selfFacts := rfl

theorem rewriteAritiesForHead_eq_ruleIndex
    (view : View) (ctor : String) :
    rewriteAritiesForHead view ctor =
      Algorithms.MeTTa.Simple.Backend.RuleIndex.aritiesForHead view.ruleIndex ctor := rfl

theorem rewriteCountForHeadArity_eq_ruleIndex
    (view : View) (ctor : String) (arity : Nat) :
    rewriteCountForHeadArity view ctor arity =
      Algorithms.MeTTa.Simple.Backend.RuleIndex.rewriteCountForHeadArity view.ruleIndex ctor arity := rfl

theorem hasRuleHead_eq_ruleIndex
    (view : View) (ctor : String) :
    hasRuleHead view ctor =
      Algorithms.MeTTa.Simple.Backend.RuleIndex.hasHead view.ruleIndex ctor := rfl

theorem hasCompatHeadConstraintRule_eq_ruleIndex
    (view : View) (ctor : String) (arity : Nat) :
    hasCompatHeadConstraintRule view ctor arity =
      Algorithms.MeTTa.Simple.Backend.RuleIndex.hasCompatHeadConstraintRule view.ruleIndex ctor arity := rfl

theorem candidateSelfFacts_eq_spaceIndex
    (view : View) (pat : Pattern) :
    candidateSelfFacts view pat =
      Algorithms.MeTTa.Simple.Backend.SpaceIndex.candidateSelfFacts view.spaceIndex pat := rfl

theorem candidateSelfTypeEntries_eq_spaceIndex
    (view : View) (x : Pattern) :
    candidateSelfTypeEntries view x =
      Algorithms.MeTTa.Simple.Backend.SpaceIndex.candidateSelfTypeEntries view.spaceIndex x := rfl

theorem typeCandidatesForSelf_eq_spaceIndex
    (view : View)
    (matchPattern : Pattern → Pattern → List Bindings)
    (x : Pattern) :
    typeCandidatesForSelf view matchPattern x =
      Algorithms.MeTTa.Simple.Backend.SpaceIndex.typeCandidatesForSelf view.spaceIndex matchPattern x := rfl

end Algorithms.MeTTa.Simple.Backend.CompiledBundleContracts
