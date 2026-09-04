import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef

/-!
# Operational canaries for official TPTP FOF formula elaboration

These exact-list checks exercise the authored rewrite relation independently
of the structural validator.  The positive result excludes duplicate or extra
reducts, while the negative result pins the semantic distinction between the
two official defined propositions and every other nullary defined word.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedLanguageDef
open Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

namespace Canary

def definedNullarySource (lexeme : String) : Pattern :=
  a "tptp92-ast:fof-defined-plain-formula:alt-1" [
    a "tptp92-ast:fof-defined-plain-term:alt-1" [
      a "tptp92-ast:defined-constant:alt-1" [
        sourceDefinedFunctor (a lexeme)]]]

def definedNullaryRequest (lexeme : String) : Pattern :=
  request "tptp-fof-elab:defined-plain" (definedNullarySource lexeme)

end Canary

/-- Decide whether a rule can structurally match an application with the
given root.  A metavariable-rooted rule remains eligible. -/
def rootMatches (label : String) (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply ruleLabel _ => ruleLabel == label
  | _ => true

theorem applyRuleUsing_eq_nil_of_root_mismatch
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (rule : RewriteRule)
    (label : String) (arguments : List Pattern)
    (mismatch : rootMatches label rule = false) :
    applyRuleUsing base lang recursiveStep rule (.apply label arguments) = [] := by
  have noMatch : matchPatternForRule lang rule (.apply label arguments) = [] := by
    rw [matchPatternForRule_eq_syntactic]
    cases ruleLeft : rule.left with
    | apply ruleLabel ruleArguments =>
        simp only [rootMatches, ruleLeft, beq_eq_false_iff_ne] at mismatch
        simp [matchPattern, mismatch]
    | bvar index => simp [matchPattern]
    | fvar name => simp [rootMatches, ruleLeft] at mismatch
    | lambda binderName body => simp [matchPattern]
    | multiLambda arity binderNames body => simp [matchPattern]
    | subst body replacement => simp [matchPattern]
    | collection collectionType elements rest => simp [matchPattern]
  rw [applyRuleUsing, noMatch]
  rfl

theorem flatMap_eq_root_filter
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (label : String) (arguments : List Pattern) (rules : List RewriteRule) :
    rules.flatMap (fun rule =>
        applyRuleUsing base lang recursiveStep rule (.apply label arguments)) =
      (rules.filter (rootMatches label)).flatMap (fun rule =>
        applyRuleUsing base lang recursiveStep rule
          (.apply label arguments)) := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      simp only [List.flatMap_cons, List.filter_cons]
      cases hRoot : rootMatches label rule with
      | false =>
          rw [applyRuleUsing_eq_nil_of_root_mismatch base lang recursiveStep
            rule label arguments hRoot]
          simp [inductionHypothesis]
      | true => simp [inductionHypothesis]

/-- Root dispatch is exact: filtering structurally impossible rule roots
preserves the complete ordered reduct list. -/
theorem rewriteAt_eq_root_filter
    (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (label : String) (arguments : List Pattern) :
    rewriteAt base lang (fuel + 1) (.apply label arguments) =
      (lang.rewrites.filter (rootMatches label)).flatMap fun rule =>
        applyRuleUsing base lang (rewriteAt base lang fuel) rule
          (.apply label arguments) := by
  rw [rewriteAt]
  exact flatMap_eq_root_filter base lang (rewriteAt base lang fuel)
    label arguments lang.rewrites

namespace Canary

private theorem definedPlainRootRules :
    language.rewrites.filter (rootMatches "tptp-fof-elab:defined-plain") =
      [definedTruthRule "tptp-fof-elab:defined-true" "$true" "verum",
       definedTruthRule "tptp-fof-elab:defined-false" "$false" "falsum",
       definedPredicateRule] := by
  rfl

theorem true_rewrite_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (definedNullaryRequest "$true") = [encodeFormula .verum] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:defined-plain" [definedNullarySource "$true"]) =
      [encodeFormula .verum]
  rw [rewriteAt_eq_root_filter, definedPlainRootRules]
  simp [definedTruthRule, definedPredicateRule, definedNullarySource,
    sourceDefinedFunctor, sourceToken, targetNullary, mkRule, request,
    congruence, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rfl

theorem other_defined_nullary_has_no_reduct (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
        (definedNullaryRequest "$other") = [] := by
  change rewriteAt (engineBasePremises RelationEnv.empty) language (fuel + 1)
    (.apply "tptp-fof-elab:defined-plain" [definedNullarySource "$other"]) = []
  rw [rewriteAt_eq_root_filter, definedPlainRootRules]
  simp [definedTruthRule, definedPredicateRule, definedNullarySource,
    sourceDefinedFunctor, sourceToken, targetNullary, mkRule, request,
    congruence, a, v, applyRuleUsing,
    matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

end Canary

#print axioms Canary.true_rewrite_exact
#print axioms Canary.other_defined_nullary_has_no_reduct
#print axioms rewriteAt_eq_root_filter

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaLanguageDef
