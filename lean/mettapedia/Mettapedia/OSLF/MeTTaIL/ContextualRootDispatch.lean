import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Root-indexed contextual-rule dispatch

The contextual interpreter is relational and preserves the complete ordered
reduct list.  This module proves that rules with a statically incompatible
application root may be removed before matching without changing that list.
The result is a reusable optimization and a convenient exactness lemma; it
does not select a first rule or assume determinism.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

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

/-- Root filtering preserves the exact ordered reduct list and its
multiplicity. -/
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

end Mettapedia.OSLF.MeTTaIL.ContextualStep
