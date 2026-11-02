import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

/-! Binding inference reads only the constructor vocabulary and declared
sort names. Selecting operational rows with the same vocabulary preserves
its actual inferred contexts and occurrence addresses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding

theorem constructor?_transport {first second : LanguageDef} (terms : first.terms = second.terms) (label : String) :
    constructor? first label = constructor? second label := by simp only [constructor?, terms]

theorem collectionElement?_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (kind : CollType) (expected : TypeExpr) : collectionElement? first kind expected = collectionElement? second kind expected := by
  simp only [collectionElement?, terms]

theorem headType?_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (context : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) :
    headType? first context bound pattern = headType? second context bound pattern := by
  cases pattern with
  | subst body replacement =>
      simp only [headType?, headType?_transport terms context bound replacement]
      congr 1
      funext domain
      exact headType?_transport terms context (domain :: bound) body
  | _ => simp only [headType?, constructor?_transport terms, terms]
termination_by sizeOf pattern

theorem contextAt?_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (context : List (String × TypeExpr)) (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (address : List Nat) : contextAt? first context bound expected pattern address = contextAt? second context bound expected pattern address := by
  induction address generalizing bound expected pattern with
  | nil => cases pattern <;> simp only [contextAt?]
  | cons index rest ih =>
      cases pattern with
      | bvar | fvar => simp only [contextAt?]
      | apply label arguments =>
          simp only [contextAt?, constructor?_transport terms, Option.bind_eq_bind]
          congr 1
          funext declaration
          congr 1
          funext expectedGuard
          congr 1
          funext ordinaryGuard
          congr 1
          funext parameter
          congr 1
          funext argument
          congr 1
          funext representationGuard
          congr 1
          funext argumentType
          exact ih _ _ _
      | lambda display body =>
          cases index <;> cases expected <;> simp only [contextAt?, ih]
      | multiLambda arity display body =>
          cases index <;> cases expected <;> try simp only [contextAt?]
          rename_i domain codomain
          cases domain <;> simp only [contextAt?, ih]
      | subst body replacement =>
          cases index with
          | zero => simp only [contextAt?, headType?_transport terms, ih]
          | succ index =>
              cases index with
              | zero =>
                  rw [contextAt?, contextAt?]
                  simp only [headType?_transport terms, ih]
              | succ _ => simp only [contextAt?]
      | collection kind elements tail =>
          simp only [contextAt?, collectionElement?_transport terms, Option.bind_eq_bind]
          congr 1
          funext elementType
          split
          · congr 1
            funext element
            exact ih _ _ _
          · rfl

theorem inspect_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (context : List (String × TypeExpr)) (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr)
    (pattern : Pattern) : inspect first context site bound expected pattern = inspect second context site bound expected pattern := by
  simp only [inspect, contextAt?_transport terms]

theorem premiseOccurrences_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (context : List (String × TypeExpr)) (index depth : Nat) (premise : Premise) :
    premiseOccurrences first context index depth premise = premiseOccurrences second context index depth premise := by
  cases premise with
  | forAll collection parameter body => exact premiseOccurrences_transport terms context index (depth + 1) body
  | _ => simp only [premiseOccurrences, headType?_transport terms, inspect_transport terms]
termination_by sizeOf premise

theorem infer?_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (rule : RewriteRule) : infer? first rule = infer? second rule := by
  simp only [infer?, headType?_transport terms, inspect_transport terms, premiseOccurrences_transport terms,
    dependencySortsDeclared, types]
  rfl

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax RuleBinding

theorem compile?_transport {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (rule : RewriteRule) : compile? first rule = compile? second rule := by
  simp only [compile?, dependencySortsDeclared, types, grammarPlan?, GeneralRuleBindingGrammar.infer?_transport terms types]
  rfl

#print axioms compile?_transport

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
