import Mettapedia.OSLF.MeTTaIL.GeneralSchemaGrammarTransport
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission

/-! Premise admission depends on the constructor grammar, declared sorts
and provider signatures. Extending operational rewrites preserves it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax

theorem schemaValuesChecked_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (rule : RewriteRule) (bound : List TypeExpr)
    (patterns : List Pattern) (expected : List TypeExpr) :
    schemaValuesChecked first rule bound patterns expected = schemaValuesChecked second rule bound patterns expected := by
  induction patterns generalizing expected with
  | nil => cases expected <;> rfl
  | cons head tail ih =>
    cases expected with
    | nil => rfl
    | cons type rest =>
      simp only [schemaValuesChecked, SchemaTyping.declaredDomains_grammar terms types,
        SchemaTyping.checkSchemaType_grammar terms, ih]

theorem sourceType?_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (rule : RewriteRule) (pattern : Pattern) : sourceType? first rule pattern = sourceType? second rule pattern := by
  cases pattern <;> simp only [sourceType?, terms]

theorem collectionElement?_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (type : TypeExpr) : collectionElement? first type = collectionElement? second type := by
  cases type <;> simp only [collectionElement?, terms]

theorem premiseFlow_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (provider : ProviderSnapshot) (rule : RewriteRule)
    (spec : RuleBindingSpec) (available : List String) (premise : Premise) :
    premiseFlow first provider rule spec available premise = premiseFlow second provider rule spec available premise := by
  induction premise generalizing available with
  | forAll collection parameter body ih => simp only [premiseFlow, collectionElement?_grammar terms, ih]
  | _ => simp only [premiseFlow, sourceType?_grammar terms, schemaValuesChecked_grammar terms types,
      SchemaTyping.declaredDomains_grammar terms types, SchemaTyping.checkSchemaType_grammar terms]

theorem premisesFlow_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (provider : ProviderSnapshot) (rule : RewriteRule)
    (spec : RuleBindingSpec) (available : List String) (premises : List Premise) :
    premisesFlow first provider rule spec available premises = premisesFlow second provider rule spec available premises := by
  induction premises generalizing available with
  | nil => rfl
  | cons head tail ih => simp only [premisesFlow, premiseFlow_grammar terms types, ih]

theorem rulePremisesAdmitted_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (provider : ProviderSnapshot) (rule : RewriteRule) (spec : RuleBindingSpec) :
    rulePremisesAdmitted first provider rule spec = rulePremisesAdmitted second provider rule spec := by
  simp only [rulePremisesAdmitted, premisesFlow_grammar terms types]

#print axioms rulePremisesAdmitted_grammar

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
