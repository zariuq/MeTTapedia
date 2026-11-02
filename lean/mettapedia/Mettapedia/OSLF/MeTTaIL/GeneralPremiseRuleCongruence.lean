import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission

/-! Premise admission depends on the declaration context and operational
fields. Attaching binding metadata preserves these checks when those fields
are unchanged. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax

theorem lookup_context_eq {first second : RewriteRule} (same : first.typeContext = second.typeContext) :
    lookupRuleType? first = lookupRuleType? second := by
  funext name
  simp only [lookupRuleType?,same]

private theorem domains_context_eq (language : LanguageDef) {first second : RewriteRule}
    (same : first.typeContext = second.typeContext) (bound : List TypeExpr) :
    SchemaTyping.declaredDomains language first bound = SchemaTyping.declaredDomains language second bound := by
  simp only [SchemaTyping.declaredDomains,same]

theorem schemaValuesChecked_context_eq (language : LanguageDef) {first second : RewriteRule}
    (same : first.typeContext = second.typeContext) (bound : List TypeExpr)
    (patterns : List Pattern) (types : List TypeExpr) :
    schemaValuesChecked language first bound patterns types = schemaValuesChecked language second bound patterns types := by
  induction patterns generalizing types with
  | nil => cases types <;> rfl
  | cons pattern patterns ih =>
    cases types with
    | nil => rfl
    | cons type types =>
      simp only [schemaValuesChecked,domains_context_eq language same,lookup_context_eq same,ih]

theorem sourceType_context_eq (language : LanguageDef) {first second : RewriteRule}
    (same : first.typeContext = second.typeContext) (pattern : Pattern) :
    sourceType? language first pattern = sourceType? language second pattern := by
  cases pattern <;> simp only [sourceType?,lookup_context_eq same]

theorem premiseFlow_context_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (same : first.typeContext = second.typeContext)
    (spec : RuleBindingSpec) (available : List String) (premise : Premise) :
    premiseFlow language provider first spec available premise = premiseFlow language provider second spec available premise := by
  induction premise generalizing available with
  | relationQuery relation arguments =>
    simp only [premiseFlow,schemaValuesChecked_context_eq language same]
  | freshness condition =>
    simp only [premiseFlow,sourceType_context_eq language same,lookup_context_eq same,domains_context_eq language same]
  | congruence source target =>
    simp only [premiseFlow,sourceType_context_eq language same,schemaValuesChecked_context_eq language same]
  | scopedStep step => simp only [premiseFlow,schemaValuesChecked_context_eq language same]
  | forAll collection parameter body ih => simp only [premiseFlow,ih,lookup_context_eq same]

theorem premisesFlow_context_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (same : first.typeContext = second.typeContext)
    (spec : RuleBindingSpec) (available : List String) (premises : List Premise) :
    premisesFlow language provider first spec available premises = premisesFlow language provider second spec available premises := by
  induction premises generalizing available with
  | nil => rfl
  | cons premise premises ih => simp only [premisesFlow,premiseFlow_context_eq language provider same,ih]

theorem rulePremisesAdmitted_fields_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (same : first.typeContext = second.typeContext)
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec) :
    rulePremisesAdmitted language provider first spec = rulePremisesAdmitted language provider second spec := by
  simp only [rulePremisesAdmitted,left,right,premises,premisesFlow_context_eq language provider same]

#print axioms rulePremisesAdmitted_fields_eq

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
