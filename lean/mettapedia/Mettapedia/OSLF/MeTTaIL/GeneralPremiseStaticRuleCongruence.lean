import Mettapedia.OSLF.MeTTaIL.GeneralPremiseRuleCongruence
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission

/-! Static premise checks retain their results when rule elaboration changes
metadata while preserving the declaration context and operational fields. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding

private theorem site_fields_eq {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (site : RulePatternSite) :
    sitePattern? first site = sitePattern? second site := by
  cases site <;> simp only [sitePattern?,left,right,premises]

private theorem arguments_fields_eq {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? first spec name site path = arguments? second spec name site path := by
  have occurrence : ∀ row, occurrenceDeclared first row = occurrenceDeclared second row := by
    intro row
    simp only [occurrenceDeclared,site_fields_eq left right premises]
  simp only [arguments?,occurrence]

mutual
  theorem projection_fields_eq {first second : RewriteRule}
      (left : first.left = second.left) (right : first.right = second.right)
      (premises : first.premises = second.premises) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (schema : Pattern) :
      checkRootProjectionSchema first spec site path schema = checkRootProjectionSchema second spec site path schema := by
    cases schema with
    | fvar name => simp only [checkRootProjectionSchema,arguments_fields_eq left right premises]
    | bvar _ => simp only [checkRootProjectionSchema]
    | apply _ arguments =>
      simpa only [checkRootProjectionSchema] using projection_arguments_fields_eq left right premises spec site path 0 arguments
    | lambda _ body =>
      simpa only [checkRootProjectionSchema] using projection_fields_eq left right premises spec site (path ++ [0]) body
    | multiLambda _ _ body =>
      simpa only [checkRootProjectionSchema] using projection_fields_eq left right premises spec site (path ++ [0]) body
    | subst body replacement =>
      simp only [checkRootProjectionSchema]
      rw [projection_fields_eq left right premises spec site (path ++ [0]) body,
        projection_fields_eq left right premises spec site (path ++ [1]) replacement]
    | collection _ elements _ =>
      simp only [checkRootProjectionSchema]
      rw [projection_arguments_fields_eq left right premises spec site path 0 elements]
  termination_by sizeOf schema

  theorem projection_arguments_fields_eq {first second : RewriteRule}
      (left : first.left = second.left) (right : first.right = second.right)
      (premises : first.premises = second.premises) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (index : Nat) (schemas : List Pattern) :
      checkRootProjectionArguments first spec site path index schemas =
        checkRootProjectionArguments second spec site path index schemas := by
    cases schemas with
    | nil => simp only [checkRootProjectionArguments]
    | cons schema schemas =>
      simp only [checkRootProjectionArguments]
      rw [projection_fields_eq left right premises spec site (path ++ [index]) schema,
        projection_arguments_fields_eq left right premises spec site path (index + 1) schemas]
  termination_by sizeOf schemas
end

private theorem query_inputs_fields_eq {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (premiseIndex depth : Nat) (available : List String) (index : Nat)
    (schemas : List Pattern) (modes : List RelationArgMode) :
    checkQueryInputs first spec premiseIndex depth available index schemas modes =
      checkQueryInputs second spec premiseIndex depth available index schemas modes := by
  induction schemas generalizing modes index with
  | nil => cases modes <;> rfl
  | cons schema schemas ih =>
    cases modes with
    | nil => rfl
    | cons mode modes =>
      cases mode <;> simp only [checkQueryInputs,projection_fields_eq left right premises,ih]

theorem premiseFlow_fields_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (context : first.typeContext = second.typeContext)
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (index depth : Nat) (refinement : Refinement) (premise : Premise) :
    premiseFlow language provider first spec index depth refinement premise =
      premiseFlow language provider second spec index depth refinement premise := by
  induction premise generalizing index depth refinement with
  | relationQuery relation arguments =>
    simp only [premiseFlow,query_inputs_fields_eq left right premises]
  | freshness condition =>
    simp only [premiseFlow,lookup_context_eq context,projection_fields_eq left right premises]
  | forAll collection parameter body ih => simp only [premiseFlow,ih,lookup_context_eq context]
  | congruence source target =>
    simp only [premiseFlow,sourceType_context_eq language context,
      schemaValuesChecked_context_eq language context,projection_fields_eq left right premises]
  | scopedStep step =>
    simp only [premiseFlow,schemaValuesChecked_context_eq language context,projection_fields_eq left right premises]

theorem premisesFlow_fields_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (context : first.typeContext = second.typeContext)
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (index : Nat) (refinement : Refinement) (bodies : List Premise) :
    premisesFlow language provider first spec index refinement bodies =
      premisesFlow language provider second spec index refinement bodies := by
  induction bodies generalizing index refinement with
  | nil => rfl
  | cons premise bodies ih =>
    simp only [premisesFlow,premiseFlow_fields_eq language provider context left right premises,ih]

theorem checkRule_fields_eq (language : LanguageDef) (provider : ProviderSnapshot)
    {first second : RewriteRule} (context : first.typeContext = second.typeContext)
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec) :
    checkRule language provider first spec = checkRule language provider second spec := by
  have initial : initialRefinement first = initialRefinement second := by simp only [initialRefinement,left]
  simp only [checkRule,initial,right,premises,premisesFlow_fields_eq language provider context left right premises,
    projection_fields_eq left right premises]

#print axioms checkRule_fields_eq

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
