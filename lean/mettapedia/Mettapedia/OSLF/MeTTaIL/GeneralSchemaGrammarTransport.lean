import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping

/-! Raw schema typing depends on the authored constructor grammar, not on
the operational rewrite list or language display name.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SchemaTyping

open Syntax Mettapedia.GSLT.LanguageDef.WellSorted

mutual
theorem checkSchemaType_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (domains : List TypeExpr) (free : FreeTypeContext) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) :
    checkSchemaType domains first free bound pattern expected = checkSchemaType domains second free bound pattern expected := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply label arguments =>
    simp only [checkSchemaType, terms, checkSchemaArguments_grammar terms domains free bound arguments]
  | lambda binder body =>
    cases expected with
    | arrow domain codomain => exact checkSchemaType_grammar terms domains free (domain :: bound) body codomain
    | _ => rfl
  | multiLambda arity binders body =>
    cases expected with
    | arrow domain codomain =>
      cases domain with
      | multiBinder element => exact checkSchemaType_grammar terms domains free (List.replicate arity element ++ bound) body codomain
      | _ => rfl
    | _ => rfl
  | subst body replacement =>
    simp only [checkSchemaType]
    congr 1
    funext domain
    rw [checkSchemaType_grammar terms domains free (domain :: bound) body expected,
      checkSchemaType_grammar terms domains free bound replacement domain]
  | collection kind elements rest =>
    simp only [checkSchemaType, terms, checkSchemaElements_grammar terms domains free bound elements]
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem checkSchemaArguments_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (domains : List TypeExpr) (free : FreeTypeContext) (bound : List TypeExpr)
    (arguments : List Pattern) (parameters : List TermParam) :
    checkSchemaArguments domains first free bound arguments parameters =
      checkSchemaArguments domains second free bound arguments parameters := by
  cases arguments with
  | nil => cases parameters <;> rfl
  | cons head tail =>
    cases parameters with
    | nil => rfl
    | cons parameter parameters =>
      simp only [checkSchemaArguments, checkSchemaType_grammar terms domains free bound head,
        checkSchemaArguments_grammar terms domains free bound tail]
termination_by sizeOf arguments
decreasing_by all_goals sizeOf_pattern_dec

theorem checkSchemaElements_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (domains : List TypeExpr) (free : FreeTypeContext) (bound : List TypeExpr)
    (elements : List Pattern) (expected : TypeExpr) :
    checkSchemaElements domains first free bound elements expected =
      checkSchemaElements domains second free bound elements expected := by
  cases elements with
  | nil => rfl
  | cons head tail => simp only [checkSchemaElements, checkSchemaType_grammar terms domains free bound head,
      checkSchemaElements_grammar terms domains free bound tail]
termination_by sizeOf elements
decreasing_by all_goals sizeOf_pattern_dec
end

theorem declaredDomains_grammar {first second : LanguageDef} (terms : first.terms = second.terms)
    (types : first.typeNames = second.typeNames) (rule : RewriteRule) (bound : List TypeExpr) :
    declaredDomains first rule bound = declaredDomains second rule bound := by
  have names : first.types.map (fun category => TypeExpr.base category.name) =
      second.types.map (fun category => TypeExpr.base category.name) := by
    simpa only [LanguageDef.typeNames, List.map_map, Function.comp_def] using congrArg (List.map TypeExpr.base) types
  simp only [declaredDomains, terms, names]

#print axioms checkSchemaType_grammar
#print axioms declaredDomains_grammar

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SchemaTyping
