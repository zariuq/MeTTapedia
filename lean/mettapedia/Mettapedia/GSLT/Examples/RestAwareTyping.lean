import Mettapedia.GSLT.LanguageDef.RestAwareTyping
import Mettapedia.GSLT.LanguageDef.RestAwareChecker
import Mettapedia.GSLT.Examples.AuthoredRuleSorting

/-!
# The communication schema and its collection rest

The shipped reflective-calculus communication schema has a well-typed
rest-free collection skeleton, but its rest name is absent from its authored
context. The rest-aware judgment records that distinction. Adding the one
collection declaration types the actual left-hand side.
-/

namespace Mettapedia.GSLT.Examples.RestAwareTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

private abbrev RHasType :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType
private abbrev RElements :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType

/-- The extra declaration gives the collection rest exactly the type of the
parallel collection whose residual it denotes. -/
def communicationContextWithRest : List (String × TypeExpr) :=
  communicationContext ++ [("rest", .collection .hashBag (.base "Proc"))]

theorem shipped_communication_rest_has_no_schema_type :
    ¬ RHasType rhoCalc (FreeTypeContext.ofList communicationContext) []
      communicationLeft (.base "Proc") := by
  intro typed
  change RHasType rhoCalc (FreeTypeContext.ofList communicationContext) []
    (.collection .hashBag
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]]
      (some "rest")) (.base "Proc") at typed
  obtain ⟨elementType, rest⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.restDeclared typed
  simp [communicationContext, FreeTypeContext.ofList] at rest

theorem shipped_rho_does_not_have_all_rewrites_typed :
    ¬ ∀ r ∈ rhoCalc.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType rhoCalc r := by
  intro allTyped
  have membership : rhoCommRewrite ∈ rhoCalc.rewrites := by
    simp [rhoCalc]
  obtain ⟨type, leftTyped, _⟩ := allTyped rhoCommRewrite membership
  change RHasType rhoCalc (FreeTypeContext.ofList communicationContext) []
    communicationLeft type at leftTyped
  obtain ⟨elementType, restTyped⟩ :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.restDeclared leftTyped
  simp [communicationContext, FreeTypeContext.ofList] at restTyped

theorem shipped_communication_left_fails_rest_aware_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType rhoCalc
      (FreeTypeContext.ofList communicationContext) []
      communicationLeft (.base "Proc") = false := by
  decide +kernel

/-- The positive control is the shipped left-hand side with its rest name
declared at the enclosing collection type. -/
theorem communication_left_typed_with_declared_rest :
    RHasType rhoCalc (FreeTypeContext.ofList communicationContextWithRest) []
      communicationLeft (.base "Proc") := by
  have elementsChecked :
      checkElementsHaveType rhoCalc
        (FreeTypeContext.ofList communicationContextWithRest) []
        [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
         .apply "POutput" [.fvar "n", .fvar "q"]] (.base "Proc") = true := by
    decide +kernel
  have elementsOld : WellSorted.ElementsHaveType rhoCalc
      (FreeTypeContext.ofList communicationContextWithRest) []
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]] (.base "Proc") :=
    checkElementsHaveType_sound_of
      (fun _ _ checked => checkHasType_sound checked) elementsChecked
  have elements : RElements rhoCalc
      (FreeTypeContext.ofList communicationContextWithRest) []
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]] (.base "Proc") :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.ElementsHaveType.ofObjects
      elementsOld (by decide +kernel)
  change RHasType rhoCalc (FreeTypeContext.ofList communicationContextWithRest) []
    (.collection .hashBag
      [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
       .apply "POutput" [.fvar "n", .fvar "q"]]
      (some "rest")) (.base "Proc")
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.collectionConstructor
    (rule := rhoCalc.terms[3]) (parameterName := "ps")
    (by decide +kernel) (by decide +kernel) elements
    (by simp [Mettapedia.GSLT.LanguageDef.RestAwareTyping.RestHasType,
      communicationContextWithRest, communicationContext,
      FreeTypeContext.ofList])

theorem old_judgment_also_types_declared_communication :
    HasType rhoCalc (FreeTypeContext.ofList communicationContextWithRest) []
      communicationLeft (.base "Proc") :=
  communication_left_typed_with_declared_rest.forget

theorem declared_communication_left_passes_rest_aware_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType rhoCalc
      (FreeTypeContext.ofList communicationContextWithRest) []
      communicationLeft (.base "Proc") = true := by
  decide +kernel

theorem checked_communication_left_has_schema_type :
    RHasType rhoCalc (FreeTypeContext.ofList communicationContextWithRest) []
      communicationLeft (.base "Proc") :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
    declared_communication_left_passes_rest_aware_check

/-- Two nested collection rests use two distinct, structurally determined
collection types. -/
def nestedRestPattern : Pattern :=
  .collection .hashBag
    [.collection .hashBag [] (some "inner")]
    (some "outer")

def nestedRestContext : List (String × TypeExpr) :=
  [("outer", .collection .hashBag (.collection .hashBag (.base "Proc"))),
   ("inner", .collection .hashBag (.base "Proc"))]

theorem nested_rests_pass_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType rhoCalc
      (FreeTypeContext.ofList nestedRestContext) [] nestedRestPattern
      (.collection .hashBag (.collection .hashBag (.base "Proc"))) = true := by
  decide +kernel

theorem nested_rests_have_schema_type :
    RHasType rhoCalc (FreeTypeContext.ofList nestedRestContext) []
      nestedRestPattern
      (.collection .hashBag (.collection .hashBag (.base "Proc"))) :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
    nested_rests_pass_check

theorem missing_inner_rest_fails_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType rhoCalc
      (FreeTypeContext.ofList [
        ("outer", .collection .hashBag (.collection .hashBag (.base "Proc")))])
      [] nestedRestPattern
      (.collection .hashBag (.collection .hashBag (.base "Proc"))) = false := by
  decide +kernel

/-- The shipped congruence rule lacks declarations for its two premise
variables and its collection rest. -/
theorem shipped_parallel_congruence_fails_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
      rhoCalc rhoParCongRewrite = false := by
  decide +kernel

/-- Supply the existing conditional rule's schema variables with their
authored process and collection types. Its premise remains part of the rule. -/
def declaredParCongRewrite : RewriteRule :=
  { rhoParCongRewrite with
    typeContext :=
      [("S", .base "Proc"), ("T", .base "Proc"),
       ("rest", .collection .hashBag (.base "Proc"))] }

theorem declared_parallel_congruence_passes_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
      rhoCalc declaredParCongRewrite = true := by
  decide +kernel

theorem declared_parallel_congruence_has_schema_type :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
      rhoCalc declaredParCongRewrite :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
    declared_parallel_congruence_passes_check

theorem declared_parallel_congruence_has_old_sorting :
    RewriteWellSorted rhoCalc declaredParCongRewrite :=
  declared_parallel_congruence_has_schema_type.forget

/-- Add the missing rest declaration to the shipped communication rule. -/
def declaredCommRewrite : RewriteRule :=
  { rhoCommRewrite with typeContext := communicationContextWithRest }

theorem declared_communication_rule_passes_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
      rhoCalc declaredCommRewrite = true := by
  decide +kernel

theorem declared_communication_rule_has_schema_type :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
      rhoCalc declaredCommRewrite :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
    declared_communication_rule_passes_check

theorem declared_communication_rule_has_old_sorting :
    RewriteWellSorted rhoCalc declaredCommRewrite :=
  declared_communication_rule_has_schema_type.forget

/-- A substitution can be declaratively typed at a compound domain even
though this finite base-sort search declines it. -/
def compoundDomain : TypeExpr := .arrow (.base "Name") (.base "Proc")

def compoundSubstitution : Pattern :=
  .subst (.bvar 0) (.fvar "f")

theorem compound_substitution_has_schema_type :
    RHasType rhoCalc (FreeTypeContext.ofList [("f", compoundDomain)]) []
      compoundSubstitution compoundDomain := by
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.subst
    (domain := compoundDomain)
    (Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.bvar (by simp))
    (Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.fvar
      (by simp [FreeTypeContext.ofList]))

theorem compound_substitution_is_outside_base_domain_search :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType rhoCalc
      (FreeTypeContext.ofList [("f", compoundDomain)]) []
      compoundSubstitution compoundDomain = false := by
  decide +kernel

/-- The shipped quote-drop equation is a rest-free, substitution-free
control for the equation-level checker. -/
theorem rho_quote_drop_equation_passes_check :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkEquationHasType
      rhoCalc rhoCalc.equations[0] = true := by
  decide +kernel

theorem rho_quote_drop_equation_has_schema_type :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.EquationHasType
      rhoCalc rhoCalc.equations[0] :=
  Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkEquationHasType_sound
    rho_quote_drop_equation_passes_check

/-- Correct only the schema variable declarations of the shipped reflective
calculus. Its constructors, equation, rewrite patterns, and premises are
unchanged. -/
def rhoCalcWithDeclaredSchemas : LanguageDef :=
  { rhoCalc with «rewrites» :=
      [declaredCommRewrite, declaredParCongRewrite] }

theorem rhoCalcWithDeclaredSchemas_validates :
    rhoCalcWithDeclaredSchemas.validate = [] := by
  simp [LanguageDef.validate, rhoCalcWithDeclaredSchemas,
    declaredCommRewrite, declaredParCongRewrite, rhoCalc,
    rhoCommRewrite, rhoParCongRewrite,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validateEquation, LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseType, TypeExpr.proc,
    TypeExpr.name, TypeExpr.funType, TypeExpr.bag, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, communicationContextWithRest,
    communicationContext]

theorem rhoCalcWithDeclaredSchemas_all_rewrites_check :
    ∀ r ∈ rhoCalcWithDeclaredSchemas.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType
        rhoCalcWithDeclaredSchemas r = true := by
  intro r membership
  change r ∈ [declaredCommRewrite, declaredParCongRewrite] at membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with equality | equality
  · subst r
    decide +kernel
  · subst r
    decide +kernel

theorem rhoCalcWithDeclaredSchemas_all_rewrites_typed :
    ∀ r ∈ rhoCalcWithDeclaredSchemas.rewrites,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
        rhoCalcWithDeclaredSchemas r := by
  intro r membership
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType_sound
    (rhoCalcWithDeclaredSchemas_all_rewrites_check r membership)

theorem rhoCalcWithDeclaredSchemas_all_equations_check :
    ∀ equation ∈ rhoCalcWithDeclaredSchemas.equations,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkEquationHasType
        rhoCalcWithDeclaredSchemas equation = true := by
  intro equation membership
  change equation ∈ [rhoCalc.equations[0]] at membership
  simp only [List.mem_singleton] at membership
  subst equation
  decide +kernel

theorem rhoCalcWithDeclaredSchemas_all_equations_typed :
    ∀ equation ∈ rhoCalcWithDeclaredSchemas.equations,
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.EquationHasType
        rhoCalcWithDeclaredSchemas equation := by
  intro equation membership
  exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkEquationHasType_sound
    (rhoCalcWithDeclaredSchemas_all_equations_check equation membership)

def validatedRhoCalcWithDeclaredSchemas : ValidatedLanguageDef :=
  ⟨rhoCalcWithDeclaredSchemas, rhoCalcWithDeclaredSchemas_validates⟩

theorem validated_rho_all_rewrites_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewritesHaveType
      validatedRhoCalcWithDeclaredSchemas :=
  rhoCalcWithDeclaredSchemas_all_rewrites_typed

theorem validated_rho_all_equations_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.EquationsHaveType
      validatedRhoCalcWithDeclaredSchemas :=
  rhoCalcWithDeclaredSchemas_all_equations_typed

end Mettapedia.GSLT.Examples.RestAwareTyping
