import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Dependent typing canary for rooted GSLT declarations

This module is an adequacy probe for generic dependent application and
explicit conversion.  The language-specific constructors, judgments, and
ordered inference rules occur only in one `CalculusLanguageDef`; the checker
contains no branch for this fixture.
-/

namespace Mettapedia.GSLT.LanguageDef.DependentTypingCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef

private def expressionType : TypeDecl := TypeDecl.plain "Expr"

private def expressionConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "Expr"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "Expr")
    syntaxPattern := [] }

private def context : Pattern := .apply "Ctx0" []
private def universeZero : Pattern := .apply "U0" []
private def universeOne : Pattern := .apply "U1" []
private def natural : Pattern := .apply "Nat" []
private def zero : Pattern := .apply "Zero" []
private def boolean : Pattern := .apply "Bool" []
private def falseTerm : Pattern := .apply "False" []
private def refl : Pattern := .apply "Refl" []

private def pi (domain codomain : Pattern) : Pattern :=
  .apply "Pi" [domain, .lambda none codomain]

private def app (function argument : Pattern) : Pattern :=
  .apply "App" [function, argument]

private def equality (carrier left right : Pattern) : Pattern :=
  .apply "Eq" [carrier, left, right]

private def typing (ctx term type : Pattern) : Pattern :=
  .apply "Ty" [ctx, term, type]

private def converts (source target : Pattern) : Pattern :=
  .apply "Converts" [source, target]

private def ruleId (value : String) : RuleId := ⟨value⟩

private def closedTypingRule (id : String) (term type : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := []
    premises := []
    conclusion := typing context term type }

private def universeZeroRule : RuleSchema :=
  closedTypingRule "ty-U0" universeZero universeOne

private def naturalRule : RuleSchema :=
  closedTypingRule "ty-Nat" natural universeZero

private def zeroRule : RuleSchema :=
  closedTypingRule "ty-Zero" zero natural

private def booleanRule : RuleSchema :=
  closedTypingRule "ty-Bool" boolean universeZero

private def falseRule : RuleSchema :=
  closedTypingRule "ty-False" falseTerm boolean

private def equalityBody : Pattern :=
  equality natural (.bvar 0) (.bvar 0)

private def reflRule : RuleSchema :=
  closedTypingRule "ty-Refl" refl (pi natural equalityBody)

/-- The codomain metavariable occurs only under one binder: in the `Pi`
premise and in the explicit-substitution result of application. -/
private def applicationRule : RuleSchema :=
  { id := ruleId "ty-application"
    metavariables :=
      [("ctx", 0), ("function", 0), ("argument", 0), ("domain", 0),
       ("codomain", 1)]
    premises :=
      [ typing (.fvar "ctx") (.fvar "function")
          (pi (.fvar "domain") (.fvar "codomain")),
        typing (.fvar "ctx") (.fvar "argument") (.fvar "domain") ]
    conclusion :=
      typing (.fvar "ctx")
        (app (.fvar "function") (.fvar "argument"))
        (.subst (.fvar "codomain") (.fvar "argument")) }

/-- One generic conversion edge executes a checked explicit substitution.
The side condition refers only to the ordered rule arguments. -/
private def explicitSubstitutionRule : RuleSchema :=
  { id := ruleId "conversion-explicit-substitution"
    metavariables := [("body", 1), ("replacement", 0), ("result", 0)]
    premises := []
    conclusion :=
      converts (.subst (.fvar "body") (.fvar "replacement"))
        (.fvar "result")
    sideConditions := [.explicitSubstitution 0 0 1 2] }

private def conversionTypingRule : RuleSchema :=
  { id := ruleId "ty-conversion"
    metavariables :=
      [("ctx", 0), ("term", 0), ("source", 0), ("target", 0)]
    premises :=
      [ typing (.fvar "ctx") (.fvar "term") (.fvar "source"),
        converts (.fvar "source") (.fvar "target") ]
    conclusion :=
      typing (.fvar "ctx") (.fvar "term") (.fvar "target") }

private abbrev definition : CalculusLanguageDef :=
  { name := "dependent-typing-canary"
    types := [expressionType]
    terms :=
      [ expressionConstructor "Ctx0" 0,
        expressionConstructor "U0" 0,
        expressionConstructor "U1" 0,
        expressionConstructor "Nat" 0,
        expressionConstructor "Zero" 0,
        expressionConstructor "Bool" 0,
        expressionConstructor "False" 0,
        expressionConstructor "Pi" 2,
        expressionConstructor "App" 2,
        expressionConstructor "Eq" 3,
        expressionConstructor "Refl" 0 ]
    equations := []
    rewrites := []
    judgments := [{ head := "Ty", arity := 3 }, { head := "Converts", arity := 2 }]
    rules :=
      [ universeZeroRule, naturalRule, zeroRule, booleanRule, falseRule,
        reflRule, applicationRule, explicitSubstitutionRule,
        conversionTypingRule ]
    conversion :=
      some { judgmentHead := "Converts", version := "explicit-substitution-v1" } }

private def language : LanguageDef := definition.toLanguageDef
private def calculus := definition.toCalculus

private theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, expressionType, expressionConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

private theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [language] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSideCondition.isValidFor, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, expressionType,
    expressionConstructor, universeZeroRule, naturalRule, zeroRule,
    booleanRule, falseRule, reflRule, applicationRule,
    explicitSubstitutionRule, conversionTypingRule, closedTypingRule, typing,
    converts, pi, app, equalityBody, equality, context, universeZero,
    universeOne, natural, zero, boolean, falseTerm, refl, ruleId]
  decide

/-- The complete canary as one GSLT, not merely as checker input. -/
private def totalTheory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfEquationFree definition_valid rfl

private theorem totalTheory_Term :
    totalTheory.Term = (Pattern ⊕ List Pattern) := by
  unfold totalTheory CalculusLanguageDef.toGSLTOfEquationFree
  rfl

private def checked : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

private def reflTypingProof : RawProof :=
  .node { ruleId := ruleId "ty-Refl", arguments := [] } []

private def zeroTypingProof : RawProof :=
  .node { ruleId := ruleId "ty-Zero", arguments := [] } []

private def falseTypingProof : RawProof :=
  .node { ruleId := ruleId "ty-False", arguments := [] } []

private def applicationTerm : Pattern := app refl zero

private def structuralResult : Pattern := .subst equalityBody zero

private def computedResult : Pattern := equality natural zero zero

private def applicationProof : RawProof :=
  .node
    { ruleId := ruleId "ty-application"
      arguments := [context, refl, zero, natural, equalityBody] }
    [reflTypingProof, zeroTypingProof]

private def conversionProof : RawProof :=
  .node
    { ruleId := ruleId "conversion-explicit-substitution"
      arguments := [equalityBody, zero, computedResult] }
    []

private def convertedApplicationProof : RawProof :=
  .node
    { ruleId := ruleId "ty-conversion"
      arguments := [context, applicationTerm, structuralResult, computedResult] }
    [applicationProof, conversionProof]

/-- Positive: dependent application followed by an explicit checked
conversion proves the computed codomain. -/
theorem dependent_application_accepts :
    checkRaw checked
      (typing context applicationTerm computedResult)
      convertedApplicationProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    convertedApplicationProof, applicationProof, conversionProof,
    reflTypingProof, zeroTypingProof, applicationTerm, structuralResult,
    computedResult, applicationRule, conversionTypingRule,
    explicitSubstitutionRule, reflRule, zeroRule, closedTypingRule,
    universeZeroRule, naturalRule, booleanRule, falseRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, RuleSideCondition.holds,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, typing, converts, app, pi,
    equalityBody, equality, context, refl, zero, natural, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateBVar,
    instantiateBVarAt, liftBVars]

private def mismatchedApplicationProof : RawProof :=
  .node
    { ruleId := ruleId "ty-application"
      arguments := [context, refl, falseTerm, natural, equalityBody] }
    [reflTypingProof, falseTypingProof]

/-- Negative: a `Bool` inhabitant cannot fill the declared `Nat` domain. -/
theorem argument_type_mismatch_rejects :
    checkRaw checked
      (typing context (app refl falseTerm) (.subst equalityBody falseTerm))
      mismatchedApplicationProof = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    mismatchedApplicationProof, reflTypingProof, falseTypingProof,
    applicationRule, reflRule, falseRule, closedTypingRule,
    universeZeroRule, naturalRule, booleanRule, zeroRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, typing, app, pi,
    equalityBody, equality, context, refl, falseTerm, zero, natural, boolean,
    ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def omittedConversionProof : RawProof :=
  .node
    { ruleId := ruleId "ty-conversion"
      arguments := [context, applicationTerm, structuralResult, computedResult] }
    [applicationProof]

/-- Negative: conversion is an ordered premise and cannot be omitted. -/
theorem omitted_conversion_rejects :
    checkRaw checked
      (typing context applicationTerm computedResult)
      omittedConversionProof = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    omittedConversionProof, applicationProof, reflTypingProof, zeroTypingProof,
    applicationTerm, structuralResult, computedResult, applicationRule,
    conversionTypingRule, explicitSubstitutionRule, reflRule, zeroRule,
    closedTypingRule,
    universeZeroRule, naturalRule, booleanRule, falseRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, typing, converts, app, pi,
    equalityBody, equality, context, refl, zero, natural, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def swappedApplicationChildren : RawProof :=
  .node
    { ruleId := ruleId "ty-application"
      arguments := [context, refl, zero, natural, equalityBody] }
    [zeroTypingProof, reflTypingProof]

/-- Negative: function and argument evidence cannot be reordered. -/
theorem swapped_application_children_reject :
    checkRaw checked
      (typing context applicationTerm structuralResult)
      swappedApplicationChildren = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    swappedApplicationChildren, reflTypingProof, zeroTypingProof,
    applicationTerm, structuralResult, applicationRule, reflRule, zeroRule,
    closedTypingRule, universeZeroRule, naturalRule, booleanRule, falseRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?,
    typing, app, pi,
    equalityBody, equality, context, refl, zero, natural, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def invalidConversionProof : RawProof :=
  .node
    { ruleId := ruleId "conversion-explicit-substitution"
      arguments := [equalityBody, zero, equality natural zero falseTerm] }
    []

/-- Negative: the generic computation side condition rejects a fabricated
substitution result. -/
theorem fabricated_conversion_result_rejects :
    checkRaw checked
      (converts structuralResult (equality natural zero falseTerm))
      invalidConversionProof = false := by
  simp [checkRaw, checked, definition,
    invalidConversionProof, structuralResult, explicitSubstitutionRule,
    conversionTypingRule, applicationRule, reflRule, zeroRule,
    closedTypingRule, universeZeroRule, naturalRule, booleanRule, falseRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    typing, converts, app, pi,
    equalityBody, equality, context, refl, falseTerm, zero, natural, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateBVar,
    instantiateBVarAt, liftBVars]

private def falseUniverseCeilingProof : RawProof :=
  .node { ruleId := ruleId "ty-U0", arguments := [] } []

/-- Negative: the finite universe declaration contains `U0 : U1` but no
rule for `U1 : U1`. -/
theorem universe_ceiling_rejects :
    checkRaw checked (typing context universeOne universeOne)
      falseUniverseCeilingProof = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    falseUniverseCeilingProof, universeZeroRule, applicationRule,
    conversionTypingRule, explicitSubstitutionRule, reflRule, zeroRule,
    closedTypingRule, naturalRule, booleanRule, falseRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, typing, converts, app, pi,
    equalityBody, equality, context, refl, universeZero, universeOne, zero,
    natural, ruleId]

end Mettapedia.GSLT.LanguageDef.DependentTypingCanary
