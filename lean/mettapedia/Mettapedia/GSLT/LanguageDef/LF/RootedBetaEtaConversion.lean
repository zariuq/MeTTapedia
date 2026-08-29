import Mettapedia.GSLT.LanguageDef.ConversionCertificate
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Rooted beta-eta conversion for indexed LF

This module places the structural beta-eta reduction rules used by the LF
checker inside one authoritative `CalculusLanguageDef`.  Rule application is
handled by the generic inference checker:

* beta uses checked binder-eliminating substitution;
* eta uses checked unused-binder elimination;
* application, product, and abstraction congruence are ordinary proof rules.

The rooted relation is directed reduction.  Definitional conversion is checked
by two directed certificates to one explicit common reduct, avoiding an
independently authored symmetry procedure.  Typing clients must still establish
that both compared LF terms are well formed at the selected PTS profile.
-/

namespace Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaConversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.ConversionCertificate
open Mettapedia.GSLT.LanguageDef

def lfSortType : TypeDecl := TypeDecl.plain "LFSort"
def lfTermType : TypeDecl := TypeDecl.plain "LFTerm"
def lfNameType : TypeDecl := TypeDecl.plain "LFName"
def lfIndexType : TypeDecl := TypeDecl.plain "LFIndex"

def constructor
    (head resultType : String) (params : List TermParam) : GrammarRule :=
  { label := head
    category := resultType
    params
    syntaxPattern := [] }

def sortType : Pattern := .apply "SortType" []
def sortKind : Pattern := .apply "SortKind" []

def srt (sort : Pattern) : Pattern := .apply "Srt" [sort]
def con (name : Pattern) : Pattern := .apply "Con" [name]
def var (index : Pattern) : Pattern := .apply "Var" [index]

def typeTerm : Pattern := srt sortType
def kindTerm : Pattern := srt sortKind

def app (function argument : Pattern) : Pattern :=
  .apply "App" [function, argument]

def pi (domain body : Pattern) : Pattern :=
  .apply "Pi" [domain, .lambda none body]

def lam (domain body : Pattern) : Pattern :=
  .apply "Lam" [domain, .lambda none body]

def converts (source target : Pattern) : Pattern :=
  .apply "Converts" [source, target]

def conversionDeclaration : ConversionDecl :=
  { judgmentHead := "Converts"
    version := "indexed-lf-beta-eta-common-reduct-v1" }

/-- Stable rule identifier constructor used by certificate producers. -/
def ruleId (value : String) : RuleId := ⟨value⟩

/-- Rooted beta contraction.  The result is independently supplied by the
certificate and checked by the generic explicit-substitution side condition. -/
def betaRule : RuleSchema :=
  { id := ruleId "lf-conv-beta"
    metavariables :=
      [("domain", 0), ("body", 1), ("argument", 0), ("result", 0)]
    premises := []
    conclusion :=
      converts
        (app (lam (.fvar "domain") (.fvar "body")) (.fvar "argument"))
        (.fvar "result")
    sideConditions := [.explicitSubstitution 0 1 2 3] }

/-- Rooted eta contraction.  The result is exactly the function obtained after
dropping the unused innermost binder. -/
def etaRule : RuleSchema :=
  { id := ruleId "lf-conv-eta"
    metavariables :=
      [("domain", 0), ("function", 1), ("result", 0)]
    premises := []
    conclusion :=
      converts
        (lam (.fvar "domain")
          (app (.fvar "function") (.bvar 0)))
        (.fvar "result")
    sideConditions := [.unusedBinderElimination 0 1 2] }

/-- Congruence for application. -/
def appCongruenceRule : RuleSchema :=
  { id := ruleId "lf-conv-app"
    metavariables :=
      [("function", 0), ("functionResult", 0),
       ("argument", 0), ("argumentResult", 0)]
    premises :=
      [ converts (.fvar "function") (.fvar "functionResult"),
        converts (.fvar "argument") (.fvar "argumentResult") ]
    conclusion :=
      converts
        (app (.fvar "function") (.fvar "argument"))
        (app (.fvar "functionResult") (.fvar "argumentResult")) }

/-- Congruence for dependent products.  Lambda wrappers preserve the exact
one-binder occurrence depth of both bodies. -/
def piCongruenceRule : RuleSchema :=
  { id := ruleId "lf-conv-pi"
    metavariables :=
      [("domain", 0), ("domainResult", 0),
       ("body", 1), ("bodyResult", 1)]
    premises :=
      [ converts (.fvar "domain") (.fvar "domainResult"),
        converts (.lambda none (.fvar "body"))
          (.lambda none (.fvar "bodyResult")) ]
    conclusion :=
      converts
        (pi (.fvar "domain") (.fvar "body"))
        (pi (.fvar "domainResult") (.fvar "bodyResult")) }

/-- Congruence for abstractions, with the same binder-depth discipline as
products. -/
def lamCongruenceRule : RuleSchema :=
  { id := ruleId "lf-conv-lam"
    metavariables :=
      [("domain", 0), ("domainResult", 0),
       ("body", 1), ("bodyResult", 1)]
    premises :=
      [ converts (.fvar "domain") (.fvar "domainResult"),
        converts (.lambda none (.fvar "body"))
          (.lambda none (.fvar "bodyResult")) ]
    conclusion :=
      converts
        (lam (.fvar "domain") (.fvar "body"))
        (lam (.fvar "domainResult") (.fvar "bodyResult")) }

/-- The sole LF term grammar and rooted conversion calculus. -/
abbrev definition : CalculusLanguageDef :=
  { name := "indexed-lf-beta-eta"
    types := [lfSortType, lfTermType, lfNameType, lfIndexType]
    terms :=
      [ constructor "SortType" "LFSort" [],
        constructor "SortKind" "LFSort" [],
        constructor "Srt" "LFTerm"
          [.simple "sort" (.base "LFSort")],
        constructor "Con" "LFTerm"
          [.simple "name" (.base "LFName")],
        constructor "Var" "LFTerm"
          [.simple "index" (.base "LFIndex")],
        constructor "App" "LFTerm"
          [.simple "function" (.base "LFTerm"),
           .simple "argument" (.base "LFTerm")],
        constructor "Pi" "LFTerm"
          [.simple "domain" (.base "LFTerm"),
           .abstraction "body" (.base "LFTerm")],
        constructor "Lam" "LFTerm"
          [.simple "domain" (.base "LFTerm"),
           .abstraction "body" (.base "LFTerm")] ]
    equations := []
    rewrites := []
    judgments := [{ head := conversionDeclaration.judgmentHead, arity := 2 }]
    rules :=
      [betaRule, etaRule, appCongruenceRule, piCongruenceRule,
        lamCongruenceRule]
    conversion := some conversionDeclaration }

def language : LanguageDef := definition.toLanguageDef
def calculus := definition.toCalculus

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, lfSortType, lfTermType, lfNameType, lfIndexType,
      constructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [language] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid, CalculusLanguageDef.lookupJudgment?,
    RuleSchema.isValidIn, RuleSideCondition.isValidFor,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead, lfSortType, lfTermType,
    lfNameType, lfIndexType, constructor, conversionDeclaration, betaRule,
    etaRule,
    appCongruenceRule, piCongruenceRule, lamCongruenceRule,
    converts, app, pi, lam, ruleId]
  decide

/-- The complete LF grammar and rooted conversion calculus as one GSLT. -/
def totalTheory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfNoEquations definition_valid rfl

theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ List Pattern) := by
  unfold totalTheory CalculusLanguageDef.toGSLTOfNoEquations
  rfl

/-- Source package consumed by the generic checker.  The identity names this
Lean definition; an exported artifact binds its byte-level digest separately. -/
def source : GSLTSource :=
  { identity :=
      { systemId := "indexed-lf"
        revision := "beta-eta-common-reduct-v1"
        artifactDigest :=
          "lean-definition:LFRootedBetaEtaConversion.language" }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "pts"
             version := "indexed-v1"
             payload := .apply "IndexedPTS" [] },
           { name := "conversion"
             version := conversionDeclaration.version
             payload := .apply "CommonReduct" [] }] }
    definition := definition }

def checked : CheckedGSLT :=
  { source
    identityValid := by decide
    assumptionsValid := by decide
    profilesValid := by decide
    definitionValid := by
      simpa [source] using definition_valid }

def rootedConversion : RootedConversion checked :=
  { declaration := conversionDeclaration
    isRooted := rfl }

/-! ## Executable positive and negative witnesses -/

def identity : Pattern := lam typeTerm (.bvar 0)
def betaSource : Pattern := app identity typeTerm

def betaProof : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-beta"
      arguments := [typeTerm, .bvar 0, typeTerm, typeTerm] }
    []

def betaCertificate : RawConversionCertificate :=
  .step typeTerm betaProof .refl

/-- Beta reduction is accepted through the rooted generic checker. -/
theorem beta_certificate_accepts :
    check checked rootedConversion betaSource typeTerm betaCertificate = true := by
  simp [check, RootedConversion.judgment, CheckedGSLT.checkRaw,
    InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
    CheckedGSLT.definition, checked, source, definition,
    rootedConversion, betaCertificate, betaProof, betaSource, identity,
    betaRule, etaRule, appCongruenceRule, piCongruenceRule,
    lamCongruenceRule, conversionDeclaration, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, RuleSideCondition.holds,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateBVar,
    instantiateBVarAt, liftBVars, converts, app, lam, typeTerm, srt,
    sortType, ruleId]

def etaSource : Pattern :=
  lam typeTerm (app typeTerm (.bvar 0))

def etaProof : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-eta"
      arguments := [typeTerm, typeTerm, typeTerm] }
    []

def etaCertificate : RawConversionCertificate :=
  .step typeTerm etaProof .refl

/-- Eta reduction is accepted only after exact unused-binder elimination. -/
theorem eta_certificate_accepts :
    check checked rootedConversion etaSource typeTerm etaCertificate = true := by
  simp [check, RootedConversion.judgment, CheckedGSLT.checkRaw,
    InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
    CheckedGSLT.definition, checked, source, definition,
    rootedConversion, etaCertificate, etaProof, etaSource, betaRule,
    etaRule, appCongruenceRule, piCongruenceRule, lamCongruenceRule,
    conversionDeclaration, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, RuleSchema.sideConditionsHold,
    RuleSideCondition.holds, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, dropBVar?, dropBVarAt?,
    converts, app, lam, typeTerm, srt, sortType, ruleId]

/-- The beta redex and its contractum are definitionally convertible through
an explicit common reduct. -/
theorem beta_common_reduct_accepts :
    checkCommonReduct checked rootedConversion betaSource typeTerm
      { common := typeTerm
        left := betaCertificate
        right := .refl } = true := by
  simp [checkCommonReduct, beta_certificate_accepts, check]

def capturedEtaSource : Pattern :=
  lam typeTerm (app (.bvar 0) (.bvar 0))

def capturedEtaProof : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-eta"
      arguments := [typeTerm, .bvar 0, typeTerm] }
    []

/-- A captured occurrence of the removed binder fails the eta side
condition. -/
theorem captured_eta_rejects :
    check checked rootedConversion capturedEtaSource typeTerm
      (.step typeTerm capturedEtaProof .refl) = false := by
  simp [check, RootedConversion.judgment, CheckedGSLT.checkRaw,
    InferenceChecker.checkRaw, CheckedGSLT.definition, checked, source,
    definition, rootedConversion, capturedEtaProof,
    capturedEtaSource, betaRule, etaRule, appCongruenceRule,
    piCongruenceRule, lamCongruenceRule, conversionDeclaration,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, RuleSideCondition.holds,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, dropBVar?, dropBVarAt?,
    converts, app, lam, typeTerm, srt, sortType, ruleId]

def fabricatedBetaProof : RawProof :=
  .node
    { ruleId := ruleId "lf-conv-beta"
      arguments := [typeTerm, .bvar 0, typeTerm, kindTerm] }
    []

/-- Supplying a fabricated beta result fails the exact substitution check. -/
theorem fabricated_beta_result_rejects :
    check checked rootedConversion betaSource kindTerm
      (.step kindTerm fabricatedBetaProof .refl) = false := by
  simp [check, RootedConversion.judgment, CheckedGSLT.checkRaw,
    InferenceChecker.checkRaw, CheckedGSLT.definition, checked, source,
    definition, rootedConversion, fabricatedBetaProof,
    betaSource, identity, betaRule, etaRule, appCongruenceRule,
    piCongruenceRule, lamCongruenceRule, conversionDeclaration,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, RuleSideCondition.holds,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, instantiateBVar,
    instantiateBVarAt, liftBVars, converts, app, lam, typeTerm, kindTerm,
    srt, sortType, sortKind, ruleId]

#print axioms language_validate
#print axioms definition_valid
#print axioms beta_certificate_accepts
#print axioms eta_certificate_accepts
#print axioms beta_common_reduct_accepts
#print axioms captured_eta_rejects
#print axioms fabricated_beta_result_rejects

end Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaConversion
