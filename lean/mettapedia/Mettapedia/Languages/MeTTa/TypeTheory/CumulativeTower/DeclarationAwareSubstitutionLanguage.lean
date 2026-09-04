import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareDataLanguage

/-!
# Authored first-order substitution for canonical Prime terms

Canonical declaration-aware terms encode intrinsically scoped variables as
ordinary first-order data.  This conservative calculus extension makes the
binding operations required by beta computation explicit and proof-carrying:

* strict order on encoded natural numbers;
* weakening by one variable above a declared cutoff;
* capture-avoiding removal and replacement of one de Bruijn variable; and
* root beta contraction, whose only computational premise is substitution.

The rule inventory traverses every constructor of `Presentation.Tm`.  It is
independent of the decode--substitute--encode reference adapter: rules mention
only the fixed canonical constructor alphabet and are consumed by the generic
inference checker.  No proof artifact is part of an ordinary computed term;
proof trees are supplied only to the checking boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionLanguage

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareDataLanguage
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Canonical first-order surface -/

def zero : Pattern := .apply "prime-nat-zero" []
def succ (value : Pattern) : Pattern := .apply "prime-nat-succ" [value]

def tmVar (index : Pattern) : Pattern := .apply "prime-tm-var" [index]
def tmConst (name : Pattern) : Pattern := .apply "prime-tm-const" [name]
def tmHead (head : Pattern) : Pattern := .apply "prime-tm-head" [head]
def tmPi (domain body : Pattern) : Pattern :=
  .apply "prime-tm-pi" [domain, body]
def tmSigma (domain body : Pattern) : Pattern :=
  .apply "prime-tm-sigma" [domain, body]
def tmId (type left right : Pattern) : Pattern :=
  .apply "prime-tm-id" [type, left, right]
def tmLam (body : Pattern) : Pattern := .apply "prime-tm-lam" [body]
def tmApp (function argument : Pattern) : Pattern :=
  .apply "prime-tm-app" [function, argument]
def tmPair (first second : Pattern) : Pattern :=
  .apply "prime-tm-pair" [first, second]
def tmFst (pair : Pattern) : Pattern := .apply "prime-tm-fst" [pair]
def tmSnd (pair : Pattern) : Pattern := .apply "prime-tm-snd" [pair]
def tmRefl (term : Pattern) : Pattern := .apply "prime-tm-refl" [term]

def indexLt (left right : Pattern) : Pattern :=
  .apply "prime-index-lt" [left, right]

def weakensAt (cutoff source target : Pattern) : Pattern :=
  .apply "prime-tm-weakens-at" [cutoff, source, target]

def substitutesAt
    (index replacement source target : Pattern) : Pattern :=
  .apply "prime-tm-substitutes-at" [index, replacement, source, target]

def rootBeta (source target : Pattern) : Pattern :=
  .apply "prime-tm-root-beta" [source, target]

def ruleId (value : String) : RuleId := ⟨value⟩
def formal (name : String) : String × Nat := (name, 0)
def m (name : String) : Pattern := .fvar name

def rule (id : String) (names : List String)
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId id
    metavariables := names.map formal
    premises
    conclusion }

/-! ## Strict order evidence -/

def ltZeroSuccRule : RuleSchema :=
  rule "prime-index-lt-zero-succ" ["right"] []
    (indexLt zero (succ (m "right")))

def ltSuccSuccRule : RuleSchema :=
  rule "prime-index-lt-succ-succ" ["left", "right"]
    [indexLt (m "left") (m "right")]
    (indexLt (succ (m "left")) (succ (m "right")))

/-! ## Weakening by one above a cutoff -/

def weakenVarBelowRule : RuleSchema :=
  rule "prime-weaken-var-below" ["cutoff", "index"]
    [indexLt (m "index") (m "cutoff")]
    (weakensAt (m "cutoff") (tmVar (m "index")) (tmVar (m "index")))

def weakenVarAtOrAboveRule : RuleSchema :=
  rule "prime-weaken-var-at-or-above" ["cutoff", "index"]
    [indexLt (m "cutoff") (succ (m "index"))]
    (weakensAt (m "cutoff") (tmVar (m "index"))
      (tmVar (succ (m "index"))))

def weakenConstRule : RuleSchema :=
  rule "prime-weaken-const" ["cutoff", "name"] []
    (weakensAt (m "cutoff") (tmConst (m "name")) (tmConst (m "name")))

def weakenHeadRule : RuleSchema :=
  rule "prime-weaken-head" ["cutoff", "head"] []
    (weakensAt (m "cutoff") (tmHead (m "head")) (tmHead (m "head")))

def weakenPiRule : RuleSchema :=
  rule "prime-weaken-pi"
    ["cutoff", "domain", "body", "domainResult", "bodyResult"]
    [weakensAt (m "cutoff") (m "domain") (m "domainResult"),
     weakensAt (succ (m "cutoff")) (m "body") (m "bodyResult")]
    (weakensAt (m "cutoff") (tmPi (m "domain") (m "body"))
      (tmPi (m "domainResult") (m "bodyResult")))

def weakenSigmaRule : RuleSchema :=
  rule "prime-weaken-sigma"
    ["cutoff", "domain", "body", "domainResult", "bodyResult"]
    [weakensAt (m "cutoff") (m "domain") (m "domainResult"),
     weakensAt (succ (m "cutoff")) (m "body") (m "bodyResult")]
    (weakensAt (m "cutoff") (tmSigma (m "domain") (m "body"))
      (tmSigma (m "domainResult") (m "bodyResult")))

def weakenIdRule : RuleSchema :=
  rule "prime-weaken-id"
    ["cutoff", "type", "left", "right", "typeResult", "leftResult",
      "rightResult"]
    [weakensAt (m "cutoff") (m "type") (m "typeResult"),
     weakensAt (m "cutoff") (m "left") (m "leftResult"),
     weakensAt (m "cutoff") (m "right") (m "rightResult")]
    (weakensAt (m "cutoff") (tmId (m "type") (m "left") (m "right"))
      (tmId (m "typeResult") (m "leftResult") (m "rightResult")))

def weakenLamRule : RuleSchema :=
  rule "prime-weaken-lam" ["cutoff", "body", "bodyResult"]
    [weakensAt (succ (m "cutoff")) (m "body") (m "bodyResult")]
    (weakensAt (m "cutoff") (tmLam (m "body"))
      (tmLam (m "bodyResult")))

def weakenAppRule : RuleSchema :=
  rule "prime-weaken-app"
    ["cutoff", "function", "argument", "functionResult", "argumentResult"]
    [weakensAt (m "cutoff") (m "function") (m "functionResult"),
     weakensAt (m "cutoff") (m "argument") (m "argumentResult")]
    (weakensAt (m "cutoff") (tmApp (m "function") (m "argument"))
      (tmApp (m "functionResult") (m "argumentResult")))

def weakenPairRule : RuleSchema :=
  rule "prime-weaken-pair"
    ["cutoff", "first", "second", "firstResult", "secondResult"]
    [weakensAt (m "cutoff") (m "first") (m "firstResult"),
     weakensAt (m "cutoff") (m "second") (m "secondResult")]
    (weakensAt (m "cutoff") (tmPair (m "first") (m "second"))
      (tmPair (m "firstResult") (m "secondResult")))

def weakenFstRule : RuleSchema :=
  rule "prime-weaken-fst" ["cutoff", "pair", "pairResult"]
    [weakensAt (m "cutoff") (m "pair") (m "pairResult")]
    (weakensAt (m "cutoff") (tmFst (m "pair"))
      (tmFst (m "pairResult")))

def weakenSndRule : RuleSchema :=
  rule "prime-weaken-snd" ["cutoff", "pair", "pairResult"]
    [weakensAt (m "cutoff") (m "pair") (m "pairResult")]
    (weakensAt (m "cutoff") (tmSnd (m "pair"))
      (tmSnd (m "pairResult")))

def weakenReflRule : RuleSchema :=
  rule "prime-weaken-refl" ["cutoff", "term", "termResult"]
    [weakensAt (m "cutoff") (m "term") (m "termResult")]
    (weakensAt (m "cutoff") (tmRefl (m "term"))
      (tmRefl (m "termResult")))

/-! ## Capture-avoiding substitution -/

def substVarEqualRule : RuleSchema :=
  rule "prime-subst-var-equal" ["index", "replacement"] []
    (substitutesAt (m "index") (m "replacement")
      (tmVar (m "index")) (m "replacement"))

def substVarBelowRule : RuleSchema :=
  rule "prime-subst-var-below" ["index", "replacement", "variable"]
    [indexLt (m "variable") (m "index")]
    (substitutesAt (m "index") (m "replacement")
      (tmVar (m "variable")) (tmVar (m "variable")))

def substVarAboveRule : RuleSchema :=
  rule "prime-subst-var-above" ["index", "replacement", "predecessor"]
    [indexLt (m "index") (succ (m "predecessor"))]
    (substitutesAt (m "index") (m "replacement")
      (tmVar (succ (m "predecessor"))) (tmVar (m "predecessor")))

def substConstRule : RuleSchema :=
  rule "prime-subst-const" ["index", "replacement", "name"] []
    (substitutesAt (m "index") (m "replacement")
      (tmConst (m "name")) (tmConst (m "name")))

def substHeadRule : RuleSchema :=
  rule "prime-subst-head" ["index", "replacement", "head"] []
    (substitutesAt (m "index") (m "replacement")
      (tmHead (m "head")) (tmHead (m "head")))

def substPiRule : RuleSchema :=
  rule "prime-subst-pi"
    ["index", "replacement", "domain", "body", "domainResult",
      "liftedReplacement", "bodyResult"]
    [substitutesAt (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
     weakensAt zero (m "replacement") (m "liftedReplacement"),
     substitutesAt (succ (m "index")) (m "liftedReplacement")
        (m "body") (m "bodyResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmPi (m "domain") (m "body"))
      (tmPi (m "domainResult") (m "bodyResult")))

def substSigmaRule : RuleSchema :=
  rule "prime-subst-sigma"
    ["index", "replacement", "domain", "body", "domainResult",
      "liftedReplacement", "bodyResult"]
    [substitutesAt (m "index") (m "replacement")
        (m "domain") (m "domainResult"),
     weakensAt zero (m "replacement") (m "liftedReplacement"),
     substitutesAt (succ (m "index")) (m "liftedReplacement")
        (m "body") (m "bodyResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmSigma (m "domain") (m "body"))
      (tmSigma (m "domainResult") (m "bodyResult")))

def substIdRule : RuleSchema :=
  rule "prime-subst-id"
    ["index", "replacement", "type", "left", "right", "typeResult",
      "leftResult", "rightResult"]
    [substitutesAt (m "index") (m "replacement")
        (m "type") (m "typeResult"),
     substitutesAt (m "index") (m "replacement")
        (m "left") (m "leftResult"),
     substitutesAt (m "index") (m "replacement")
        (m "right") (m "rightResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmId (m "type") (m "left") (m "right"))
      (tmId (m "typeResult") (m "leftResult") (m "rightResult")))

def substLamRule : RuleSchema :=
  rule "prime-subst-lam"
    ["index", "replacement", "body", "liftedReplacement", "bodyResult"]
    [weakensAt zero (m "replacement") (m "liftedReplacement"),
     substitutesAt (succ (m "index")) (m "liftedReplacement")
        (m "body") (m "bodyResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmLam (m "body")) (tmLam (m "bodyResult")))

def substAppRule : RuleSchema :=
  rule "prime-subst-app"
    ["index", "replacement", "function", "argument", "functionResult",
      "argumentResult"]
    [substitutesAt (m "index") (m "replacement")
        (m "function") (m "functionResult"),
     substitutesAt (m "index") (m "replacement")
        (m "argument") (m "argumentResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmApp (m "function") (m "argument"))
      (tmApp (m "functionResult") (m "argumentResult")))

def substPairRule : RuleSchema :=
  rule "prime-subst-pair"
    ["index", "replacement", "first", "second", "firstResult",
      "secondResult"]
    [substitutesAt (m "index") (m "replacement")
        (m "first") (m "firstResult"),
     substitutesAt (m "index") (m "replacement")
        (m "second") (m "secondResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmPair (m "first") (m "second"))
      (tmPair (m "firstResult") (m "secondResult")))

def substFstRule : RuleSchema :=
  rule "prime-subst-fst" ["index", "replacement", "pair", "pairResult"]
    [substitutesAt (m "index") (m "replacement")
      (m "pair") (m "pairResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmFst (m "pair")) (tmFst (m "pairResult")))

def substSndRule : RuleSchema :=
  rule "prime-subst-snd" ["index", "replacement", "pair", "pairResult"]
    [substitutesAt (m "index") (m "replacement")
      (m "pair") (m "pairResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmSnd (m "pair")) (tmSnd (m "pairResult")))

def substReflRule : RuleSchema :=
  rule "prime-subst-refl" ["index", "replacement", "term", "termResult"]
    [substitutesAt (m "index") (m "replacement")
      (m "term") (m "termResult")]
    (substitutesAt (m "index") (m "replacement")
      (tmRefl (m "term")) (tmRefl (m "termResult")))

/-! ## Root beta -/

def rootBetaRule : RuleSchema :=
  rule "prime-root-beta" ["body", "argument", "result"]
    [substitutesAt zero (m "argument") (m "body") (m "result")]
    (rootBeta (tmApp (tmLam (m "body")) (m "argument")) (m "result"))

def allRules : List RuleSchema :=
  [ltZeroSuccRule, ltSuccSuccRule,
   weakenVarBelowRule, weakenVarAtOrAboveRule,
   weakenConstRule, weakenHeadRule, weakenPiRule, weakenSigmaRule,
   weakenIdRule, weakenLamRule, weakenAppRule, weakenPairRule,
   weakenFstRule, weakenSndRule, weakenReflRule,
   substVarEqualRule, substVarBelowRule, substVarAboveRule,
   substConstRule, substHeadRule, substPiRule, substSigmaRule,
   substIdRule, substLamRule, substAppRule, substPairRule,
   substFstRule, substSndRule, substReflRule, rootBetaRule]

def substitutionDelta : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments :=
      [{ head := "prime-index-lt", arity := 2 },
       { head := "prime-tm-weakens-at", arity := 3 },
       { head := "prime-tm-substitutes-at", arity := 4 },
       { head := "prime-tm-root-beta", arity := 2 }]
    newRules := allRules }

private theorem substitutionDelta_disjoint :
    substitutionDelta.disjointFrom checked.1 = true := by
  decide

private theorem substitutionDelta_policy :
    substitutionDelta.policyHolds checked.1 .newJudgmentsOnly = true := by
  decide

private theorem substitutionTarget_valid :
    (substitutionDelta.apply checked.1).isValid = true := by
  have validatedLanguage :
      (substitutionDelta.apply checked.1).toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [substitutionDelta, CalculusLanguageExtension.apply, checked,
        DeclarationAwareDataLanguage.checked,
        DeclarationAwareDataLanguage.definition,
        DeclarationAwareDataLanguage.constructorArities,
        DeclarationAwareDataLanguage.dataConstructor,
        DeclarationAwareDataLanguage.kernelDataType,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validatedLanguage]
  simp [substitutionDelta, CalculusLanguageExtension.apply, allRules,
    ltZeroSuccRule, ltSuccSuccRule,
    weakenVarBelowRule, weakenVarAtOrAboveRule,
    weakenConstRule, weakenHeadRule, weakenPiRule, weakenSigmaRule,
    weakenIdRule, weakenLamRule, weakenAppRule, weakenPairRule,
    weakenFstRule, weakenSndRule, weakenReflRule,
    substVarEqualRule, substVarBelowRule, substVarAboveRule,
    substConstRule, substHeadRule, substPiRule, substSigmaRule,
    substIdRule, substLamRule, substAppRule, substPairRule,
    substFstRule, substSndRule, substReflRule, rootBetaRule,
    rule, formal, m, ruleId, indexLt, weakensAt, substitutesAt, rootBeta,
    zero, succ, tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
    tmApp, tmPair, tmFst, tmSnd, tmRefl,
    DeclarationAwareDataLanguage.checked,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.kernelDataType,
    CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

/-- The authored binding calculus is a conservative new-judgment extension of
the exact canonical Prime data language. -/
def substitutionExtension :
    ValidatedCalculusLanguageExtension checked where
  extension := substitutionDelta
  policy := .newJudgmentsOnly
  disjoint := substitutionDelta_disjoint
  policyHolds := substitutionDelta_policy
  valid := substitutionTarget_valid

abbrev definition : ValidatedCalculusLanguageDef :=
  substitutionExtension.target

def rawProof (id : String) (arguments : List Pattern)
    (children : List RawProof) : RawProof :=
  .node { ruleId := ruleId id, arguments } children

/-! ## Executable positive and negative controls -/

def variableOpeningInstance (argument : Pattern) : RuleInstance :=
  { ruleId := ruleId "prime-subst-var-equal"
    arguments := [zero, argument] }

def variableBetaInstance (argument : Pattern) : RuleInstance :=
  { ruleId := ruleId "prime-root-beta"
    arguments := [tmVar zero, argument, argument] }

def variableOpeningProof (argument : Pattern) : RawProof :=
  .node (variableOpeningInstance argument) []

def variableBetaProof (argument : Pattern) : RawProof :=
  .node (variableBetaInstance argument)
    [variableOpeningProof argument]

def canaryArgument : Pattern :=
  tmHead (.apply "prime-head-sort"
    [.apply "prime-level-const" [zero]])

private theorem substVarEqual_lookup :
    definition.1.lookupRule? substVarEqualRule.id =
      some substVarEqualRule := by
  apply lookupRule?_eq_some_of_mem definition
  simp [definition, substitutionExtension,
    ValidatedCalculusLanguageExtension.target,
    substitutionDelta, CalculusLanguageExtension.apply, allRules]

private theorem rootBeta_lookup :
    definition.1.lookupRule? rootBetaRule.id = some rootBetaRule := by
  apply lookupRule?_eq_some_of_mem definition
  simp [definition, substitutionExtension,
    ValidatedCalculusLanguageExtension.target,
    substitutionDelta, CalculusLanguageExtension.apply, allRules]

private theorem canaryOpening_instantiates :
    instantiateRule? definition (variableOpeningInstance canaryArgument) =
      some ([], substitutesAt zero canaryArgument (tmVar zero)
        canaryArgument) := by
  unfold instantiateRule?
  rw [show definition.1.lookupRule?
      (variableOpeningInstance canaryArgument).ruleId =
        some substVarEqualRule by
    simpa [variableOpeningInstance, substVarEqualRule, rule, ruleId] using
      substVarEqual_lookup]
  simp [variableOpeningInstance, substVarEqualRule, rule, formal, m, ruleId,
    substitutesAt, tmVar, zero, canaryArgument, tmHead, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?, lookupArgumentAt?]

private theorem canaryBeta_instantiates :
    instantiateRule? definition (variableBetaInstance canaryArgument) =
      some ([substitutesAt zero canaryArgument (tmVar zero) canaryArgument],
        rootBeta (tmApp (tmLam (tmVar zero)) canaryArgument)
          canaryArgument) := by
  unfold instantiateRule?
  rw [show definition.1.lookupRule?
      (variableBetaInstance canaryArgument).ruleId = some rootBetaRule by
    simpa [variableBetaInstance, rootBetaRule, rule, ruleId] using
      rootBeta_lookup]
  simp [variableBetaInstance, rootBetaRule, rule, formal, m, ruleId,
    rootBeta, substitutesAt, tmApp, tmLam, tmVar, zero, canaryArgument,
    tmHead, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemasAt?, lookupArgumentAt?]

/-- The authored checker computes the canonical variable beta redex. -/
theorem canonical_variable_beta_accepts :
    checkRaw definition
      (rootBeta
        (tmApp (tmLam (tmVar zero)) canaryArgument)
        canaryArgument)
      (variableBetaProof canaryArgument) = true := by
  simp [variableBetaProof, variableOpeningProof,
    InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
    canaryBeta_instantiates, canaryOpening_instantiates]

/-- The same proof cannot be replayed against a fabricated beta target. -/
theorem changed_variable_beta_target_rejects :
    checkRaw definition
      (rootBeta
        (tmApp (tmLam (tmVar zero)) canaryArgument)
        (tmVar zero))
      (variableBetaProof canaryArgument) = false := by
  have target_ne :
      rootBeta (tmApp (tmLam (tmVar zero)) canaryArgument)
          canaryArgument ≠
        rootBeta (tmApp (tmLam (tmVar zero)) canaryArgument)
          (tmVar zero) := by
    decide
  simp [variableBetaProof, InferenceChecker.checkRaw,
    canaryBeta_instantiates, target_ne]

/-! ## Axiom audit -/

#print axioms substitutionTarget_valid
#print axioms canonical_variable_beta_accepts
#print axioms changed_variable_beta_target_rejects

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionLanguage
