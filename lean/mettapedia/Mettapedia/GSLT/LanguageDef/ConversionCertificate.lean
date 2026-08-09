import Mettapedia.GSLT.LanguageDef.CheckedSource

/-!
# Explicit conversion certificates through the generic checker

Conversion steps remain ordinary judgments and ordinary proof trees in the
validated presentation.  This module only checks that an explicit sequence of
such steps has the requested endpoints.  It adds no source-specific rule
branch and does not interpret certificate rejection as proof of inequality.
-/

namespace Mettapedia.GSLT.LanguageDef.ConversionCertificate

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource

/-- Evidence that a conversion declaration was obtained from the checked
`LanguageDef`, rather than supplied as a second independent profile. -/
structure RootedConversion (checked : CheckedGSLT) where
  declaration : ConversionDecl
  isRooted :
    checked.source.presentation.conversion = some declaration

def RootedConversion.judgment {checked : CheckedGSLT}
    (conversion : RootedConversion checked)
    (source target : Pattern) : Pattern :=
  .apply conversion.declaration.judgmentHead [source, target]

/-- Untrusted, finite evidence for a reflexive-transitive conversion path. -/
inductive RawConversionCertificate where
  | refl
  | step : (next : Pattern) → RawProof → RawConversionCertificate →
      RawConversionCertificate
deriving Repr

/-- Structurally total certificate replay.  Every non-reflexive edge is
accepted by the same generic checker as every other hosted judgment. -/
def check (checked : CheckedGSLT) (conversion : RootedConversion checked) :
    Pattern → Pattern → RawConversionCertificate → Bool
  | source, target, .refl => decide (source = target)
  | source, target, .step next proof tail =>
      checked.checkRaw (conversion.judgment source next) proof &&
        check checked conversion next target tail
termination_by _ _ certificate => sizeOf certificate

/-- Proof-relevant semantics of an accepted conversion certificate. -/
inductive ConversionDerivation (checked : CheckedGSLT)
    (conversion : RootedConversion checked) : Pattern → Pattern → Type where
  | refl (term : Pattern) : ConversionDerivation checked conversion term term
  | step {source next target : Pattern} :
      Derivation checked.presentation (conversion.judgment source next) →
      ConversionDerivation checked conversion next target →
      ConversionDerivation checked conversion source target

def ConversionDerivation.erase
    {checked : CheckedGSLT} {conversion : RootedConversion checked}
    {source target : Pattern} :
    ConversionDerivation checked conversion source target →
      RawConversionCertificate
  | .refl _ => .refl
  | .step (next := next) head tail =>
      .step next head.erase tail.erase

/-- Certificate acceptance always reconstructs a proof-relevant path. -/
theorem check_soundness {checked : CheckedGSLT}
    {conversion : RootedConversion checked} {source target : Pattern}
    {certificate : RawConversionCertificate}
    (hcheck : check checked conversion source target certificate = true) :
    Nonempty (ConversionDerivation checked conversion source target) := by
  induction certificate generalizing source with
  | refl =>
      simp only [check, decide_eq_true_eq] at hcheck
      subst target
      exact ⟨.refl source⟩
  | step next proof tail ih =>
      simp only [check, Bool.and_eq_true] at hcheck
      rcases CheckedGSLT.checkRaw_soundness hcheck.1 with ⟨head⟩
      rcases ih hcheck.2 with ⟨tailDerivation⟩
      exact ⟨.step head tailDerivation⟩

/-- Erasing a typed conversion derivation yields an accepted certificate. -/
theorem check_erase {checked : CheckedGSLT}
    {conversion : RootedConversion checked} {source target : Pattern}
    (derivation : ConversionDerivation checked conversion source target) :
    check checked conversion source target derivation.erase = true := by
  induction derivation with
  | refl term => simp [ConversionDerivation.erase, check]
  | step head tail ih =>
      simp [ConversionDerivation.erase, check,
        CheckedGSLT.checkRaw_erase head, ih]

/-- Accepted raw certificates are exactly erasures of typed paths, including
the exact intermediate terms and raw edge proofs supplied by the producer. -/
theorem check_exists_derivation_with_exact_erasure
    {checked : CheckedGSLT} {conversion : RootedConversion checked}
    {source target : Pattern} {certificate : RawConversionCertificate}
    (hcheck : check checked conversion source target certificate = true) :
    ∃ derivation : ConversionDerivation checked conversion source target,
      derivation.erase = certificate := by
  induction certificate generalizing source with
  | refl =>
      simp only [check, decide_eq_true_eq] at hcheck
      subst target
      exact ⟨.refl source, rfl⟩
  | step next proof tail ih =>
      simp only [check, Bool.and_eq_true] at hcheck
      rcases CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure hcheck.1 with
        ⟨head, hhead⟩
      rcases ih hcheck.2 with ⟨tailDerivation, htail⟩
      refine ⟨.step head tailDerivation, ?_⟩
      simp [ConversionDerivation.erase, hhead, htail]

/-! ## Conversion through a common reduct

A directed reduction interface does not need a symmetry rule in its authored
calculus.  Definitional conversion can instead be certified by two checked
paths ending at one explicit common reduct. -/

/-- Untrusted evidence that two terms reduce to one supplied common term. -/
structure RawCommonReductCertificate where
  common : Pattern
  left : RawConversionCertificate
  right : RawConversionCertificate
deriving Repr

/-- Check both directed paths against the same rooted conversion relation. -/
def checkCommonReduct (checked : CheckedGSLT)
    (conversion : RootedConversion checked) (left right : Pattern)
    (certificate : RawCommonReductCertificate) : Bool :=
  check checked conversion left certificate.common certificate.left &&
    check checked conversion right certificate.common certificate.right

/-- Proof-relevant meaning of a common-reduct certificate. -/
structure CommonReductDerivation (checked : CheckedGSLT)
    (conversion : RootedConversion checked) (left right : Pattern) where
  common : Pattern
  leftDerivation :
    ConversionDerivation checked conversion left common
  rightDerivation :
    ConversionDerivation checked conversion right common

/-- Accepted common-reduct certificates reconstruct both exact directed
derivations. -/
theorem checkCommonReduct_soundness {checked : CheckedGSLT}
    {conversion : RootedConversion checked} {left right : Pattern}
    {certificate : RawCommonReductCertificate}
    (hcheck :
      checkCommonReduct checked conversion left right certificate = true) :
    Nonempty (CommonReductDerivation checked conversion left right) := by
  simp only [checkCommonReduct, Bool.and_eq_true] at hcheck
  rcases check_soundness hcheck.1 with ⟨leftDerivation⟩
  rcases check_soundness hcheck.2 with ⟨rightDerivation⟩
  exact
    ⟨{ common := certificate.common
       leftDerivation
       rightDerivation }⟩

/-- Erasing two typed paths produces an accepted common-reduct
certificate. -/
theorem checkCommonReduct_erase {checked : CheckedGSLT}
    {conversion : RootedConversion checked} {left right common : Pattern}
    (leftDerivation :
      ConversionDerivation checked conversion left common)
    (rightDerivation :
      ConversionDerivation checked conversion right common) :
    checkCommonReduct checked conversion left right
      { common
        left := leftDerivation.erase
        right := rightDerivation.erase } = true := by
  simp [checkCommonReduct, check_erase]

/-! ## Positive and negative certificate fixtures -/

private def datumConstructor (head : String) : GrammarRule :=
  { label := head
    category := "Datum"
    params := []
    syntaxPattern := [] }

private def conversionLanguage : LanguageDef :=
  { name := "conversion-certificate-fixture"
    types := [TypeDecl.plain "Datum"]
    terms := [datumConstructor "A", datumConstructor "B", datumConstructor "C"]
    equations := []
    rewrites := [] }

private def conversionDecl : ConversionDecl :=
  { judgmentHead := "Converts"
    version := "explicit-certificate-v1" }

private def a : Pattern := .apply "A" []
private def b : Pattern := .apply "B" []
private def c : Pattern := .apply "C" []

private def abRule : RuleSchema :=
  { id := ⟨"A-to-B"⟩
    metavariables := []
    premises := []
    conclusion := .apply conversionDecl.judgmentHead [a, b] }

private def bcRule : RuleSchema :=
  { id := ⟨"B-to-C"⟩
    metavariables := []
    premises := []
    conclusion := .apply conversionDecl.judgmentHead [b, c] }

private def conversionPresentation : Presentation :=
  { language := conversionLanguage
    calculus :=
      { judgments := [{ head := "Converts", arity := 2 }]
        rules := [abRule, bcRule]
        conversion := some conversionDecl } }

private theorem conversionPresentation_language_validate :
    conversionPresentation.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
      conversionPresentation.language <;>
    simp [conversionPresentation, conversionLanguage, datumConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr]

private theorem conversionPresentation_valid :
    conversionPresentation.isValidV2 = true := by
  have hvalidate : conversionPresentation.language.validate = [] :=
    conversionPresentation_language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hvalidate]
  simp [conversionPresentation, conversionLanguage, conversionDecl,
    abRule, bcRule, datumConstructor,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead, a, b, c]
  decide

private def conversionSource : GSLTSource :=
  { identity :=
      { systemId := "conversion-fixture"
        revision := "v1"
        artifactDigest := "sha256:conversion-fixture" }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "conversion"
             version := "v1"
             payload := .apply "ExplicitCertificates" [] }] }
    presentation := conversionPresentation }

private def conversionChecked : CheckedGSLT :=
  { source := conversionSource
    identityValid := by decide
    assumptionsValid := by decide
    profilesValid := by decide
    presentationValid := by
      simpa [conversionSource] using conversionPresentation_valid }

private def rootedConversion : RootedConversion conversionChecked :=
  { declaration := conversionDecl
    isRooted := rfl }

private def abProof : RawProof :=
  .node { ruleId := ⟨"A-to-B"⟩, arguments := [] } []

private def bcProof : RawProof :=
  .node { ruleId := ⟨"B-to-C"⟩, arguments := [] } []

private def acCertificate : RawConversionCertificate :=
  .step b abProof (.step c bcProof .refl)

/-- Positive: two ordinary checked edges form an exact conversion path. -/
example : check conversionChecked rootedConversion a c acCertificate = true := by
  simp [check, RootedConversion.judgment, conversionChecked,
    rootedConversion, acCertificate, abProof,
    bcProof, CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
    conversionSource, conversionPresentation, conversionLanguage,
    conversionDecl, abRule, bcRule, datumConstructor,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    a, b, c]

/-- Positive: reflexivity is literal endpoint equality and needs no rule. -/
example :
    check conversionChecked rootedConversion a a .refl = true := by
  simp [check, a]

/-- Negative: omitting a required edge cannot reach the requested endpoint. -/
example :
    check conversionChecked rootedConversion a c
      (.step b abProof .refl) = false := by
  simp [check, RootedConversion.judgment, conversionChecked,
    rootedConversion, abProof,
    CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
    conversionSource, conversionPresentation, conversionLanguage,
    conversionDecl, abRule, bcRule, datumConstructor,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    a, b, c]

/-- Negative: reordering edge evidence fails at its exact local judgment. -/
example :
    check conversionChecked rootedConversion a c
      (.step b bcProof (.step c abProof .refl)) = false := by
  simp [check, RootedConversion.judgment, conversionChecked,
    rootedConversion, bcProof,
    CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
    conversionSource, conversionPresentation, conversionLanguage,
    conversionDecl, abRule, bcRule, datumConstructor,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    a, b, c]

/-- Negative: certificate rejection is not exposed as mathematical
inequality; it is only failure to establish the requested path. -/
example : check conversionChecked rootedConversion c a .refl = false := by
  simp [check, a, c]

/-- Positive: directed reduction paths certify symmetric conversion through
their shared endpoint without adding a symmetry rule. -/
example :
    checkCommonReduct conversionChecked rootedConversion a c
      { common := c
        left := acCertificate
        right := .refl } = true := by
  simp [checkCommonReduct, acCertificate, check,
    RootedConversion.judgment, conversionChecked, rootedConversion,
    abProof, bcProof, CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
    conversionSource, conversionPresentation, conversionLanguage,
    conversionDecl, abRule, bcRule, datumConstructor,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    a, b, c]

/-- Negative: choosing a non-common endpoint rejects even when one side has a
valid path to a different term. -/
example :
    checkCommonReduct conversionChecked rootedConversion a c
      { common := b
        left := .step b abProof .refl
        right := .refl } = false := by
  simp [checkCommonReduct, check, RootedConversion.judgment,
    conversionChecked, rootedConversion, abProof,
    CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
    InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
    conversionSource, conversionPresentation, conversionLanguage,
    conversionDecl, abRule, bcRule, datumConstructor,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    a, b, c]

end Mettapedia.GSLT.LanguageDef.ConversionCertificate
