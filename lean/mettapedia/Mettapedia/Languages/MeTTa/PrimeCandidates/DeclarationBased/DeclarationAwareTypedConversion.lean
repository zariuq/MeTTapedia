import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareFormedTyping
import Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity

/-!
# Declaration-aware typed conversion in the cumulative-tower candidate root

cumulative-tower candidate's checked structural presentation and its native dependent calculus are
different realization capabilities of one hosted language.  In particular,
the native Pi calculus constructs proof-relevant beta conversion directly,
while the present generic inference presentation covers only a smaller
structural typing fragment.

This module gives both capabilities one exact judgment index:

`Gamma |- source == target : type @ U level`.

Its intrinsic meaning retains context formation, formation of the common
type, both endpoint typings, and the complete typed conversion path.  The
path is never replaced by endpoint equality.  A conservative reflexivity
rule is the first generic-checker image; native Pi beta is a strictly richer
inhabitant of the same semantic family.  Raw ill-typed beta remains outside
that family even though an untyped structural beta receipt exists.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareTypedConversion

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareCheckedContext
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareFormedTyping
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticContextual
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticJudgmentalPi
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticTypedConversion
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.JudgmentalEquality

private abbrev retainedTower :=
  SyntacticJudgmentalPi.TowerExamples.retainedTower

/-! ## Exact judgment index -/

/-- A typed conversion claim in one formed cumulative-tower candidate world.  The common type and
its universe are explicit because cumulativity can provide more than one
formation derivation for the same raw type. -/
structure TypedConversionQuery where
  arity : Nat
  context : Tower.Ctx arity
  levels : LevelSpine arity
  source : Tower.Tm arity
  target : Tower.Tm arity
  type : Tower.Tm arity
  level : LevelExpr

/-- The source endpoint as an ordinary formed-typing query. -/
def TypedConversionQuery.sourceQuery (query : TypedConversionQuery) :
    FormedTypingQuery where
  arity := query.arity
  context := query.context
  levels := query.levels
  subject := query.source
  type := query.type
  level := query.level

/-- The target endpoint as an ordinary formed-typing query. -/
def TypedConversionQuery.targetQuery (query : TypedConversionQuery) :
    FormedTypingQuery where
  arity := query.arity
  context := query.context
  levels := query.levels
  subject := query.target
  type := query.type
  level := query.level

def typedConversionPattern
    (arity context levels source target type level : Pattern) : Pattern :=
  .apply "prime-typed-conversion"
    [arity, context, levels, source, target, type, level]

def encodeTypedConversionQuery (query : TypedConversionQuery) : Pattern :=
  typedConversionPattern (encodeNat query.arity)
    (encodeCtx towerHeadCodec query.context)
    (encodeLevelSpine query.levels)
    (encodeTm towerHeadCodec query.source)
    (encodeTm towerHeadCodec query.target)
    (encodeTm towerHeadCodec query.type)
    (encodeLevel query.level)

def decodeTypedConversionQuery? : Pattern → Option TypedConversionQuery
  | .apply "prime-typed-conversion"
      [arity, context, levels, source, target, type, level] => do
      let n ← decodeNat? arity
      pure
        { arity := n
          context := ← decodeCtx? towerHeadCodec n context
          levels := ← decodeLevelSpine? n levels
          source := ← decodeTm? towerHeadCodec n source
          target := ← decodeTm? towerHeadCodec n target
          type := ← decodeTm? towerHeadCodec n type
          level := ← decodeLevel? level }
  | _ => none

@[simp] theorem decodeTypedConversionQuery?_encode
    (query : TypedConversionQuery) :
    decodeTypedConversionQuery? (encodeTypedConversionQuery query) =
      some query := by
  cases query
  simp [encodeTypedConversionQuery, typedConversionPattern,
    decodeTypedConversionQuery?]

def typedConversionQueryCodec :
    PartialCodec TypedConversionQuery Pattern where
  encode := encodeTypedConversionQuery
  decode := decodeTypedConversionQuery?
  decode_encode := decodeTypedConversionQuery?_encode

theorem encodeTypedConversionQuery_injective :
    Function.Injective encodeTypedConversionQuery :=
  typedConversionQueryCodec.encode_injective

/-- Typing, context formation, formed typing, and typed conversion retain
distinct canonical judgment heads in the one wire language. -/
theorem prior_conversion_images_disjoint :
    EncoderImagesDisjoint towerRootCodec typedConversionQueryCodec := by
  intro prior conversion equality
  rcases prior with (typingOrContext | formed)
  · rcases typingOrContext with (typing | context)
    · cases typing
      cases conversion
      simp [towerRootCodec, sumOfDisjoint, towerJudgmentCodec,
        towerTypingClaimCodec, typingClaimCodec, encodeTypingClaim,
        typedConversionQueryCodec, encodeTypedConversionQuery,
        typedConversionPattern] at equality
    · cases context
      cases conversion
      simp [towerRootCodec, sumOfDisjoint, towerJudgmentCodec,
        contextFormationQueryCodec, encodeContextFormationQuery,
        contextFormedPattern, typedConversionQueryCodec,
        encodeTypedConversionQuery, typedConversionPattern] at equality
  · cases formed
    cases conversion
    simp [towerRootCodec, sumOfDisjoint, formedTypingQueryCodec,
      encodeFormedTypingQuery, formedHasTypePattern,
      typedConversionQueryCodec, encodeTypedConversionQuery,
      typedConversionPattern] at equality

/-- The exact heterogeneous index after adding typed conversion to the cumulative-tower candidate
root. -/
def towerConversionRootCodec :
    PartialCodec
      (((TypingClaim Tower.Head ⊕ ContextFormationQuery) ⊕
          FormedTypingQuery) ⊕ TypedConversionQuery)
      Pattern :=
  sumOfDisjoint towerRootCodec typedConversionQueryCodec
    prior_conversion_images_disjoint

/-! ## Conservative reflexive checker image -/

/-- The generic inference presentation first earns only reflexivity.  Its
single premise is the complete formed-typing judgment, so the rule cannot
manufacture either context formation or endpoint typing. -/
def typedConversionReflRule : RuleSchema :=
  { id := ⟨"prime-typed-conversion-refl"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("levels", 0), ("term", 0),
        ("type", 0), ("level", 0)]
    premises :=
      [formedHasTypePattern (.fvar "arity") (.fvar "context")
        (.fvar "levels") (.fvar "term") (.fvar "type")
        (.fvar "level")]
    conclusion :=
      typedConversionPattern (.fvar "arity") (.fvar "context")
        (.fvar "levels") (.fvar "term") (.fvar "term")
        (.fvar "type") (.fvar "level") }

def typedConversionDelta : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments := [{ head := "prime-typed-conversion", arity := 7 }]
    newRules := [typedConversionReflRule] }

private theorem typedConversionDelta_disjoint :
    typedConversionDelta.disjointFrom formedTypingExtension.target.1 = true := by
  decide

private theorem typedConversionDelta_policy :
    typedConversionDelta.policyHolds formedTypingExtension.target.1
      .newJudgmentsOnly = true := by
  decide

private theorem typedConversionTarget_valid :
    (typedConversionDelta.apply
      formedTypingExtension.target.1).isValid = true := by
  have validatedLanguage :
      (typedConversionDelta.apply
        formedTypingExtension.target.1).toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [typedConversionDelta, CalculusLanguageExtension.apply,
        formedTypingExtension, ValidatedCalculusLanguageExtension.target,
        formedTypingDelta, contextFormationExtension,
        contextFormationDelta,
        DeclarationAwareStructuralTyping.checked,
        DeclarationAwareStructuralTyping.definition,
        DeclarationAwareStructuralTyping.definition,
        DeclarationAwareDataLanguage.definition,
        DeclarationAwareDataLanguage.constructorArities,
        levelSpineNilConstructor, levelSpineSnocConstructor,
        DeclarationAwareDataLanguage.dataConstructor,
        DeclarationAwareDataLanguage.kernelDataType,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [validatedLanguage]
  simp [typedConversionDelta, CalculusLanguageExtension.apply,
    typedConversionReflRule, typedConversionPattern,
    formedTypingExtension, ValidatedCalculusLanguageExtension.target,
    formedTypingDelta, formedTypingRule, formedHasTypePattern,
    contextFormationExtension, contextFormationDelta,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    DeclarationAwareStructuralTyping.hasTypePattern,
    DeclarationAwareStructuralTyping.tmHeadPattern,
    DeclarationAwareStructuralTyping.tmReflPattern,
    DeclarationAwareStructuralTyping.tmIdPattern,
    DeclarationAwareStructuralTyping.tmPiPattern,
    DeclarationAwareStructuralTyping.headSortPattern,
    DeclarationAwareStructuralTyping.levelSuccPattern,
    DeclarationAwareStructuralTyping.levelMaxPattern,
    DeclarationAwareStructuralTyping.natSuccPattern,
    DeclarationAwareStructuralTyping.ctxSnocPattern,
    contextNilRule, contextSnocRule, contextFormedPattern,
    encodeLevelSpine, levelSpineNilConstructor,
    levelSpineSnocConstructor,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.kernelDataType,
    TypeDecl.plain, encodeTowerHead, Tower.zero, encodeLevel, encodeNat,
    encodeCtx, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
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

/-- Reflexive typed conversion is one conservative checked capability over
the existing cumulative-tower candidate root. -/
def typedConversionExtension :
    ValidatedCalculusLanguageExtension formedTypingExtension.target where
  extension := typedConversionDelta
  policy := .newJudgmentsOnly
  disjoint := typedConversionDelta_disjoint
  policyHolds := typedConversionDelta_policy
  valid := typedConversionTarget_valid

/-! ## Intrinsic proof-relevant meaning -/

/-- The formed context selected by retained structural context evidence. -/
def TypedConversionQuery.formedContext (query : TypedConversionQuery)
    (formation : StructuralContextFormation query.context query.levels) :
    FormedContext Tower.rules where
  arity := query.arity
  context := query.context
  wellFormed := formation.toContextWellFormed

/-- The common formed type of both conversion endpoints. -/
def TypedConversionQuery.typeOver (query : TypedConversionQuery)
    (contextFormation :
      StructuralContextFormation query.context query.levels)
    (typeFormation :
      Tower.HasType query.context query.type
        (.head (.sort query.level))) :
    TypeOver (query.formedContext contextFormation) where
  code := query.type
  level := .sort query.level
  isUniverse := .sort query.level
  formed := typeFormation

/-- The source endpoint as an intrinsic term of the retained common type. -/
def TypedConversionQuery.sourceTerm (query : TypedConversionQuery)
    (contextFormation :
      StructuralContextFormation query.context query.levels)
    (typeFormation :
      Tower.HasType query.context query.type
        (.head (.sort query.level)))
    (sourceTyping : Tower.HasType query.context query.source query.type) :
    Term (query.formedContext contextFormation)
      (query.typeOver contextFormation typeFormation) where
  code := query.source
  typed := sourceTyping

/-- The target endpoint as an intrinsic term of the same retained type. -/
def TypedConversionQuery.targetTerm (query : TypedConversionQuery)
    (contextFormation :
      StructuralContextFormation query.context query.levels)
    (typeFormation :
      Tower.HasType query.context query.type
        (.head (.sort query.level)))
    (targetTyping : Tower.HasType query.context query.target query.type) :
    Term (query.formedContext contextFormation)
      (query.typeOver contextFormation typeFormation) where
  code := query.target
  typed := targetTyping

/-- Intrinsic typed conversion in one common judgment fibre.  Structural
context evidence remains proof-relevant, the endpoint typing obligations are
the native cumulative calculus, and the conversion path retains every
primitive receipt and intermediate typed term. -/
structure IntrinsicTypedConversion
    (query : TypedConversionQuery) : Type where
  contextFormation :
    StructuralContextFormation query.context query.levels
  typeFormation :
    Tower.HasType query.context query.type (.head (.sort query.level))
  sourceTyping : Tower.HasType query.context query.source query.type
  targetTyping : Tower.HasType query.context query.target query.type
  conversion :
    ConversionEvidence
      (termComputation retainedTower
        (query.formedContext contextFormation))
      (query.sourceTerm contextFormation typeFormation sourceTyping)
      (query.targetTerm contextFormation typeFormation targetTyping)

namespace IntrinsicTypedConversion

/-- A formed structural typing judgment embeds into reflexive native
conversion without replaying a checker. -/
def reflOfFormed {query : FormedTypingQuery}
    (evidence : IntrinsicFormedTyping query) :
    IntrinsicTypedConversion
      { arity := query.arity
        context := query.context
        levels := query.levels
        source := query.subject
        target := query.subject
        type := query.type
        level := query.level } where
  contextFormation := evidence.contextFormation
  typeFormation := evidence.typeFormation.toHasType
  sourceTyping := evidence.subjectTyping.toHasType
  targetTyping := evidence.subjectTyping.toHasType
  conversion := .refl _

end IntrinsicTypedConversion

/-- Canonical semantic view of native typed conversion. -/
def TypedConversionCanonicalMeaning (goal : Pattern) : Type :=
  UniversalFibre typedConversionQueryCodec IntrinsicTypedConversion goal

def TowerConversionRootEvidence :
    (((TypingClaim Tower.Head ⊕ ContextFormationQuery) ⊕
        FormedTypingQuery) ⊕ TypedConversionQuery) → Type :=
  SumEvidence TowerRootEvidence IntrinsicTypedConversion

def TowerConversionRootMeaning (goal : Pattern) : Type :=
  TowerRootMeaning goal × TypedConversionCanonicalMeaning goal

def TowerConversionRootSumMeaning (goal : Pattern) : Type :=
  UniversalFibre towerConversionRootCodec TowerConversionRootEvidence goal

/-- The usable product semantics is exactly the universal fibre of the one
heterogeneous cumulative-tower candidate root. -/
def towerConversionRootMeaning_equiv_sumFibre (goal : Pattern) :
    TowerConversionRootMeaning goal ≃ TowerConversionRootSumMeaning goal := by
  simpa [TowerConversionRootMeaning, TowerConversionRootSumMeaning,
    TowerConversionRootEvidence, TypedConversionCanonicalMeaning,
    towerConversionRootCodec] using
    (Equiv.prodCongr (towerRootMeaning_equiv_sumFibre goal)
      (Equiv.refl (TypedConversionCanonicalMeaning goal))).trans
      (universalFibre_product_equiv_sumOfDisjoint
        towerRootCodec typedConversionQueryCodec
        prior_conversion_images_disjoint TowerRootEvidence
        IntrinsicTypedConversion goal)

/-! ## Compositional semantics of the checked reflexive image -/

private theorem conversionEncoding_not_formedTargetShape
    (query : TypedConversionQuery) :
    formedTypingExtension.target.1.hasJudgmentShape
        (encodeTypedConversionQuery query) = false := by
  cases query
  simp [formedTypingExtension, ValidatedCalculusLanguageExtension.target,
    formedTypingDelta, CalculusLanguageExtension.apply,
    contextFormationExtension, contextFormationDelta,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareDataLanguage.definition,
    CalculusLanguageDef.hasJudgmentShape, CalculusLanguageDef.lookupJudgment?,
    encodeTypedConversionQuery, typedConversionPattern]

private theorem typedConversionCodec_avoids_baseConclusions :
    CalculusLanguageConclusionsAvoid formedTypingExtension.target
      typedConversionQueryCodec := by
  intro ruleInstance premises conclusion application query equality
  have shape := application.conclusion_hasJudgmentShape
  rw [← equality] at shape
  change
    formedTypingExtension.target.1.hasJudgmentShape
      (encodeTypedConversionQuery query) = true at shape
  rw [conversionEncoding_not_formedTargetShape] at shape
  contradiction

/-- Retained cumulative-tower candidate rules acquire the larger semantic family without gaining
conversion evidence at conclusions outside the conversion image. -/
noncomputable def towerConversionBaseSemantics :
    CalculusLanguageSemantics formedTypingExtension.target
      TowerConversionRootMeaning :=
  Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure.CalculusLanguageSemantics.productWithVacuousFibre
    formedTypingSemanticExtension.targetSemantics
      typedConversionQueryCodec IntrinsicTypedConversion
      typedConversionCodec_avoids_baseConclusions

private def typedConversionReflConclusion_reflects
    (query : TypedConversionQuery)
    (arityPattern contextPattern levelsPattern termPattern typePattern
      levelPattern : Pattern)
    (premiseMeaning :
      TowerConversionRootMeaning
        (formedHasTypePattern arityPattern contextPattern levelsPattern
          termPattern typePattern levelPattern))
    (equality :
      encodeTypedConversionQuery query =
        typedConversionPattern arityPattern contextPattern levelsPattern
          termPattern termPattern typePattern levelPattern) :
    IntrinsicTypedConversion query := by
  rcases query with
    ⟨arity, context, levels, source, target, type, level⟩
  simp only [encodeTypedConversionQuery, typedConversionPattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have sourceTarget : source = target := by
    apply (tmCodec towerHeadCodec arity).encode_injective
    exact equality.2.2.2.1.trans equality.2.2.2.2.1.symm
  subst target
  let formedQuery : FormedTypingQuery :=
    { arity := arity
      context := context
      levels := levels
      subject := source
      type := type
      level := level }
  have formedEquality :
      encodeFormedTypingQuery formedQuery =
        formedHasTypePattern arityPattern contextPattern levelsPattern
          termPattern typePattern levelPattern := by
    simp only [formedQuery, encodeFormedTypingQuery, formedHasTypePattern,
      Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
    exact
      ⟨equality.1, equality.2.1, equality.2.2.1,
        equality.2.2.2.1, equality.2.2.2.2.2.1,
        equality.2.2.2.2.2.2⟩
  exact IntrinsicTypedConversion.reflOfFormed
    (premiseMeaning.1.2 formedQuery formedEquality)

private def typedConversionAddedMeaning
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (lookup :
      typedConversionExtension.target.1.lookupRule? ruleInstance.ruleId =
        some typedConversionReflRule)
    (application :
      RuleApplication typedConversionExtension.target ruleInstance premises
        conclusion)
    (premiseEvidence : EvidenceList TowerConversionRootMeaning premises) :
    TowerConversionRootMeaning conclusion := by
  have instantiated :=
    instantiateRule?_eq_some_iff_application.mpr application
  rcases ruleInstance with ⟨ruleId, arguments⟩
  cases arguments with
  | nil =>
      simp [instantiateRule?, lookup, typedConversionReflRule,
        argumentsValidAt] at instantiated
  | cons arityPattern remaining =>
    cases remaining with
    | nil =>
        simp [instantiateRule?, lookup, typedConversionReflRule,
          argumentsValidAt] at instantiated
    | cons contextPattern remaining =>
      cases remaining with
      | nil =>
          simp [instantiateRule?, lookup, typedConversionReflRule,
            argumentsValidAt] at instantiated
      | cons levelsPattern remaining =>
        cases remaining with
        | nil =>
            simp [instantiateRule?, lookup, typedConversionReflRule,
              argumentsValidAt] at instantiated
        | cons termPattern remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, typedConversionReflRule,
                argumentsValidAt] at instantiated
          | cons typePattern remaining =>
            cases remaining with
            | nil =>
                simp [instantiateRule?, lookup, typedConversionReflRule,
                  argumentsValidAt] at instantiated
            | cons levelPattern remaining =>
              cases remaining with
              | cons extra tail =>
                  simp [instantiateRule?, lookup, typedConversionReflRule,
                    argumentsValidAt] at instantiated
              | nil =>
                  simp [instantiateRule?, lookup, typedConversionReflRule,
                    RuleSchema.sideConditionsHold, argumentsValidAt,
                    instantiateSchema?, instantiateSchemaAt?,
                    instantiateSchemas?, instantiateSchemasAt?,
                    lookupArgumentAt?, formedHasTypePattern,
                    typedConversionPattern] at instantiated
                  rcases instantiated with ⟨_, rfl, rfl⟩
                  cases premiseEvidence with
                  | cons premiseMeaning rest =>
                    cases rest
                    exact
                      ⟨⟨⟨fun typingQuery equality => by
                              cases typingQuery
                              simp [towerTypingClaimCodec, typingClaimCodec,
                                encodeTypingClaim] at equality,
                            fun contextQuery equality => by
                              cases contextQuery
                              simp [contextFormationQueryCodec,
                                encodeContextFormationQuery,
                                contextFormedPattern] at equality⟩,
                          fun formedQuery equality => by
                            cases formedQuery
                            simp [formedTypingQueryCodec,
                              encodeFormedTypingQuery,
                              formedHasTypePattern] at equality⟩,
                        fun query equality =>
                          typedConversionReflConclusion_reflects query
                            arityPattern contextPattern levelsPattern
                            termPattern typePattern levelPattern
                            premiseMeaning equality⟩

/-- Every checked derivation in the enlarged cumulative-tower candidate presentation has the one
rooted intrinsic meaning.  Retained rules preserve their earlier evidence;
the new reflexivity rule constructs typed conversion directly from its formed
typing premise. -/
noncomputable def typedConversionSemanticExtension :
    SemanticExtension formedTypingExtension.target typedConversionExtension
      TowerConversionRootMeaning where
  baseSemantics := towerConversionBaseSemantics
  addedRuleMeaning := by
    intro rule member ruleInstance premises conclusion lookup application
      premiseEvidence
    have ruleEquality : rule = typedConversionReflRule := by
      simpa [typedConversionExtension, typedConversionDelta] using member
    subst rule
    exact typedConversionAddedMeaning ruleInstance premises conclusion lookup
      application premiseEvidence

/-! ## Exact checked ingress for the reflexive fragment -/

/-- Promote one formed-typing query to the diagonal conversion claim. -/
def TypedConversionQuery.refl (query : FormedTypingQuery) :
    TypedConversionQuery where
  arity := query.arity
  context := query.context
  levels := query.levels
  source := query.subject
  target := query.subject
  type := query.type
  level := query.level

/-- Exact arguments of the generic reflexivity rule. -/
def conversionReflArguments
    (query : FormedTypingQuery) : List Pattern :=
  [encodeNat query.arity, encodeCtx towerHeadCodec query.context,
    encodeLevelSpine query.levels, encodeTm towerHeadCodec query.subject,
    encodeTm towerHeadCodec query.type, encodeLevel query.level]

/-- One raw boundary node whose child proves complete formed typing. -/
def checkedReflRaw (query : FormedTypingQuery) (formedProof : RawProof) :
    RawProof :=
  .node
    { ruleId := typedConversionReflRule.id
      arguments := conversionReflArguments query }
    [formedProof]

private theorem instantiateTypedConversionReflRule
    (query : FormedTypingQuery) :
    instantiateRule? typedConversionExtension.target
        { ruleId := typedConversionReflRule.id
          arguments := conversionReflArguments query } =
      some
        ([encodeFormedTypingQuery query],
          encodeTypedConversionQuery (TypedConversionQuery.refl query)) := by
  have arityValid := encodeNat_argumentValid query.arity
  have contextValid := encodeTowerCtx_argumentValid query.context
  have levelsValid := encodeLevelSpine_argumentValid query.levels
  have subjectValid := encodeTowerTm_argumentValid query.subject
  have typeValid := encodeTowerTm_argumentValid query.type
  have levelValid := encodeLevel_argumentValid query.level
  simp [typedConversionExtension, ValidatedCalculusLanguageExtension.target,
    typedConversionDelta, CalculusLanguageExtension.apply,
    formedTypingExtension, ValidatedCalculusLanguageExtension.target, formedTypingDelta,
    contextFormationExtension, ValidatedCalculusLanguageExtension.target,
    contextFormationDelta,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    contextNilRule, contextSnocRule, formedTypingRule,
    typedConversionReflRule, conversionReflArguments,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    arityValid, contextValid, levelsValid, subjectValid, typeValid, levelValid,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, encodeFormedTypingQuery, formedHasTypePattern,
    TypedConversionQuery.refl, encodeTypedConversionQuery,
    typedConversionPattern]

/-- Boundary adequacy in the positive direction: any accepted formed proof
becomes one accepted reflexive conversion proof, with the exact child artifact
retained. -/
theorem checkedReflRaw_accepted
    (query : FormedTypingQuery) (formedProof : RawProof)
    (accepted :
      InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query) formedProof = true) :
    InferenceChecker.checkRaw typedConversionExtension.target
        (encodeTypedConversionQuery (TypedConversionQuery.refl query))
        (checkedReflRaw query formedProof) = true := by
  have childAccepted :=
    checkRaw_true_of_ruleLookupRefines typedConversionExtension.refines
      accepted
  simpa only [checkedReflRaw, InferenceChecker.checkRaw,
    instantiateTypedConversionReflRule, decide_true, Bool.true_and,
    InferenceChecker.checkRawChildren, Bool.and_true] using childAccepted

/-- The deliberately small generic-checker image is diagonal: any derivation
of the new judgment concludes conversion from a term to that same term.  This
does not constrain richer native realizations of the intrinsic family. -/
theorem checkedConversionDerivation_endpoints_eq
    (query : TypedConversionQuery)
    (derivation :
      Derivation typedConversionExtension.target
        (encodeTypedConversionQuery query)) :
    query.source = query.target := by
  cases derivation with
  | byRule ruleInstance application children =>
    rcases
        Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension.SemanticExtension.target_application_classifies
          application with baseApplication | ⟨rule, member, lookup⟩
    · have shape := baseApplication.conclusion_hasJudgmentShape
      rw [conversionEncoding_not_formedTargetShape query] at shape
      contradiction
    · have ruleEquality : rule = typedConversionReflRule := by
        simpa [typedConversionExtension, typedConversionDelta] using member
      subst rule
      have instantiated :=
        instantiateRule?_eq_some_iff_application.mpr application
      rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | nil =>
          simp [instantiateRule?, lookup, typedConversionReflRule,
            argumentsValidAt] at instantiated
      | cons arityPattern remaining =>
        cases remaining with
        | nil =>
            simp [instantiateRule?, lookup, typedConversionReflRule,
              argumentsValidAt] at instantiated
        | cons contextPattern remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, typedConversionReflRule,
                argumentsValidAt] at instantiated
          | cons levelsPattern remaining =>
            cases remaining with
            | nil =>
                simp [instantiateRule?, lookup, typedConversionReflRule,
                  argumentsValidAt] at instantiated
            | cons termPattern remaining =>
              cases remaining with
              | nil =>
                  simp [instantiateRule?, lookup, typedConversionReflRule,
                    argumentsValidAt] at instantiated
              | cons typePattern remaining =>
                cases remaining with
                | nil =>
                    simp [instantiateRule?, lookup, typedConversionReflRule,
                      argumentsValidAt] at instantiated
                | cons levelPattern remaining =>
                  cases remaining with
                  | cons extra tail =>
                      simp [instantiateRule?, lookup,
                        typedConversionReflRule, argumentsValidAt] at instantiated
                  | nil =>
                      simp [instantiateRule?, lookup,
                        typedConversionReflRule,
                        RuleSchema.sideConditionsHold, argumentsValidAt,
                        instantiateSchema?, instantiateSchemaAt?,
                        instantiateSchemas?, instantiateSchemasAt?,
                        lookupArgumentAt?, formedHasTypePattern,
                        typedConversionPattern] at instantiated
                      rcases instantiated with ⟨_, _, conclusionEquality⟩
                      rcases query with
                        ⟨arity, context, levels, source, target, type, level⟩
                      simp only [encodeTypedConversionQuery,
                        typedConversionPattern, Pattern.apply.injEq,
                        List.cons.injEq, and_true, true_and] at conclusionEquality
                      apply (tmCodec towerHeadCodec arity).encode_injective
                      exact conclusionEquality.2.2.2.1.symm.trans
                        conclusionEquality.2.2.2.2.1

/-! ## Native positive and negative controls -/

namespace NativeExamples

private abbrev levelOne : LevelExpr := .succ Tower.zero
private abbrev levelTwo : LevelExpr := .succ levelOne

open SyntacticTypedConversion.TowerExamples

/-- Positive generic-checker control: the already formed Pi term passes
through the exact reflexive boundary node. -/
theorem simplePi_refl_checked :
    InferenceChecker.checkRaw typedConversionExtension.target
        (encodeTypedConversionQuery
          (TypedConversionQuery.refl
            DeclarationAwareFormedTyping.Examples.simplePiQuery))
        (checkedReflRaw
          DeclarationAwareFormedTyping.Examples.simplePiQuery
          (DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw.derived
            DeclarationAwareFormedTyping.Examples.simplePiQuery)) = true :=
  checkedReflRaw_accepted
    DeclarationAwareFormedTyping.Examples.simplePiQuery
    (DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw.derived
      DeclarationAwareFormedTyping.Examples.simplePiQuery)
    DeclarationAwareFormedTyping.Examples.simplePi_derived_raw_accepted

/-- The nontrivial Pi-beta conversion already constructed by cumulative-tower candidate's native
dependent calculus, stated in the single rooted conversion index. -/
def betaQuery : TypedConversionQuery where
  arity := 0
  context := .nil
  levels := .nil
  source := betaSource.code
  target := betaTarget.code
  type := universeOneDisplay.type.code
  level := levelTwo

/-- Native Pi computation constructs the complete typed judgment directly;
there is no post-hoc conversion check in this value. -/
def betaIntrinsic : IntrinsicTypedConversion betaQuery where
  contextFormation := .nil
  typeFormation := universeOneDisplay.type.formed
  sourceTyping := betaSource.typed
  targetTyping := betaTarget.typed
  conversion := betaTypedConversion

/-- The rooted native inhabitant is genuinely computational: its endpoint
syntax is unequal. -/
theorem betaIntrinsic_endpoints_ne :
    betaQuery.source ≠ betaQuery.target :=
  betaTypedConversion_endpoints_ne

/-- Strict capability witness: native Pi beta inhabits the common intrinsic
judgment but lies outside the deliberately reflexive generic-checker image. -/
theorem beta_has_no_checked_refl_derivation :
    ¬ Nonempty
      (Derivation typedConversionExtension.target
        (encodeTypedConversionQuery betaQuery)) := by
  rintro ⟨derivation⟩
  exact betaIntrinsic_endpoints_ne
    (checkedConversionDerivation_endpoints_eq betaQuery derivation)

/-- The beta inhabitant appears in the exact universal semantic fibre of the
same wire judgment used by every other cumulative-tower candidate root component. -/
def betaCanonicalMeaning :
    TypedConversionCanonicalMeaning (encodeTypedConversionQuery betaQuery) :=
  fun query equality => by
    exact encodeTypedConversionQuery_injective equality |>.symm ▸ betaIntrinsic

/-- Raw beta reduction can erase an untypable argument.  This query therefore
has an untyped structural step but no inhabitant of the typed conversion
family. -/
def illTypedBetaQuery : TypedConversionQuery where
  arity := 0
  context := .nil
  levels := .nil
  source := illTypedBetaSource
  target := betaTarget.code
  type := universeOneDisplay.type.code
  level := levelTwo

theorem illTypedBetaQuery_has_raw_step :
    Nonempty
      (ProofRelevantStructuralComputation.StructuralStepReceipt
        retainedTower.computation Tower.rules.headEq
        illTypedBetaQuery.source illTypedBetaQuery.target) := by
  exact ⟨illTypedBetaStep⟩

/-- Negative control: structural computation alone cannot mint a typed
conversion judgment. -/
theorem illTypedBetaQuery_has_no_intrinsic_conversion :
    ¬ Nonempty (IntrinsicTypedConversion illTypedBetaQuery) := by
  rintro ⟨evidence⟩
  exact illTypedBetaSource_not_typed evidence.sourceTyping

end NativeExamples

/-! ## Axiom audit -/

#print axioms encodeTypedConversionQuery_injective
#print axioms prior_conversion_images_disjoint
#print axioms towerConversionRootMeaning_equiv_sumFibre
#print axioms IntrinsicTypedConversion.reflOfFormed
#print axioms typedConversionSemanticExtension
#print axioms checkedReflRaw_accepted
#print axioms checkedConversionDerivation_endpoints_eq
#print axioms NativeExamples.simplePi_refl_checked
#print axioms NativeExamples.betaIntrinsic
#print axioms NativeExamples.betaIntrinsic_endpoints_ne
#print axioms NativeExamples.beta_has_no_checked_refl_derivation
#print axioms NativeExamples.betaCanonicalMeaning
#print axioms NativeExamples.illTypedBetaQuery_has_raw_step
#print axioms NativeExamples.illTypedBetaQuery_has_no_intrinsic_conversion

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareTypedConversion
