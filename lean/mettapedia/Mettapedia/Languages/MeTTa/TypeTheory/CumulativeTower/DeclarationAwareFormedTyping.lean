import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareCheckedContext
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticTypedConversion
import Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Formed declaration-aware Prime judgments

The structural Prime presentation checks judgments of the form
`Gamma |- term : type`.  A native dependent-type-theoretic judgment needs one
more piece of data: the universe in which `type` was formed.  This module
packages that stronger object without introducing a second typing relation.

A formed query retains the context's universe spine and the result universe
level explicitly.  Its evidence is the ordered triple

* `Gamma` is formed at the retained spine;
* `Gamma |- type : U level`;
* `Gamma |- term : type`.

All three premises are checked by the same validated structural presentation and
interpreted by its independently defined intrinsic semantics.  Together with
formation of `Gamma`, they construct a displayed type and an intrinsic term in
the syntactic contextual category.  Thus checking is an ingress theorem; the
resulting native object does not contain or call a checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareCheckedContext
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticTypedConversion
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Structural

abbrev checked := DeclarationAwareStructuralTyping.checked
abbrev StructuralTyping {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) :=
  DeclarationAwareStructuralTyping.StructuralTyping context term type
abbrev CanonicalMeaning := DeclarationAwareStructuralTyping.CanonicalMeaning

end Structural

/-! ## The universe-indexed query and its exact wire image -/

/-- A scope-coherent typing claim together with the universe level at which
its expected type is required to be formed. -/
structure FormedTypingQuery where
  arity : Nat
  context : Tower.Ctx arity
  levels : LevelSpine arity
  subject : Tower.Tm arity
  type : Tower.Tm arity
  level : LevelExpr

/-- The context-formation premise selected by a formed query. -/
def FormedTypingQuery.contextClaim (query : FormedTypingQuery) :
    ContextFormationQuery where
  arity := query.arity
  context := query.context
  levels := query.levels

/-- The ordinary typing premise of a formed query. -/
def FormedTypingQuery.subjectClaim (query : FormedTypingQuery) :
    TypingClaim Tower.Head where
  arity := query.arity
  context := query.context
  subject := query.subject
  type := query.type

/-- The type-formation premise of a formed query. -/
def FormedTypingQuery.formationClaim (query : FormedTypingQuery) :
    TypingClaim Tower.Head where
  arity := query.arity
  context := query.context
  subject := query.type
  type := .head (.sort query.level)

/-- Surface constructor for the derived formed-typing judgment. -/
def formedHasTypePattern
    (arity context levels subject type level : Pattern) : Pattern :=
  .apply "prime-formed-has-type"
    [arity, context, levels, subject, type, level]

/-- Canonical surface form of a formed typing judgment.  The universe level is
not inferred from the four-field claim because cumulative presentations may
offer more than one formation derivation for the same raw type. -/
def encodeFormedTypingQuery (query : FormedTypingQuery) : Pattern :=
  formedHasTypePattern (encodeNat query.arity)
    (encodeCtx towerHeadCodec query.context)
    (encodeLevelSpine query.levels)
    (encodeTm towerHeadCodec query.subject)
    (encodeTm towerHeadCodec query.type) (encodeLevel query.level)

def decodeFormedTypingQuery? : Pattern → Option FormedTypingQuery
  | .apply "prime-formed-has-type"
      [arity, context, levels, subject, type, level] => do
      let n ← decodeNat? arity
      pure
        { arity := n
          context := ← decodeCtx? towerHeadCodec n context
          levels := ← decodeLevelSpine? n levels
          subject := ← decodeTm? towerHeadCodec n subject
          type := ← decodeTm? towerHeadCodec n type
          level := ← decodeLevel? level }
  | _ => none

@[simp] theorem decodeFormedTypingQuery?_encode
    (query : FormedTypingQuery) :
    decodeFormedTypingQuery? (encodeFormedTypingQuery query) = some query := by
  cases query
  simp [encodeFormedTypingQuery, formedHasTypePattern,
    decodeFormedTypingQuery?]

def formedTypingQueryCodec : PartialCodec FormedTypingQuery Pattern where
  encode := encodeFormedTypingQuery
  decode := decodeFormedTypingQuery?
  decode_encode := decodeFormedTypingQuery?_encode

theorem encodeFormedTypingQuery_injective :
    Function.Injective encodeFormedTypingQuery :=
  formedTypingQueryCodec.encode_injective

/-- The already-rooted typing/context presentation and the new formed-typing
judgment have disjoint canonical images.  This is stronger than merely having
different decoders: it makes judgment identity stable under exact replay. -/
theorem prior_formed_images_disjoint :
    EncoderImagesDisjoint primeJudgmentCodec formedTypingQueryCodec := by
  intro prior formed equality
  cases prior with
  | inl typing =>
      cases typing
      cases formed
      simp [primeJudgmentCodec, sumOfDisjoint, towerTypingClaimCodec,
        typingClaimCodec, encodeTypingClaim, formedTypingQueryCodec,
        encodeFormedTypingQuery, formedHasTypePattern] at equality
  | inr context =>
      cases context
      cases formed
      simp [primeJudgmentCodec, sumOfDisjoint,
        contextFormationQueryCodec, encodeContextFormationQuery,
        contextFormedPattern, formedTypingQueryCodec,
        encodeFormedTypingQuery, formedHasTypePattern] at equality

/-- The exact index of the first single-root Prime presentation: ordinary
typing, context formation, and formed typing inhabit one canonical wire waist. -/
def primeRootCodec :
    PartialCodec
      ((TypingClaim Tower.Head ⊕ ContextFormationQuery) ⊕ FormedTypingQuery)
      Pattern :=
  sumOfDisjoint primeJudgmentCodec formedTypingQueryCodec
    prior_formed_images_disjoint

/-! ## Conservative one-node packaging -/

/-- The derived rule packages type formation followed by subject typing.  It
does not add a new primitive typing principle. -/
def formedTypingRule : RuleSchema :=
  { id := ⟨"prime-structural-formed-typing"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("levels", 0), ("subject", 0),
        ("type", 0), ("level", 0)]
    premises :=
      [contextFormedPattern (.fvar "arity") (.fvar "context")
        (.fvar "levels"),
       DeclarationAwareStructuralTyping.hasTypePattern
        (.fvar "arity") (.fvar "context") (.fvar "type")
        (DeclarationAwareStructuralTyping.tmHeadPattern
          (DeclarationAwareStructuralTyping.headSortPattern (.fvar "level"))),
       DeclarationAwareStructuralTyping.hasTypePattern
        (.fvar "arity") (.fvar "context") (.fvar "subject")
        (.fvar "type")]
    conclusion :=
      formedHasTypePattern (.fvar "arity") (.fvar "context")
        (.fvar "levels") (.fvar "subject") (.fvar "type")
        (.fvar "level") }

def formedTypingDelta : CalculusLanguageExtension :=
  { newTerms := []
    newJudgments := [{ head := "prime-formed-has-type", arity := 6 }]
    newRules := [formedTypingRule] }

private theorem formedTypingDelta_disjoint :
    formedTypingDelta.disjointFrom contextFormationExtension.target.1 = true := by
  decide

private theorem formedTypingDelta_policy :
    formedTypingDelta.policyHolds contextFormationExtension.target.1
      .newJudgmentsOnly = true := by
  decide

private theorem formedTypingTarget_valid :
    (formedTypingDelta.apply contextFormationExtension.target.1).isValid = true := by
  have validatedLanguage :
      (formedTypingDelta.apply
        contextFormationExtension.target.1).toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [formedTypingDelta, contextFormationExtension,
        ValidatedCalculusLanguageExtension.target, contextFormationDelta,
        CalculusLanguageExtension.apply,
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
  simp [formedTypingDelta, CalculusLanguageExtension.apply, formedTypingRule,
    formedHasTypePattern, contextFormationExtension,
    ValidatedCalculusLanguageExtension.target, contextFormationDelta,
    CalculusLanguageExtension.apply,
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
    DeclarationAwareStructuralTyping.ctxSnocPattern, contextNilRule,
    contextSnocRule, contextFormedPattern, encodeLevelSpine,
    levelSpineNilConstructor, levelSpineSnocConstructor,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.kernelDataType,
    TypeDecl.plain,
    encodeTowerHead, Tower.zero, encodeLevel, encodeNat, encodeCtx,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

/-- The formed judgment is a validated conservative extension of the one
structural Prime presentation. -/
def formedTypingExtension :
    ValidatedCalculusLanguageExtension contextFormationExtension.target where
  extension := formedTypingDelta
  policy := .newJudgmentsOnly
  disjoint := formedTypingDelta_disjoint
  policyHolds := formedTypingDelta_policy
  valid := formedTypingTarget_valid

/-! ## Intrinsic evidence and native construction -/

/-- The intrinsic meaning of a formed query.  All three fields reuse the one
declaration-aware presentation; their order mirrors formation followed by
bidirectional checking. -/
structure IntrinsicFormedTyping (query : FormedTypingQuery) : Type where
  contextFormation :
    StructuralContextFormation query.context query.levels
  typeFormation :
    Structural.StructuralTyping query.context query.type
      (.head (.sort query.level))
  subjectTyping :
    Structural.StructuralTyping query.context query.subject query.type

/-- A formed native goal additionally retains positive context-formation
evidence.  Raw structural proof search remains meaningful without this field,
but it cannot construct a native contextual term. -/
structure NativeGoal where
  query : FormedTypingQuery
  contextWellFormed : ContextWellFormed Tower.rules query.context

namespace NativeGoal

/-- The ambient world as an object of Prime's syntactic contextual category. -/
def formedContext (goal : NativeGoal) : FormedContext Tower.rules where
  arity := goal.query.arity
  context := goal.query.context
  wellFormed := goal.contextWellFormed

/-- The selected universe displayed as a formed type in the ambient world. -/
def displayedUniverse (goal : NativeGoal) :
    DisplayedUniverse goal.formedContext where
  level := .sort goal.query.level
  upper := .sort (.succ goal.query.level)
  levelIsUniverse := .sort goal.query.level
  upperIsUniverse := .sort (.succ goal.query.level)
  formation := .sort goal.query.level

def surface (goal : NativeGoal) : Pattern :=
  encodeFormedTypingQuery goal.query

/-- Forgetting proof-irrelevant context formation remains injective because
the complete raw query, including its selected universe level, is retained. -/
theorem query_injective :
    Function.Injective (fun goal : NativeGoal ↦ goal.query) := by
  intro first second equality
  cases first with
  | mk firstQuery firstFormed =>
      cases second with
      | mk secondQuery secondFormed =>
          dsimp at equality
          subst secondQuery
          rfl

theorem surface_injective : Function.Injective surface := by
  intro first second equality
  apply query_injective
  exact encodeFormedTypingQuery_injective equality

end NativeGoal

namespace IntrinsicFormedTyping

/-- Checked intrinsic context evidence supplies the full context witness used
by the syntactic contextual category. -/
def nativeGoal {query : FormedTypingQuery}
    (evidence : IntrinsicFormedTyping query) : NativeGoal where
  query := query
  contextWellFormed := evidence.contextFormation.toContextWellFormed

/-- The expected type becomes an intrinsic term of the selected displayed
universe. -/
def displayedType {query : FormedTypingQuery} (goal : NativeGoal)
    (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    DisplayedType goal.displayedUniverse := by
  subst query
  exact
    { code := goal.query.type
      typed := evidence.typeFormation.toHasType }

/-- Forget the displayed-universe presentation while retaining the same type
formation derivation. -/
def typeOver {query : FormedTypingQuery} (goal : NativeGoal)
    (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    TypeOver goal.formedContext :=
  (evidence.displayedType goal sameQuery).toTypeOver

/-- The subject is constructed directly as an intrinsic term at the formed
type.  No checker appears in this definition. -/
def term {query : FormedTypingQuery} (goal : NativeGoal)
    (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    Term goal.formedContext (evidence.typeOver goal sameQuery) := by
  subst query
  exact
    { code := goal.query.subject
      typed := evidence.subjectTyping.toHasType }

@[simp] theorem displayedType_code {query : FormedTypingQuery}
    (goal : NativeGoal) (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    (evidence.displayedType goal sameQuery).code = goal.query.type := by
  subst query
  rfl

@[simp] theorem typeOver_code {query : FormedTypingQuery}
    (goal : NativeGoal) (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    (evidence.typeOver goal sameQuery).code = goal.query.type := by
  subst query
  rfl

@[simp] theorem term_code {query : FormedTypingQuery}
    (goal : NativeGoal) (evidence : IntrinsicFormedTyping query)
    (sameQuery : goal.query = query := by rfl) :
    (evidence.term goal sameQuery).code = goal.query.subject := by
  subst query
  rfl

end IntrinsicFormedTyping

/-! ## One proof-relevant semantics for the complete rooted presentation -/

/-- Universal semantic view of the exact formed-typing image.  It is vacuous
away from that image, so raw relational derivations outside the native fragment
remain interpretable. -/
def FormedCanonicalMeaning (goal : Pattern) : Type :=
  UniversalFibre formedTypingQueryCodec IntrinsicFormedTyping goal

/-- Intrinsic evidence indexed by all three judgment families in the current
Prime root. -/
def PrimeRootEvidence :
    ((TypingClaim Tower.Head ⊕ ContextFormationQuery) ⊕ FormedTypingQuery) →
      Type :=
  SumEvidence PrimeJudgmentEvidence IntrinsicFormedTyping

/-- The usable product view of the rooted semantics: prior typing/context
meaning together with formed-typing meaning. -/
def PrimeRootMeaning (goal : Pattern) : Type :=
  PrimeMeaning goal × FormedCanonicalMeaning goal

/-- The same semantics presented as the universal fibre of one exact
heterogeneous codec. -/
def PrimeRootSumMeaning (goal : Pattern) : Type :=
  UniversalFibre primeRootCodec PrimeRootEvidence goal

/-- The product interpreter is exactly the universal fibre of the single-root
codec; it is not a parallel semantic hierarchy. -/
def primeRootMeaning_equiv_sumFibre (goal : Pattern) :
    PrimeRootMeaning goal ≃ PrimeRootSumMeaning goal := by
  simpa [PrimeRootMeaning, PrimeRootSumMeaning, PrimeRootEvidence,
    FormedCanonicalMeaning, primeRootCodec] using
    (Equiv.prodCongr (primeMeaning_equiv_sumFibre goal)
      (Equiv.refl (FormedCanonicalMeaning goal))).trans
      (universalFibre_product_equiv_sumOfDisjoint
        primeJudgmentCodec formedTypingQueryCodec
        prior_formed_images_disjoint PrimeJudgmentEvidence
        IntrinsicFormedTyping goal)

private theorem formedEncoding_not_contextTargetShape
    (query : FormedTypingQuery) :
    contextFormationExtension.target.1.hasJudgmentShape
        (encodeFormedTypingQuery query) = false := by
  cases query
  simp [contextFormationExtension, ValidatedCalculusLanguageExtension.target,
    contextFormationDelta, CalculusLanguageExtension.apply,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareDataLanguage.definition,
    CalculusLanguageDef.hasJudgmentShape, CalculusLanguageDef.lookupJudgment?,
    encodeFormedTypingQuery, formedHasTypePattern]

private theorem formedCodec_avoids_baseConclusions :
    CalculusLanguageConclusionsAvoid contextFormationExtension.target
      formedTypingQueryCodec := by
  intro ruleInstance premises conclusion application query equality
  have shape := application.conclusion_hasJudgmentShape
  rw [← equality] at shape
  change
    contextFormationExtension.target.1.hasJudgmentShape
      (encodeFormedTypingQuery query) = true at shape
  rw [formedEncoding_not_contextTargetShape] at shape
  contradiction

/-- The already interpreted typing/context presentation acquires the larger
root meaning pointwise.  Its retained rules construct their established
meaning, while the disjoint formed-typing view is vacuous at their conclusions. -/
noncomputable def primeRootBaseSemantics :
    CalculusLanguageSemantics contextFormationExtension.target
      PrimeRootMeaning :=
  Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure.CalculusLanguageSemantics.productWithVacuousFibre
    contextSemanticExtension.targetSemantics formedTypingQueryCodec
      IntrinsicFormedTyping formedCodec_avoids_baseConclusions

private def formedTypingConclusion_reflects
    (query : FormedTypingQuery)
    (arityPattern contextPattern levelsPattern subjectPattern typePattern
      levelPattern : Pattern)
    (contextMeaning :
      PrimeRootMeaning
        (contextFormedPattern arityPattern contextPattern levelsPattern))
    (formationMeaning :
      PrimeRootMeaning
        (DeclarationAwareStructuralTyping.hasTypePattern arityPattern
          contextPattern typePattern
          (DeclarationAwareStructuralTyping.tmHeadPattern
            (DeclarationAwareStructuralTyping.headSortPattern
              levelPattern))))
    (subjectMeaning :
      PrimeRootMeaning
        (DeclarationAwareStructuralTyping.hasTypePattern arityPattern
          contextPattern subjectPattern typePattern))
    (equality :
      encodeFormedTypingQuery query =
        formedHasTypePattern arityPattern contextPattern levelsPattern
          subjectPattern typePattern levelPattern) :
    IntrinsicFormedTyping query := by
  rcases query with ⟨arity, context, levels, subject, type, level⟩
  simp only [encodeFormedTypingQuery, formedHasTypePattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have contextEquality :
      encodeContextFormationQuery
          { arity := arity, context := context, levels := levels } =
        contextFormedPattern arityPattern contextPattern levelsPattern := by
    simp only [encodeContextFormationQuery, contextFormedPattern,
      Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
    exact ⟨equality.1, equality.2.1, equality.2.2.1⟩
  have encodedSort :
      encodeTm towerHeadCodec
          (.head (.sort level) : Tower.Tm arity) =
        DeclarationAwareStructuralTyping.tmHeadPattern
          (DeclarationAwareStructuralTyping.headSortPattern levelPattern) := by
    simp [encodeTm, towerHeadCodec, encodeTowerHead,
      DeclarationAwareStructuralTyping.tmHeadPattern,
      DeclarationAwareStructuralTyping.headSortPattern,
      equality.2.2.2.2.2]
  have formationEquality :
      encodeTypingClaim towerHeadCodec
          { arity := arity, context := context, subject := type,
            type := .head (.sort level) } =
        DeclarationAwareStructuralTyping.hasTypePattern arityPattern
          contextPattern typePattern
          (DeclarationAwareStructuralTyping.tmHeadPattern
            (DeclarationAwareStructuralTyping.headSortPattern
              levelPattern)) := by
    simp only [encodeTypingClaim,
      DeclarationAwareStructuralTyping.hasTypePattern,
      Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
    exact
      ⟨equality.1, equality.2.1, equality.2.2.2.2.1, encodedSort⟩
  have subjectEquality :
      encodeTypingClaim towerHeadCodec
          { arity := arity, context := context, subject := subject,
            type := type } =
        DeclarationAwareStructuralTyping.hasTypePattern arityPattern
          contextPattern subjectPattern typePattern := by
    simp only [encodeTypingClaim,
      DeclarationAwareStructuralTyping.hasTypePattern,
      Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
    exact
      ⟨equality.1, equality.2.1, equality.2.2.2.1,
        equality.2.2.2.2.1⟩
  exact
    { contextFormation := contextMeaning.1.2
        { arity := arity, context := context, levels := levels }
        contextEquality
      typeFormation := formationMeaning.1.1
        { arity := arity, context := context, subject := type,
          type := .head (.sort level) }
        formationEquality
      subjectTyping := subjectMeaning.1.1
        { arity := arity, context := context, subject := subject,
          type := type }
        subjectEquality }

private def formedTypingAddedMeaning
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (lookup :
      formedTypingExtension.target.1.lookupRule? ruleInstance.ruleId =
        some formedTypingRule)
    (application :
      RuleApplication formedTypingExtension.target ruleInstance premises
        conclusion)
    (premiseEvidence : EvidenceList PrimeRootMeaning premises) :
    PrimeRootMeaning conclusion := by
  have instantiated :=
    instantiateRule?_eq_some_iff_application.mpr application
  rcases ruleInstance with ⟨ruleId, arguments⟩
  cases arguments with
  | nil =>
      simp [instantiateRule?, lookup, formedTypingRule, argumentsValidAt]
        at instantiated
  | cons arityPattern remaining =>
    cases remaining with
    | nil =>
        simp [instantiateRule?, lookup, formedTypingRule, argumentsValidAt]
          at instantiated
    | cons contextPattern remaining =>
      cases remaining with
      | nil =>
          simp [instantiateRule?, lookup, formedTypingRule, argumentsValidAt]
            at instantiated
      | cons levelsPattern remaining =>
        cases remaining with
        | nil =>
            simp [instantiateRule?, lookup, formedTypingRule,
              argumentsValidAt] at instantiated
        | cons subjectPattern remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, formedTypingRule,
                argumentsValidAt] at instantiated
          | cons typePattern remaining =>
            cases remaining with
            | nil =>
                simp [instantiateRule?, lookup, formedTypingRule,
                  argumentsValidAt] at instantiated
            | cons levelPattern remaining =>
              cases remaining with
              | cons extra tail =>
                  simp [instantiateRule?, lookup, formedTypingRule,
                    argumentsValidAt] at instantiated
              | nil =>
                  simp [instantiateRule?, lookup, formedTypingRule,
                    RuleSchema.sideConditionsHold, argumentsValidAt,
                    instantiateSchema?, instantiateSchemaAt?,
                    instantiateSchemas?, instantiateSchemasAt?,
                    lookupArgumentAt?, contextFormedPattern,
                    DeclarationAwareStructuralTyping.hasTypePattern,
                    DeclarationAwareStructuralTyping.tmHeadPattern,
                    DeclarationAwareStructuralTyping.headSortPattern,
                    formedHasTypePattern] at instantiated
                  rcases instantiated with ⟨_, rfl, rfl⟩
                  cases premiseEvidence with
                  | cons contextMeaning rest =>
                    cases rest with
                    | cons formationMeaning rest =>
                      cases rest with
                      | cons subjectMeaning rest =>
                        cases rest
                        exact
                          ⟨⟨fun typingQuery equality => by
                                cases typingQuery
                                simp [towerTypingClaimCodec, typingClaimCodec,
                                  encodeTypingClaim] at equality,
                              fun contextQuery equality => by
                                cases contextQuery
                                simp [contextFormationQueryCodec,
                                  encodeContextFormationQuery,
                                  contextFormedPattern] at equality⟩,
                            fun query equality =>
                              formedTypingConclusion_reflects query
                                arityPattern contextPattern levelsPattern
                                subjectPattern typePattern levelPattern
                                contextMeaning formationMeaning subjectMeaning
                                equality⟩

/-- Formed typing is not merely accepted by the same presentation: every
checked target derivation is interpreted compositionally in the single-root
intrinsic semantics, with all ordered premise occurrences retained. -/
noncomputable def formedTypingSemanticExtension :
    SemanticExtension contextFormationExtension.target formedTypingExtension
      PrimeRootMeaning where
  baseSemantics := primeRootBaseSemantics
  addedRuleMeaning := by
    intro rule member ruleInstance premises conclusion lookup application
      premiseEvidence
    have ruleEquality : rule = formedTypingRule := by
      simpa [formedTypingExtension, formedTypingDelta] using member
    subst rule
    exact formedTypingAddedMeaning ruleInstance premises conclusion lookup
      application premiseEvidence

/-! ## One validated presentation checks all ordered premises -/

/-- Raw proof package for one formed judgment.  The fields remain distinct so a
consumer cannot exchange formation and inhabitation evidence. -/
structure RawFormedProof where
  contextFormation : RawProof
  typeFormation : RawProof
  subjectTyping : RawProof

/-- The six exact arguments supplied to the derived formation rule. -/
def FormedTypingQuery.ruleArguments (query : FormedTypingQuery) :
    List Pattern :=
  [encodeNat query.arity, encodeCtx towerHeadCodec query.context,
    encodeLevelSpine query.levels, encodeTm towerHeadCodec query.subject,
    encodeTm towerHeadCodec query.type, encodeLevel query.level]

/-- Package the ordered component trees as one proof of the derived formed
judgment.  The wrapper retains all three child occurrences and their order. -/
def RawFormedProof.derived (query : FormedTypingQuery)
    (proof : RawFormedProof) : RawProof :=
  .node
    { ruleId := formedTypingRule.id
      arguments := query.ruleArguments }
    [proof.contextFormation, proof.typeFormation, proof.subjectTyping]

/-- Adversarial wrapper with the two typing children exchanged while context
formation remains fixed.  It shows that the derived node does not quotient
formation and inhabitation evidence. -/
def RawFormedProof.swappedDerived (query : FormedTypingQuery)
    (proof : RawFormedProof) : RawProof :=
  .node
    { ruleId := formedTypingRule.id
      arguments := query.ruleArguments }
    [proof.contextFormation, proof.subjectTyping, proof.typeFormation]

private theorem instantiateFormedTypingRule (query : FormedTypingQuery) :
    instantiateRule? formedTypingExtension.target
        { ruleId := formedTypingRule.id
          arguments := query.ruleArguments } =
      some
        ([encodeContextFormationQuery query.contextClaim,
          encodeTypingClaim towerHeadCodec query.formationClaim,
          encodeTypingClaim towerHeadCodec query.subjectClaim],
          encodeFormedTypingQuery query) := by
  have arityValid := encodeNat_argumentValid query.arity
  have contextValid := encodeTowerCtx_argumentValid query.context
  have levelsValid := encodeLevelSpine_argumentValid query.levels
  have subjectValid := encodeTowerTm_argumentValid query.subject
  have typeValid := encodeTowerTm_argumentValid query.type
  have levelValid := encodeLevel_argumentValid query.level
  have encodedSort :
      DeclarationAwareStructuralTyping.tmHeadPattern
          (DeclarationAwareStructuralTyping.headSortPattern
            (encodeLevel query.level)) =
        encodeTm towerHeadCodec
          (Tm.head (.sort query.level) : Tower.Tm query.arity) := by
    rfl
  simp [formedTypingExtension, ValidatedCalculusLanguageExtension.target,
    formedTypingDelta, CalculusLanguageExtension.apply,
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
    FormedTypingQuery.ruleArguments, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt,
    arityValid, contextValid, levelsValid, subjectValid, typeValid, levelValid,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, encodeContextFormationQuery,
    FormedTypingQuery.contextClaim, contextFormedPattern,
    encodeFormedTypingQuery, formedHasTypePattern,
    encodeLevelSpine,
    FormedTypingQuery.formationClaim, FormedTypingQuery.subjectClaim,
    encodeTypingClaim, DeclarationAwareStructuralTyping.hasTypePattern,
    DeclarationAwareStructuralTyping.tmHeadPattern,
    DeclarationAwareStructuralTyping.headSortPattern]
  exact encodedSort

/-- All three trees are checked by the same declaration-aware presentation. -/
def checkRaw (query : FormedTypingQuery) (proof : RawFormedProof) : Bool :=
  InferenceChecker.checkRaw contextFormationExtension.target
      (encodeContextFormationQuery query.contextClaim)
      proof.contextFormation &&
    (InferenceChecker.checkRaw contextFormationExtension.target
        (encodeTypingClaim towerHeadCodec query.formationClaim)
        proof.typeFormation &&
      InferenceChecker.checkRaw contextFormationExtension.target
        (encodeTypingClaim towerHeadCodec query.subjectClaim)
        proof.subjectTyping)

private theorem structuralClaim_hasJudgmentShape
    (claim : TypingClaim Tower.Head) :
    Structural.checked.1.hasJudgmentShape
      (encodeTypingClaim towerHeadCodec claim) = true := by
  cases claim
  simp [Structural.checked, DeclarationAwareStructuralTyping.checked,
    CalculusLanguageDef.hasJudgmentShape, encodeTypingClaim,
    DeclarationAwareStructuralTyping.hasTypingJudgment]

private theorem structuralClaim_hasContextTargetJudgmentShape
    (claim : TypingClaim Tower.Head) :
    contextFormationExtension.target.1.hasJudgmentShape
        (encodeTypingClaim towerHeadCodec claim) = true := by
  have baseShape := structuralClaim_hasJudgmentShape claim
  simpa [contextFormationExtension, ValidatedCalculusLanguageExtension.target,
    contextFormationDelta, CalculusLanguageExtension.apply,
    CalculusLanguageDef.hasJudgmentShape, CalculusLanguageDef.lookupJudgment?,
    encodeTypingClaim] using baseShape

private theorem contextClaim_hasContextTargetJudgmentShape
    (claim : ContextFormationQuery) :
    contextFormationExtension.target.1.hasJudgmentShape
        (encodeContextFormationQuery claim) = true := by
  exact contextQuery_hasTargetJudgmentShape claim

/-- The derived wrapper is semantically transparent: target acceptance is
exactly acceptance of the three ordered component artifacts by the base
presentation.  This is an instance of generic `newJudgmentsOnly`
conservativity, not a Prime-specific inversion of the checker. -/
theorem RawFormedProof.derived_accepted_iff_components
    (query : FormedTypingQuery) (proof : RawFormedProof) :
    InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query) (proof.derived query) = true ↔
      checkRaw query proof = true := by
  have contextIff :=
    InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      formedTypingExtension rfl
      (contextClaim_hasContextTargetJudgmentShape query.contextClaim)
      proof.contextFormation
  have formationIff :=
    InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      formedTypingExtension rfl
      (structuralClaim_hasContextTargetJudgmentShape query.formationClaim)
      proof.typeFormation
  have subjectIff :=
    InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      formedTypingExtension rfl
      (structuralClaim_hasContextTargetJudgmentShape query.subjectClaim)
      proof.subjectTyping
  simp only [RawFormedProof.derived, InferenceChecker.checkRaw,
    instantiateFormedTypingRule, decide_true, Bool.true_and,
    InferenceChecker.checkRawChildren, Bool.and_true, checkRaw,
    Bool.and_eq_true]
  exact and_congr contextIff (and_congr formationIff subjectIff)

/-- Compile intrinsic evidence into the exact recursively generated raw proof
package used by the generic checker. -/
def IntrinsicFormedTyping.raw {query : FormedTypingQuery}
    (evidence : IntrinsicFormedTyping query) : RawFormedProof where
  contextFormation := evidence.contextFormation.raw
  typeFormation := evidence.typeFormation.raw
  subjectTyping := evidence.subjectTyping.raw

/-- Intrinsic evidence compiles not only to three accepted component trees but
also to one accepted proof of the conservative derived judgment. -/
theorem IntrinsicFormedTyping.derivedRaw_accepted
    {query : FormedTypingQuery} (evidence : IntrinsicFormedTyping query) :
    InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query) (evidence.raw.derived query) = true := by
  have contextAccepted :=
    checkRaw_true_of_ruleLookupRefines formedTypingExtension.refines
      evidence.contextFormation.raw_accepted
  have formationAccepted :=
    checkRaw_true_of_ruleLookupRefines formedTypingExtension.refines
      (checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
        (by
          simpa [FormedTypingQuery.formationClaim,
            DeclarationAwareStructuralTyping.claimPattern] using
            evidence.typeFormation.raw_accepted))
  have subjectAccepted :=
    checkRaw_true_of_ruleLookupRefines formedTypingExtension.refines
      (checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
        (by
          simpa [FormedTypingQuery.subjectClaim,
            DeclarationAwareStructuralTyping.claimPattern] using
            evidence.subjectTyping.raw_accepted))
  simp only [RawFormedProof.derived, InferenceChecker.checkRaw,
    instantiateFormedTypingRule, decide_true, Bool.true_and,
    InferenceChecker.checkRawChildren, Bool.and_true]
  exact Bool.and_eq_true_iff.mpr
    ⟨contextAccepted,
      Bool.and_eq_true_iff.mpr ⟨formationAccepted, subjectAccepted⟩⟩

/-- Exchanging the two ordered typing children is rejected whenever formation
and inhabitation are genuinely different judgments.  The context child stays
fixed.  The proof uses the generic checker's goal-uniqueness theorem rather
than inspecting a particular Prime constructor. -/
theorem IntrinsicFormedTyping.swappedDerived_rejected
    {query : FormedTypingQuery} (evidence : IntrinsicFormedTyping query)
    (distinct :
      encodeTypingClaim towerHeadCodec query.formationClaim ≠
        encodeTypingClaim towerHeadCodec query.subjectClaim) :
    InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query)
        (evidence.raw.swappedDerived query) ≠ true := by
  intro accepted
  have swappedChecks :
      InferenceChecker.checkRaw formedTypingExtension.target
          (encodeContextFormationQuery query.contextClaim)
          evidence.raw.contextFormation = true ∧
        (InferenceChecker.checkRaw formedTypingExtension.target
          (encodeTypingClaim towerHeadCodec query.formationClaim)
          evidence.raw.subjectTyping = true ∧
        InferenceChecker.checkRaw formedTypingExtension.target
          (encodeTypingClaim towerHeadCodec query.subjectClaim)
          evidence.raw.typeFormation = true) := by
    simpa only [RawFormedProof.swappedDerived, InferenceChecker.checkRaw,
      instantiateFormedTypingRule, decide_true, Bool.true_and,
      InferenceChecker.checkRawChildren, Bool.and_true,
      Bool.and_eq_true_iff] using accepted
  have subjectAccepted :=
    checkRaw_true_of_ruleLookupRefines formedTypingExtension.refines
      (checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
        (by
          simpa [FormedTypingQuery.subjectClaim,
            DeclarationAwareStructuralTyping.claimPattern] using
            evidence.subjectTyping.raw_accepted))
  exact distinct
    (checkRaw_goal_unique swappedChecks.2.1 subjectAccepted)

theorem IntrinsicFormedTyping.raw_accepted {query : FormedTypingQuery}
    (evidence : IntrinsicFormedTyping query) :
    checkRaw query evidence.raw = true := by
  simp only [checkRaw, IntrinsicFormedTyping.raw, Bool.and_eq_true]
  constructor
  · exact evidence.contextFormation.raw_accepted
  · constructor
    · exact
        checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
          (by
            simpa [FormedTypingQuery.formationClaim,
              DeclarationAwareStructuralTyping.claimPattern] using
              evidence.typeFormation.raw_accepted)
    · exact
        checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
          (by
            simpa [FormedTypingQuery.subjectClaim,
              DeclarationAwareStructuralTyping.claimPattern] using
              evidence.subjectTyping.raw_accepted)

/-- Accepted boundary evidence reflects back into the independently defined
intrinsic fibre. -/
noncomputable def reflectAcceptedRaw {query : FormedTypingQuery}
    (proof : RawFormedProof) (accepted : checkRaw query proof = true) :
    IntrinsicFormedTyping query := by
  have checks :
      InferenceChecker.checkRaw contextFormationExtension.target
          (encodeContextFormationQuery query.contextClaim)
          proof.contextFormation = true ∧
        (InferenceChecker.checkRaw contextFormationExtension.target
          (encodeTypingClaim towerHeadCodec query.formationClaim)
          proof.typeFormation = true ∧
        InferenceChecker.checkRaw contextFormationExtension.target
          (encodeTypingClaim towerHeadCodec query.subjectClaim)
          proof.subjectTyping = true) := by
    simpa [checkRaw] using accepted
  have formationBase :
      InferenceChecker.checkRaw Structural.checked
          (encodeTypingClaim towerHeadCodec query.formationClaim)
          proof.typeFormation = true :=
    (InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      contextFormationExtension rfl
      (structuralClaim_hasJudgmentShape query.formationClaim)
      proof.typeFormation).mp checks.2.1
  have subjectBase :
      InferenceChecker.checkRaw Structural.checked
          (encodeTypingClaim towerHeadCodec query.subjectClaim)
          proof.subjectTyping = true :=
    (InferenceNewJudgmentConservativity.ValidatedCalculusLanguageExtension.checkRaw_iff_base_of_newJudgmentsOnly
      contextFormationExtension rfl
      (structuralClaim_hasJudgmentShape query.subjectClaim)
      proof.subjectTyping).mp checks.2.2
  exact
    { contextFormation :=
        DeclarationAwareCheckedContext.reflectAcceptedRaw
          proof.contextFormation (by
            simpa [FormedTypingQuery.contextClaim] using checks.1)
      typeFormation :=
        DeclarationAwareStructuralTyping.reflectAcceptedRaw
          proof.typeFormation (by
            simpa [FormedTypingQuery.formationClaim,
              DeclarationAwareStructuralTyping.claimPattern] using
              formationBase)
      subjectTyping :=
        DeclarationAwareStructuralTyping.reflectAcceptedRaw
          proof.subjectTyping (by
            simpa [FormedTypingQuery.subjectClaim,
              DeclarationAwareStructuralTyping.claimPattern] using
              subjectBase) }

/-- Exact-image adequacy of the formed boundary: some accepted ordered proof
package exists exactly when the native formed-typing fibre is inhabited. -/
theorem exists_accepted_raw_iff_nonempty_intrinsic
    (query : FormedTypingQuery) :
    (∃ proof : RawFormedProof, checkRaw query proof = true) ↔
      Nonempty (IntrinsicFormedTyping query) := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact ⟨reflectAcceptedRaw proof accepted⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.raw, evidence.raw_accepted⟩

/-- Exact single-node reflection for the conservative formed-judgment
package.  The derived presentation accepts some ordered proof package exactly
when the independently defined intrinsic formed-typing fibre is inhabited. -/
theorem exists_derived_accepted_iff_nonempty_intrinsic
    (query : FormedTypingQuery) :
    (∃ proof : RawFormedProof,
      InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query) (proof.derived query) = true) ↔
      Nonempty (IntrinsicFormedTyping query) := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact exists_accepted_raw_iff_nonempty_intrinsic query |>.mp
      ⟨proof, (proof.derived_accepted_iff_components query).mp accepted⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.raw,
      (evidence.raw.derived_accepted_iff_components query).mpr
        evidence.raw_accepted⟩

/-! ## Nodewise canonical native ingress -/

/-- The production boundary checks the exact context fibre and strengthens
both typing components to exact codec support at every proof node. -/
def checkCanonicalRaw (query : FormedTypingQuery)
    (proof : RawFormedProof) : Bool :=
  InferenceChecker.checkRaw contextFormationExtension.target
      (encodeContextFormationQuery query.contextClaim)
      proof.contextFormation &&
    (DeclarationAwareStructuralTyping.checkCanonicalRaw
        (encodeTypingClaim towerHeadCodec query.formationClaim)
        proof.typeFormation &&
      DeclarationAwareStructuralTyping.checkCanonicalRaw
        (encodeTypingClaim towerHeadCodec query.subjectClaim)
        proof.subjectTyping)

theorem IntrinsicFormedTyping.canonicalRaw_accepted
    {query : FormedTypingQuery} (evidence : IntrinsicFormedTyping query) :
    checkCanonicalRaw query evidence.raw = true := by
  simp only [checkCanonicalRaw, IntrinsicFormedTyping.raw, Bool.and_eq_true]
  constructor
  · exact evidence.contextFormation.raw_accepted
  · constructor
    · simpa [FormedTypingQuery.formationClaim,
        DeclarationAwareStructuralTyping.claimPattern] using
        evidence.typeFormation.canonicalTreeRaw_accepted
    · simpa [FormedTypingQuery.subjectClaim,
        DeclarationAwareStructuralTyping.claimPattern] using
        evidence.subjectTyping.canonicalTreeRaw_accepted

/-- Nodewise canonical acceptance reflects into the intrinsic structural
fibre.  The canonical derivation first supplies an accepted ordinary tree;
the independent semantics then reconstructs its indexed evidence. -/
noncomputable def reflectCanonicalAcceptedComponent
    (claim : TypingClaim Tower.Head) (proof : RawProof)
    (accepted :
      DeclarationAwareStructuralTyping.checkCanonicalRaw
        (encodeTypingClaim towerHeadCodec claim) proof = true) :
    Structural.StructuralTyping claim.context claim.subject claim.type := by
  let witness :=
    (DeclarationAwareStructuralTyping.checkCanonicalRaw_eq_true_iff_exists_canonicalDerivation_erases
      (encodeTypingClaim towerHeadCodec claim) proof).mp accepted
  let derivation := witness.choose
  have erases : derivation.erase = proof := witness.choose_spec
  have rawAccepted :
      InferenceChecker.checkRaw Structural.checked
        (encodeTypingClaim towerHeadCodec claim) proof = true := by
    rw [← erases]
    exact checkRaw_erase derivation.toDerivation
  rcases claim with ⟨n, context, subject, type⟩
  exact DeclarationAwareStructuralTyping.reflectAcceptedRaw proof (by
    simpa [DeclarationAwareStructuralTyping.claimPattern] using rawAccepted)

noncomputable def reflectCanonicalAcceptedRaw
    {query : FormedTypingQuery} (proof : RawFormedProof)
    (accepted : checkCanonicalRaw query proof = true) :
    IntrinsicFormedTyping query := by
  have checks :
      InferenceChecker.checkRaw contextFormationExtension.target
          (encodeContextFormationQuery query.contextClaim)
          proof.contextFormation = true ∧
        (DeclarationAwareStructuralTyping.checkCanonicalRaw
          (encodeTypingClaim towerHeadCodec query.formationClaim)
          proof.typeFormation = true ∧
        DeclarationAwareStructuralTyping.checkCanonicalRaw
          (encodeTypingClaim towerHeadCodec query.subjectClaim)
          proof.subjectTyping = true) := by
    simpa [checkCanonicalRaw] using accepted
  exact
    { contextFormation :=
        DeclarationAwareCheckedContext.reflectAcceptedRaw
          proof.contextFormation (by
            simpa [FormedTypingQuery.contextClaim] using checks.1)
      typeFormation :=
        reflectCanonicalAcceptedComponent query.formationClaim
          proof.typeFormation checks.2.1
      subjectTyping :=
        reflectCanonicalAcceptedComponent query.subjectClaim
          proof.subjectTyping checks.2.2 }

/-- The actual check-once boundary is exactly the native formed-judgment
inhabitation boundary. -/
theorem exists_canonical_accepted_iff_nonempty_intrinsic
    (query : FormedTypingQuery) :
    (∃ proof : RawFormedProof, checkCanonicalRaw query proof = true) ↔
      Nonempty (IntrinsicFormedTyping query) := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact ⟨reflectCanonicalAcceptedRaw proof accepted⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.raw, evidence.canonicalRaw_accepted⟩

/-! ## Positive and negative controls -/

namespace Examples

open DeclarationAwareStructuralTyping

private abbrev simplePiLevel : LevelExpr :=
  .max (.succ Tower.zero) (.succ Tower.zero)

def simplePiQuery : FormedTypingQuery where
  arity := 0
  context := .nil
  levels := .nil
  subject := simplePi
  type := simplePiUniverse
  level := .succ simplePiLevel

def simplePiIntrinsic : IntrinsicFormedTyping simplePiQuery where
  contextFormation := .nil
  typeFormation := .sort .nil simplePiLevel
  subjectTyping := simplePiEvidence

def simplePiGoal : NativeGoal := simplePiIntrinsic.nativeGoal

/-- The checked structural derivations construct an actual intrinsic Prime
term over a formed context and a displayed universe. -/
def simplePiNativeTerm :
    Term simplePiGoal.formedContext
      (simplePiIntrinsic.typeOver simplePiGoal) :=
  simplePiIntrinsic.term simplePiGoal

theorem simplePi_raw_accepted :
    checkRaw simplePiQuery simplePiIntrinsic.raw = true :=
  simplePiIntrinsic.raw_accepted

theorem simplePi_canonical_raw_accepted :
    checkCanonicalRaw simplePiQuery simplePiIntrinsic.raw = true :=
  simplePiIntrinsic.canonicalRaw_accepted

theorem simplePi_derived_raw_accepted :
    InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery simplePiQuery)
        (simplePiIntrinsic.raw.derived simplePiQuery) = true :=
  simplePiIntrinsic.derivedRaw_accepted

theorem simplePi_component_judgments_distinct :
    encodeTypingClaim towerHeadCodec simplePiQuery.formationClaim ≠
      encodeTypingClaim towerHeadCodec simplePiQuery.subjectClaim := by
  decide

/-- The derived rule retains its ordered proof-relevant boundary: even two
individually valid component trees cannot be exchanged. -/
theorem simplePi_swapped_derived_rejected :
    InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery simplePiQuery)
        (simplePiIntrinsic.raw.swappedDerived simplePiQuery) ≠ true :=
  simplePiIntrinsic.swappedDerived_rejected
    simplePi_component_judgments_distinct

theorem simplePi_native_codes_exact :
    (simplePiIntrinsic.displayedType simplePiGoal).code = simplePiUniverse ∧
      simplePiNativeTerm.code = simplePi := by
  exact ⟨rfl, rfl⟩

/-- The same term-typing claim paired with a false formation level. -/
def wrongLevelQuery : FormedTypingQuery where
  arity := 0
  context := .nil
  levels := .nil
  subject := simplePi
  type := simplePiUniverse
  level := simplePiLevel

/-- Ordinary structural typing alone still proves the subject component. -/
theorem wrongLevel_subject_component_inhabited :
    Nonempty
      (Structural.StructuralTyping wrongLevelQuery.context
        wrongLevelQuery.subject wrongLevelQuery.type) :=
  ⟨simplePiEvidence⟩

/-- But the formed judgment is uninhabited: the selected universe is one
level too low.  This is why the fifth field is semantic data, not metadata. -/
theorem wrongLevel_has_no_intrinsic_formed_typing :
    ¬ Nonempty (IntrinsicFormedTyping wrongLevelQuery) := by
  rintro ⟨evidence⟩
  cases evidence.typeFormation

theorem wrongLevel_has_no_accepted_raw_bundle :
    ¬ ∃ proof : RawFormedProof, checkRaw wrongLevelQuery proof = true := by
  intro accepted
  exact wrongLevel_has_no_intrinsic_formed_typing
    (exists_accepted_raw_iff_nonempty_intrinsic wrongLevelQuery |>.mp accepted)

/-- The conservative derived wrapper cannot manufacture the missing universe
formation evidence. -/
theorem wrongLevel_has_no_derived_accepted_node :
    ¬ ∃ proof : RawFormedProof,
      InferenceChecker.checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery wrongLevelQuery)
        (proof.derived wrongLevelQuery) = true := by
  intro accepted
  exact wrongLevel_has_no_intrinsic_formed_typing
    (exists_derived_accepted_iff_nonempty_intrinsic wrongLevelQuery |>.mp
      accepted)

theorem wrongLevel_has_no_canonical_accepted_bundle :
    ¬ ∃ proof : RawFormedProof,
      checkCanonicalRaw wrongLevelQuery proof = true := by
  intro accepted
  exact wrongLevel_has_no_intrinsic_formed_typing
    (exists_canonical_accepted_iff_nonempty_intrinsic wrongLevelQuery |>.mp
      accepted)

/-! ### A well-typed-looking term cannot repair an unformed context -/

def unformedContextLevels : LevelSpine 1 :=
  .snoc .nil Tower.zero

def unformedContextQuery : FormedTypingQuery where
  arity := 1
  context := missingDeclarationContext
  levels := unformedContextLevels
  subject := .head .legacyGround
  type := .head (.sort Tower.zero)
  level := .succ Tower.zero

/-- Both old typing components are inhabited even over the malformed
telescope.  This is the precise leak closed by the new first premise. -/
theorem unformedContext_typing_components_inhabited :
    Nonempty
      (Structural.StructuralTyping unformedContextQuery.context
          unformedContextQuery.type (.head (.sort unformedContextQuery.level)) ×
        Structural.StructuralTyping unformedContextQuery.context
          unformedContextQuery.subject unformedContextQuery.type) :=
  ⟨.sort missingDeclarationContext Tower.zero,
    .legacyGround missingDeclarationContext⟩

/-- The complete native judgment remains uninhabited because no structural
context-formation tree can introduce the undeclared constant. -/
theorem unformedContext_has_no_intrinsic_formed_typing :
    ¬ Nonempty (IntrinsicFormedTyping unformedContextQuery) := by
  rintro ⟨evidence⟩
  cases evidence.contextFormation with
  | snoc _ entryFormation => cases entryFormation

theorem unformedContext_has_no_accepted_raw_bundle :
    ¬ ∃ proof : RawFormedProof,
      checkRaw unformedContextQuery proof = true := by
  intro accepted
  exact unformedContext_has_no_intrinsic_formed_typing
    (exists_accepted_raw_iff_nonempty_intrinsic unformedContextQuery |>.mp
      accepted)

end Examples

#print axioms encodeFormedTypingQuery_injective
#print axioms prior_formed_images_disjoint
#print axioms primeRootMeaning_equiv_sumFibre
#print axioms primeRootBaseSemantics
#print axioms formedTypingSemanticExtension
#print axioms NativeGoal.surface_injective
#print axioms IntrinsicFormedTyping.displayedType
#print axioms IntrinsicFormedTyping.term
#print axioms IntrinsicFormedTyping.nativeGoal
#print axioms IntrinsicFormedTyping.raw_accepted
#print axioms IntrinsicFormedTyping.derivedRaw_accepted
#print axioms IntrinsicFormedTyping.swappedDerived_rejected
#print axioms reflectAcceptedRaw
#print axioms exists_accepted_raw_iff_nonempty_intrinsic
#print axioms RawFormedProof.derived_accepted_iff_components
#print axioms exists_derived_accepted_iff_nonempty_intrinsic
#print axioms IntrinsicFormedTyping.canonicalRaw_accepted
#print axioms reflectCanonicalAcceptedComponent
#print axioms reflectCanonicalAcceptedRaw
#print axioms exists_canonical_accepted_iff_nonempty_intrinsic
#print axioms Examples.simplePi_raw_accepted
#print axioms Examples.simplePi_canonical_raw_accepted
#print axioms Examples.simplePi_derived_raw_accepted
#print axioms Examples.simplePi_swapped_derived_rejected
#print axioms Examples.simplePi_native_codes_exact
#print axioms Examples.wrongLevel_has_no_intrinsic_formed_typing
#print axioms Examples.wrongLevel_has_no_accepted_raw_bundle
#print axioms Examples.wrongLevel_has_no_derived_accepted_node
#print axioms Examples.wrongLevel_has_no_canonical_accepted_bundle
#print axioms Examples.unformedContext_typing_components_inhabited
#print axioms Examples.unformedContext_has_no_intrinsic_formed_typing
#print axioms Examples.unformedContext_has_no_accepted_raw_bundle

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping
