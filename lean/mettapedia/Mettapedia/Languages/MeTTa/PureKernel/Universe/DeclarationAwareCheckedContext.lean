import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareStructuralTyping
import Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity

/-!
# Checked context formation for declaration-aware Prime

Prime term typing is indexed by a raw telescope.  Native construction also
needs evidence that the telescope itself was formed.  This module adds that
evidence as a genuine judgment in the same validated inference presentation:

* the empty context is formed;
* extending a formed context by `A` requires `Gamma |- A : U level`.

The intrinsic evidence is deliberately restricted to the structural fragment
already represented by the finite presentation.  It maps into the full Prime
`ContextWellFormed` judgment, while unsupported full-calculus derivations stay
outside this checked fragment rather than being rejected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareCheckedContext

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferencePresentationExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Structural

abbrev checked := DeclarationAwareStructuralTyping.checked
abbrev StructuralTyping {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) :=
  DeclarationAwareStructuralTyping.StructuralTyping context term type
abbrev CanonicalMeaning := DeclarationAwareStructuralTyping.CanonicalMeaning

end Structural

/-! ## Context judgment and exact codec -/

/-- Universe annotations for each entry of a telescope.  Unlike a plain list,
the length is definitionally the ambient arity. -/
inductive LevelSpine : Nat → Type where
  | nil : LevelSpine 0
  | snoc {n : Nat} : LevelSpine n → LevelExpr → LevelSpine (n + 1)

def encodeLevelSpine : {n : Nat} → LevelSpine n → Pattern
  | _, .nil => .apply "prime-level-spine-nil" []
  | _, .snoc levels level =>
      .apply "prime-level-spine-snoc"
        [encodeLevelSpine levels, encodeLevel level]

def decodeLevelSpine? : (n : Nat) → Pattern → Option (LevelSpine n)
  | 0, .apply "prime-level-spine-nil" [] => some .nil
  | n + 1, .apply "prime-level-spine-snoc" [levels, level] => do
      pure (.snoc (← decodeLevelSpine? n levels) (← decodeLevel? level))
  | _, _ => none

@[simp] theorem decodeLevelSpine?_encodeLevelSpine
    {n : Nat} (levels : LevelSpine n) :
    decodeLevelSpine? n (encodeLevelSpine levels) = some levels := by
  induction levels with
  | nil => rfl
  | snoc levels level inductionHypothesis =>
      simp [encodeLevelSpine, decodeLevelSpine?, inductionHypothesis]

theorem encodeLevelSpine_argumentValid {n : Nat}
    (levels : LevelSpine n) :
    argumentValidAt 0 (encodeLevelSpine levels) = true := by
  induction levels with
  | nil =>
      simp [encodeLevelSpine, argumentValidAt, Pattern.isGroundAt,
        Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | snoc levels level inductionHypothesis =>
      have levelValid := encodeLevel_argumentValid level
      rw [argumentValidAt_zero] at inductionHypothesis levelValid ⊢
      simp only [Bool.and_eq_true] at inductionHypothesis levelValid ⊢
      exact
        ⟨by
          have levelsGround :
              Pattern.isGroundAt 0 (encodeLevelSpine levels) = true := by
            simpa [Pattern.isGround] using inductionHypothesis.1
          have levelGround :
              Pattern.isGroundAt 0 (encodeLevel level) = true := by
            simpa [Pattern.isGround] using levelValid.1
          change
            Pattern.isGroundAt 0
              (.apply "prime-level-spine-snoc"
                [encodeLevelSpine levels, encodeLevel level]) = true
          simpa [Pattern.isGroundAt, Pattern.isGroundListAt] using
            And.intro levelsGround levelGround,
         by
          simp [encodeLevelSpine, Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList,
            inductionHypothesis.2, levelValid.2]⟩

structure ContextFormationQuery where
  arity : Nat
  context : Tower.Ctx arity
  levels : LevelSpine arity

def contextFormedPattern (arity context levels : Pattern) : Pattern :=
  .apply "prime-context-formed" [arity, context, levels]

def encodeContextFormationQuery (query : ContextFormationQuery) : Pattern :=
  contextFormedPattern (encodeNat query.arity)
    (encodeCtx towerHeadCodec query.context)
    (encodeLevelSpine query.levels)

def decodeContextFormationQuery? : Pattern → Option ContextFormationQuery
  | .apply "prime-context-formed" [arity, context, levels] => do
      let n ← decodeNat? arity
      pure
        { arity := n
          context := ← decodeCtx? towerHeadCodec n context
          levels := ← decodeLevelSpine? n levels }
  | _ => none

@[simp] theorem decodeContextFormationQuery?_encode
    (query : ContextFormationQuery) :
    decodeContextFormationQuery? (encodeContextFormationQuery query) =
      some query := by
  cases query
  simp [encodeContextFormationQuery, contextFormedPattern,
    decodeContextFormationQuery?, decodeLevelSpine?_encodeLevelSpine]

def contextFormationQueryCodec :
    PartialCodec ContextFormationQuery Pattern where
  encode := encodeContextFormationQuery
  decode := decodeContextFormationQuery?
  decode_encode := decodeContextFormationQuery?_encode

theorem encodeContextFormationQuery_injective :
    Function.Injective encodeContextFormationQuery :=
  contextFormationQueryCodec.encode_injective

/-- Structural typing and structural context formation occupy disjoint outer
judgment heads.  Their exact coproduct therefore retains which judgment was
authored; tolerant aliases cannot change the summand at ingress. -/
theorem typing_context_images_disjoint :
    EncoderImagesDisjoint towerTypingClaimCodec
      contextFormationQueryCodec := by
  intro typingQuery contextQuery equality
  cases typingQuery
  cases contextQuery
  simp [towerTypingClaimCodec, typingClaimCodec,
    contextFormationQueryCodec, encodeContextFormationQuery,
    contextFormedPattern, encodeTypingClaim] at equality

/-- The first genuinely heterogeneous Prime judgment codec: ordinary
structural typing and structural context formation share one exact wire waist
without surrendering their distinct intrinsic indices. -/
def primeJudgmentCodec :
    PartialCodec (TypingClaim Tower.Head ⊕ ContextFormationQuery) Pattern :=
  sumOfDisjoint towerTypingClaimCodec contextFormationQueryCodec
    typing_context_images_disjoint

/-! ## Intrinsic structural context formation -/

/-- Context formation internal to the exact structural typing fragment.  Each
snoc retains the universe level and its structural type-formation derivation. -/
inductive StructuralContextFormation :
    {n : Nat} → Tower.Ctx n → LevelSpine n → Type where
  | nil : StructuralContextFormation (.nil : Tower.Ctx 0) .nil
  | snoc {n : Nat} {context : Tower.Ctx n} {type : Tower.Tm n}
      {levels : LevelSpine n} {level : LevelExpr} :
      StructuralContextFormation context levels →
      Structural.StructuralTyping context type (.head (.sort level)) →
      StructuralContextFormation (.snoc context type) (.snoc levels level)

namespace StructuralContextFormation

/-- Structural context evidence embeds into Prime's full declaration-aware
context judgment without forgetting any formation derivation. -/
def toContextWellFormed :
    {n : Nat} → {context : Tower.Ctx n} → {levels : LevelSpine n} →
      StructuralContextFormation context levels →
      ContextWellFormed Tower.rules context
  | _, _, _, .nil => .nil
  | _, _, _, .snoc prior typeFormation =>
      .snoc prior.toContextWellFormed typeFormation.toHasType
        (.sort _)

end StructuralContextFormation

/-! ## Heterogeneous proof-relevant meaning -/

/-- Intrinsic evidence selected by the exact heterogeneous judgment index. -/
def PrimeJudgmentEvidence :
    TypingClaim Tower.Head ⊕ ContextFormationQuery → Type :=
  SumEvidence DeclarationAwareStructuralTyping.ClaimEvidence
    (fun query => StructuralContextFormation query.context query.levels)

def ContextCanonicalMeaning (goal : Pattern) : Type :=
  UniversalFibre contextFormationQueryCodec
    (fun query => StructuralContextFormation query.context query.levels) goal

/-- The compositional form of the one-root Prime meaning.  The product is not
an extra hierarchy: `primeMeaning_equiv_sumFibre` below proves it is exactly
the universal fibre of the disjoint coproduct codec. -/
def PrimeMeaning (goal : Pattern) : Type :=
  Structural.CanonicalMeaning goal × ContextCanonicalMeaning goal

def PrimeSumMeaning (goal : Pattern) : Type :=
  UniversalFibre primeJudgmentCodec PrimeJudgmentEvidence goal

/-- Universal semantics turns a disjoint coproduct of intrinsic judgments
into the product of their independently usable semantic views. -/
def primeMeaning_equiv_sumFibre (goal : Pattern) :
    PrimeMeaning goal ≃ PrimeSumMeaning goal := by
  simpa [PrimeMeaning, PrimeSumMeaning, PrimeJudgmentEvidence,
    Structural.CanonicalMeaning, ContextCanonicalMeaning,
    DeclarationAwareStructuralTyping.CanonicalMeaning,
    primeJudgmentCodec] using
    (universalFibre_product_equiv_sumOfDisjoint
      towerTypingClaimCodec contextFormationQueryCodec
      typing_context_images_disjoint
      DeclarationAwareStructuralTyping.ClaimEvidence
      (fun query =>
        StructuralContextFormation query.context query.levels) goal)

/-! ## One conservative context-formation layer -/

def contextNilRule : RuleSchema :=
  { id := ⟨"prime-context-formed-nil"⟩
    metavariables := []
    premises := []
    conclusion :=
      contextFormedPattern (encodeNat 0)
        (encodeCtx towerHeadCodec (.nil : Tower.Ctx 0))
        (encodeLevelSpine (.nil : LevelSpine 0)) }

def contextSnocRule : RuleSchema :=
  { id := ⟨"prime-context-formed-snoc"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("levels", 0), ("type", 0),
        ("level", 0)]
    premises :=
      [contextFormedPattern (.fvar "arity") (.fvar "context")
        (.fvar "levels"),
       DeclarationAwareStructuralTyping.hasTypePattern
        (.fvar "arity") (.fvar "context") (.fvar "type")
        (DeclarationAwareStructuralTyping.tmHeadPattern
          (DeclarationAwareStructuralTyping.headSortPattern
            (.fvar "level")))]
    conclusion :=
      contextFormedPattern
        (DeclarationAwareStructuralTyping.natSuccPattern (.fvar "arity"))
        (DeclarationAwareStructuralTyping.ctxSnocPattern
          (.fvar "context") (.fvar "type"))
        (.apply "prime-level-spine-snoc"
          [.fvar "levels", .fvar "level"]) }

def levelSpineNilConstructor : GrammarRule :=
  DeclarationAwareDataLanguage.dataConstructor "prime-level-spine-nil" 0

def levelSpineSnocConstructor : GrammarRule :=
  DeclarationAwareDataLanguage.dataConstructor "prime-level-spine-snoc" 2

def contextFormationDelta : PresentationExtension :=
  { newTerms := [levelSpineNilConstructor, levelSpineSnocConstructor]
    newJudgments := [{ head := "prime-context-formed", arity := 3 }]
    newRules := [contextNilRule, contextSnocRule] }

private theorem contextFormationDelta_disjoint :
    contextFormationDelta.disjointFrom Structural.checked.1 = true := by
  decide

private theorem contextFormationDelta_policy :
    contextFormationDelta.policyHolds Structural.checked.1
      .newJudgmentsOnly = true := by
  decide

private theorem contextFormationTarget_valid :
    (contextFormationDelta.apply Structural.checked.1).isValidV2 = true := by
  have validatedLanguage :
      (contextFormationDelta.apply Structural.checked.1).language.validate =
        [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [contextFormationDelta, PresentationExtension.apply,
        Structural.checked, DeclarationAwareStructuralTyping.checked,
        DeclarationAwareStructuralTyping.presentation,
        DeclarationAwareStructuralTyping.definition,
        DeclarationAwareDataLanguage.definition,
        DeclarationAwareDataLanguage.constructorArities,
        levelSpineNilConstructor, levelSpineSnocConstructor,
        DeclarationAwareDataLanguage.dataConstructor,
        DeclarationAwareDataLanguage.kernelDataType,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
        TypeExpr.baseNames]
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [validatedLanguage]
  simp [contextFormationDelta, PresentationExtension.apply,
    Structural.checked, DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    contextNilRule, contextSnocRule, contextFormedPattern,
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
    encodeLevelSpine, levelSpineNilConstructor,
    levelSpineSnocConstructor,
    DeclarationAwareDataLanguage.dataConstructor,
    DeclarationAwareDataLanguage.definition,
    DeclarationAwareDataLanguage.constructorArities,
    DeclarationAwareDataLanguage.kernelDataType,
    encodeTowerHead, Tower.zero, encodeLevel, encodeNat,
    encodeCtx, Presentation.ruleIds,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    Presentation.conversionDeclarationValid, Presentation.lookupJudgment?,
    RuleSchema.isValidIn, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSchemaValid,
    fixedConstructorsValid, fixedConstructorListsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead,
    Pattern.mapHead, Pattern.evalHead]
  decide

def contextFormationExtension : ValidatedExtension Structural.checked where
  extension := contextFormationDelta
  policy := .newJudgmentsOnly
  disjoint := contextFormationDelta_disjoint
  policyHolds := contextFormationDelta_policy
  valid := contextFormationTarget_valid

/-! ## The retained structural calculus in the heterogeneous meaning -/

private theorem contextEncoding_not_baseShape
    (query : ContextFormationQuery) :
    Structural.checked.1.hasJudgmentShape
        (encodeContextFormationQuery query) = false := by
  cases query
  simp [Structural.checked, DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareDataLanguage.definition,
    Presentation.hasJudgmentShape, Presentation.lookupJudgment?,
    encodeContextFormationQuery, contextFormedPattern]

private def contextMeaning_of_baseApplication
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication Structural.checked ruleInstance premises conclusion) :
    ContextCanonicalMeaning conclusion := by
  intro query equality
  have shape := application.conclusion_hasJudgmentShape
  rw [← equality] at shape
  change
    Structural.checked.1.hasJudgmentShape
      (encodeContextFormationQuery query) = true at shape
  rw [contextEncoding_not_baseShape] at shape
  contradiction

/-- Every canonical context query has the newly declared target judgment
shape.  This is the shape premise consumed by later conservative layers. -/
theorem contextQuery_hasTargetJudgmentShape
    (query : ContextFormationQuery) :
    contextFormationExtension.target.1.hasJudgmentShape
        (encodeContextFormationQuery query) = true := by
  cases query
  simp [contextFormationExtension, ValidatedExtension.target,
    contextFormationDelta, PresentationExtension.apply, Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.Data.definition,
    DeclarationAwareDataLanguage.definition,
    Presentation.hasJudgmentShape, Presentation.lookupJudgment?,
    encodeContextFormationQuery, contextFormedPattern]

/-- Retained typing rules acquire the heterogeneous meaning pointwise:
typing evidence is interpreted by the established structural semantics,
while the disjoint context view is vacuous at a typing conclusion. -/
def primeBaseSemantics :
    PresentationSemantics Structural.checked PrimeMeaning where
  ruleMeaning := by
    intro ruleInstance premises conclusion application premiseEvidence
    exact
      ⟨DeclarationAwareStructuralTyping.structuralSemantics.ruleMeaning
          application
          (premiseEvidence.map (fun _ evidence => evidence.1)),
        contextMeaning_of_baseApplication application⟩

private def primeMeaningOfContextEvidence
    (query : ContextFormationQuery)
    (evidence : StructuralContextFormation query.context query.levels) :
    PrimeMeaning (encodeContextFormationQuery query) :=
  ⟨fun typingQuery equality =>
      False.elim (typing_context_images_disjoint typingQuery query equality),
    fun otherQuery equality => by
      have sameQuery : otherQuery = query :=
        encodeContextFormationQuery_injective equality
      subst otherQuery
      exact evidence⟩

private def contextSnocConclusion_reflects
    (query : ContextFormationQuery)
    (arityPattern contextPattern levelsPattern typePattern levelPattern : Pattern)
    (contextMeaning :
      PrimeMeaning
        (contextFormedPattern arityPattern contextPattern levelsPattern))
    (typeMeaning :
      PrimeMeaning
        (DeclarationAwareStructuralTyping.hasTypePattern arityPattern
          contextPattern typePattern
          (DeclarationAwareStructuralTyping.tmHeadPattern
            (DeclarationAwareStructuralTyping.headSortPattern levelPattern))))
    (equality :
      encodeContextFormationQuery query =
        contextFormedPattern
          (DeclarationAwareStructuralTyping.natSuccPattern arityPattern)
          (DeclarationAwareStructuralTyping.ctxSnocPattern
            contextPattern typePattern)
          (.apply "prime-level-spine-snoc"
            [levelsPattern, levelPattern])) :
    StructuralContextFormation query.context query.levels := by
  rcases query with ⟨arity, context, levels⟩
  simp only [encodeContextFormationQuery, contextFormedPattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  cases arity with
  | zero =>
      simp [encodeNat, DeclarationAwareStructuralTyping.natSuccPattern]
        at equality
  | succ predecessor =>
      cases context with
      | snoc priorContext entryType =>
          cases levels with
          | snoc priorLevels entryLevel =>
              have arityEquality :
                  encodeNat predecessor = arityPattern := by
                simpa [encodeNat,
                  DeclarationAwareStructuralTyping.natSuccPattern] using
                  equality.1
              have contextEquality :
                  encodeCtx towerHeadCodec priorContext = contextPattern ∧
                    encodeTm towerHeadCodec entryType = typePattern := by
                simpa [encodeCtx,
                  DeclarationAwareStructuralTyping.ctxSnocPattern] using
                  equality.2.1
              have levelsEquality :
                  encodeLevelSpine priorLevels = levelsPattern ∧
                    encodeLevel entryLevel = levelPattern := by
                simpa [encodeLevelSpine] using equality.2.2
              have priorEvidence :
                  StructuralContextFormation priorContext priorLevels :=
                contextMeaning.2
                  { arity := predecessor
                    context := priorContext
                    levels := priorLevels }
                  (by
                    simp only [contextFormationQueryCodec,
                      encodeContextFormationQuery,
                      contextFormedPattern, Pattern.apply.injEq,
                      List.cons.injEq, and_true, true_and]
                    exact
                      ⟨arityEquality, contextEquality.1,
                        levelsEquality.1⟩)
              have encodedSort :
                  encodeTm towerHeadCodec
                      (.head (.sort entryLevel) : Tower.Tm predecessor) =
                    DeclarationAwareStructuralTyping.tmHeadPattern
                      (DeclarationAwareStructuralTyping.headSortPattern
                        levelPattern) := by
                simp [encodeTm, towerHeadCodec, encodeTowerHead,
                  DeclarationAwareStructuralTyping.tmHeadPattern,
                  DeclarationAwareStructuralTyping.headSortPattern,
                  levelsEquality.2]
              have typeEvidence :
                  Structural.StructuralTyping priorContext entryType
                    (.head (.sort entryLevel)) :=
                typeMeaning.1
                  { arity := predecessor
                    context := priorContext
                    subject := entryType
                    type := .head (.sort entryLevel) }
                  (by
                    simp only [towerTypingClaimCodec, typingClaimCodec,
                      encodeTypingClaim,
                      DeclarationAwareStructuralTyping.hasTypePattern,
                      Pattern.apply.injEq, List.cons.injEq, and_true,
                      true_and]
                    exact
                      ⟨arityEquality, contextEquality.1,
                        contextEquality.2, encodedSort⟩)
              exact .snoc priorEvidence typeEvidence

private def contextNilAddedMeaning
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (lookup :
      contextFormationExtension.target.1.lookupRule?
          ruleInstance.ruleId = some contextNilRule)
    (application :
      RuleApplication contextFormationExtension.target ruleInstance
        premises conclusion)
    (premiseEvidence : EvidenceList PrimeMeaning premises) :
    PrimeMeaning conclusion := by
  have instantiated :=
    instantiateRule?_eq_some_iff_application.mpr application
  rcases ruleInstance with ⟨ruleId, arguments⟩
  cases arguments with
  | nil =>
      simp [instantiateRule?, lookup, contextNilRule, argumentsValidAt,
        RuleSchema.sideConditionsHold, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        contextFormedPattern,
        encodeNat, encodeCtx, encodeLevelSpine] at instantiated
      rcases instantiated with ⟨rfl, rfl⟩
      cases premiseEvidence
      exact
        primeMeaningOfContextEvidence
          { arity := 0, context := .nil, levels := .nil } .nil
  | cons argument arguments =>
      simp [instantiateRule?, lookup, contextNilRule, argumentsValidAt]
        at instantiated

private def contextSnocAddedMeaning
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (lookup :
      contextFormationExtension.target.1.lookupRule?
          ruleInstance.ruleId = some contextSnocRule)
    (application :
      RuleApplication contextFormationExtension.target ruleInstance
        premises conclusion)
    (premiseEvidence : EvidenceList PrimeMeaning premises) :
    PrimeMeaning conclusion := by
  have instantiated :=
    instantiateRule?_eq_some_iff_application.mpr application
  rcases ruleInstance with ⟨ruleId, arguments⟩
  cases arguments with
  | nil =>
      simp [instantiateRule?, lookup, contextSnocRule, argumentsValidAt]
        at instantiated
  | cons arityPattern remaining =>
    cases remaining with
    | nil =>
        simp [instantiateRule?, lookup, contextSnocRule, argumentsValidAt]
          at instantiated
    | cons contextPattern remaining =>
      cases remaining with
      | nil =>
          simp [instantiateRule?, lookup, contextSnocRule, argumentsValidAt]
            at instantiated
      | cons levelsPattern remaining =>
        cases remaining with
        | nil =>
            simp [instantiateRule?, lookup, contextSnocRule, argumentsValidAt]
              at instantiated
        | cons typePattern remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, contextSnocRule,
                argumentsValidAt] at instantiated
          | cons levelPattern remaining =>
            cases remaining with
            | cons extra tail =>
                simp [instantiateRule?, lookup, contextSnocRule,
                  argumentsValidAt] at instantiated
            | nil =>
                simp [instantiateRule?, lookup, contextSnocRule,
                  RuleSchema.sideConditionsHold, argumentsValidAt,
                  instantiateSchema?, instantiateSchemaAt?,
                  instantiateSchemas?, instantiateSchemasAt?,
                  lookupArgumentAt?, contextFormedPattern,
                  DeclarationAwareStructuralTyping.hasTypePattern,
                  DeclarationAwareStructuralTyping.tmHeadPattern,
                  DeclarationAwareStructuralTyping.headSortPattern,
                  DeclarationAwareStructuralTyping.natSuccPattern,
                  DeclarationAwareStructuralTyping.ctxSnocPattern]
                  at instantiated
                rcases instantiated with ⟨_, rfl, rfl⟩
                cases premiseEvidence with
                | cons contextMeaning rest =>
                  cases rest with
                  | cons typeMeaning rest =>
                    cases rest
                    exact
                      ⟨fun typingQuery equality => by
                          cases typingQuery
                          simp [towerTypingClaimCodec, typingClaimCodec,
                            encodeTypingClaim] at equality,
                        fun query equality =>
                          contextSnocConclusion_reflects query arityPattern
                            contextPattern levelsPattern typePattern
                            levelPattern contextMeaning typeMeaning equality⟩

/-- Context formation and retained structural typing form one interpreted
presentation.  Added context rules consume the ordered evidence supplied by
the generic checker and construct the corresponding intrinsic telescope. -/
def contextSemanticExtension :
    SemanticExtension Structural.checked contextFormationExtension
      PrimeMeaning where
  baseSemantics := primeBaseSemantics
  addedRuleMeaning := by
    intro rule member ruleInstance premises conclusion lookup application
      premiseEvidence
    simp only [contextFormationExtension, contextFormationDelta,
      List.mem_cons, List.not_mem_nil, or_false] at member
    by_cases nilMember : rule = contextNilRule
    · subst rule
      exact contextNilAddedMeaning ruleInstance premises conclusion lookup
        application premiseEvidence
    · have snocMember : rule = contextSnocRule := by
        rcases member with nilEquality | snocEquality
        · exact False.elim (nilMember nilEquality)
        · exact snocEquality
      subst rule
      exact contextSnocAddedMeaning ruleInstance premises conclusion lookup
        application premiseEvidence

/-! ## Compilation to exact raw proof trees -/

def contextNilRaw : RawProof :=
  .node { ruleId := contextNilRule.id, arguments := [] } []

def contextSnocRaw {n : Nat} (context : Tower.Ctx n)
    (levels : LevelSpine n) (type : Tower.Tm n) (level : LevelExpr)
    (contextPremise typePremise : RawProof) : RawProof :=
  .node
    { ruleId := contextSnocRule.id
      arguments :=
        [encodeNat n, encodeCtx towerHeadCodec context,
          encodeLevelSpine levels, encodeTm towerHeadCodec type,
          encodeLevel level] }
    [contextPremise, typePremise]

def StructuralContextFormation.raw :
    {n : Nat} → {context : Tower.Ctx n} → {levels : LevelSpine n} →
      StructuralContextFormation context levels → RawProof
  | _, _, _, .nil => contextNilRaw
  | _, _, _, @StructuralContextFormation.snoc n context type levels level
      prior typeFormation =>
      contextSnocRaw context levels type level prior.raw typeFormation.raw

private theorem instantiateContextNilRule :
    instantiateRule? contextFormationExtension.target
        { ruleId := contextNilRule.id, arguments := [] } =
      some ([], encodeContextFormationQuery
        { arity := 0, context := .nil, levels := .nil }) := by
  simp [contextFormationExtension, ValidatedExtension.target,
    contextFormationDelta, PresentationExtension.apply, Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    contextNilRule, contextSnocRule, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    encodeContextFormationQuery, contextFormedPattern, encodeLevelSpine,
    encodeNat, encodeCtx]

private theorem instantiateContextSnocRule {n : Nat}
    (context : Tower.Ctx n) (levels : LevelSpine n)
    (type : Tower.Tm n) (level : LevelExpr) :
    instantiateRule? contextFormationExtension.target
        { ruleId := contextSnocRule.id
          arguments :=
            [encodeNat n, encodeCtx towerHeadCodec context,
              encodeLevelSpine levels, encodeTm towerHeadCodec type,
              encodeLevel level] } =
      some
        ([encodeContextFormationQuery
            { arity := n, context := context, levels := levels },
          encodeTypingClaim towerHeadCodec
            { arity := n, context := context, subject := type,
              type := .head (.sort level) }],
          encodeContextFormationQuery
            { arity := n + 1, context := .snoc context type,
              levels := .snoc levels level }) := by
  have arityValid := encodeNat_argumentValid n
  have contextValid := encodeTowerCtx_argumentValid context
  have levelsValid := encodeLevelSpine_argumentValid levels
  have typeValid := encodeTowerTm_argumentValid type
  have levelValid := encodeLevel_argumentValid level
  simp [contextFormationExtension, ValidatedExtension.target,
    contextFormationDelta, PresentationExtension.apply, Structural.checked,
    DeclarationAwareStructuralTyping.checked,
    DeclarationAwareStructuralTyping.presentation,
    DeclarationAwareStructuralTyping.definition,
    DeclarationAwareStructuralTyping.legacyGroundRule,
    DeclarationAwareStructuralTyping.sortRule,
    DeclarationAwareStructuralTyping.reflRule,
    DeclarationAwareStructuralTyping.piFormRule,
    contextNilRule, contextSnocRule, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, arityValid, levelsValid,
    levelValid,
    RuleSchema.sideConditionsHold,
    instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, encodeContextFormationQuery,
    contextFormedPattern, encodeTypingClaim,
    DeclarationAwareStructuralTyping.hasTypePattern,
    DeclarationAwareStructuralTyping.tmHeadPattern,
    DeclarationAwareStructuralTyping.headSortPattern,
    DeclarationAwareStructuralTyping.natSuccPattern,
    DeclarationAwareStructuralTyping.ctxSnocPattern, encodeNat, encodeCtx,
    encodeTm, towerHeadCodec, encodeTowerHead]
  exact ⟨⟨contextValid, typeValid⟩, rfl⟩

theorem StructuralContextFormation.raw_accepted
    {n : Nat} {context : Tower.Ctx n} {levels : LevelSpine n}
    (formation : StructuralContextFormation context levels) :
    checkRaw contextFormationExtension.target
        (encodeContextFormationQuery
          { arity := n, context := context, levels := levels })
        formation.raw = true := by
  induction formation with
  | nil =>
      simp [StructuralContextFormation.raw, contextNilRaw, checkRaw,
        instantiateContextNilRule, checkRawChildren]
  | @snoc n context type levels level prior typeFormation priorIH =>
      have typeAccepted :
          checkRaw contextFormationExtension.target
            (encodeTypingClaim towerHeadCodec
              { arity := n, context := context, subject := type,
                type := .head (.sort level) })
            typeFormation.raw = true :=
        checkRaw_true_of_ruleLookupRefines contextFormationExtension.refines
          (by
            simpa [DeclarationAwareStructuralTyping.claimPattern] using
              typeFormation.raw_accepted)
      simp only [StructuralContextFormation.raw, contextSnocRaw, checkRaw,
        instantiateContextSnocRule context levels type level, decide_true,
        Bool.true_and,
        checkRawChildren, Bool.and_true, Bool.and_eq_true]
      exact ⟨priorIH, typeAccepted⟩

/-! ## Exact checker reflection -/

/-- A raw proof accepted at a canonical context-formation query reconstructs
the independently defined intrinsic telescope evidence.  Choice selects the
checked derivation whose erasure is the supplied artifact; interpretation is
then structural and retains every ordered premise. -/
noncomputable def reflectAcceptedRaw
    {n : Nat} {context : Tower.Ctx n} {levels : LevelSpine n}
    (proof : RawProof)
    (accepted :
      checkRaw contextFormationExtension.target
        (encodeContextFormationQuery
          { arity := n, context := context, levels := levels }) proof = true) :
    StructuralContextFormation context levels := by
  let derivation :=
    (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted).choose
  exact
    (contextSemanticExtension.interpret derivation).2
      { arity := n, context := context, levels := levels } rfl

/-- On the exact context codec image, acceptance by the one generic checker
is equivalent to inhabitation of the intrinsic formed-context fibre. -/
theorem exists_accepted_raw_iff_nonempty_contextFormation
    {n : Nat} {context : Tower.Ctx n} {levels : LevelSpine n} :
    (∃ proof : RawProof,
      checkRaw contextFormationExtension.target
        (encodeContextFormationQuery
          { arity := n, context := context, levels := levels }) proof = true) ↔
      Nonempty (StructuralContextFormation context levels) := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact ⟨reflectAcceptedRaw proof accepted⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.raw, evidence.raw_accepted⟩

/-! ## Controls -/

namespace Examples

def emptyFormation :
    StructuralContextFormation (.nil : Tower.Ctx 0) .nil :=
  .nil

theorem empty_raw_accepted :
    checkRaw contextFormationExtension.target
        (encodeContextFormationQuery
          { arity := 0, context := .nil, levels := .nil })
        emptyFormation.raw = true :=
  emptyFormation.raw_accepted

def oneType : Tower.Tm 0 := .head .legacyGround

def oneTypeFormation :
    Structural.StructuralTyping (.nil : Tower.Ctx 0) oneType
      (.head (.sort Tower.zero)) :=
  .legacyGround .nil

def oneContextFormation :
    StructuralContextFormation
      (.snoc (.nil : Tower.Ctx 0) oneType)
      (.snoc .nil Tower.zero) :=
  .snoc emptyFormation oneTypeFormation

theorem one_context_raw_accepted :
    checkRaw contextFormationExtension.target
        (encodeContextFormationQuery
          { arity := 1, context := .snoc .nil oneType,
            levels := .snoc .nil Tower.zero })
        oneContextFormation.raw = true :=
  oneContextFormation.raw_accepted

/-- A one-entry telescope cannot be relabelled as an empty-context judgment.
The dependent index is recovered by decoding, rather than trusted as wire
metadata. -/
theorem mismatched_context_arity_rejected :
    decodeContextFormationQuery?
        (contextFormedPattern (encodeNat 0)
          (encodeCtx towerHeadCodec
            (.snoc (.nil : Tower.Ctx 0) oneType))
          (encodeLevelSpine (.nil : LevelSpine 0))) = none := by
  rfl

end Examples

#print axioms encodeContextFormationQuery_injective
#print axioms contextQuery_hasTargetJudgmentShape
#print axioms StructuralContextFormation.toContextWellFormed
#print axioms contextSemanticExtension
#print axioms StructuralContextFormation.raw_accepted
#print axioms reflectAcceptedRaw
#print axioms exists_accepted_raw_iff_nonempty_contextFormation
#print axioms Examples.empty_raw_accepted
#print axioms Examples.one_context_raw_accepted
#print axioms Examples.mismatched_context_arity_rejected

end Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareCheckedContext
