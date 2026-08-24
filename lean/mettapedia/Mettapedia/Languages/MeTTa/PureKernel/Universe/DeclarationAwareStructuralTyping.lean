import Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
import Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation
import Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareDataLanguage
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationSignature
import Mettapedia.Languages.MeTTa.PureKernel.Universe.TypingGeneration

/-!
# A checked structural fragment of declaration-aware Prime typing

This module is the first recursive typing calculus authored over the exact
declaration-aware data language.  It covers tower-head formation, dependent
reflexivity, and dependent-function formation across a telescope extension.
Its intrinsic evidence maps into the common Prime `HasType` spine, and every
such evidence tree compiles to a proof accepted by the generic inference
checker.

The checker is intentionally composed with the canonical intrinsic codec at
raw ingress and with a positively formed context at native realization.  Two
negative controls show why: schema replay alone can accept an arity-incoherent
context argument, while a canonical structural derivation may still inhabit a
telescope whose declaration is missing.  Neither can cross the formed native
boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareStructuralTyping

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.GSLT.LanguageDef.CanonicalPremiseClosure
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Data
abbrev definition := DeclarationAwareDataLanguage.definition
abbrev language := DeclarationAwareDataLanguage.language
end Data

def hasTypePattern (arity context subject type : Pattern) : Pattern :=
  .apply "prime-has-type" [arity, context, subject, type]

def tmHeadPattern (head : Pattern) : Pattern := .apply "prime-tm-head" [head]
def tmReflPattern (term : Pattern) : Pattern := .apply "prime-tm-refl" [term]
def tmIdPattern (type left right : Pattern) : Pattern :=
  .apply "prime-tm-id" [type, left, right]
def tmPiPattern (domain body : Pattern) : Pattern :=
  .apply "prime-tm-pi" [domain, body]
def headSortPattern (level : Pattern) : Pattern :=
  .apply "prime-head-sort" [level]
def levelSuccPattern (level : Pattern) : Pattern :=
  .apply "prime-level-succ" [level]
def levelMaxPattern (left right : Pattern) : Pattern :=
  .apply "prime-level-max" [left, right]
def natSuccPattern (value : Pattern) : Pattern :=
  .apply "prime-nat-succ" [value]
def ctxSnocPattern (context type : Pattern) : Pattern :=
  .apply "prime-ctx-snoc" [context, type]

def legacyGroundRule : RuleSchema :=
  { id := ⟨"prime-structural-legacy-ground"⟩
    metavariables := [("arity", 0), ("context", 0)]
    premises := []
    conclusion :=
      hasTypePattern (.fvar "arity") (.fvar "context")
        (tmHeadPattern (encodeTowerHead .legacyGround))
        (tmHeadPattern (encodeTowerHead (.sort Tower.zero))) }

def sortRule : RuleSchema :=
  { id := ⟨"prime-structural-sort"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("level", 0)]
    premises := []
    conclusion :=
      hasTypePattern (.fvar "arity") (.fvar "context")
        (tmHeadPattern (headSortPattern (.fvar "level")))
        (tmHeadPattern
          (headSortPattern (levelSuccPattern (.fvar "level")))) }

def reflRule : RuleSchema :=
  { id := ⟨"prime-structural-refl"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("term", 0), ("type", 0)]
    premises :=
      [hasTypePattern (.fvar "arity") (.fvar "context")
        (.fvar "term") (.fvar "type")]
    conclusion :=
      hasTypePattern (.fvar "arity") (.fvar "context")
        (tmReflPattern (.fvar "term"))
        (tmIdPattern (.fvar "type") (.fvar "term") (.fvar "term")) }

/-- Dependent function formation is represented without an auxiliary
substitution oracle: the codomain premise is checked directly in the encoded
telescope extension, and the result universe is the explicit level maximum. -/
def piFormRule : RuleSchema :=
  { id := ⟨"prime-structural-pi-form"⟩
    metavariables :=
      [("arity", 0), ("context", 0), ("domain", 0), ("body", 0),
        ("domainLevel", 0), ("bodyLevel", 0)]
    premises :=
      [hasTypePattern (.fvar "arity") (.fvar "context")
        (.fvar "domain")
        (tmHeadPattern (headSortPattern (.fvar "domainLevel"))),
       hasTypePattern (natSuccPattern (.fvar "arity"))
        (ctxSnocPattern (.fvar "context") (.fvar "domain"))
        (.fvar "body")
        (tmHeadPattern (headSortPattern (.fvar "bodyLevel")))]
    conclusion :=
      hasTypePattern (.fvar "arity") (.fvar "context")
        (tmPiPattern (.fvar "domain") (.fvar "body"))
        (tmHeadPattern
          (headSortPattern
            (levelMaxPattern (.fvar "domainLevel")
              (.fvar "bodyLevel")))) }

def definition : CalculusLanguageDef :=
  { Data.definition with
    rules := [legacyGroundRule, sortRule, reflRule, piFormRule] }

def language : LanguageDef := definition.toLanguageDef
def presentation : Presentation := definition.toNested

theorem language_validate : language.validate = [] := by
  simpa [language, definition, Data.definition,
    DeclarationAwareDataLanguage.language] using
    DeclarationAwareDataLanguage.language_validate

@[simp] theorem presentation_language_eq_data :
    presentation.language = DeclarationAwareDataLanguage.language := by
  rfl

private theorem legacyGroundRule_validV1 :
    RuleSchema.isValidV1 legacyGroundRule = true := by
  simp [RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, legacyGroundRule,
    hasTypePattern, tmHeadPattern, encodeTowerHead, Tower.zero,
    encodeLevel, encodeNat]
  decide

private theorem sortRule_validV1 :
    RuleSchema.isValidV1 sortRule = true := by
  simp [RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, sortRule, hasTypePattern,
    tmHeadPattern, headSortPattern, levelSuccPattern]
  decide

private theorem reflRule_validV1 :
    RuleSchema.isValidV1 reflRule = true := by
  simp [RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, reflRule, hasTypePattern,
    tmReflPattern, tmIdPattern]
  decide

private theorem piFormRule_validV1 :
    RuleSchema.isValidV1 piFormRule = true := by
  simp [RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, piFormRule, hasTypePattern,
    tmHeadPattern, tmPiPattern, headSortPattern, levelMaxPattern,
    natSuccPattern, ctxSnocPattern]
  decide

@[simp] theorem hasTypingJudgment :
    (presentation.lookupJudgment? "prime-has-type" 4).isSome = true := by
  decide

private theorem legacyGroundRule_validIn :
    RuleSchema.isValidIn presentation legacyGroundRule = true := by
  simp only [RuleSchema.isValidIn, legacyGroundRule_validV1, Bool.true_and]
  simp [
    RuleSchema.patterns, legacyGroundRule, hasTypePattern, tmHeadPattern,
    Presentation.judgmentSchemaValid, hasTypingJudgment,
    fixedConstructorListsValid, fixedConstructorsValid,
    presentation_language_eq_data,
    DeclarationAwareDataLanguage.fixed_encodeTowerHead]

private theorem sortRule_validIn :
    RuleSchema.isValidIn presentation sortRule = true := by
  simp only [RuleSchema.isValidIn, sortRule_validV1, Bool.true_and]
  simp [RuleSchema.patterns,
    sortRule, hasTypePattern, tmHeadPattern, headSortPattern,
    levelSuccPattern, Presentation.judgmentSchemaValid, hasTypingJudgment,
    fixedConstructorListsValid, fixedConstructorsValid,
    presentation_language_eq_data]

private theorem reflRule_validIn :
    RuleSchema.isValidIn presentation reflRule = true := by
  simp only [RuleSchema.isValidIn, reflRule_validV1, Bool.true_and]
  simp [RuleSchema.patterns,
    reflRule, hasTypePattern, tmReflPattern, tmIdPattern,
    Presentation.judgmentSchemaValid, hasTypingJudgment,
    fixedConstructorListsValid, fixedConstructorsValid,
    presentation_language_eq_data]

private theorem piFormRule_validIn :
    RuleSchema.isValidIn presentation piFormRule = true := by
  simp only [RuleSchema.isValidIn, piFormRule_validV1, Bool.true_and]
  simp [RuleSchema.patterns, piFormRule, hasTypePattern, tmHeadPattern,
    tmPiPattern, headSortPattern, levelMaxPattern, natSuccPattern,
    ctxSnocPattern, Presentation.judgmentSchemaValid, hasTypingJudgment,
    fixedConstructorListsValid, fixedConstructorsValid,
    presentation_language_eq_data]

theorem presentation_valid : presentation.isValidV2 = true := by
  have validatedLanguage : presentation.language.validate = [] := by
    simpa [presentation, language] using language_validate
  have signatureValid : presentation.judgmentSignatureValid = true := by
    have dataValid := DeclarationAwareDataLanguage.presentation_valid
    unfold Presentation.isValidV2 at dataValid
    simp only [Bool.and_eq_true] at dataValid
    have dataSignature := dataValid.1.1.2
    change DeclarationAwareDataLanguage.presentation.judgmentSignatureValid =
      true
    exact dataSignature
  have conversionValid : presentation.conversionDeclarationValid = true := by
    have dataValid := DeclarationAwareDataLanguage.presentation_valid
    unfold Presentation.isValidV2 at dataValid
    simp only [Bool.and_eq_true] at dataValid
    have dataConversion := dataValid.2
    change
      DeclarationAwareDataLanguage.presentation.conversionDeclarationValid =
        true
    exact dataConversion
  have v1Valid : presentation.isValidV1 = true := by
    have validEmpty : presentation.language.validate.isEmpty = true :=
      congrArg List.isEmpty validatedLanguage
    unfold Presentation.isValidV1
    rw [validEmpty]
    simp only [Bool.true_and]
    change
      (([legacyGroundRule, sortRule, reflRule, piFormRule].all
          RuleSchema.isValidV1) &&
        ([legacyGroundRule.id, sortRule.id, reflRule.id,
          piFormRule.id].eraseDups.length == 4)) = true
    rw [show [legacyGroundRule, sortRule, reflRule, piFormRule].all
        RuleSchema.isValidV1 = true by
      simp [legacyGroundRule_validV1, sortRule_validV1,
        reflRule_validV1, piFormRule_validV1]]
    decide
  unfold Presentation.isValidV2
  rw [v1Valid, signatureValid, conversionValid]
  simp only [Bool.true_and, Bool.and_true]
  change
    [legacyGroundRule, sortRule, reflRule, piFormRule].all
      (RuleSchema.isValidIn presentation) = true
  simp [legacyGroundRule_validIn, sortRule_validIn, reflRule_validIn,
    piFormRule_validIn]

def checked : ValidatedPresentation := ⟨presentation, presentation_valid⟩

/-! ## Independent intrinsic meaning -/

/-- The exact intrinsic fragment represented by the four authored rules. -/
inductive StructuralTyping : {n : Nat} →
    Tower.Ctx n → Tower.Tm n → Tower.Tm n → Type where
  | legacyGround {n : Nat} (context : Tower.Ctx n) :
      StructuralTyping context (.head .legacyGround)
        (.head (.sort Tower.zero))
  | sort {n : Nat} (context : Tower.Ctx n) (level : LevelExpr) :
      StructuralTyping context (.head (.sort level))
        (.head (.sort (.succ level)))
  | reflIntro {n : Nat} {context : Tower.Ctx n}
      {term type : Tower.Tm n} :
      StructuralTyping context term type →
      StructuralTyping context (.refl term) (.id type term term)
  | piForm {n : Nat} {context : Tower.Ctx n}
      {domain : Tower.Tm n} {body : Tower.Tm (n + 1)}
      {domainLevel bodyLevel : LevelExpr} :
      StructuralTyping context domain
        (.head (.sort domainLevel)) →
      StructuralTyping (.snoc context domain) body
        (.head (.sort bodyLevel)) →
      StructuralTyping context (.pi domain body)
        (.head (.sort (.max domainLevel bodyLevel)))

/-- Structural evidence is genuine evidence in the common cumulative Prime
typing spine; it is not defined by checker acceptance. -/
def StructuralTyping.toHasType :
    {n : Nat} → {context : Tower.Ctx n} →
    {term type : Tower.Tm n} →
    (evidence : StructuralTyping context term type) →
      Tower.HasType context term type
  | _, _, _, _, .legacyGround _ => .headType .legacyGround
  | _, _, _, _, .sort _ level => .headType (.sort level)
  | _, _, _, _, .reflIntro premise => .reflIntro premise.toHasType
  | _, _, _, _, @piForm _ _ _ _ domainLevel bodyLevel domain body =>
      .piForm domain.toHasType (.sort domainLevel) body.toHasType
        (.sort bodyLevel) (.sorts domainLevel bodyLevel)

/-- Intrinsic evidence indexed by one decoded typing claim. -/
def ClaimEvidence (claim : TypingClaim Tower.Head) : Type :=
  StructuralTyping claim.context claim.subject claim.type

/-- A checked Pattern goal receives the total universal fibre of the exact
typing-claim codec.  This is intentionally vacuous outside the canonical
image so unrestricted relational proof search remains interpretable.  Native
construction recovers a positive fibre only through canonical-premise closure
and the exact decoder. -/
def CanonicalMeaning (goal : Pattern) : Type :=
  UniversalFibre towerTypingClaimCodec ClaimEvidence goal

/-- The corresponding positive native fibre retains the decoded claim, exact
wire identity, and its intrinsic structural evidence. -/
def PositiveCanonicalMeaning (goal : Pattern) : Type :=
  PositiveFibre towerTypingClaimCodec ClaimEvidence goal

/-- Universal and positive meanings agree on every supported Prime typing
wire, but not globally. -/
theorem positiveCanonicalMeaning_iff_universal_of_inImage
    {goal : Pattern} (support : InImage towerTypingClaimCodec goal) :
    Nonempty (PositiveCanonicalMeaning goal) ↔
      Nonempty (CanonicalMeaning goal) :=
  nonempty_positive_iff_nonempty_universal_of_inImage support

/-! ## Formed native worlds -/

/-- A canonical typing claim together with positive evidence that its ambient
telescope is a legitimate Prime context.  The surface representation forgets
only this proof-irrelevant witness; it does not forget any term, type, scope,
or declaration data. -/
structure FormedTypingClaim where
  claim : TypingClaim Tower.Head
  contextWellFormed : ContextWellFormed Tower.rules claim.context

namespace FormedTypingClaim

def surface (formed : FormedTypingClaim) : Pattern :=
  encodeTypingClaim towerHeadCodec formed.claim

/-- Forgetting context-formation evidence is injective because the retained
claim is complete and formation evidence lives in `Prop`. -/
theorem claim_injective :
    Function.Injective (fun formed : FormedTypingClaim ↦ formed.claim) := by
  intro first second equality
  cases first with
  | mk firstClaim firstWellFormed =>
      cases second with
      | mk secondClaim secondWellFormed =>
          dsimp at equality
          subst secondClaim
          rfl

theorem surface_injective : Function.Injective surface := by
  intro first second equality
  apply claim_injective
  exact encodeTowerTypingClaim_injective equality

/-- A universe-typed domain extends the retained formed world exactly once.
Dependent premises may then be checked or constructed in this new world
without replaying context formation inside the eventual hot artifact. -/
def extendContext (formed : FormedTypingClaim)
    {domain : Tower.Tm formed.claim.arity} {level : LevelExpr}
    (domainEvidence :
      StructuralTyping formed.claim.context domain (.head (.sort level))) :
    ContextWellFormed Tower.rules (.snoc formed.claim.context domain) :=
  .snoc formed.contextWellFormed domainEvidence.toHasType (.sort level)

end FormedTypingClaim

def claimPattern {n : Nat} (context : Tower.Ctx n)
    (subject type : Tower.Tm n) : Pattern :=
  encodeTypingClaim towerHeadCodec
    { arity := n, context := context, subject := subject, type := type }

private def legacyConclusion_reflects
    {n : Nat} (intrinsicContext : Tower.Ctx n)
    (subject type : Tower.Tm n) (arity context : Pattern)
    (equality :
      claimPattern intrinsicContext subject type =
        hasTypePattern arity context
          (tmHeadPattern (encodeTowerHead .legacyGround))
          (tmHeadPattern (encodeTowerHead (.sort Tower.zero)))) :
    StructuralTyping intrinsicContext subject type := by
  simp only [claimPattern, encodeTypingClaim, hasTypePattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have subjectEquality : subject = .head .legacyGround :=
    (tmCodec towerHeadCodec n).encode_injective (by
      simpa [tmCodec, tmHeadPattern, towerHeadCodec, encodeTm] using
        equality.2.2.1)
  have typeEquality : type = .head (.sort Tower.zero) :=
    (tmCodec towerHeadCodec n).encode_injective (by
      simpa [tmCodec, tmHeadPattern, towerHeadCodec, encodeTm] using
        equality.2.2.2)
  subst subject
  subst type
  exact .legacyGround intrinsicContext

private def sortConclusion_reflects
    {n : Nat} (intrinsicContext : Tower.Ctx n)
    (subject type : Tower.Tm n) (arity context levelPattern : Pattern)
    (equality :
      claimPattern intrinsicContext subject type =
        hasTypePattern arity context
          (tmHeadPattern (headSortPattern levelPattern))
          (tmHeadPattern (headSortPattern
            (levelSuccPattern levelPattern)))) :
    StructuralTyping intrinsicContext subject type := by
  simp only [claimPattern, encodeTypingClaim, hasTypePattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have decodedSubject :
      decodeTm? towerHeadCodec n
          (tmHeadPattern (headSortPattern levelPattern)) = some subject := by
    rw [← equality.2.2.1]
    exact decodeTm?_encodeTm towerHeadCodec subject
  cases decodedLevel : decodeLevel? levelPattern with
  | none =>
      simp [tmHeadPattern, headSortPattern, decodeTm?, towerHeadCodec,
        decodeTowerHead?, decodedLevel] at decodedSubject
  | some level =>
      have subjectEquality : subject = .head (.sort level) := by
        simpa [tmHeadPattern, headSortPattern, decodeTm?, towerHeadCodec,
          decodeTowerHead?, decodedLevel] using decodedSubject.symm
      have decodedType :
          decodeTm? towerHeadCodec n
              (tmHeadPattern
                (headSortPattern (levelSuccPattern levelPattern))) =
            some type := by
        rw [← equality.2.2.2]
        exact decodeTm?_encodeTm towerHeadCodec type
      have typeEquality : type = .head (.sort (.succ level)) := by
        simpa [tmHeadPattern, headSortPattern, levelSuccPattern, decodeTm?,
          towerHeadCodec, decodeTowerHead?, decodeLevel?, decodedLevel] using
          decodedType.symm
      subst subject
      subst type
      exact .sort intrinsicContext level

private def reflConclusion_reflects
    {n : Nat} (intrinsicContext : Tower.Ctx n)
    (subject type : Tower.Tm n)
    (arity context termPattern typePattern : Pattern)
    (premiseMeaning :
      CanonicalMeaning
        (hasTypePattern arity context termPattern typePattern))
    (equality :
      claimPattern intrinsicContext subject type =
        hasTypePattern arity context (tmReflPattern termPattern)
          (tmIdPattern typePattern termPattern termPattern)) :
    StructuralTyping intrinsicContext subject type := by
  simp only [claimPattern, encodeTypingClaim, hasTypePattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have decodedSubject :
      decodeTm? towerHeadCodec n (tmReflPattern termPattern) = some subject := by
    rw [← equality.2.2.1]
    exact decodeTm?_encodeTm towerHeadCodec subject
  cases decodedTerm : decodeTm? towerHeadCodec n termPattern with
  | none =>
      simp [tmReflPattern, decodeTm?, decodedTerm] at decodedSubject
  | some term =>
      have subjectEquality : subject = .refl term := by
        simpa [tmReflPattern, decodeTm?, decodedTerm] using
          decodedSubject.symm
      have decodedResult :
          decodeTm? towerHeadCodec n
              (tmIdPattern typePattern termPattern termPattern) = some type := by
        rw [← equality.2.2.2]
        exact decodeTm?_encodeTm towerHeadCodec type
      cases decodedType : decodeTm? towerHeadCodec n typePattern with
      | none =>
          simp [tmIdPattern, decodeTm?, decodedTerm, decodedType] at decodedResult
      | some premiseType =>
          have typeEquality : type = .id premiseType term term := by
            simpa [tmIdPattern, decodeTm?, decodedTerm, decodedType] using
              decodedResult.symm
          have termPatternEquality :
              encodeTm towerHeadCodec term = termPattern := by
            have encodedSubject := equality.2.2.1
            rw [subjectEquality] at encodedSubject
            simpa [encodeTm, tmReflPattern] using encodedSubject
          have typePatternEquality :
              encodeTm towerHeadCodec premiseType = typePattern := by
            have encodedType := equality.2.2.2
            rw [typeEquality] at encodedType
            simpa [encodeTm, tmIdPattern, termPatternEquality] using
              encodedType
          have premiseEvidence :
              StructuralTyping intrinsicContext term premiseType :=
            premiseMeaning
              { arity := n
                context := intrinsicContext
                subject := term
                type := premiseType }
              (by
                change
                  encodeTypingClaim towerHeadCodec
                      { arity := n
                        context := intrinsicContext
                        subject := term
                        type := premiseType } =
                    hasTypePattern arity context termPattern typePattern
                simp only [encodeTypingClaim, hasTypePattern,
                  Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
                exact ⟨equality.1, equality.2.1, termPatternEquality,
                  typePatternEquality⟩)
          subst subject
          subst type
          exact .reflIntro premiseEvidence

private def piConclusion_reflects
    {n : Nat} (intrinsicContext : Tower.Ctx n)
    (subject type : Tower.Tm n)
    (arity context domainPattern bodyPattern domainLevelPattern
      bodyLevelPattern : Pattern)
    (domainMeaning :
      CanonicalMeaning
        (hasTypePattern arity context domainPattern
          (tmHeadPattern (headSortPattern domainLevelPattern))))
    (bodyMeaning :
      CanonicalMeaning
        (hasTypePattern (natSuccPattern arity)
          (ctxSnocPattern context domainPattern) bodyPattern
          (tmHeadPattern (headSortPattern bodyLevelPattern))))
    (equality :
      claimPattern intrinsicContext subject type =
        hasTypePattern arity context
          (tmPiPattern domainPattern bodyPattern)
          (tmHeadPattern
            (headSortPattern
              (levelMaxPattern domainLevelPattern bodyLevelPattern)))) :
    StructuralTyping intrinsicContext subject type := by
  simp only [claimPattern, encodeTypingClaim, hasTypePattern,
    Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equality
  have decodedSubject :
      decodeTm? towerHeadCodec n
          (tmPiPattern domainPattern bodyPattern) = some subject := by
    rw [← equality.2.2.1]
    exact decodeTm?_encodeTm towerHeadCodec subject
  cases decodedDomain : decodeTm? towerHeadCodec n domainPattern with
  | none =>
      simp [tmPiPattern, decodeTm?, decodedDomain] at decodedSubject
  | some domain =>
      cases decodedBody :
          decodeTm? towerHeadCodec (n + 1) bodyPattern with
      | none =>
          simp [tmPiPattern, decodeTm?, decodedDomain, decodedBody] at decodedSubject
      | some body =>
          have subjectEquality : subject = .pi domain body := by
            simpa [tmPiPattern, decodeTm?, decodedDomain, decodedBody] using
              decodedSubject.symm
          have decodedResult :
              decodeTm? towerHeadCodec n
                  (tmHeadPattern
                    (headSortPattern
                      (levelMaxPattern domainLevelPattern bodyLevelPattern))) =
                some type := by
            rw [← equality.2.2.2]
            exact decodeTm?_encodeTm towerHeadCodec type
          cases decodedDomainLevel : decodeLevel? domainLevelPattern with
          | none =>
              simp [tmHeadPattern, headSortPattern, levelMaxPattern,
                decodeTm?, towerHeadCodec, decodeTowerHead?, decodeLevel?,
                decodedDomainLevel] at decodedResult
          | some domainLevel =>
              cases decodedBodyLevel : decodeLevel? bodyLevelPattern with
              | none =>
                  simp [tmHeadPattern, headSortPattern, levelMaxPattern,
                    decodeTm?, towerHeadCodec, decodeTowerHead?, decodeLevel?,
                    decodedDomainLevel, decodedBodyLevel] at decodedResult
              | some bodyLevel =>
                  have typeEquality :
                      type = .head (.sort (.max domainLevel bodyLevel)) := by
                    simpa [tmHeadPattern, headSortPattern, levelMaxPattern,
                      decodeTm?, towerHeadCodec, decodeTowerHead?,
                      decodeLevel?, decodedDomainLevel, decodedBodyLevel] using
                      decodedResult.symm
                  have subjectPatterns :
                      encodeTm towerHeadCodec domain = domainPattern ∧
                        encodeTm towerHeadCodec body = bodyPattern := by
                    have encodedSubject := equality.2.2.1
                    rw [subjectEquality] at encodedSubject
                    simpa [encodeTm, tmPiPattern] using encodedSubject
                  have levelPatterns :
                      encodeLevel domainLevel = domainLevelPattern ∧
                        encodeLevel bodyLevel = bodyLevelPattern := by
                    have encodedType := equality.2.2.2
                    rw [typeEquality] at encodedType
                    simpa [encodeTm, towerHeadCodec, encodeTowerHead,
                      encodeLevel, tmHeadPattern, headSortPattern,
                      levelMaxPattern] using encodedType
                  have domainTypePattern :
                      encodeTm towerHeadCodec
                          (.head (.sort domainLevel) : Tower.Tm n) =
                        tmHeadPattern
                          (headSortPattern domainLevelPattern) := by
                    simp [encodeTm, towerHeadCodec, encodeTowerHead,
                      tmHeadPattern, headSortPattern, levelPatterns.1]
                  have bodyTypePattern :
                      encodeTm towerHeadCodec
                          (.head (.sort bodyLevel) : Tower.Tm (n + 1)) =
                        tmHeadPattern (headSortPattern bodyLevelPattern) := by
                    simp [encodeTm, towerHeadCodec, encodeTowerHead,
                      tmHeadPattern, headSortPattern, levelPatterns.2]
                  have domainEvidence :
                      StructuralTyping intrinsicContext domain
                        (.head (.sort domainLevel)) :=
                    domainMeaning
                      { arity := n
                        context := intrinsicContext
                        subject := domain
                        type := .head (.sort domainLevel) }
                      (by
                        change
                          encodeTypingClaim towerHeadCodec
                              { arity := n
                                context := intrinsicContext
                                subject := domain
                                type := .head (.sort domainLevel) } =
                            hasTypePattern arity context domainPattern
                              (tmHeadPattern
                                (headSortPattern domainLevelPattern))
                        simp only [encodeTypingClaim, hasTypePattern,
                          Pattern.apply.injEq, List.cons.injEq, and_true,
                          true_and]
                        exact ⟨equality.1, equality.2.1,
                          subjectPatterns.1, domainTypePattern⟩)
                  have successorArity :
                      encodeNat (n + 1) = natSuccPattern arity := by
                    simp only [encodeNat, natSuccPattern,
                      Pattern.apply.injEq, List.cons.injEq, and_true]
                    exact ⟨True.intro, equality.1⟩
                  have extendedContext :
                      encodeCtx towerHeadCodec (.snoc intrinsicContext domain) =
                        ctxSnocPattern context domainPattern := by
                    simp only [encodeCtx, ctxSnocPattern,
                      Pattern.apply.injEq, List.cons.injEq, and_true,
                      true_and]
                    exact ⟨equality.2.1, subjectPatterns.1⟩
                  have bodyEvidence :
                      StructuralTyping (.snoc intrinsicContext domain) body
                        (.head (.sort bodyLevel)) :=
                    bodyMeaning
                      { arity := n + 1
                        context := .snoc intrinsicContext domain
                        subject := body
                        type := .head (.sort bodyLevel) }
                      (by
                        change
                          encodeTypingClaim towerHeadCodec
                              { arity := n + 1
                                context := .snoc intrinsicContext domain
                                subject := body
                                type := .head (.sort bodyLevel) } =
                            hasTypePattern (natSuccPattern arity)
                              (ctxSnocPattern context domainPattern)
                              bodyPattern
                              (tmHeadPattern
                                (headSortPattern bodyLevelPattern))
                        simp only [encodeTypingClaim, hasTypePattern,
                          Pattern.apply.injEq, List.cons.injEq, and_true,
                          true_and]
                        exact ⟨successorArity, extendedContext,
                          subjectPatterns.2, bodyTypePattern⟩)
                  subst subject
                  subst type
                  exact .piForm domainEvidence bodyEvidence

/-! ## Proof-relevant semantic reflection -/

/-- Every structurally valid rule application preserves canonical intrinsic
meaning.  Arbitrary relational instances remain available to the generic
checker, but only their canonical Prime image yields intrinsic evidence. -/
def structuralSemantics :
    PresentationSemantics checked CanonicalMeaning where
  ruleMeaning := by
    intro ruleInstance premises conclusion application premiseEvidence
    have instantiated :=
      instantiateRule?_eq_some_iff_application.mpr application
    rcases ruleInstance with ⟨ruleId, arguments⟩
    cases lookupResult : checked.1.lookupRule? ruleId with
    | none =>
        simp [instantiateRule?, lookupResult] at instantiated
    | some rule =>
        by_cases legacyEquality : rule = legacyGroundRule
        · subst rule
          cases arguments with
          | nil =>
              simp [instantiateRule?, lookupResult, legacyGroundRule,
                argumentsValidAt] at instantiated
          | cons arity remaining =>
              cases remaining with
              | nil =>
                  simp [instantiateRule?, lookupResult, legacyGroundRule,
                    argumentsValidAt] at instantiated
              | cons context remaining =>
                  cases remaining with
                  | cons extra tail =>
                      simp [instantiateRule?, lookupResult, legacyGroundRule,
                        argumentsValidAt] at instantiated
                  | nil =>
                      simp [instantiateRule?, lookupResult, legacyGroundRule,
                        instantiateSchema?, instantiateSchemaAt?,
                        instantiateSchemas?, instantiateSchemasAt?,
                        lookupArgumentAt?, hasTypePattern, tmHeadPattern,
                        encodeTowerHead, encodeLevel, encodeNat,
                        Tower.zero] at instantiated
                      rcases instantiated with ⟨_, rfl, rfl⟩
                      intro claim equality
                      rcases claim with ⟨n, contextValue, subject, type⟩
                      exact legacyConclusion_reflects contextValue subject type
                        arity context equality
        · by_cases sortEquality : rule = sortRule
          · subst rule
            cases arguments with
            | nil =>
                simp [instantiateRule?, lookupResult, sortRule,
                  argumentsValidAt] at instantiated
            | cons arity remaining =>
                cases remaining with
                | nil =>
                    simp [instantiateRule?, lookupResult, sortRule,
                      argumentsValidAt] at instantiated
                | cons context remaining =>
                    cases remaining with
                    | nil =>
                        simp [instantiateRule?, lookupResult, sortRule,
                          argumentsValidAt] at instantiated
                    | cons levelPattern remaining =>
                        cases remaining with
                        | cons extra tail =>
                            simp [instantiateRule?, lookupResult, sortRule,
                              argumentsValidAt] at instantiated
                        | nil =>
                            simp [instantiateRule?, lookupResult, sortRule,
                              instantiateSchema?, instantiateSchemaAt?,
                              instantiateSchemas?, instantiateSchemasAt?,
                              lookupArgumentAt?, hasTypePattern, tmHeadPattern,
                              headSortPattern, levelSuccPattern] at instantiated
                            rcases instantiated with ⟨_, rfl, rfl⟩
                            intro claim equality
                            rcases claim with
                              ⟨n, contextValue, subject, type⟩
                            exact sortConclusion_reflects contextValue subject
                              type arity context levelPattern equality
          · by_cases reflEquality : rule = reflRule
            · subst rule
              cases arguments with
              | nil =>
                  simp [instantiateRule?, lookupResult, reflRule,
                    argumentsValidAt] at instantiated
              | cons arity remaining =>
                  cases remaining with
                  | nil =>
                      simp [instantiateRule?, lookupResult, reflRule,
                        argumentsValidAt] at instantiated
                  | cons context remaining =>
                      cases remaining with
                      | nil =>
                          simp [instantiateRule?, lookupResult, reflRule,
                            argumentsValidAt] at instantiated
                      | cons termPattern remaining =>
                          cases remaining with
                          | nil =>
                              simp [instantiateRule?, lookupResult, reflRule,
                                argumentsValidAt] at instantiated
                          | cons typePattern remaining =>
                              cases remaining with
                              | cons extra tail =>
                                  simp [instantiateRule?, lookupResult,
                                    reflRule, argumentsValidAt] at instantiated
                              | nil =>
                                  simp [instantiateRule?, lookupResult,
                                    reflRule, instantiateSchema?,
                                    instantiateSchemaAt?, instantiateSchemas?,
                                    instantiateSchemasAt?, lookupArgumentAt?,
                                    hasTypePattern, tmReflPattern,
                                    tmIdPattern] at instantiated
                                  rcases instantiated with ⟨_, rfl, rfl⟩
                                  cases premiseEvidence with
                                  | cons premiseMeaning tailEvidence =>
                                      cases tailEvidence
                                      intro claim equality
                                      rcases claim with
                                        ⟨n, contextValue, subject, type⟩
                                      exact reflConclusion_reflects contextValue
                                        subject type arity context termPattern
                                        typePattern premiseMeaning equality
            · by_cases piEquality : rule = piFormRule
              · subst rule
                cases arguments with
                | nil =>
                    simp [instantiateRule?, lookupResult, piFormRule,
                      argumentsValidAt] at instantiated
                | cons arity remaining =>
                    cases remaining with
                    | nil =>
                        simp [instantiateRule?, lookupResult, piFormRule,
                          argumentsValidAt] at instantiated
                    | cons context remaining =>
                        cases remaining with
                        | nil =>
                            simp [instantiateRule?, lookupResult, piFormRule,
                              argumentsValidAt] at instantiated
                        | cons domainPattern remaining =>
                            cases remaining with
                            | nil =>
                                simp [instantiateRule?, lookupResult,
                                  piFormRule, argumentsValidAt] at instantiated
                            | cons bodyPattern remaining =>
                                cases remaining with
                                | nil =>
                                    simp [instantiateRule?, lookupResult,
                                      piFormRule, argumentsValidAt] at instantiated
                                | cons domainLevelPattern remaining =>
                                    cases remaining with
                                    | nil =>
                                        simp [instantiateRule?, lookupResult,
                                          piFormRule, argumentsValidAt] at instantiated
                                    | cons bodyLevelPattern remaining =>
                                        cases remaining with
                                        | cons extra tail =>
                                            simp [instantiateRule?,
                                              lookupResult, piFormRule,
                                              argumentsValidAt] at instantiated
                                        | nil =>
                                            simp [instantiateRule?,
                                              lookupResult, piFormRule,
                                              instantiateSchema?,
                                              instantiateSchemaAt?,
                                              instantiateSchemas?,
                                              instantiateSchemasAt?,
                                              lookupArgumentAt?,
                                              hasTypePattern, tmHeadPattern,
                                              tmPiPattern, headSortPattern,
                                              levelMaxPattern, natSuccPattern,
                                              ctxSnocPattern] at instantiated
                                            rcases instantiated with
                                              ⟨_, rfl, rfl⟩
                                            cases premiseEvidence with
                                            | cons domainMeaning tailEvidence =>
                                                cases tailEvidence with
                                                | cons bodyMeaning tail =>
                                                    cases tail
                                                    intro claim equality
                                                    rcases claim with
                                                      ⟨n, contextValue,
                                                        subject, type⟩
                                                    exact
                                                      piConclusion_reflects
                                                        contextValue subject
                                                        type arity context
                                                        domainPattern
                                                        bodyPattern
                                                        domainLevelPattern
                                                        bodyLevelPattern
                                                        domainMeaning
                                                        bodyMeaning equality
              · have member :
                    rule ∈
                      [legacyGroundRule, sortRule, reflRule, piFormRule] := by
                  change rule ∈ checked.1.rules
                  exact List.mem_of_find?_eq_some lookupResult
                have impossible : False := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with equality | equality | equality | equality
                  · exact legacyEquality equality
                  · exact sortEquality equality
                  · exact reflEquality equality
                  · exact piEquality equality
                exact False.elim impossible

/-! ## Common checked-native waist -/

/-- The declaration-aware native realization is indexed by a formed Prime
world.  Its hot artifact is the intrinsically indexed, proof-relevant
structural judgment; context formation remains available in the goal rather
than being replayed inside every typing derivation. -/
def nativeRealization :
    NativeRealization FormedTypingClaim
      (fun formed => CanonicalMeaning formed.surface) where
  Artifact := fun formed =>
    StructuralTyping formed.claim.context formed.claim.subject
      formed.claim.type
  realize := fun formed evidence => evidence formed.claim rfl

/-- Unlike the generic collapsing canary, this exact-image realization earns
artifact faithfulness: injectivity of the full typing-claim encoder makes a
canonical semantic function completely determined by its native structural
judgment. -/
theorem nativeRealization_artifactFaithful :
    nativeRealization.ArtifactFaithful := by
  intro formed first second artifactsEqual
  funext otherClaim equality
  have claimsEqual : otherClaim = formed.claim :=
    encodeTowerTypingClaim_injective equality
  subst otherClaim
  have proofsEqual : equality = rfl := Subsingleton.elim _ _
  cases proofsEqual
  exact artifactsEqual

/-- Equivalently, after retaining the semantic/native agreement graph, its
artifact projection is injective for every canonical Prime typing claim. -/
theorem nativeRealization_graphProjectionInjective :
    ∀ claim,
      Function.Injective
        (fun point : nativeRealization.Graph claim => point.artifact) :=
  (nativeRealization.artifactFaithful_iff_graphProjectionInjective).mp
    nativeRealization_artifactFaithful

/-- One reusable waist joins the authored presentation, independent
proof-relevant semantics, and Prime's native cumulative typing calculus. -/
def checkedNativeWaist : CheckedNativeWaist checked where
  Meaning := CanonicalMeaning
  semantics := structuralSemantics
  Goal := FormedTypingClaim
  surface := FormedTypingClaim.surface
  native := nativeRealization

/-- The generic waist's raw-program equivalence specialized to a complete
declaration-aware Prime typing claim. -/
theorem checkRaw_iff_checkedNativeProgram
    (formed : FormedTypingClaim) (proof : RawProof) :
    checkRaw checked formed.surface proof = true ↔
      Nonempty (checkedNativeWaist.CheckedRawProgram formed proof) :=
  checkedNativeWaist.checkRaw_iff_nonempty formed proof

/-- Native artifact extraction is exactly intrinsic structural evidence;
mapping it into the common cumulative spine agrees definitionally with
mapping the independently interpreted evidence. -/
@[simp] theorem checkedProgram_artifact_eq_evidence
    {formed : FormedTypingClaim}
    (program : checkedNativeWaist.CheckedProgram formed) :
    program.artifact = program.evidence formed.claim rfl :=
  rfl

@[simp] theorem checkedProgram_artifact_toHasType
    {formed : FormedTypingClaim}
    (program : checkedNativeWaist.CheckedProgram formed) :
    program.artifact.toHasType =
      (program.evidence formed.claim rfl).toHasType :=
  rfl

/-! ## Proof compilation -/

private def ruleInstance (id : String) (arguments : List Pattern) :
    RuleInstance :=
  { ruleId := ⟨id⟩, arguments }

def legacyGroundRaw {n : Nat} (context : Tower.Ctx n) : RawProof :=
  .node
    (ruleInstance "prime-structural-legacy-ground"
      [encodeNat n, encodeCtx towerHeadCodec context]) []

def sortRaw {n : Nat} (context : Tower.Ctx n)
    (level : LevelExpr) : RawProof :=
  .node
    (ruleInstance "prime-structural-sort"
      [encodeNat n, encodeCtx towerHeadCodec context, encodeLevel level]) []

def reflRaw {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) (premise : RawProof) : RawProof :=
  .node
    (ruleInstance "prime-structural-refl"
      [encodeNat n, encodeCtx towerHeadCodec context,
        encodeTm towerHeadCodec term, encodeTm towerHeadCodec type])
    [premise]

def piFormRaw {n : Nat} (context : Tower.Ctx n)
    (domain : Tower.Tm n) (body : Tower.Tm (n + 1))
    (domainLevel bodyLevel : LevelExpr)
    (domainPremise bodyPremise : RawProof) : RawProof :=
  .node
    (ruleInstance "prime-structural-pi-form"
      [encodeNat n, encodeCtx towerHeadCodec context,
        encodeTm towerHeadCodec domain, encodeTm towerHeadCodec body,
        encodeLevel domainLevel, encodeLevel bodyLevel])
    [domainPremise, bodyPremise]

def StructuralTyping.raw :
    {n : Nat} → {context : Tower.Ctx n} →
    {term type : Tower.Tm n} →
    StructuralTyping context term type → RawProof
  | _, context, _, _, .legacyGround _ => legacyGroundRaw context
  | _, context, _, _, .sort _ level => sortRaw context level
  | _, context, _, _, @reflIntro _ _ term type premise =>
      reflRaw context term type premise.raw
  | _, context, _, _,
      @piForm _ _ domain body domainLevel bodyLevel domainPremise bodyPremise =>
      piFormRaw context domain body domainLevel bodyLevel domainPremise.raw
        bodyPremise.raw

private theorem instantiateLegacyPattern
    (arity context : Pattern)
    (arityValid : argumentValidAt 0 arity = true)
    (contextValid : argumentValidAt 0 context = true) :
    instantiateRule? checked
        (ruleInstance "prime-structural-legacy-ground" [arity, context]) =
      some ([],
        hasTypePattern arity context
          (tmHeadPattern (encodeTowerHead .legacyGround))
          (tmHeadPattern (encodeTowerHead (.sort Tower.zero)))) := by
  simp [instantiateRule?, checked, presentation, definition, Data.definition,
    Presentation.lookupRule?, ruleInstance, legacyGroundRule, sortRule,
    reflRule, piFormRule, argumentsValidAt, arityValid, contextValid,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, hasTypePattern, tmHeadPattern, Tower.zero,
    encodeTowerHead, encodeLevel, encodeNat]

private theorem instantiateSortPattern
    (arity context level : Pattern)
    (arityValid : argumentValidAt 0 arity = true)
    (contextValid : argumentValidAt 0 context = true)
    (levelValid : argumentValidAt 0 level = true) :
    instantiateRule? checked
        (ruleInstance "prime-structural-sort" [arity, context, level]) =
      some ([],
        hasTypePattern arity context
          (tmHeadPattern (headSortPattern level))
          (tmHeadPattern (headSortPattern (levelSuccPattern level)))) := by
  simp [instantiateRule?, checked, presentation, definition, Data.definition,
    Presentation.lookupRule?, ruleInstance, legacyGroundRule, sortRule,
    reflRule, piFormRule, argumentsValidAt, arityValid, contextValid,
    levelValid,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, hasTypePattern, tmHeadPattern, headSortPattern,
    levelSuccPattern]

private theorem instantiateReflPattern
    (arity context term type : Pattern)
    (arityValid : argumentValidAt 0 arity = true)
    (contextValid : argumentValidAt 0 context = true)
    (termValid : argumentValidAt 0 term = true)
    (typeValid : argumentValidAt 0 type = true) :
    instantiateRule? checked
        (ruleInstance "prime-structural-refl"
          [arity, context, term, type]) =
      some ([hasTypePattern arity context term type],
        hasTypePattern arity context (tmReflPattern term)
          (tmIdPattern type term term)) := by
  simp [instantiateRule?, checked, presentation, definition, Data.definition,
    Presentation.lookupRule?, ruleInstance, legacyGroundRule, sortRule,
    reflRule, piFormRule, argumentsValidAt, arityValid, contextValid, termValid,
    typeValid, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, hasTypePattern, tmReflPattern, tmIdPattern]

private theorem instantiatePiFormPattern
    (arity context domain body domainLevel bodyLevel : Pattern)
    (arityValid : argumentValidAt 0 arity = true)
    (contextValid : argumentValidAt 0 context = true)
    (domainValid : argumentValidAt 0 domain = true)
    (bodyValid : argumentValidAt 0 body = true)
    (domainLevelValid : argumentValidAt 0 domainLevel = true)
    (bodyLevelValid : argumentValidAt 0 bodyLevel = true) :
    instantiateRule? checked
        (ruleInstance "prime-structural-pi-form"
          [arity, context, domain, body, domainLevel, bodyLevel]) =
      some
        ([hasTypePattern arity context domain
            (tmHeadPattern (headSortPattern domainLevel)),
          hasTypePattern (natSuccPattern arity)
            (ctxSnocPattern context domain) body
            (tmHeadPattern (headSortPattern bodyLevel))],
          hasTypePattern arity context (tmPiPattern domain body)
            (tmHeadPattern
              (headSortPattern (levelMaxPattern domainLevel bodyLevel)))) := by
  simp [instantiateRule?, checked, presentation, definition, Data.definition,
    Presentation.lookupRule?, ruleInstance, legacyGroundRule, sortRule,
    reflRule, piFormRule, argumentsValidAt, arityValid, contextValid,
    domainValid, bodyValid, domainLevelValid, bodyLevelValid,
    RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, hasTypePattern, tmHeadPattern, tmPiPattern,
    headSortPattern, levelMaxPattern, natSuccPattern, ctxSnocPattern]

private theorem legacyGround_accepted {n : Nat} (context : Tower.Ctx n) :
    checkRaw checked
        (claimPattern context (.head .legacyGround)
          (.head (.sort Tower.zero)))
        (legacyGroundRaw context) = true := by
  simp only [legacyGroundRaw, checkRaw]
  rw [instantiateLegacyPattern (encodeNat n)
    (encodeCtx towerHeadCodec context) (encodeNat_argumentValid n)
    (encodeTowerCtx_argumentValid context)]
  simp [claimPattern, encodeTypingClaim, encodeTm, towerHeadCodec,
    encodeTowerHead, Tower.zero, encodeLevel, hasTypePattern,
    tmHeadPattern, checkRawChildren]

private theorem sort_accepted {n : Nat} (context : Tower.Ctx n)
    (level : LevelExpr) :
    checkRaw checked
        (claimPattern context (.head (.sort level))
          (.head (.sort (.succ level))))
        (sortRaw context level) = true := by
  simp only [sortRaw, checkRaw]
  rw [instantiateSortPattern (encodeNat n)
    (encodeCtx towerHeadCodec context) (encodeLevel level)
    (encodeNat_argumentValid n) (encodeTowerCtx_argumentValid context)
    (encodeLevel_argumentValid level)]
  simp [claimPattern, encodeTypingClaim, encodeTm, towerHeadCodec,
    encodeTowerHead, encodeLevel, hasTypePattern, tmHeadPattern,
    headSortPattern, levelSuccPattern, checkRawChildren]

private theorem refl_accepted {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) (premise : RawProof)
    (premiseAccepted :
      checkRaw checked (claimPattern context term type) premise = true) :
    checkRaw checked
        (claimPattern context (.refl term) (.id type term term))
        (reflRaw context term type premise) = true := by
  simp only [reflRaw, checkRaw]
  rw [instantiateReflPattern (encodeNat n)
    (encodeCtx towerHeadCodec context) (encodeTm towerHeadCodec term)
    (encodeTm towerHeadCodec type) (encodeNat_argumentValid n)
    (encodeTowerCtx_argumentValid context) (encodeTowerTm_argumentValid term)
    (encodeTowerTm_argumentValid type)]
  simpa [checkRawChildren, claimPattern, encodeTypingClaim, encodeTm,
    hasTypePattern, tmReflPattern, tmIdPattern] using premiseAccepted

private theorem piForm_accepted {n : Nat} (context : Tower.Ctx n)
    (domain : Tower.Tm n) (body : Tower.Tm (n + 1))
    (domainLevel bodyLevel : LevelExpr)
    (domainPremise bodyPremise : RawProof)
    (domainAccepted :
      checkRaw checked
        (claimPattern context domain (.head (.sort domainLevel)))
        domainPremise = true)
    (bodyAccepted :
      checkRaw checked
        (claimPattern (.snoc context domain) body
          (.head (.sort bodyLevel))) bodyPremise = true) :
    checkRaw checked
        (claimPattern context (.pi domain body)
          (.head (.sort (.max domainLevel bodyLevel))))
        (piFormRaw context domain body domainLevel bodyLevel domainPremise
          bodyPremise) = true := by
  simp only [piFormRaw, checkRaw]
  rw [instantiatePiFormPattern (encodeNat n)
    (encodeCtx towerHeadCodec context) (encodeTm towerHeadCodec domain)
    (encodeTm towerHeadCodec body) (encodeLevel domainLevel)
    (encodeLevel bodyLevel) (encodeNat_argumentValid n)
    (encodeTowerCtx_argumentValid context)
    (encodeTowerTm_argumentValid domain) (encodeTowerTm_argumentValid body)
    (encodeLevel_argumentValid domainLevel)
    (encodeLevel_argumentValid bodyLevel)]
  simpa [checkRawChildren, claimPattern, encodeTypingClaim, encodeTm,
    encodeCtx, encodeNat, towerHeadCodec, encodeTowerHead, encodeLevel,
    hasTypePattern, tmHeadPattern, tmPiPattern, headSortPattern,
    levelMaxPattern, natSuccPattern, ctxSnocPattern] using
    And.intro domainAccepted bodyAccepted

/-- Every intrinsic evidence tree compiles to a proof accepted by the generic
checker, while retaining the exact recursively generated raw proof. -/
theorem StructuralTyping.raw_accepted
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (evidence : StructuralTyping context term type) :
    checkRaw checked (claimPattern context term type) evidence.raw = true := by
  induction evidence with
  | legacyGround context =>
      simpa [StructuralTyping.raw] using legacyGround_accepted context
  | sort context level =>
      simpa [StructuralTyping.raw] using sort_accepted context level
  | @reflIntro n context term type premise inductionHypothesis =>
      simpa [StructuralTyping.raw] using
        refl_accepted context _ _ premise.raw inductionHypothesis
  | @piForm n context domain body domainLevel bodyLevel domainPremise
      bodyPremise domainIH bodyIH =>
      simpa [StructuralTyping.raw] using
        piForm_accepted context domain body domainLevel bodyLevel
          domainPremise.raw bodyPremise.raw domainIH bodyIH

/-- An accepted proof of a canonical claim reconstructs intrinsic evidence.
The noncomputability is only the choice of a typed derivation from the
checker-equivalence theorem; the semantic interpretation itself is recursive
over that derivation. -/
noncomputable def reflectAcceptedRaw
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (proof : RawProof)
    (accepted : checkRaw checked (claimPattern context term type) proof = true) :
    StructuralTyping context term type := by
  let derivation :=
    (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted).choose
  exact structuralSemantics.interpret derivation
    { arity := n, context := context, subject := term, type := type } rfl

/-- On the exact intrinsic image, proof existence in the generic checker is
equivalent to inhabitation of the independently defined structural typing
fibre. -/
theorem exists_accepted_raw_iff_nonempty_structuralTyping
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n} :
    (∃ proof : RawProof,
        checkRaw checked (claimPattern context term type) proof = true) ↔
      Nonempty (StructuralTyping context term type) := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact ⟨reflectAcceptedRaw proof accepted⟩
  · rintro ⟨evidence⟩
    exact ⟨evidence.raw, evidence.raw_accepted⟩

/-! ## Root-only calibration and nodewise canonical ingress -/

/-- The early root-only calibration checks exact-image support for the
conclusion and then delegates the entire tree to the ordinary raw checker.
It remains useful for comparing boundaries, but it is not the final native
ingress because a later rule may hide a noncanonical premise. -/
def checkCanonicalRootRaw (goal : Pattern) (proof : RawProof) : Bool :=
  match decodeCanonical? towerTypingClaimCodec goal with
  | none => false
  | some claim =>
      checkRaw checked (encodeTypingClaim towerHeadCodec claim) proof

@[simp] theorem checkCanonicalRootRaw_encode
    (claim : TypingClaim Tower.Head) (proof : RawProof) :
    checkCanonicalRootRaw (encodeTypingClaim towerHeadCodec claim) proof =
      checkRaw checked (encodeTypingClaim towerHeadCodec claim) proof := by
  have decoded :=
    CanonicalPartialCodec.decodeCanonical?_encode towerTypingClaimCodec claim
  change
    decodeCanonical? towerTypingClaimCodec
        (encodeTypingClaim towerHeadCodec claim) = some claim at decoded
  unfold checkCanonicalRootRaw
  rw [decoded]

/-- Canonical ingress accepts exactly a checker-accepted goal in the image of
the intrinsic typing-claim encoder.  This is wire reflection, independent of
the stronger semantic reflection theorem below. -/
theorem checkCanonicalRootRaw_eq_true_iff
    (goal : Pattern) (proof : RawProof) :
    checkCanonicalRootRaw goal proof = true ↔
      ∃ claim : TypingClaim Tower.Head,
        encodeTypingClaim towerHeadCodec claim = goal ∧
          checkRaw checked (encodeTypingClaim towerHeadCodec claim) proof =
            true := by
  constructor
  · intro accepted
    unfold checkCanonicalRootRaw at accepted
    cases decoded : decodeCanonical? towerTypingClaimCodec goal with
    | none => simp [decoded] at accepted
    | some claim =>
        have canonical :=
          (decodeCanonical?_eq_some_iff towerTypingClaimCodec goal claim).mp
            decoded
        exact ⟨claim, canonical.2, by simpa [decoded] using accepted⟩
  · rintro ⟨claim, rfl, accepted⟩
    simpa using accepted

theorem StructuralTyping.canonicalRootRaw_accepted
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (evidence : StructuralTyping context term type) :
    checkCanonicalRootRaw (claimPattern context term type) evidence.raw = true := by
  simpa [claimPattern] using evidence.raw_accepted

/-- Global exact-image adequacy: a raw Pattern goal has some proof at the
canonical boundary exactly when it is the encoding of an inhabited intrinsic
structural typing fibre. -/
theorem exists_canonicalRootRaw_accepted_iff (goal : Pattern) :
    (∃ proof : RawProof, checkCanonicalRootRaw goal proof = true) ↔
      ∃ claim : TypingClaim Tower.Head,
        encodeTypingClaim towerHeadCodec claim = goal ∧
          Nonempty
            (StructuralTyping claim.context claim.subject claim.type) := by
  constructor
  · rintro ⟨proof, accepted⟩
    rcases (checkCanonicalRootRaw_eq_true_iff goal proof).mp accepted with
      ⟨claim, canonical, checkedProof⟩
    refine ⟨claim, canonical, ?_⟩
    rcases claim with ⟨n, context, subject, type⟩
    exact ⟨reflectAcceptedRaw proof (by
      simpa [claimPattern] using checkedProof)⟩
  · rintro ⟨claim, rfl, ⟨evidence⟩⟩
    rcases claim with ⟨n, context, subject, type⟩
    exact ⟨evidence.raw, by
      simpa [claimPattern] using evidence.canonicalRootRaw_accepted⟩

/-- The actual check-once native ingress validates exact codec support at
every proof node. -/
def checkCanonicalRaw (goal : Pattern) (proof : RawProof) : Bool :=
  Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw
    checked towerTypingClaimCodec goal proof

/-- Every encoded intrinsic claim is supported by the exact codec image. -/
theorem claimPattern_inImage {n : Nat} (context : Tower.Ctx n)
    (subject type : Tower.Tm n) :
    InImage towerTypingClaimCodec (claimPattern context subject type) := by
  exact
    ⟨{ arity := n, context := context, subject := subject, type := type },
      rfl⟩

theorem decodeCanonical_claimPattern {n : Nat}
    (context : Tower.Ctx n) (subject type : Tower.Tm n) :
    decodeCanonical? towerTypingClaimCodec (claimPattern context subject type) =
      some
        { arity := n, context := context, subject := subject, type := type } := by
  change
    decodeCanonical? towerTypingClaimCodec
        (towerTypingClaimCodec.encode
          ({ arity := n, context := context, subject := subject, type := type } :
            TypingClaim Tower.Head)) =
      some
        ({ arity := n, context := context, subject := subject, type := type } :
          TypingClaim Tower.Head)
  exact decodeCanonical?_encode towerTypingClaimCodec _

/-- Intrinsically constructed Prime typing trees pass the stronger nodewise
boundary.  Recursive premises are checked in their own exact fibres rather
than inheriting legitimacy from the conclusion. -/
theorem StructuralTyping.canonicalTreeRaw_accepted
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (evidence : StructuralTyping context term type) :
    checkCanonicalRaw (claimPattern context term type) evidence.raw = true := by
  induction evidence with
  | legacyGround context =>
      simp only [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw,
        StructuralTyping.raw, legacyGroundRaw]
      rw [decodeCanonical_claimPattern]
      rw [instantiateLegacyPattern (encodeNat _)
        (encodeCtx towerHeadCodec context) (encodeNat_argumentValid _)
        (encodeTowerCtx_argumentValid context)]
      simp [claimPattern, encodeTypingClaim, encodeTm, towerHeadCodec,
        encodeTowerHead, Tower.zero, encodeLevel, hasTypePattern,
        tmHeadPattern,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRawChildren]
  | sort context level =>
      simp only [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw,
        StructuralTyping.raw, sortRaw]
      rw [decodeCanonical_claimPattern]
      rw [instantiateSortPattern (encodeNat _)
        (encodeCtx towerHeadCodec context) (encodeLevel level)
        (encodeNat_argumentValid _) (encodeTowerCtx_argumentValid context)
        (encodeLevel_argumentValid level)]
      simp [claimPattern, encodeTypingClaim, encodeTm, towerHeadCodec,
        encodeTowerHead, encodeLevel, hasTypePattern, tmHeadPattern,
        headSortPattern, levelSuccPattern,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRawChildren]
  | @reflIntro n context term type premise inductionHypothesis =>
      simp only [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw,
        StructuralTyping.raw, reflRaw]
      rw [decodeCanonical_claimPattern]
      rw [instantiateReflPattern (encodeNat n)
        (encodeCtx towerHeadCodec context) (encodeTm towerHeadCodec term)
        (encodeTm towerHeadCodec type) (encodeNat_argumentValid n)
        (encodeTowerCtx_argumentValid context)
        (encodeTowerTm_argumentValid term)
        (encodeTowerTm_argumentValid type)]
      simpa [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRawChildren,
        claimPattern, encodeTypingClaim, encodeTm, hasTypePattern,
        tmReflPattern, tmIdPattern] using inductionHypothesis
  | @piForm n context domain body domainLevel bodyLevel domainPremise
      bodyPremise domainIH bodyIH =>
      simp only [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw,
        StructuralTyping.raw, piFormRaw]
      rw [decodeCanonical_claimPattern]
      rw [instantiatePiFormPattern (encodeNat n)
        (encodeCtx towerHeadCodec context) (encodeTm towerHeadCodec domain)
        (encodeTm towerHeadCodec body) (encodeLevel domainLevel)
        (encodeLevel bodyLevel) (encodeNat_argumentValid n)
        (encodeTowerCtx_argumentValid context)
        (encodeTowerTm_argumentValid domain)
        (encodeTowerTm_argumentValid body)
        (encodeLevel_argumentValid domainLevel)
        (encodeLevel_argumentValid bodyLevel)]
      simpa [checkCanonicalRaw,
        Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRawChildren,
        claimPattern, encodeTypingClaim, encodeTm, encodeCtx, encodeNat,
        towerHeadCodec, encodeTowerHead, encodeLevel, hasTypePattern,
        tmHeadPattern, tmPiPattern, headSortPattern, levelMaxPattern,
        natSuccPattern, ctxSnocPattern] using And.intro domainIH bodyIH

/-- The specialized boundary inherits the generic exact-erasure theorem:
acceptance is neither merely Boolean nor merely existence of some proof. -/
theorem checkCanonicalRaw_eq_true_iff_exists_canonicalDerivation_erases
    (goal : Pattern) (proof : RawProof) :
    checkCanonicalRaw goal proof = true ↔
      ∃ derivation :
          Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.CanonicalDerivation
            checked towerTypingClaimCodec goal,
        derivation.erase = proof :=
  Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw_iff_exists_derivation_erases
    goal proof

/-- A nodewise canonical derivation has a positive Prime-native meaning.  The
ordinary semantic interpreter is reused, while exact support constructively
reifies the indexed claim through the decoder. -/
def canonicalDerivationPositiveMeaning {goal : Pattern}
    (derivation :
      Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.CanonicalDerivation
        checked towerTypingClaimCodec goal) :
    PositiveCanonicalMeaning goal :=
  (structuralSemantics.interpret derivation.toDerivation).toPositive
    derivation.support

/-- The full check-once boundary is exactly the inhabitation boundary of
positive native meaning.  This is the theorem consumed by native execution:
after admission, no checker is needed inside the constructed artifact. -/
theorem exists_canonicalTreeRaw_accepted_iff_positiveMeaning
    (goal : Pattern) :
    (∃ proof : RawProof, checkCanonicalRaw goal proof = true) ↔
      Nonempty (PositiveCanonicalMeaning goal) := by
  constructor
  · rintro ⟨proof, accepted⟩
    rcases
        (checkCanonicalRaw_eq_true_iff_exists_canonicalDerivation_erases
          goal proof).mp accepted with
      ⟨derivation, _⟩
    exact ⟨canonicalDerivationPositiveMeaning derivation⟩
  · rintro ⟨⟨claim, rfl, evidence⟩⟩
    rcases claim with ⟨n, context, subject, type⟩
    refine ⟨evidence.raw, ?_⟩
    change
      checkCanonicalRaw (claimPattern context subject type) evidence.raw = true
    exact evidence.canonicalTreeRaw_accepted

/-! ## The exact-image boundary is semantically necessary -/

def malformedZeroContext : Pattern :=
  .apply "prime-ctx-snoc"
    [.apply "prime-ctx-nil" [],
      encodeTm towerHeadCodec
        (Tm.head (Head := Tower.Head) .legacyGround : Tower.Tm 0)]

def malformedLegacyGoal : Pattern :=
  hasTypePattern (encodeNat 0) malformedZeroContext
    (tmHeadPattern (encodeTowerHead .legacyGround))
    (tmHeadPattern (encodeTowerHead (.sort Tower.zero)))

def malformedLegacyProof : RawProof :=
  .node
    (ruleInstance "prime-structural-legacy-ground"
      [encodeNat 0, malformedZeroContext]) []

private theorem malformedZeroContext_argumentValid :
    argumentValidAt 0 malformedZeroContext = true := by
  simp [malformedZeroContext, argumentValidAt, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    encodeTm_ground towerHeadCodec encodeTowerHead_ground,
    encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

/-- Schema replay alone sees ground constructor data and accepts it.  This is
not yet a typed Prime judgment because the context and arity disagree. -/
theorem generic_checker_alone_accepts_malformed_context :
    checkRaw checked malformedLegacyGoal malformedLegacyProof = true := by
  simp only [malformedLegacyProof, checkRaw]
  rw [instantiateLegacyPattern (encodeNat 0) malformedZeroContext
    (encodeNat_argumentValid 0) malformedZeroContext_argumentValid]
  simp [malformedLegacyGoal, checkRawChildren]

theorem malformed_context_has_no_intrinsic_decode :
    decodeTypingClaim? towerHeadCodec malformedLegacyGoal = none := by
  rfl

theorem malformedLegacyGoal_not_inImage :
    ¬ InImage towerTypingClaimCodec malformedLegacyGoal := by
  rintro ⟨claim, equality⟩
  have decoded :
      decodeTypingClaim? towerHeadCodec malformedLegacyGoal = some claim := by
    rw [← equality]
    exact decodeTypingClaim?_encodeTypingClaim towerHeadCodec claim
  rw [malformed_context_has_no_intrinsic_decode] at decoded
  contradiction

/-- The universal fibre deliberately interprets the malformed raw goal: there
is no intrinsic claim to which it must assign evidence. -/
def malformedLegacyGoal_universalMeaning :
    CanonicalMeaning malformedLegacyGoal := by
  intro claim equality
  exact False.elim (malformedLegacyGoal_not_inImage ⟨claim, equality⟩)

/-- The positive native fibre makes the opposite and equally necessary fact
explicit: malformed raw syntax cannot construct intrinsic evidence. -/
theorem malformedLegacyGoal_no_positiveMeaning :
    PositiveCanonicalMeaning malformedLegacyGoal → False :=
  noPositiveFibre_of_not_inImage malformedLegacyGoal_not_inImage

/-- The raw-to-native projection therefore cannot be global.  It is licensed
only after exact-image support and canonical-premise closure are established. -/
theorem no_global_universalToPositive_forPrime :
    ¬ Nonempty
      (CanonicalMeaning malformedLegacyGoal →
        PositiveCanonicalMeaning malformedLegacyGoal) := by
  rintro ⟨projection⟩
  exact malformedLegacyGoal_no_positiveMeaning
    (projection malformedLegacyGoal_universalMeaning)

/-- The composed raw boundary rejects the same proof before it can be treated
as intrinsic typing evidence. -/
theorem canonical_boundary_rejects_malformed_context :
    checkCanonicalRaw malformedLegacyGoal malformedLegacyProof = false := by
  have decodedNone :
      decodeCanonical? towerTypingClaimCodec malformedLegacyGoal = none := by
    cases decoded : decodeCanonical? towerTypingClaimCodec malformedLegacyGoal with
    | none => rfl
    | some claim =>
        exact False.elim
          (malformedLegacyGoal_not_inImage
            ⟨claim,
              (decodeCanonical?_eq_some_iff towerTypingClaimCodec
                malformedLegacyGoal claim).mp decoded |>.2⟩)
  simp [checkCanonicalRaw, malformedLegacyProof,
    Mettapedia.GSLT.LanguageDef.CanonicalInferenceDerivation.checkCanonicalRaw,
    decodedNone]

/-! ## Waist controls -/

def universeZero {n : Nat} : Tower.Tm n :=
  .head (.sort Tower.zero)

def simplePi : Tower.Tm 0 :=
  .pi universeZero universeZero

def simplePiUniverse : Tower.Tm 0 :=
  .head
    (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))

def simplePiEvidence :
    StructuralTyping (.nil : Tower.Ctx 0) simplePi simplePiUniverse := by
  apply StructuralTyping.piForm
  · exact .sort .nil Tower.zero
  · exact .sort (.snoc .nil universeZero) Tower.zero

def formedSimplePiClaim : FormedTypingClaim where
  claim :=
    { arity := 0
      context := .nil
      subject := simplePi
      type := simplePiUniverse }
  contextWellFormed := .nil

theorem simplePi_extendedContext_wellFormed :
    ContextWellFormed Tower.rules
      (.snoc (.nil : Tower.Ctx 0) universeZero) :=
  formedSimplePiClaim.extendContext (.sort .nil Tower.zero)

/-- The first genuinely binder-sensitive Prime rule crosses the same native
waist, retaining both universe-formation children in its raw and intrinsic
evidence trees. -/
theorem simplePi_crosses_checkedNativeWaist :
    Nonempty
      (checkedNativeWaist.CheckedRawProgram formedSimplePiClaim
        simplePiEvidence.raw) := by
  apply (checkRaw_iff_checkedNativeProgram formedSimplePiClaim
    simplePiEvidence.raw).mp
  simpa [formedSimplePiClaim, FormedTypingClaim.surface, claimPattern] using
    simplePiEvidence.raw_accepted

def wrongSimplePiClaim : FormedTypingClaim where
  claim :=
    { arity := 0
      context := .nil
      subject := simplePi
      type := universeZero }
  contextWellFormed := .nil

theorem wrongSimplePiClaim_has_no_structuralEvidence :
    ¬ Nonempty
      (StructuralTyping wrongSimplePiClaim.claim.context
        wrongSimplePiClaim.claim.subject wrongSimplePiClaim.claim.type) := by
  rintro ⟨evidence⟩
  cases evidence

/-- A Π result cannot claim an arbitrary smaller universe: the explicit
`max` in the authored rule is reflected into the intrinsic evidence index. -/
theorem wrongSimplePiClaim_has_no_checkedProof :
    ¬ ∃ proof : RawProof,
      checkRaw checked wrongSimplePiClaim.surface proof = true := by
  intro accepted
  apply wrongSimplePiClaim_has_no_structuralEvidence
  apply exists_accepted_raw_iff_nonempty_structuralTyping.mp
  simpa [wrongSimplePiClaim, FormedTypingClaim.surface, claimPattern] using
    accepted

def structuralLegacyClaim : FormedTypingClaim where
  claim :=
    { arity := 0
      context := .nil
      subject := .head .legacyGround
      type := .head (.sort Tower.zero) }
  contextWellFormed := .nil

/-- The simplest cumulative Prime judgment crosses the common waist with its
exact raw proof tree. -/
theorem structuralLegacyClaim_crosses_checkedNativeWaist :
    Nonempty
      (checkedNativeWaist.CheckedRawProgram structuralLegacyClaim
        (legacyGroundRaw (.nil : Tower.Ctx 0))) := by
  apply (checkRaw_iff_checkedNativeProgram structuralLegacyClaim
    (legacyGroundRaw (.nil : Tower.Ctx 0))).mp
  simpa [structuralLegacyClaim, FormedTypingClaim.surface, claimPattern] using
    legacyGround_accepted (.nil : Tower.Ctx 0)

/-! ### Canonical syntax is not yet a formed native world -/

def missingDeclarationContext : Tower.Ctx 1 :=
  .snoc .nil (.const .anonymous)

theorem missingDeclarationContext_not_wellFormed :
    ¬ ContextWellFormed Tower.rules missingDeclarationContext := by
  intro formed
  cases formed with
  | snoc _ typing _ =>
      exact typing.constantImpossibleWhenMissing rfl

def unformedLegacyClaim : TypingClaim Tower.Head where
  arity := 1
  context := missingDeclarationContext
  subject := .head .legacyGround
  type := .head (.sort Tower.zero)

/-- Structural schema replay accepts the canonical term derivation even when
the supplied telescope is not a legitimate Prime world.  This is deliberate:
raw structural checking and context authority are separate capabilities. -/
theorem unformedLegacyClaim_structurallyAccepted :
    checkRaw checked (encodeTypingClaim towerHeadCodec unformedLegacyClaim)
        (legacyGroundRaw missingDeclarationContext) = true := by
  simpa [unformedLegacyClaim, claimPattern] using
    legacyGround_accepted missingDeclarationContext

/-- No formed native goal has the same complete surface claim.  Therefore the
structurally accepted proof above cannot cross the checked/native waist. -/
theorem unformedLegacyClaim_has_no_nativeGoal :
    ¬ ∃ formed : FormedTypingClaim,
      formed.surface =
        encodeTypingClaim towerHeadCodec unformedLegacyClaim := by
  rintro ⟨⟨claim, wellFormed⟩, surfaceEquality⟩
  have claimEquality : claim = unformedLegacyClaim :=
    encodeTowerTypingClaim_injective surfaceEquality
  subst claim
  exact missingDeclarationContext_not_wellFormed (by
    simpa [unformedLegacyClaim] using wellFormed)

def wrongLegacyClaim : FormedTypingClaim where
  claim :=
    { arity := 0
      context := .nil
      subject := .head .legacyGround
      type := .head .legacyGround }
  contextWellFormed := .nil

theorem wrongLegacyClaim_has_no_structuralEvidence :
    ¬ Nonempty
      (StructuralTyping wrongLegacyClaim.claim.context
        wrongLegacyClaim.claim.subject wrongLegacyClaim.claim.type) := by
  rintro ⟨evidence⟩
  cases evidence

/-- The waist cannot manufacture a native artifact for a canonically encoded
but intrinsically false typing claim. -/
theorem wrongLegacyClaim_has_no_checkedProof :
    ¬ ∃ proof : RawProof,
      checkRaw checked wrongLegacyClaim.surface proof = true := by
  intro accepted
  have intrinsic :
      Nonempty
        (StructuralTyping wrongLegacyClaim.claim.context
          wrongLegacyClaim.claim.subject wrongLegacyClaim.claim.type) := by
    apply exists_accepted_raw_iff_nonempty_structuralTyping.mp
    simpa [wrongLegacyClaim, FormedTypingClaim.surface, claimPattern] using
      accepted
  exact wrongLegacyClaim_has_no_structuralEvidence intrinsic

#print axioms structuralSemantics
#print axioms reflectAcceptedRaw
#print axioms exists_accepted_raw_iff_nonempty_structuralTyping
#print axioms nativeRealization_artifactFaithful
#print axioms nativeRealization_graphProjectionInjective
#print axioms checkedNativeWaist
#print axioms exists_canonicalRootRaw_accepted_iff
#print axioms checkCanonicalRaw_eq_true_iff_exists_canonicalDerivation_erases
#print axioms exists_canonicalTreeRaw_accepted_iff_positiveMeaning
#print axioms canonical_boundary_rejects_malformed_context
#print axioms positiveCanonicalMeaning_iff_universal_of_inImage
#print axioms malformedLegacyGoal_not_inImage
#print axioms no_global_universalToPositive_forPrime
#print axioms FormedTypingClaim.surface_injective
#print axioms simplePi_crosses_checkedNativeWaist
#print axioms simplePi_extendedContext_wellFormed
#print axioms wrongSimplePiClaim_has_no_checkedProof
#print axioms unformedLegacyClaim_structurallyAccepted
#print axioms unformedLegacyClaim_has_no_nativeGoal
#print axioms wrongLegacyClaim_has_no_checkedProof

end Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationAwareStructuralTyping
