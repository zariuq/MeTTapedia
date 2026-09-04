import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredVariableClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
import Mettapedia.GSLT.LanguageDef.ContextualInferenceCanonicalContext

/-!
# Guard-retaining source-indexed modal introduction

Premise-bearing source rewrites require a guarded generalization of modal
introduction.  The exact authored variable row and ordered source-premise
claims occur in both the body and conclusion contexts.  Introduction may
discharge the rely-typing assumptions abstracted by the modal former, but it
does not discharge the source match support or the rewrite guards.

The premise profile is computed from the authored source rows and contains no
relation answer.  This module generates syntax only; its semantic soundness is
proved from independent context satisfaction and one coherent activation
certificate in downstream modules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceCanonicalContext
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax

abbrev PremiseProfile {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeBoundRelationClaim.Profile demand

/-- The exact ordered guard row derived from one selected authored rewrite
occurrence. -/
def authoredGuardClaims {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : List Pattern :=
  SelectedNativeTypeBoundRelationClaim.authoredClaims profile slot

/-- Variable support retained across guarded introduction. -/
def guardedAuthoredVariableClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : List Pattern :=
  SelectedNativeTypeAuthoredVariableClaim.authoredClaims demand slot

/-- Variable support retained across guarded introduction.  Each formula head
retains its exact occurrence and endpoint-support position after grounding. -/
def guardedVariableContext {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : ContextSchema :=
  ContextSchema.prepend (guardedAuthoredVariableClaims demand slot) gamma

/-- The body sees both the authored rewrite guards and the rely typings. -/
def guardedBodyRelationContext {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : ContextSchema :=
  ContextSchema.prepend
    (authoredGuardClaims profile slot ++ authoredRelyTypingClaims demand slot)
    delta

/-- The conclusion retains the authored rewrite guards while discharging only
the rely typings represented by the modal former. -/
def guardedConclusionRelationContext {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : ContextSchema :=
  ContextSchema.prepend (authoredGuardClaims profile slot) delta

/-- Proof-only premises certifying that both ambient context arguments are
canonical context encodings.  Ground checker arguments alone do not provide
this fact. -/
def ambientContextPremises : List Sequent :=
  [ ContextualInferenceCanonicalContext.premise "Gamma"
  , ContextualInferenceCanonicalContext.premise "Delta" ]

/-- Guarded formation is the source-indexed formation schema with explicit
canonicality premises for its two ambient contexts. -/
def formationRuleCore {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : ContextualInference.Rule :=
  { SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore demand slot with
    premises := ambientContextPremises ++
      (SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore
        demand slot).premises }

/-- Close guarded formation over the complete occurrence-derived formal row. -/
def formationRule {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : ContextualInference.Rule :=
  inferMetavariables (formationRuleCore demand slot)

def formationAdmissionCheck {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : Bool :=
  inferredRuleAdmissionCheck (formationRuleCore demand slot)

theorem formationAdmission_of_check {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand)
    (checked : formationAdmissionCheck demand slot = true) :
    InferredRuleAdmission (formationRuleCore demand slot) :=
  inferredRuleAdmission_of_check _ checked

theorem formationRule_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand)
    (admission : InferredRuleAdmission (formationRuleCore demand slot)) :
    RuleSchema.isLocallyValid (lowerRule (formationRule demand slot)) = true :=
  inferMetavariables_locallyValid _ admission

/-- Typed authored right-hand side under one exact source support and guard
context. -/
def introductionBodyPremise {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Sequent :=
  { variableContext := guardedVariableContext demand slot
    relationContext := guardedBodyRelationContext profile slot
    conclusion := ContextualCarrierClaims.typingClaim
      (sourceCarrierAt demand (typingAt demand slot).rewriteType)
      (authoredTarget demand slot)
      (authoredFamilyApplication demand slot (.fvar "result-family")) }

/-- Modal conclusion retaining the same exact authored support and guard row
as the body. -/
def introductionConclusion {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Sequent :=
  { variableContext := guardedVariableContext demand slot
    relationContext := guardedConclusionRelationContext profile slot
    conclusion := ContextualCarrierClaims.typingClaim
      (sourceCarrierAt demand (typingAt demand slot).focusType)
      (authoredFocus demand slot)
      (modalType demand slot (.fvar "result-family")) }

/-- Guard-retaining open introduction for one exact authored occurrence. -/
def introductionRuleCore {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : ContextualInference.Rule where
  id := ⟨ruleName .introduction slot.val⟩
  metavariables := []
  premises :=
    ambientContextPremises ++
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises demand slot ++
        [ authoredResultSortPremise demand slot
        , introductionBodyPremise profile slot ]
  conclusion := introductionConclusion profile slot

/-- Close the guarded rule over exactly the metavariables occurring in its
authored syntax. -/
def introductionRule {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : ContextualInference.Rule :=
  inferMetavariables (introductionRuleCore profile slot)

/-- Finite structural admission for the guarded introduction schema.  This
checks syntax only and grants no semantic relation evidence. -/
def introductionAdmissionCheck {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Bool :=
  inferredRuleAdmissionCheck (introductionRuleCore profile slot)

theorem introductionAdmission_of_check {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (checked : introductionAdmissionCheck profile slot = true) :
    InferredRuleAdmission (introductionRuleCore profile slot) :=
  inferredRuleAdmission_of_check _ checked

theorem introductionRule_locallyValid {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (admission : InferredRuleAdmission
      (introductionRuleCore profile slot)) :
    RuleSchema.isLocallyValid
      (lowerRule (introductionRule profile slot)) = true :=
  inferMetavariables_locallyValid _ admission

/-! ## Compositional source admission -/

/-- Structural source evidence for every argument retained by the decoded
authored guard row.  This classifies syntax only; it does not assert that any
relation query succeeds. -/
structure GuardArgumentAdmission {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Prop where
  argument : ∀ premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length,
    ∀ pattern ∈
      (SelectedNativeTypeBoundRelationClaim.sourceView
        profile slot premise).arguments,
      TopLevelPatternAdmission pattern

/-- One source-derived guard claim is an admitted open schema whenever all of
its literal arguments are admitted at the authored top level. -/
theorem authoredGuardClaim_schemaAdmission
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    (premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length)
    (guard : GuardArgumentAdmission profile slot) :
    SchemaPatternAdmission
      (SelectedNativeTypeBoundRelationClaim.authoredClaim
        profile slot premise) := by
  unfold SelectedNativeTypeBoundRelationClaim.authoredClaim
    SelectedNativeTypeBoundRelationClaim.claim
  apply SchemaPatternAdmission.apply
  intro pattern membership
  unfold SelectedNativeTypeBoundRelationClaim.authoredArguments at membership
  obtain ⟨sourcePattern, sourceMembership, rfl⟩ := List.mem_map.mp membership
  exact SchemaPatternAdmission.authored demand slot sourcePattern
    (guard.argument premise sourcePattern sourceMembership)

/-- The complete ordered guard row is structurally admitted from one uniform
source-argument certificate. -/
theorem authoredGuardClaims_schemaAdmission
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    (guard : GuardArgumentAdmission profile slot) :
    ∀ formula ∈ authoredGuardClaims profile slot,
      SchemaPatternAdmission formula := by
  intro formula membership
  unfold authoredGuardClaims
    SelectedNativeTypeBoundRelationClaim.authoredClaims at membership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp membership
  exact authoredGuardClaim_schemaAdmission profile slot premise guard

/-- A canonical-context premise is itself an admitted open schema. -/
theorem ambientContextPremise_schemaAdmission
    (name : String) (nonempty : name ≠ "") :
    SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.premise name)) := by
  have emptyAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext .empty) := by
    apply SchemaPatternAdmission.apply
    simp
  have claimAdmission : SchemaPatternAdmission
      (ContextualInferenceCanonicalContext.claim (.fvar name)) := by
    apply SchemaPatternAdmission.apply
    intro pattern membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    subst pattern
    exact SchemaPatternAdmission.fvar name nonempty
  exact SchemaPatternAdmission.lowerSequent _ emptyAdmission emptyAdmission
    claimAdmission

/-- Adding the two canonical-context premises to root-like formation preserves
generator-family admission. -/
theorem formationRuleCore_admission_of_bindingsAt_eq_nil
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = []) :
    InferredRuleAdmission (formationRuleCore demand slot) := by
  refine
    { identifierNonempty := ?_
      occurrenceNamesNonempty := ?_
      occurrenceNamesNodup := ?_
      patternsWellScoped := ?_
      patternsHaveNoCollectionRest := ?_
      patternsHaveCanonicalBinders := ?_ }
  all_goals
    simp [formationRuleCore, ambientContextPremises,
      ContextualInferenceCanonicalContext.premise,
      ContextualInferenceCanonicalContext.sequent,
      ContextualInferenceCanonicalContext.claim,
      ContextualInferenceCanonicalContext.contextCodeTerm,
      SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
      authoredResultSortPremise, authoredRelyValues,
      authoredRelyVariableClaims, authoredRelyTypingClaims,
      authoredFamilyApplication,
      SelectedNativeTypeContextualCalculus.modalType,
      SelectedNativeTypeContextualCalculus.relyTypes,
      SelectedNativeTypeContextualCalculus.sortCode,
      emptyBindings, ruleName, RuleKind.tag,
      auxiliaryLabel, AuxiliaryKind.tag,
      ContextualFamilyApplication.applyFamily,
      ContextualCarrierClaims.typingClaim,
      ContextualCarrierClaims.claimLabel,
      ContextualCarrierClaims.ClaimKind.tag,
      ContextualInference.lowerRule, ContextualInference.lowerSequent,
      ContextualInference.encodeContext,
      ContextualInference.emptyContextTerm,
      gamma, delta,
      CarrierUniverseSignature.label, CarrierUniverseSignature.Code.tag,
      RuleSchema.occurrences, RuleSchema.patterns,
      patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt,
      patternHasNoCollectionRest,
      patternsHaveNoCollectionRest,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList] <;>
    decide

/-- Root-like guarded introduction is structurally admissible from the same
authored endpoint evidence as unguarded introduction plus one source argument
certificate for the exact ordered guard row. -/
theorem introductionRuleCore_admission_of_source
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = [])
    (sourceAdmission : IntroductionSourceAdmission demand slot)
    (guardAdmission : GuardArgumentAdmission profile slot) :
    InferredRuleAdmission (introductionRuleCore profile slot) := by
  have gammaAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext gamma) := by
    simpa [gamma, ContextualInference.encodeContext] using
      SchemaPatternAdmission.fvar "Gamma" (by decide)
  have deltaAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext delta) := by
    simpa [delta, ContextualInference.encodeContext] using
      SchemaPatternAdmission.fvar "Delta" (by decide)
  have contextGammaAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.premise "Gamma")) :=
    ambientContextPremise_schemaAdmission "Gamma" (by decide)
  have contextDeltaAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.premise "Delta")) :=
    ambientContextPremise_schemaAdmission "Delta" (by decide)
  have resultFamilyAdmission :
      SchemaPatternAdmission (.fvar "result-family") :=
    SchemaPatternAdmission.fvar _ (by decide)
  have sortAdmission (carrier : String)
      (code : CarrierUniverseSignature.Code) :
      SchemaPatternAdmission (sortCode carrier code) := by
    apply SchemaPatternAdmission.apply
    simp
  have modalAdmission :
      SchemaPatternAdmission
        (modalType demand slot (.fvar "result-family")) := by
    have applied := SchemaPatternAdmission.apply
      (SelectedModalNaming.label slot.val) [.fvar "result-family"]
      (by
        intro pattern membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst pattern
        exact resultFamilyAdmission)
    simpa [modalType, relyTypes, emptyBindings] using applied
  have familyAdmission :
      SchemaPatternAdmission
        (authoredFamilyApplication demand slot (.fvar "result-family")) := by
    have applied := SchemaPatternAdmission.apply
      (auxiliaryLabel .familyApplication slot.val) [.fvar "result-family"]
      (by
        intro pattern membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        subst pattern
        exact resultFamilyAdmission)
    simpa [authoredFamilyApplication, authoredRelyValues, emptyBindings,
      ContextualFamilyApplication.applyFamily] using applied
  have resultSortVariableContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (authoredResultSortPremise demand slot).variableContext) := by
    simpa [authoredResultSortPremise, authoredRelyVariableClaims,
      emptyBindings] using gammaAdmission
  have resultSortRelationContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (authoredResultSortPremise demand slot).relationContext) := by
    simpa [authoredResultSortPremise, authoredRelyTypingClaims,
      emptyBindings] using deltaAdmission
  have resultSortConclusionAdmission : SchemaPatternAdmission
      (authoredResultSortPremise demand slot).conclusion := by
    apply SchemaPatternAdmission.typingClaim
    · exact familyAdmission
    · exact sortAdmission _ _
  have resultSortAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (authoredResultSortPremise demand slot)) :=
    SchemaPatternAdmission.lowerSequent _
      resultSortVariableContextAdmission resultSortRelationContextAdmission
      resultSortConclusionAdmission
  have authoredTargetAdmission : SchemaPatternAdmission
      (authoredTarget demand slot) := by
    simpa [authoredTarget] using SchemaPatternAdmission.authored demand slot
      (typingAt demand slot).site.rewrite.right sourceAdmission.target
  have authoredFocusAdmission : SchemaPatternAdmission
      (authoredFocus demand slot) := by
    simpa [authoredFocus] using SchemaPatternAdmission.authored demand slot
      (typingAt demand slot).site.focus sourceAdmission.focus
  have variableClaimsAdmission :
      ∀ formula ∈ guardedAuthoredVariableClaims demand slot,
        SchemaPatternAdmission formula := by
    intro formula membership
    rw [guardedAuthoredVariableClaims,
      SelectedNativeTypeAuthoredVariableClaim.authoredClaims,
      List.mem_ofFn] at membership
    obtain ⟨binding, rfl⟩ := membership
    apply SchemaPatternAdmission.apply
    intro pattern patternMembership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at patternMembership
    subst pattern
    exact SchemaPatternAdmission.fvar _
      (renameVariable_ne_empty demand slot
        (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
          demand slot binding).1)
  have guardClaimsAdmission :
      ∀ formula ∈ authoredGuardClaims profile slot,
        SchemaPatternAdmission formula :=
    authoredGuardClaims_schemaAdmission profile slot guardAdmission
  have guardedVariableContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (guardedVariableContext demand slot)) := by
    simpa [guardedVariableContext, gamma] using
      SchemaPatternAdmission.encodeContext_prepend
        (guardedAuthoredVariableClaims demand slot) "Gamma" (by decide)
        variableClaimsAdmission
  have guardedBodyRelationContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (guardedBodyRelationContext profile slot)) := by
    have admitted := SchemaPatternAdmission.encodeContext_prepend
      (authoredGuardClaims profile slot) "Delta" (by decide)
      guardClaimsAdmission
    simpa [guardedBodyRelationContext, authoredRelyTypingClaims,
      emptyBindings, delta] using admitted
  have guardedConclusionRelationContextAdmission : SchemaPatternAdmission
      (ContextualInference.encodeContext
        (guardedConclusionRelationContext profile slot)) := by
    simpa [guardedConclusionRelationContext, delta] using
      SchemaPatternAdmission.encodeContext_prepend
        (authoredGuardClaims profile slot) "Delta" (by decide)
        guardClaimsAdmission
  have bodyConclusionAdmission : SchemaPatternAdmission
      (introductionBodyPremise profile slot).conclusion :=
    SchemaPatternAdmission.typingClaim _ _ _ authoredTargetAdmission
      familyAdmission
  have bodyAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (introductionBodyPremise profile slot)) :=
    SchemaPatternAdmission.lowerSequent _ guardedVariableContextAdmission
      guardedBodyRelationContextAdmission bodyConclusionAdmission
  have finalConclusionAdmission : SchemaPatternAdmission
      (introductionConclusion profile slot).conclusion :=
    SchemaPatternAdmission.typingClaim _ _ _ authoredFocusAdmission
      modalAdmission
  have finalAdmission : SchemaPatternAdmission
      (ContextualInference.lowerSequent
        (introductionConclusion profile slot)) :=
    SchemaPatternAdmission.lowerSequent _ guardedVariableContextAdmission
      guardedConclusionRelationContextAdmission finalConclusionAdmission
  apply inferredRuleAdmission_of_schemaPatterns
  · simp [introductionRuleCore, ruleName, RuleKind.tag]
  · intro pattern membership
    have normalized : pattern ∈
        [ ContextualInference.lowerSequent
            (ContextualInferenceCanonicalContext.premise "Gamma")
        , ContextualInference.lowerSequent
            (ContextualInferenceCanonicalContext.premise "Delta")
        , ContextualInference.lowerSequent
            (authoredResultSortPremise demand slot)
        , ContextualInference.lowerSequent
            (introductionBodyPremise profile slot)
        , ContextualInference.lowerSequent
            (introductionConclusion profile slot) ] := by
      simpa [RuleSchema.patterns, ContextualInference.lowerRule,
        introductionRuleCore, ambientContextPremises,
        SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
        emptyBindings] using membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at normalized
    rcases normalized with rfl | rfl | rfl | rfl | rfl
    · exact contextGammaAdmission
    · exact contextDeltaAdmission
    · exact resultSortAdmission
    · exact bodyAdmission
    · exact finalAdmission

/-- Formation remains the existing universe-indexed family; only
introduction changes its contextual support discipline. -/
def rulesAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (slot : Occurrence demand) : List RuleSchema :=
  [ lowerRule (formationRule demand slot)
  , lowerRule (introductionRule profile slot) ]

/-- Structural admission required at each selected occurrence. -/
structure OccurrenceAdmission {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Prop where
  formation : InferredRuleAdmission
    (formationRuleCore demand slot)
  introduction : InferredRuleAdmission (introductionRuleCore profile slot)

/-- Uniform guarded occurrence admission for the binder-free root fragment. -/
theorem occurrenceAdmission_of_root_source
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    (emptyBindings : bindingsAt demand slot = [])
    (sourceAdmission : IntroductionSourceAdmission demand slot)
    (guardAdmission : GuardArgumentAdmission profile slot) :
    OccurrenceAdmission demand profile slot :=
  { formation := formationRuleCore_admission_of_bindingsAt_eq_nil
      demand slot emptyBindings
    introduction := introductionRuleCore_admission_of_source
      demand profile slot emptyBindings sourceAdmission guardAdmission }

def occurrenceAdmissionCheck {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (slot : Occurrence demand) : Bool :=
  inferredRuleAdmissionCheck
      (formationRuleCore demand slot) &&
    introductionAdmissionCheck profile slot

theorem occurrenceAdmission_of_check {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (checked : occurrenceAdmissionCheck demand profile slot = true) :
    OccurrenceAdmission demand profile slot := by
  simp only [occurrenceAdmissionCheck, Bool.and_eq_true] at checked
  exact
    { formation := inferredRuleAdmission_of_check _ checked.1
      introduction := introductionAdmission_of_check profile slot checked.2 }

theorem rulesAt_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (slot : Occurrence demand)
    (admission : OccurrenceAdmission demand profile slot) :
    (rulesAt demand profile slot).all RuleSchema.isLocallyValid = true := by
  simp [rulesAt,
    formationRule_locallyValid demand slot admission.formation,
    introductionRule_locallyValid profile slot admission.introduction]

def profiledRules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) : List RuleSchema :=
  (List.ofFn fun slot : Occurrence demand =>
    rulesAt demand profile slot).flatten

theorem profiledRules_locallyValid {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand)
    (admission : ∀ slot, OccurrenceAdmission demand profile slot) :
    (profiledRules demand profile).all RuleSchema.isLocallyValid = true := by
  rw [profiledRules, List.all_flatten]
  apply List.all_eq_true.mpr
  intro row membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp membership
  exact rulesAt_locallyValid demand profile slot (admission slot)

/-- Complete occurrence-specific proof suffix for the guarded source-indexed
fragment.  Canonical-context constructors are already supplied by the shared
contextual-claim signature; premise constructors are generated from the same
source profile used by these rules. -/
def profileExtension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (profile : PremiseProfile demand) :
    CalculusLanguageExtension where
  newTerms := familyApplicationTerms demand ++
    SelectedNativeTypeAuthoredVariableClaim.terms demand ++
      SelectedNativeTypeBoundRelationClaim.terms profile
  newRules := profiledRules demand profile

/-! ## Structural laws -/

theorem body_variableContext_exact {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) :
    (introductionBodyPremise profile slot).variableContext =
      guardedVariableContext demand slot :=
  rfl

theorem formation_retains_context_certificates
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (formationRuleCore demand slot).premises.take 2 =
      ambientContextPremises := by
  simp [formationRuleCore, ambientContextPremises]

theorem introduction_retains_context_certificates
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand) :
    (introductionRuleCore profile slot).premises.take 2 =
      ambientContextPremises := by
  simp [introductionRuleCore, ambientContextPremises]

theorem conclusion_variableContext_exact {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) :
    (introductionConclusion profile slot).variableContext =
      guardedVariableContext demand slot :=
  rfl

theorem conclusion_retains_guards {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) :
    (introductionConclusion profile slot).relationContext =
      ContextSchema.prepend
        (SelectedNativeTypeBoundRelationClaim.authoredClaims profile slot)
        delta :=
  rfl

theorem body_retains_guards {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : PremiseProfile demand)
    (slot : Occurrence demand) :
    (introductionBodyPremise profile slot).relationContext =
      ContextSchema.prepend
        (SelectedNativeTypeBoundRelationClaim.authoredClaims profile slot ++
          authoredRelyTypingClaims demand slot)
        delta :=
  rfl

@[simp] theorem profileExtension_rewrites_empty
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) :
    (profileExtension demand profile).newRewrites = [] :=
  rfl

@[simp] theorem profileExtension_equations_empty
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) :
    (profileExtension demand profile).newEquations = [] :=
  rfl

/-- The guarded suffix contains exactly the occurrence-indexed formation and
introduction rows.  Canonical-context rules live in the shared contextual
signature and are therefore emitted once. -/
@[simp] theorem profileExtension_rules
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (profile : PremiseProfile demand) :
    (profileExtension demand profile).newRules =
      profiledRules demand profile :=
  rfl

#print axioms introductionAdmission_of_check
#print axioms formationAdmission_of_check
#print axioms formationRule_locallyValid
#print axioms introductionRule_locallyValid
#print axioms occurrenceAdmission_of_check
#print axioms profiledRules_locallyValid
#print axioms body_variableContext_exact
#print axioms conclusion_variableContext_exact
#print axioms conclusion_retains_guards
#print axioms body_retains_guards
#print axioms formation_retains_context_certificates
#print axioms introduction_retains_context_certificates
#print axioms profileExtension_rewrites_empty
#print axioms profileExtension_rules

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
