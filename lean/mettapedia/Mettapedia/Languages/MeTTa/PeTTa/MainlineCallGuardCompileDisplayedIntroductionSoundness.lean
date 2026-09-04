import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
import Mettapedia.GSLT.LanguageDef.ContextualInferenceInstantiation

/-!
# Grounded guarded-introduction soundness for the PeTTa call guard

The generated guarded introduction schema is open in two ambient contexts
and in the result family.  This module first exposes its exact grounded
structured sequents.  The variable and guard prefixes are computed from one
checker endpoint environment; the ambient tails are decoded canonical
contexts; and the body target and conclusion focus are reconstructed from the
authored cold occurrence.

The construction is syntactic.  Relation truth, carrier typing, and modal
membership enter only in the subsequent displayed-semantic proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedIntroductionSoundness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceInstantiation
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ContextualFamilyApplication
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel

abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

abbrev IntroductionFormals (slot : Occurrence) :=
  (introductionRule guardProfile slot).metavariables

/-- Ambient-context and result-family parameters are genuine occurrences in
the generated guarded-introduction syntax, hence are retained in its inferred
formal row. -/
theorem introductionFormals_contains_publicParameters (slot : Occurrence) :
    ("Gamma", 0) ∈ IntroductionFormals slot ∧
      ("Delta", 0) ∈ IntroductionFormals slot ∧
      ("result-family", 0) ∈ IntroductionFormals slot := by
  constructor
  · simp [IntroductionFormals,
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule,
      inferMetavariables,
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore,
      ambientContextPremises,
      ContextualInferenceCanonicalContext.premise,
      ContextualInferenceCanonicalContext.sequent,
      ContextualInferenceCanonicalContext.claim,
      ContextualInference.lowerRule, ContextualInference.lowerSequent,
      ContextualInference.encodeContext, RuleSchema.occurrences,
      RuleSchema.patterns, patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt]
  · constructor
    · simp [IntroductionFormals,
        SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule,
        inferMetavariables,
        SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore,
        ambientContextPremises,
        ContextualInferenceCanonicalContext.premise,
        ContextualInferenceCanonicalContext.sequent,
        ContextualInferenceCanonicalContext.claim,
        ContextualInference.lowerRule, ContextualInference.lowerSequent,
        ContextualInference.encodeContext, RuleSchema.occurrences,
        RuleSchema.patterns, patternMetavariableOccurrencesAt,
        patternsMetavariableOccurrencesAt]
    · have formalInConclusion : ("result-family", 0) ∈
          patternMetavariableOccurrencesAt 0
            (ContextualInference.lowerSequent
              (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
                guardProfile slot)) := by
        unfold ContextualInference.lowerSequent
          SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
        simp [patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt, modalType,
          SelectedNativeTypeContextualCalculus.relyTypes,
          selected_bindings_eq_nil,
          ContextualCarrierClaims.typingClaim]
      change ("result-family", 0) ∈
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).metavariables
      unfold SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
      change ("result-family", 0) ∈
        (RuleSchema.occurrences
          (ContextualInference.lowerRule
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore
              guardProfile slot))).eraseDups
      rw [List.mem_eraseDups]
      unfold RuleSchema.occurrences RuleSchema.patterns
      simp only [ContextualInference.lowerRule]
      rw [patternsMetavariableOccurrencesAt_append]
      apply List.mem_append_right
      change ("result-family", 0) ∈
        patternsMetavariableOccurrencesAt 0
          [ContextualInference.lowerSequent
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
              guardProfile slot)]
      simpa [patternsMetavariableOccurrencesAt] using formalInConclusion

/-- The three public parameters of a guarded introduction, read from the
checker's actual ordered argument vector.  Exact lookup equations are stored
with the values so every subsequent instantiation uses the same rule
application. -/
structure IntroductionPublicArguments (slot : Occurrence)
    (arguments : List Pattern) where
  gammaWire : Pattern
  deltaWire : Pattern
  resultFamily : Pattern
  gammaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
    "Gamma" 0 = some gammaWire
  deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
    "Delta" 0 = some deltaWire
  familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
    "result-family" 0 = some resultFamily

/-- A checker-valid argument vector supplies every public parameter occurring
in the generated guarded-introduction schema. -/
theorem introductionPublicArguments_of_valid (slot : Occurrence)
    {arguments : List Pattern}
    (valid : argumentsValidAt (IntroductionFormals slot) arguments = true) :
    Nonempty (IntroductionPublicArguments slot arguments) := by
  obtain ⟨bindings, bindingsExact⟩ :=
    bindingsOfArguments?_exists_of_argumentsValidAt valid
  have namesNodup :
      ((IntroductionFormals slot).map Prod.fst).Nodup :=
    generated_introductionFormalNames_nodup slot
  have publicMembers := introductionFormals_contains_publicParameters slot
  have gammaSome : (Bindings.lookup bindings "Gamma").isSome :=
    bindingsOfArguments?_lookup_isSome namesNodup bindingsExact
      ("Gamma", 0) publicMembers.1
  have deltaSome : (Bindings.lookup bindings "Delta").isSome :=
    bindingsOfArguments?_lookup_isSome namesNodup bindingsExact
      ("Delta", 0) publicMembers.2.1
  have familySome : (Bindings.lookup bindings "result-family").isSome :=
    bindingsOfArguments?_lookup_isSome namesNodup bindingsExact
      ("result-family", 0) publicMembers.2.2
  obtain ⟨gammaWire, gammaLookup⟩ := Option.isSome_iff_exists.mp gammaSome
  obtain ⟨deltaWire, deltaLookup⟩ := Option.isSome_iff_exists.mp deltaSome
  obtain ⟨resultFamily, familyLookup⟩ :=
    Option.isSome_iff_exists.mp familySome
  have gammaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Gamma" 0 = some gammaWire := by
    rw [← bindingsOfArguments?_lookup_eq_lookupArgumentAt? namesNodup
      bindingsExact ("Gamma", 0) publicMembers.1]
    exact gammaLookup
  have deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Delta" 0 = some deltaWire := by
    rw [← bindingsOfArguments?_lookup_eq_lookupArgumentAt? namesNodup
      bindingsExact ("Delta", 0) publicMembers.2.1]
    exact deltaLookup
  have familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily := by
    rw [← bindingsOfArguments?_lookup_eq_lookupArgumentAt? namesNodup
      bindingsExact ("result-family", 0) publicMembers.2.2]
    exact familyLookup
  exact ⟨⟨gammaWire, deltaWire, resultFamily,
    gammaExact, deltaExact, familyExact⟩⟩

/-- The selected call-guard root has exactly four guarded-introduction
premises: two canonical ambient-context certificates, the result-sort
premise, and the typed authored body. -/
theorem introductionRule_premises_exact (slot : Occurrence) :
    (ContextualInference.lowerRule
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
        guardProfile slot)).premises =
      [ ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Gamma")
      , ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Delta")
      , ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot)
      , ContextualInference.lowerSequent
          (introductionBodyPremise guardProfile slot) ] := by
  have relyPremisesEmpty :
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot = [] := by
    simp [SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
      selected_bindings_eq_nil]
  simp [ContextualInference.lowerRule,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule,
    inferMetavariables,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore,
    ambientContextPremises, relyPremisesEmpty]

/-- The ordinary checker conclusion is exactly the lowering of the authored
guard-retaining modal conclusion. -/
theorem introductionRule_conclusion_exact (slot : Occurrence) :
    (ContextualInference.lowerRule
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
        guardProfile slot)).conclusion =
      ContextualInference.lowerSequent
        (introductionConclusion guardProfile slot) := rfl

/-- Instantiating an ambient-context certificate through any checker formal
row containing the named context coordinate yields the canonical certificate
for the exact argument wire. -/
theorem instantiate_canonicalContextPremiseAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    (name : String) (wire : Pattern)
    (exact : lookupArgumentAt? formals arguments
      name 0 = some wire) :
    instantiateSchemaAt? formals arguments 0
        (ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise name)) =
      some (ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.sequent wire)) := by
  apply instantiateSchemaAt?_lowerSequent_of_sequent
  simp [instantiateSequentAt?, instantiateContextAt?,
    ContextualInferenceCanonicalContext.premise,
    ContextualInferenceCanonicalContext.sequent,
    ContextualInferenceCanonicalContext.claim,
    instantiateSchemaAt?, instantiateSchemasAt?, exact]

/-- The introduction-specific specialization of the generic ambient-context
instantiation theorem. -/
theorem instantiate_canonicalContextPremise
    (slot : Occurrence) {arguments : List Pattern}
    (name : String) (wire : Pattern)
    (exact : lookupArgumentAt? (IntroductionFormals slot) arguments
      name 0 = some wire) :
    instantiateSchemaAt? (IntroductionFormals slot) arguments 0
        (ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise name)) =
      some (ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.sequent wire)) :=
  instantiate_canonicalContextPremiseAt name wire exact

/-- Exact grounded body sequent of one generated guarded introduction. -/
def groundedBodySequent (slot : Occurrence) (bindings : Bindings)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern) :
    Sequent where
  variableContext := ContextSchema.prepend
    (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
      demand slot bindings) gammaContext
  relationContext := ContextSchema.prepend
    (SelectedNativeTypeBoundRelationClaim.groundedClaims
      guardProfile slot bindings) deltaContext
  conclusion := ContextualCarrierClaims.typingClaim
    (sourceCarrierAt demand (typingAt demand slot).rewriteType)
    (applyBindingsForRule language
      (typingAt demand slot).site.rewrite bindings)
    (authoredFamilyApplication demand slot resultFamily)

/-- Exact grounded conclusion sequent of the same introduction instance. -/
def groundedConclusionSequent (slot : Occurrence) (bindings : Bindings)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern) :
    Sequent where
  variableContext := ContextSchema.prepend
    (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
      demand slot bindings) gammaContext
  relationContext := ContextSchema.prepend
    (SelectedNativeTypeBoundRelationClaim.groundedClaims
      guardProfile slot bindings) deltaContext
  conclusion := ContextualCarrierClaims.typingClaim
    (sourceCarrierAt demand (typingAt demand slot).focusType)
    (applyBindings bindings (typingAt demand slot).site.focus)
    (modalType demand slot resultFamily)

/-- One coherent endpoint instantiation grounds the complete retained
variable context without changing its ambient tail. -/
theorem instantiate_guardedVariableContext
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (gammaContext : ContextSchema)
    (gammaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Gamma" 0 = some (encodeContext gammaContext)) :
    instantiateContextAt? (IntroductionFormals slot) arguments 0
        (guardedVariableContext demand slot) =
      some (ContextSchema.prepend
        (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
          demand slot instantiation.endpoint.bindings)
        gammaContext) := by
  apply instantiateContextAt?_prepend
  · simpa only [instantiateSchemas?, guardedAuthoredVariableClaims,
      SelectedNativeTypeAuthoredVariableClaim.groundedClaims] using
      MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredVariableClaims
        instantiation
        (generated_introductionFormalNames_nodup slot)
        (generated_introductionEndpoint_declared slot)
  · simp [instantiateContextAt?, gamma, gammaExact]

/-- The selected cold roots have no rely telescope, so the body relation
context grounds to exactly the ordered authored guard row and the decoded
ambient relation tail. -/
theorem instantiate_guardedBodyRelationContext
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (deltaContext : ContextSchema)
    (deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext)) :
    instantiateContextAt? (IntroductionFormals slot) arguments 0
        (guardedBodyRelationContext guardProfile slot) =
      some (ContextSchema.prepend
        (SelectedNativeTypeBoundRelationClaim.groundedClaims
          guardProfile slot instantiation.endpoint.bindings)
        deltaContext) := by
  rw [show guardedBodyRelationContext guardProfile slot =
      ContextSchema.prepend (authoredGuardClaims guardProfile slot)
        (.hole "Delta") by
    simp [guardedBodyRelationContext, authoredRelyTypingClaims,
      selected_bindings_eq_nil, delta]]
  apply instantiateContextAt?_prepend
  · simpa only [instantiateSchemas?, authoredGuardClaims,
      SelectedNativeTypeBoundRelationClaim.groundedClaims] using
      MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredGuardClaimsFor
        instantiation guardProfile
        (generated_introductionFormalNames_nodup slot)
        (generated_introductionEndpoint_declared slot)
  · simp [instantiateContextAt?, deltaExact]

/-- The conclusion retains precisely the same grounded guard row. -/
theorem instantiate_guardedConclusionRelationContext
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (deltaContext : ContextSchema)
    (deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext)) :
    instantiateContextAt? (IntroductionFormals slot) arguments 0
        (guardedConclusionRelationContext guardProfile slot) =
      some (ContextSchema.prepend
        (SelectedNativeTypeBoundRelationClaim.groundedClaims
          guardProfile slot instantiation.endpoint.bindings)
        deltaContext) := by
  apply instantiateContextAt?_prepend
  · simpa only [instantiateSchemas?, authoredGuardClaims,
      SelectedNativeTypeBoundRelationClaim.groundedClaims] using
      MainlineCallGuardCompileOccurrenceInstantiation.CheckerEndpointInstantiation.instantiate_authoredGuardClaimsFor
        instantiation guardProfile
        (generated_introductionFormalNames_nodup slot)
        (generated_introductionEndpoint_declared slot)
  · simp [instantiateContextAt?, delta, deltaExact]

/-! ## Exact conclusion-formula grounding -/

/-- The authored result-family application grounds uniformly under any
formal row containing the public result-family coordinate. -/
theorem instantiate_authoredFamilyApplicationAt
    (slot : Occurrence) {formals : List (String × Nat)}
    {arguments : List Pattern} (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? formals arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? formals arguments 0
        (authoredFamilyApplication demand slot (.fvar "result-family")) =
      some (authoredFamilyApplication demand slot resultFamily) := by
  simp [authoredFamilyApplication, applyFamily, authoredRelyValues_eq_nil,
    instantiateSchemaAt?, instantiateSchemasAt?, familyExact]

/-- The open result-family application uses the checker's one declared
result-family argument and no hidden rely values at a selected cold root. -/
theorem instantiate_authoredFamilyApplication
    (slot : Occurrence) {arguments : List Pattern} (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? (IntroductionFormals slot) arguments 0
        (authoredFamilyApplication demand slot (.fvar "result-family")) =
      some (authoredFamilyApplication demand slot resultFamily) :=
  instantiate_authoredFamilyApplicationAt slot resultFamily familyExact

/-- The occurrence-indexed modal application likewise grounds uniformly
under any formal row containing the public result-family coordinate. -/
theorem instantiate_modalTypeAt
    (slot : Occurrence) {formals : List (String × Nat)}
    {arguments : List Pattern} (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? formals arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? formals arguments 0
        (modalType demand slot (.fvar "result-family")) =
      some (modalType demand slot resultFamily) := by
  simp [modalType, relyTypes_eq_nil, instantiateSchemaAt?,
    instantiateSchemasAt?, familyExact]

/-- The occurrence-indexed modal head is fixed by generation; only its result
family argument is instantiated. -/
theorem instantiate_modalType
    (slot : Occurrence) {arguments : List Pattern} (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? (IntroductionFormals slot) arguments 0
        (modalType demand slot (.fvar "result-family")) =
      some (modalType demand slot resultFamily) :=
  instantiate_modalTypeAt slot resultFamily familyExact

/-- The body formula reconstructs the authored target and the same result
family application from one checker endpoint environment. -/
theorem instantiate_introductionBodyConclusion
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? (IntroductionFormals slot) arguments 0
        (introductionBodyPremise guardProfile slot).conclusion =
      some (groundedBodySequent slot instantiation.endpoint.bindings
        .empty .empty resultFamily).conclusion := by
  have targetExact :
      instantiateSchemaAt? (IntroductionFormals slot) arguments 0
          (authoredTarget demand slot) =
        some (applyBindingsForRule language
          (typingAt demand slot).site.rewrite
          instantiation.endpoint.bindings) := by
    simpa only [instantiateSchema?, authoredTarget,
      applyBindingsForRule_eq_syntactic] using
      instantiation.instantiate_authoredPattern
        (generated_introductionFormalNames_nodup slot)
        (generated_introductionEndpoint_declared slot)
        (selected_target_fragment slot)
  have familyApplicationExact :=
    instantiate_authoredFamilyApplication slot resultFamily familyExact
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise,
    groundedBodySequent,
    ContextualCarrierClaims.typingClaim, instantiateSchemaAt?,
    instantiateSchemasAt?, targetExact, familyApplicationExact]

/-- The modal conclusion reconstructs the authored focus and the same
occurrence-indexed modal application. -/
theorem instantiate_introductionConclusionFormula
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (resultFamily : Pattern)
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSchemaAt? (IntroductionFormals slot) arguments 0
        (introductionConclusion guardProfile slot).conclusion =
      some (groundedConclusionSequent slot instantiation.endpoint.bindings
        .empty .empty resultFamily).conclusion := by
  have focusExact :
      instantiateSchemaAt? (IntroductionFormals slot) arguments 0
          (authoredFocus demand slot) =
        some (applyBindings instantiation.endpoint.bindings
          (typingAt demand slot).site.focus) := by
    simpa only [instantiateSchema?, authoredFocus] using
      instantiation.instantiate_authoredPattern
        (generated_introductionFormalNames_nodup slot)
        (generated_introductionEndpoint_declared slot)
        (selected_focus_fragment slot)
  have modalExact := instantiate_modalType slot resultFamily familyExact
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion,
    groundedConclusionSequent,
    ContextualCarrierClaims.typingClaim, instantiateSchemaAt?,
    instantiateSchemasAt?, focusExact, modalExact]

/-! ## Exact structured-sequent grounding -/

/-- The complete generated body premise grounds to the named body sequent.
Every component is instantiated by the same ordered checker argument row. -/
theorem instantiate_introductionBodyPremise
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern)
    (gammaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Gamma" 0 = some (encodeContext gammaContext))
    (deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext))
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSequentAt? (IntroductionFormals slot) arguments 0
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise
          guardProfile slot) =
      some (groundedBodySequent slot instantiation.endpoint.bindings
        gammaContext deltaContext resultFamily) := by
  have variablesExact := instantiate_guardedVariableContext slot
    instantiation gammaContext gammaExact
  have relationsExact := instantiate_guardedBodyRelationContext slot
    instantiation deltaContext deltaExact
  have conclusionExact := instantiate_introductionBodyConclusion slot
    instantiation resultFamily familyExact
  have conclusionExact' :
      instantiateSchemaAt? (IntroductionFormals slot) arguments 0
          (ContextualCarrierClaims.typingClaim
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (authoredTarget demand slot)
            (authoredFamilyApplication demand slot (.fvar "result-family"))) =
        some (groundedBodySequent slot instantiation.endpoint.bindings
          gammaContext deltaContext resultFamily).conclusion := by
    simpa [
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise,
      groundedBodySequent] using conclusionExact
  unfold instantiateSequentAt?
  simp only [
    SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionBodyPremise]
  rw [variablesExact, relationsExact, conclusionExact']
  rfl

/-- The generated conclusion grounds through the same endpoint environment,
ambient contexts, and result-family argument as its body premise. -/
theorem instantiate_introductionConclusion
    (slot : Occurrence) {arguments : List Pattern}
    (instantiation : CheckerEndpointInstantiation demand slot
      (IntroductionFormals slot) arguments)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern)
    (gammaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Gamma" 0 = some (encodeContext gammaContext))
    (deltaExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext))
    (familyExact : lookupArgumentAt? (IntroductionFormals slot) arguments
      "result-family" 0 = some resultFamily) :
    instantiateSequentAt? (IntroductionFormals slot) arguments 0
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
          guardProfile slot) =
      some (groundedConclusionSequent slot instantiation.endpoint.bindings
        gammaContext deltaContext resultFamily) := by
  have variablesExact := instantiate_guardedVariableContext slot
    instantiation gammaContext gammaExact
  have relationsExact := instantiate_guardedConclusionRelationContext slot
    instantiation deltaContext deltaExact
  have conclusionExact := instantiate_introductionConclusionFormula slot
    instantiation resultFamily familyExact
  have conclusionExact' :
      instantiateSchemaAt? (IntroductionFormals slot) arguments 0
          (ContextualCarrierClaims.typingClaim
            (sourceCarrierAt demand (typingAt demand slot).focusType)
            (authoredFocus demand slot)
            (modalType demand slot (.fvar "result-family"))) =
        some (groundedConclusionSequent slot instantiation.endpoint.bindings
          gammaContext deltaContext resultFamily).conclusion := by
    simpa [
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion,
      groundedConclusionSequent] using conclusionExact
  unfold instantiateSequentAt?
  simp only [
    SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion]
  rw [variablesExact, relationsExact, conclusionExact']
  rfl

/-! ## One retained endpoint, one semantic world -/

/-- If two binding environments both cover a variable, equality of the
values observed by binding application recovers equality of the underlying
lookups.  Coverage is essential: without it, an absent binding and an
explicit self-binding would have the same gradual observation. -/
private theorem lookup_eq_of_covered_fvar_eq
    {left right : Bindings} {name : String}
    (leftCovered : (Bindings.lookup left name).isSome)
    (rightCovered : (Bindings.lookup right name).isSome)
    (observed : applyBindings left (.fvar name) =
      applyBindings right (.fvar name)) :
    Bindings.lookup left name = Bindings.lookup right name := by
  obtain ⟨leftValue, leftLookup⟩ :=
    Option.isSome_iff_exists.mp leftCovered
  obtain ⟨rightValue, rightLookup⟩ :=
    Option.isSome_iff_exists.mp rightCovered
  have valuesExact : leftValue = rightValue := by
    rw [applyBindings_fvar_eq_of_lookup leftLookup,
      applyBindings_fvar_eq_of_lookup rightLookup] at observed
    exact observed
  rw [leftLookup, rightLookup, valuesExact]

/-- Exact coordinate labels in the retained variable row force the reference
endpoint and the semantic world to observe the same value at every authored
source variable.  The equality is about values, not merely carrier types. -/
theorem sourceValue_eq_of_variableRowEvidence
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot reference.bindings))
    (slotExact : world.slot = slot) {name : String}
    (sourceMember :
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames) :
    applyBindings reference.bindings (.fvar name) =
      applyBindings world.environment.bindings (.fvar name) := by
  rcases world with ⟨worldSlot, before, environment⟩
  change worldSlot = slot at slotExact
  subst worldSlot
  have endpointMember : name ∈ endpointVariableNames demand slot :=
    (mem_endpointVariableNames_iff demand slot name).2 (Or.inl sourceMember)
  have bindingNameMember :
      name ∈ (authoredBindings demand slot).map Prod.fst := by
    rw [authoredBindingNames_of_endpointSourceBound demand slot
      (selected_endpoint_sourceBound slot)]
    exact endpointMember
  obtain ⟨authored, authoredMember, authoredName⟩ :=
    List.mem_map.mp bindingNameMember
  obtain ⟨binding, bindingAt⟩ := List.get_of_mem authoredMember
  have sourceBindingName :
      (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
        demand slot binding).1 = name := by
    rw [SelectedNativeTypeAuthoredVariableClaim.sourceBinding, bindingAt]
    exact authoredName
  let meaning := variableMeaningOfGroundedRowEvidence model
    ⟨slot, before, environment⟩ slot reference.bindings evidence binding
  have bindingExact : binding = meaning.binding := by
    apply Fin.ext
    exact congrArg
      (fun view : SelectedNativeTypeAuthoredVariableClaim.View demand =>
        view.binding.val)
      meaning.viewExact
  have valueExact := congrArg
    (fun view : SelectedNativeTypeAuthoredVariableClaim.View demand =>
      view.value)
    meaning.viewExact
  simpa only [SelectedNativeTypeAuthoredVariableClaim.groundedView,
    ← bindingExact, sourceBindingName] using valueExact

/-- On the covered source support, the retained coordinate row also recovers
the underlying binding lookups.  The coverage premises come from the exact
endpoint contract and the authentic source match, respectively. -/
theorem sourceLookup_eq_of_variableRowEvidence
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot reference.bindings))
    (slotExact : world.slot = slot) {name : String}
    (sourceMember :
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames) :
    Bindings.lookup reference.bindings name =
      Bindings.lookup world.environment.bindings name := by
  have endpointMember : name ∈ endpointVariableNames demand slot :=
    (mem_endpointVariableNames_iff demand slot name).2 (Or.inl sourceMember)
  have worldCovered :
      (Bindings.lookup world.environment.bindings name).isSome := by
    rcases world with ⟨worldSlot, before, environment⟩
    change worldSlot = slot at slotExact
    subst worldSlot
    exact (activationEndpointInstantiation environment).covers
      name endpointMember
  exact lookup_eq_of_covered_fvar_eq
    (reference.covers name endpointMember) worldCovered
    (sourceValue_eq_of_variableRowEvidence model slot reference world
      evidence slotExact sourceMember)

/-- The retained authored-variable row prevents a checked endpoint from
being spliced into an unrelated semantic activation.  Once body-claim
inversion identifies the selected occurrence, the exact coordinate labels
force every source-variable observation to agree; authentic source matching
then reconstructs the same focus state. -/
theorem endpointFocus_eq_worldBefore_of_variableRowEvidence
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot reference.bindings))
    (slotExact : world.slot = slot) :
    applyBindings reference.bindings (typingAt demand slot).site.focus =
      world.before := by
  rcases world with ⟨worldSlot, before, environment⟩
  change worldSlot = slot at slotExact
  subst worldSlot
  change applyBindings reference.bindings
      (typingAt demand slot).site.focus = before
  rw [← activation_focus_eq_before environment]
  have focusExact : (typingAt demand slot).site.focus =
      (typingAt demand slot).site.rewrite.left := by
    rw [typingAt_eq_rootTyping]
    simp [rootTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite]
  rw [focusExact]
  apply applyBindings_agree
  · rw [typingAt_eq_rootTyping]
    exact root_left_holeSkeleton _
  · intro name occurrenceMember
    have sourceMember :
        name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames := by
      rw [← selected_source_occurrenceNames_eq_freeFvarNames slot]
      exact occurrenceMember
    exact sourceLookup_eq_of_variableRowEvidence model slot reference
      ⟨slot, before, environment⟩ evidence rfl sourceMember

/-- The same retained endpoint evidence reconstructs the authored target in
the semantic world's matcher environment.  This is a structural target
equation; no target typing or rule conclusion is inspected. -/
theorem endpointTargetForRule_eq_worldTargetForRule_of_variableRowEvidence
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot reference.bindings))
    (slotExact : world.slot = slot) :
    applyBindingsForRule language (typingAt demand slot).site.rewrite
        reference.bindings =
      applyBindingsForRule language (typingAt demand slot).site.rewrite
        world.environment.bindings := by
  simp only [applyBindingsForRule_eq_syntactic]
  apply applyBindings_agree
  · rw [typingAt_eq_rootTyping]
    exact root_target_holeSkeleton _
  · intro name occurrenceMember
    have targetMember :
        name ∈ (typingAt demand slot).site.rewrite.right.freeFvarNames := by
      rw [← selected_target_occurrenceNames_eq_freeFvarNames slot]
      exact occurrenceMember
    exact sourceLookup_eq_of_variableRowEvidence model slot reference world
      evidence slotExact (selected_right_sourceBound slot name targetMember)

/-- Guard-row evidence grounded at the checked endpoint denotes the same
ordered relation queries in the semantic world's matcher environment.  Each
query argument is source-bound, so the retained variable row transports the
argument values without re-evaluating or reordering the guard. -/
theorem worldGroundMeanings_of_retainedEvidence
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (world : ActivationWorld)
    (variableEvidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot reference.bindings))
    (guardEvidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeBoundRelationClaim.groundedClaims
        guardProfile slot reference.bindings))
    (slotExact : world.slot = slot) :
    GroundMeanings guardProfile relationEnv slot
      world.environment.bindings := by
  have referenceMeanings := groundMeaningsOfGroundedGuardRowEvidence
    model world slot reference.bindings guardEvidence
  intro premise
  have argumentsExact :
      (sourceView guardProfile slot premise).arguments.map
          (applyBindings reference.bindings) =
        (sourceView guardProfile slot premise).arguments.map
          (applyBindings world.environment.bindings) := by
    apply List.map_congr_left
    intro argument argumentMember
    obtain ⟨name, rfl, sourceMember⟩ :=
      selected_view_sourceBound slot
        (sourceView guardProfile slot premise)
        (List.get_mem _ premise) argument argumentMember
    exact sourceValue_eq_of_variableRowEvidence model slot reference world
      variableEvidence slotExact sourceMember
  simpa [SelectedNativeTypeBoundRelationClaim.groundedView,
    SelectedNativeTypeBoundRelationClaim.View.Meaning,
    argumentsExact] using referenceMeanings premise

/-! ## Grounded guarded-introduction soundness -/

/-- One grounded M-Intro instance is sound in the independent shared-world
displayed model.  The rule retains both authored prefixes, so the body is
checked in exactly the conclusion's world.  Body inversion identifies the
authored occurrence; the retained rows then reconstruct the authentic match,
ordered guard truth, target, and modal witness. -/
theorem groundedIntroduction_valid
    (model : CarrierModel) (slot : Occurrence)
    (reference : EndpointInstantiation demand slot)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern)
    (bodyValid : SequentValid (displayedModel model)
      (groundedBodySequent slot reference.bindings
        gammaContext deltaContext resultFamily)) :
    SequentValid (displayedModel model)
      (groundedConclusionSequent slot reference.bindings
        gammaContext deltaContext resultFamily) := by
  rintro ⟨world, variableContextEvidence, relationContextEvidence⟩
  let variableSplit := ContextEvidence.splitPrepend
    (displayedModel model) world
    (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
      demand slot reference.bindings)
    gammaContext variableContextEvidence
  let relationSplit := ContextEvidence.splitPrepend
    (displayedModel model) world
    (SelectedNativeTypeBoundRelationClaim.groundedClaims
      guardProfile slot reference.bindings)
    deltaContext relationContextEvidence
  let bodyEnvironment : SequentEnvironment (displayedModel model)
      (groundedBodySequent slot reference.bindings
        gammaContext deltaContext resultFamily) :=
    { world := world
      variableEvidence := ContextEvidence.joinPrepend
        (displayedModel model) world variableSplit.1 variableSplit.2
      relationEvidence := ContextEvidence.joinPrepend
        (displayedModel model) world relationSplit.1 relationSplit.2 }
  obtain ⟨bodyEvidence⟩ := bodyValid bodyEnvironment
  have bodyMeaning := bodyEvidence.bodyTypedMeaningDetailed
  have slotExact : world.slot = slot := bodyMeaning.1
  cases slotExact
  have variableEvidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand world.slot reference.bindings) := variableSplit.1
  have guardEvidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeBoundRelationClaim.groundedClaims
        guardProfile world.slot reference.bindings) := relationSplit.1
  have worldMeanings : GroundMeanings guardProfile relationEnv world.slot
      world.environment.bindings :=
    worldGroundMeanings_of_retainedEvidence model world.slot reference world
      variableEvidence guardEvidence rfl
  have guardSupport :
      ContextSatisfies (guardModel world.slot world.before)
        world.environment
        (guardedConclusionRelationContext guardProfile world.slot) :=
    (guardContextSatisfies_iff_groundMeanings world.environment).2
      worldMeanings
  have worldBodyTyped :
      model.Typed (typingAt demand world.slot).rewriteType
        (applyBindingsForRule language
          (typingAt demand world.slot).site.rewrite world.environment.bindings)
        resultFamily := by
    rw [← endpointTargetForRule_eq_worldTargetForRule_of_variableRowEvidence
      model world.slot reference world variableEvidence rfl]
    exact bodyMeaning.2
  have member := guardedIntroduction_family_sound model world.slot
    world.environment guardSupport resultFamily worldBodyTyped
  rw [activation_focus_eq_before world.environment] at member
  have focusExact := endpointFocus_eq_worldBefore_of_variableRowEvidence
    model world.slot reference world variableEvidence rfl
  refine ⟨?_⟩
  change FormulaEvidence model world
    (ContextualCarrierClaims.typingClaim
      (sourceCarrierAt demand (typingAt demand world.slot).focusType)
      (applyBindings reference.bindings
        (typingAt demand world.slot).site.focus)
      (modalType demand world.slot resultFamily))
  simpa only [focusExact] using
    (FormulaEvidence.modalMember model world resultFamily member)

/-! ## Actual generated-rule application -/

/-- Every actual checker application of a selected generated M-Intro row is
sound in the independent displayed semantics.  Canonical-context premises
decode the two ambient wires, the typed-body premise supplies the grounded
body meaning, and `groundedIntroduction_valid` constructs the modal
conclusion.  The proof uses the generated rule's actual argument vector and
does not inspect a derivation of the conclusion. -/
theorem generated_introductionApplication_sound
    (model : CarrierModel) (slot : Occurrence)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      JudgmentMeaning model premise) :
    JudgmentMeaning model conclusion := by
  obtain ⟨endpointInstantiation⟩ :=
    generated_introductionApplication_endpoint slot ruleId application
  rcases application with
    ⟨actualRule, lookup, argumentsValid, _sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  let expected := ContextualInference.lowerRule
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
      guardProfile slot)
  have lookupActual : generated.1.lookupRule? expected.id =
      some actualRule := by
    simpa [expected, ruleId] using lookup
  have lookupExpected : generated.1.lookupRule? expected.id =
      some expected := by
    simpa [expected] using generated_introductionRule_lookup slot
  have actualRuleExact : actualRule = expected :=
    Option.some.inj (lookupActual.symm.trans lookupExpected)
  subst actualRule
  have argumentsValid' :
      argumentsValidAt (IntroductionFormals slot)
        ruleInstance.arguments = true := by
    simpa [expected, ContextualInference.lowerRule] using argumentsValid
  obtain ⟨publicArguments⟩ :=
    introductionPublicArguments_of_valid slot argumentsValid'
  have gammaInstantiation := instantiate_canonicalContextPremise slot
    "Gamma" publicArguments.gammaWire publicArguments.gammaExact
  have deltaInstantiation := instantiate_canonicalContextPremise slot
    "Delta" publicArguments.deltaWire publicArguments.deltaExact
  have premiseSchemasExact : expected.premises =
      [ ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Gamma")
      , ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Delta")
      , ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot)
      , ContextualInference.lowerSequent
          (introductionBodyPremise guardProfile slot) ] := by
    simpa [expected] using introductionRule_premises_exact slot
  have expectedFormalsExact : expected.metavariables =
      IntroductionFormals slot := by
    rfl
  have premisesComputed :=
    instantiateSchemasAt?_complete premisesInstantiate
  rw [premiseSchemasExact, expectedFormalsExact] at premisesComputed
  cases resultSortInstantiation :
      instantiateSchemaAt? (IntroductionFormals slot)
        ruleInstance.arguments 0
        (ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot)) with
  | none =>
      simp [instantiateSchemasAt?, gammaInstantiation, deltaInstantiation,
        resultSortInstantiation] at premisesComputed
  | some resultSortWire =>
      cases bodyInstantiation :
          instantiateSchemaAt? (IntroductionFormals slot)
            ruleInstance.arguments 0
            (ContextualInference.lowerSequent
              (introductionBodyPremise guardProfile slot)) with
      | none =>
          simp [instantiateSchemasAt?, gammaInstantiation,
            deltaInstantiation, resultSortInstantiation,
            bodyInstantiation] at premisesComputed
      | some bodyWire =>
          have premisesExact : premises =
              [ ContextualInference.lowerSequent
                  (ContextualInferenceCanonicalContext.sequent
                    publicArguments.gammaWire)
              , ContextualInference.lowerSequent
                  (ContextualInferenceCanonicalContext.sequent
                    publicArguments.deltaWire)
              , resultSortWire
              , bodyWire ] := by
            have forward :
                [ ContextualInference.lowerSequent
                    (ContextualInferenceCanonicalContext.sequent
                      publicArguments.gammaWire)
                , ContextualInference.lowerSequent
                    (ContextualInferenceCanonicalContext.sequent
                      publicArguments.deltaWire)
                , resultSortWire
                , bodyWire ] = premises := by
              simpa [instantiateSchemasAt?, gammaInstantiation,
                deltaInstantiation, resultSortInstantiation,
                bodyInstantiation] using premisesComputed
            exact forward.symm
          have gammaMeaning : JudgmentMeaning model
              (ContextualInference.lowerSequent
                (ContextualInferenceCanonicalContext.sequent
                  publicArguments.gammaWire)) := by
            apply premisesMeaning
            rw [premisesExact]
            simp
          have deltaMeaning : JudgmentMeaning model
              (ContextualInference.lowerSequent
                (ContextualInferenceCanonicalContext.sequent
                  publicArguments.deltaWire)) := by
            apply premisesMeaning
            rw [premisesExact]
            simp
          obtain ⟨gammaContext, gammaEncoding⟩ :=
            (judgmentMeaning_canonicalContext model
              publicArguments.gammaWire).mp
              gammaMeaning
          obtain ⟨deltaContext, deltaEncoding⟩ :=
            (judgmentMeaning_canonicalContext model
              publicArguments.deltaWire).mp
              deltaMeaning
          have gammaExact : lookupArgumentAt? (IntroductionFormals slot)
              ruleInstance.arguments "Gamma" 0 =
                some (encodeContext gammaContext) := by
            simpa only [gammaEncoding] using publicArguments.gammaExact
          have deltaExact : lookupArgumentAt? (IntroductionFormals slot)
              ruleInstance.arguments "Delta" 0 =
                some (encodeContext deltaContext) := by
            simpa only [deltaEncoding] using publicArguments.deltaExact
          have bodyExpected := instantiateSchemaAt?_lowerSequent_of_sequent
            (instantiate_introductionBodyPremise slot endpointInstantiation
              gammaContext deltaContext publicArguments.resultFamily gammaExact
              deltaExact publicArguments.familyExact)
          have bodyWireExact : bodyWire =
              ContextualInference.lowerSequent
                (groundedBodySequent slot endpointInstantiation.endpoint.bindings
                  gammaContext deltaContext publicArguments.resultFamily) := by
            exact Option.some.inj
              (bodyInstantiation.symm.trans bodyExpected)
          have bodyMeaning : JudgmentMeaning model
              (ContextualInference.lowerSequent
                (groundedBodySequent slot endpointInstantiation.endpoint.bindings
                  gammaContext deltaContext publicArguments.resultFamily)) := by
            rw [← bodyWireExact]
            apply premisesMeaning
            rw [premisesExact]
            simp
          have bodyNotCanonical :
              ContextualInferenceCanonicalContext.decodeClaim?
                (groundedBodySequent slot
                  endpointInstantiation.endpoint.bindings gammaContext
                  deltaContext publicArguments.resultFamily).conclusion = none := by
            simp [groundedBodySequent, ContextualCarrierClaims.typingClaim,
              ContextualInferenceCanonicalContext.decodeClaim?]
          have bodyValid : SequentValid (displayedModel model)
              (groundedBodySequent slot endpointInstantiation.endpoint.bindings
                gammaContext deltaContext publicArguments.resultFamily) :=
            (judgmentMeaning_contextual model _ bodyNotCanonical).mp
              bodyMeaning
          have conclusionValid := groundedIntroduction_valid model slot
            endpointInstantiation.endpoint gammaContext deltaContext
            publicArguments.resultFamily bodyValid
          have conclusionExpected :=
            instantiateSchemaAt?_lowerSequent_of_sequent
              (instantiate_introductionConclusion slot endpointInstantiation
                gammaContext deltaContext publicArguments.resultFamily gammaExact
                deltaExact publicArguments.familyExact)
          have conclusionSchemaExact : expected.conclusion =
              ContextualInference.lowerSequent
                (introductionConclusion guardProfile slot) := by
            simpa [expected] using introductionRule_conclusion_exact slot
          have conclusionComputed :=
            instantiateSchemaAt?_complete conclusionInstantiates
          rw [conclusionSchemaExact] at conclusionComputed
          have conclusionExact : conclusion =
              ContextualInference.lowerSequent
                (groundedConclusionSequent slot
                  endpointInstantiation.endpoint.bindings gammaContext
                  deltaContext publicArguments.resultFamily) := by
            exact Option.some.inj
              (conclusionComputed.symm.trans conclusionExpected)
          rw [conclusionExact]
          have conclusionNotCanonical :
              ContextualInferenceCanonicalContext.decodeClaim?
                (groundedConclusionSequent slot
                  endpointInstantiation.endpoint.bindings gammaContext
                  deltaContext publicArguments.resultFamily).conclusion = none := by
            simp [groundedConclusionSequent,
              ContextualCarrierClaims.typingClaim,
              ContextualInferenceCanonicalContext.decodeClaim?]
          exact (judgmentMeaning_contextual model _
            conclusionNotCanonical).2 conclusionValid

#print axioms introductionFormals_contains_publicParameters
#print axioms introductionPublicArguments_of_valid
#print axioms introductionRule_premises_exact
#print axioms introductionRule_conclusion_exact
#print axioms instantiate_canonicalContextPremiseAt
#print axioms instantiate_canonicalContextPremise
#print axioms instantiate_guardedVariableContext
#print axioms instantiate_guardedBodyRelationContext
#print axioms instantiate_guardedConclusionRelationContext
#print axioms instantiate_authoredFamilyApplication
#print axioms instantiate_modalType
#print axioms instantiate_introductionBodyConclusion
#print axioms instantiate_introductionConclusionFormula
#print axioms instantiate_introductionBodyPremise
#print axioms instantiate_introductionConclusion
#print axioms sourceValue_eq_of_variableRowEvidence
#print axioms sourceLookup_eq_of_variableRowEvidence
#print axioms endpointFocus_eq_worldBefore_of_variableRowEvidence
#print axioms endpointTargetForRule_eq_worldTargetForRule_of_variableRowEvidence
#print axioms worldGroundMeanings_of_retainedEvidence
#print axioms groundedIntroduction_valid
#print axioms generated_introductionApplication_sound

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedIntroductionSoundness
