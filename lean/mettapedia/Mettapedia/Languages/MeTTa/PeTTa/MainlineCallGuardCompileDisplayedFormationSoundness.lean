import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedIntroductionSoundness

/-!
# Generated formation soundness for the PeTTa call guard

The guarded formation schema has two canonical ambient-context premises and
one result-family sorting premise.  This module grounds all three through one
actual checker argument vector and proves the instantiated modal-formation
conclusion in the same independent shared-world displayed model used by
guarded introduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedFormationSoundness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceInstantiation
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ContextualFamilyApplication
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedIntroductionSoundness

abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

abbrev FormationFormals (slot : Occurrence) :=
  (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
    demand slot).metavariables

/-- All three public formation parameters occur in the inferred formal row. -/
theorem formationFormals_contains_publicParameters (slot : Occurrence) :
    ("Gamma", 0) ∈ FormationFormals slot ∧
      ("Delta", 0) ∈ FormationFormals slot ∧
      ("result-family", 0) ∈ FormationFormals slot := by
  constructor
  · simp [FormationFormals,
      SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
      inferMetavariables,
      SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
      ambientContextPremises,
      ContextualInferenceCanonicalContext.premise,
      ContextualInferenceCanonicalContext.sequent,
      ContextualInferenceCanonicalContext.claim,
      ContextualInference.lowerRule, ContextualInference.lowerSequent,
      ContextualInference.encodeContext, RuleSchema.occurrences,
      RuleSchema.patterns, patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt]
  · constructor
    · simp [FormationFormals,
        SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
        inferMetavariables,
        SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
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
              (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore
                demand slot).conclusion) := by
        simp [
          SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
          SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
          ContextualInference.lowerSequent,
          patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt,
          modalType, relyTypes_eq_nil,
          ContextualCarrierClaims.typingClaim]
      change ("result-family", 0) ∈
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot).metavariables
      unfold SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
      change ("result-family", 0) ∈
        (RuleSchema.occurrences
          (ContextualInference.lowerRule
            (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore
              demand slot))).eraseDups
      rw [List.mem_eraseDups]
      unfold RuleSchema.occurrences RuleSchema.patterns
      simp only [ContextualInference.lowerRule]
      rw [patternsMetavariableOccurrencesAt_append]
      apply List.mem_append_right
      simpa [patternsMetavariableOccurrencesAt] using formalInConclusion

structure FormationPublicArguments (slot : Occurrence)
    (arguments : List Pattern) where
  gammaWire : Pattern
  deltaWire : Pattern
  resultFamily : Pattern
  gammaExact : lookupArgumentAt? (FormationFormals slot) arguments
    "Gamma" 0 = some gammaWire
  deltaExact : lookupArgumentAt? (FormationFormals slot) arguments
    "Delta" 0 = some deltaWire
  familyExact : lookupArgumentAt? (FormationFormals slot) arguments
    "result-family" 0 = some resultFamily

theorem formationPublicArguments_of_valid (slot : Occurrence)
    {arguments : List Pattern}
    (valid : argumentsValidAt (FormationFormals slot) arguments = true) :
    Nonempty (FormationPublicArguments slot arguments) := by
  have namesNodup : ((FormationFormals slot).map Prod.fst).Nodup := by
    simpa [FormationFormals,
      SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
      inferMetavariables] using
      (occurrenceAdmission slot).formation.occurrenceNamesNodup
  have members := formationFormals_contains_publicParameters slot
  obtain ⟨gammaWire, gammaExact⟩ :=
    lookupArgumentAt?_exists_of_argumentsValidAt namesNodup valid
      ("Gamma", 0) members.1
  obtain ⟨deltaWire, deltaExact⟩ :=
    lookupArgumentAt?_exists_of_argumentsValidAt namesNodup valid
      ("Delta", 0) members.2.1
  obtain ⟨resultFamily, familyExact⟩ :=
    lookupArgumentAt?_exists_of_argumentsValidAt namesNodup valid
      ("result-family", 0) members.2.2
  exact ⟨⟨gammaWire, deltaWire, resultFamily,
    gammaExact, deltaExact, familyExact⟩⟩

/-- Ground result-family sorting judgment of one formation instance. -/
def groundedResultSortSequent (slot : Occurrence)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern) :
    Sequent where
  variableContext := gammaContext
  relationContext := deltaContext
  conclusion := ContextualCarrierClaims.typingClaim
    (sourceCarrierAt demand (typingAt demand slot).rewriteType)
    (authoredFamilyApplication demand slot resultFamily)
    (sortCode
      (sourceCarrierAt demand (typingAt demand slot).rewriteType)
      (ContextualModalProfile.resultCode
        (occurrenceAt demand slot).profile))

/-- Ground modal-formation conclusion of the same instance. -/
def groundedFormationConclusionSequent (slot : Occurrence)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern) :
    Sequent where
  variableContext := gammaContext
  relationContext := deltaContext
  conclusion := ContextualCarrierClaims.typingClaim
    (sourceCarrierAt demand (typingAt demand slot).focusType)
    (modalType demand slot resultFamily)
    (sortCode
      (sourceCarrierAt demand (typingAt demand slot).focusType)
      (ContextualModalProfile.resultCode
        (occurrenceAt demand slot).profile))

theorem instantiate_formationResultSortPremise
    (slot : Occurrence) {arguments : List Pattern}
    (publicArguments : FormationPublicArguments slot arguments)
    (gammaContext deltaContext : ContextSchema)
    (gammaExact : encodeContext gammaContext = publicArguments.gammaWire)
    (deltaExact : encodeContext deltaContext = publicArguments.deltaWire) :
    instantiateSequentAt? (FormationFormals slot) arguments 0
        (authoredResultSortPremise demand slot) =
      some (groundedResultSortSequent slot gammaContext deltaContext
        publicArguments.resultFamily) := by
  have gammaLookup : lookupArgumentAt? (FormationFormals slot) arguments
      "Gamma" 0 = some (encodeContext gammaContext) := by
    simpa only [gammaExact] using publicArguments.gammaExact
  have deltaLookup : lookupArgumentAt? (FormationFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext) := by
    simpa only [deltaExact] using publicArguments.deltaExact
  have familyInstantiation := instantiate_authoredFamilyApplicationAt slot
    publicArguments.resultFamily publicArguments.familyExact
  have sortInstantiation :
      instantiateSchemaAt? (FormationFormals slot) arguments 0
          (sortCode
            (carrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) =
        some (sortCode
          (carrierAt demand (typingAt demand slot).rewriteType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand slot).profile)) := by
    simp [sortCode, instantiateSchemaAt?, instantiateSchemasAt?]
  simp [instantiateSequentAt?, instantiateContextAt?,
    authoredResultSortPremise, authoredRelyVariableClaims,
    authoredRelyTypingClaims, selected_bindings_eq_nil,
    groundedResultSortSequent, gamma, delta, gammaLookup, deltaLookup,
    ContextualCarrierClaims.typingClaim, instantiateSchemaAt?,
    instantiateSchemasAt?, familyInstantiation, sortInstantiation]

theorem instantiate_formationConclusion
    (slot : Occurrence) {arguments : List Pattern}
    (publicArguments : FormationPublicArguments slot arguments)
    (gammaContext deltaContext : ContextSchema)
    (gammaExact : encodeContext gammaContext = publicArguments.gammaWire)
    (deltaExact : encodeContext deltaContext = publicArguments.deltaWire) :
    instantiateSequentAt? (FormationFormals slot) arguments 0
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot).conclusion =
      some (groundedFormationConclusionSequent slot gammaContext deltaContext
        publicArguments.resultFamily) := by
  have gammaLookup : lookupArgumentAt? (FormationFormals slot) arguments
      "Gamma" 0 = some (encodeContext gammaContext) := by
    simpa only [gammaExact] using publicArguments.gammaExact
  have deltaLookup : lookupArgumentAt? (FormationFormals slot) arguments
      "Delta" 0 = some (encodeContext deltaContext) := by
    simpa only [deltaExact] using publicArguments.deltaExact
  have modalInstantiation := instantiate_modalTypeAt slot
    publicArguments.resultFamily publicArguments.familyExact
  have sortInstantiation :
      instantiateSchemaAt? (FormationFormals slot) arguments 0
          (sortCode
            (carrierAt demand (typingAt demand slot).focusType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) =
        some (sortCode
          (carrierAt demand (typingAt demand slot).focusType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand slot).profile)) := by
    simp [sortCode, instantiateSchemaAt?, instantiateSchemasAt?]
  simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
    inferMetavariables,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
    instantiateSequentAt?, instantiateContextAt?,
    groundedFormationConclusionSequent, gamma, delta,
    gammaLookup, deltaLookup,
    ContextualCarrierClaims.typingClaim, instantiateSchemaAt?,
    instantiateSchemasAt?, modalInstantiation, sortInstantiation]

theorem formationRule_premises_exact (slot : Occurrence) :
    (ContextualInference.lowerRule
      (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
        demand slot)).premises =
      [ ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Gamma")
      , ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Delta")
      , ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot) ] := by
  have relyPremisesEmpty :
      SelectedNativeTypeSourceIndexedIntroduction.relySortPremises
          demand slot = [] := by
    simp [SelectedNativeTypeSourceIndexedIntroduction.relySortPremises,
      selected_bindings_eq_nil]
  simp [ContextualInference.lowerRule,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule,
    inferMetavariables,
    SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRuleCore,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore,
    ambientContextPremises, relyPremisesEmpty]

/-- At a selected cold root the result-family sorting premise supplies the
complete displayed formation meaning: the rely telescope is empty, so its
unique assignment is the empty row. -/
theorem groundedFormation_valid
    (model : CarrierModel) (slot : Occurrence)
    (gammaContext deltaContext : ContextSchema) (resultFamily : Pattern)
    (resultSortValid : SequentValid (displayedModel model)
      (groundedResultSortSequent slot gammaContext deltaContext resultFamily)) :
    SequentValid (displayedModel model)
      (groundedFormationConclusionSequent slot gammaContext deltaContext
        resultFamily) := by
  intro environment
  let world : ActivationWorld := environment.world
  let resultEnvironment : SequentEnvironment (displayedModel model)
      (groundedResultSortSequent slot gammaContext deltaContext resultFamily) :=
    { world := world
      variableEvidence := environment.variableEvidence
      relationEvidence := environment.relationEvidence }
  obtain ⟨resultEvidence⟩ := resultSortValid resultEnvironment
  have detailed := resultEvidence.resultFamilySortedMeaningDetailed
  have slotExact : world.slot = slot := detailed.1
  have resultTyped :
      model.Typed (typingAt demand world.slot).rewriteType
        resultFamily
        (model.universeObject
          (typingAt demand world.slot).rewriteType
          (ContextualModalProfile.resultCode
            (occurrenceAt demand world.slot).profile)) := by
    exact slotExact.symm ▸ detailed.2
  have relySorted : RelyTypesSorted model
      (occurrenceAt demand world.slot)
      (rootFormer world.slot resultFamily).relyTypes := by
    intro index
    have impossible := index.isLt
    change index.val < (bindingsAt demand world.slot).length at impossible
    have emptyBindings := selected_bindings_eq_nil world.slot
    simp [emptyBindings] at impossible
  have resultSorted : ResultFamilySorted model
      (occurrenceAt demand world.slot)
      (rootFormer world.slot resultFamily).relyTypes
      resultFamily := by
    intro values _valuesTyped
    refine ⟨resultFamily, ?_, resultTyped⟩
    have emptyBindings :
        DisplayedContextProfile.bindings
            (occurrenceAt demand world.slot).typing = [] :=
      selected_bindings_eq_nil world.slot
    have valuesEmpty : rowList values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [rowList, List.length_ofFn] using
        congrArg List.length emptyBindings
    rw [valuesEmpty]
    exact ⟨resultFamily, rfl, rfl⟩
  refine ⟨?_⟩
  have modalEvidence : FormulaEvidence model world
      (groundedFormationConclusionSequent world.slot gammaContext deltaContext
        resultFamily).conclusion :=
    FormulaEvidence.modalWellFormed model world resultFamily
      ⟨relySorted, resultSorted⟩
  have formulaExact := congrArg
    (fun selected : Occurrence =>
      (groundedFormationConclusionSequent selected gammaContext deltaContext
        resultFamily).conclusion) slotExact
  exact formulaExact ▸ modalEvidence

/-- Every actual generated formation application has the independent
displayed meaning whenever all of its exact instantiated premises do. -/
theorem generated_formationApplication_sound
    (model : CarrierModel) (slot : Occurrence)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (ruleId : ruleInstance.ruleId =
      (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot)).id)
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      JudgmentMeaning model premise) :
    JudgmentMeaning model conclusion := by
  rcases application with
    ⟨actualRule, lookup, argumentsValid, _sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  let expected := ContextualInference.lowerRule
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
      demand slot)
  have lookupActual : generated.1.lookupRule? expected.id =
      some actualRule := by
    simpa [expected, ruleId] using lookup
  have lookupExpected : generated.1.lookupRule? expected.id =
      some expected := by
    simpa [expected] using generated_formationRule_lookup slot
  have actualRuleExact : actualRule = expected :=
    Option.some.inj (lookupActual.symm.trans lookupExpected)
  subst actualRule
  have argumentsValid' : argumentsValidAt (FormationFormals slot)
      ruleInstance.arguments = true := by
    simpa [expected, ContextualInference.lowerRule] using argumentsValid
  obtain ⟨publicArguments⟩ :=
    formationPublicArguments_of_valid slot argumentsValid'
  have gammaInstantiation := instantiate_canonicalContextPremiseAt
    "Gamma" publicArguments.gammaWire publicArguments.gammaExact
  have deltaInstantiation := instantiate_canonicalContextPremiseAt
    "Delta" publicArguments.deltaWire publicArguments.deltaExact
  have premiseSchemasExact : expected.premises =
      [ ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Gamma")
      , ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.premise "Delta")
      , ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot) ] := by
    simpa [expected] using formationRule_premises_exact slot
  have expectedFormalsExact : expected.metavariables =
      FormationFormals slot := by rfl
  have premisesComputed :=
    instantiateSchemasAt?_complete premisesInstantiate
  rw [premiseSchemasExact, expectedFormalsExact] at premisesComputed
  cases resultSortInstantiation :
      instantiateSchemaAt? (FormationFormals slot) ruleInstance.arguments 0
        (ContextualInference.lowerSequent
          (authoredResultSortPremise demand slot)) with
  | none =>
      simp [instantiateSchemasAt?, gammaInstantiation, deltaInstantiation,
        resultSortInstantiation] at premisesComputed
  | some resultSortWire =>
      have premisesExact : premises =
          [ ContextualInference.lowerSequent
              (ContextualInferenceCanonicalContext.sequent
                publicArguments.gammaWire)
          , ContextualInference.lowerSequent
              (ContextualInferenceCanonicalContext.sequent
                publicArguments.deltaWire)
          , resultSortWire ] := by
        have forward :
            [ ContextualInference.lowerSequent
                (ContextualInferenceCanonicalContext.sequent
                  publicArguments.gammaWire)
            , ContextualInference.lowerSequent
                (ContextualInferenceCanonicalContext.sequent
                  publicArguments.deltaWire)
            , resultSortWire ] = premises := by
          simpa [instantiateSchemasAt?, gammaInstantiation,
            deltaInstantiation, resultSortInstantiation] using premisesComputed
        exact forward.symm
      have gammaMeaning := premisesMeaning
        (ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.sequent
            publicArguments.gammaWire)) (by simp [premisesExact])
      have deltaMeaning := premisesMeaning
        (ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.sequent
            publicArguments.deltaWire)) (by simp [premisesExact])
      obtain ⟨gammaContext, gammaEncoding⟩ :=
        (judgmentMeaning_canonicalContext model
          publicArguments.gammaWire).mp gammaMeaning
      obtain ⟨deltaContext, deltaEncoding⟩ :=
        (judgmentMeaning_canonicalContext model
          publicArguments.deltaWire).mp deltaMeaning
      have resultSortExpected := instantiateSchemaAt?_lowerSequent_of_sequent
        (instantiate_formationResultSortPremise slot publicArguments
          gammaContext deltaContext gammaEncoding deltaEncoding)
      have resultSortExact : resultSortWire =
          ContextualInference.lowerSequent
            (groundedResultSortSequent slot gammaContext deltaContext
              publicArguments.resultFamily) :=
        Option.some.inj (resultSortInstantiation.symm.trans resultSortExpected)
      have resultSortMeaning : JudgmentMeaning model
          (ContextualInference.lowerSequent
            (groundedResultSortSequent slot gammaContext deltaContext
              publicArguments.resultFamily)) := by
        rw [← resultSortExact]
        apply premisesMeaning
        rw [premisesExact]
        simp
      have resultSortNotCanonical :
          ContextualInferenceCanonicalContext.decodeClaim?
            (groundedResultSortSequent slot gammaContext deltaContext
              publicArguments.resultFamily).conclusion = none := by
        simp [groundedResultSortSequent,
          ContextualCarrierClaims.typingClaim,
          ContextualInferenceCanonicalContext.decodeClaim?]
      have resultSortValid : SequentValid (displayedModel model)
          (groundedResultSortSequent slot gammaContext deltaContext
            publicArguments.resultFamily) :=
        (judgmentMeaning_contextual model _ resultSortNotCanonical).mp
          resultSortMeaning
      have conclusionValid := groundedFormation_valid model slot
        gammaContext deltaContext publicArguments.resultFamily resultSortValid
      have conclusionExpected := instantiateSchemaAt?_lowerSequent_of_sequent
        (instantiate_formationConclusion slot publicArguments
          gammaContext deltaContext gammaEncoding deltaEncoding)
      have conclusionComputed :=
        instantiateSchemaAt?_complete conclusionInstantiates
      have conclusionExact : conclusion =
          ContextualInference.lowerSequent
            (groundedFormationConclusionSequent slot gammaContext deltaContext
              publicArguments.resultFamily) :=
        Option.some.inj (conclusionComputed.symm.trans conclusionExpected)
      rw [conclusionExact]
      have conclusionNotCanonical :
          ContextualInferenceCanonicalContext.decodeClaim?
            (groundedFormationConclusionSequent slot gammaContext deltaContext
              publicArguments.resultFamily).conclusion = none := by
        simp [groundedFormationConclusionSequent,
          ContextualCarrierClaims.typingClaim,
          ContextualInferenceCanonicalContext.decodeClaim?]
      exact (judgmentMeaning_contextual model _ conclusionNotCanonical).2
        conclusionValid

#print axioms formationFormals_contains_publicParameters
#print axioms formationPublicArguments_of_valid
#print axioms instantiate_formationResultSortPremise
#print axioms instantiate_formationConclusion
#print axioms formationRule_premises_exact
#print axioms groundedFormation_valid
#print axioms generated_formationApplication_sound

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedFormationSoundness
