import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedFormationSoundness
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedRuleOrigin

/-!
# Binder-free derivation soundness for the generated PeTTa call-guard calculus

The generated calculus contains six rule families: universe, canonical empty
and extended contexts, direct-to-contextual carrier typing, occurrence-indexed
formation, and guarded introduction.  This module proves one semantic closure
theorem by generator provenance and then lifts it to arbitrary proof trees.

The induction predicate strengthens independent judgment meaning only at the
direct carrier-typing boundary.  There it also records that both exposed terms
belong to the ordinary fragment.  This is precisely the invariant needed by
the carrier bridge: private modal and family-application syntax can receive
its stronger displayed evidence, but can never be smuggled through the generic
direct-typing rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedDerivationSoundness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedRuleOrigin
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedIntroductionSoundness
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedFormationSoundness

abbrev CarrierSlot :=
  SelectedNativeTypeSourceIndexedSemanticDecoding.CarrierSlot demand

/-- Strengthened induction meaning.  The independent displayed meaning remains
the public semantic statement; the additional field is an internal closure
invariant for direct carrier-typing judgments only. -/
structure GeneratedJudgmentMeaning (model : CarrierModel)
    (judgment : Pattern) : Prop where
  meaning : JudgmentMeaning model judgment
  directOrdinary : ∀ view,
    decodeCarrierTyping? demand judgment = some view →
      ordinaryTypingTerm view.term = true ∧
        ordinaryTypingTerm view.type = true

/-- Any independently meaningful non-direct judgment satisfies the strengthened
induction invariant vacuously. -/
theorem GeneratedJudgmentMeaning.of_not_direct
    (model : CarrierModel) (judgment : Pattern)
    (meaning : JudgmentMeaning model judgment)
    (notDirect : decodeCarrierTyping? demand judgment = none) :
    GeneratedJudgmentMeaning model judgment := by
  refine ⟨meaning, ?_⟩
  intro view decoded
  rw [notDirect] at decoded
  contradiction

/-- Every name in the generated carrier inventory comes from one exact slot of
the augmented request. -/
theorem carrierSlot_of_name_mem {carrier : String}
    (membership : carrier ∈ carrierNames demand) :
    ∃ slot : CarrierSlot, carrierName slot = carrier := by
  rw [carrierNames,
    SelectedNativeTypeSourceIndexedCarrierSupport.carrierNames_append]
    at membership
  change carrier ∈
    (CarrierObjectLanguageDef.carrierSignature
      (CarrierObjectLanguageDef.Naming.indexed
        (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
          demand))).typeNames at membership
  rw [CarrierObjectLanguageDef.carrierTypeNames] at membership
  obtain ⟨slot, nameExact⟩ := List.mem_ofFn.mp membership
  exact ⟨slot, nameExact⟩

/-- Carrier-universe codes are ordinary at the direct-typing boundary even
though their denotation is interpreted by the carrier model. -/
@[simp] theorem ordinaryTypingTerm_carrierUniverse
    (code : CarrierUniverseSignature.Code) (carrier : CarrierSlot) :
    ordinaryTypingTerm
        (.apply (CarrierUniverseSignature.label code (carrierName carrier)) []) =
      true := by
  unfold ordinaryTypingTerm
  rw [decodeApplication?_carrierUniverse]

/-- A contextual outer judgment can never decode as a direct carrier-typing
judgment. -/
@[simp] theorem decodeCarrierTyping?_contextualApply (arguments : List Pattern) :
    decodeCarrierTyping? demand
        (.apply ContextualInference.contextualJudgment.head arguments) = none := by
  cases arguments with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third more => rfl

/-- Structural instantiation cannot change the fixed contextual outer head. -/
theorem not_direct_of_contextual_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {schemas : List Pattern} {result : Pattern}
    (instantiates : Instantiates formals arguments
      (.apply ContextualInference.contextualJudgment.head schemas) result) :
    decodeCarrierTyping? demand result = none := by
  cases instantiates with
  | apply items => exact decodeCarrierTyping?_contextualApply _

/-- Independent canonical-context meaning embeds into the shared displayed
judgment model.  The proof reconstructs the contextual wire from the public
decoders, so malformed lookalikes remain rejected. -/
theorem canonicalMeaning_to_generated (model : CarrierModel)
    {judgment : Pattern}
    (canonicalMeaning :
      ContextualInferenceCanonicalContext.Meaning judgment) :
    GeneratedJudgmentMeaning model judgment := by
  unfold ContextualInferenceCanonicalContext.Meaning at canonicalMeaning
  cases sequentDecode : ContextualInference.decodeSequent? judgment with
  | none => simp [sequentDecode] at canonicalMeaning
  | some sequent =>
      simp only [sequentDecode] at canonicalMeaning
      cases claimDecode :
          ContextualInferenceCanonicalContext.decodeClaim?
            sequent.conclusion with
      | none => simp [claimDecode] at canonicalMeaning
      | some contextWire =>
          simp only [claimDecode] at canonicalMeaning
          have judgmentExact :=
            ContextualInference.lowerSequent_of_decodeSequent?_eq_some
              sequentDecode
          have notDirect : decodeCarrierTyping? demand judgment = none := by
            rw [← judgmentExact]
            simp [decodeCarrierTyping?, ContextualInference.lowerSequent]
          apply GeneratedJudgmentMeaning.of_not_direct model judgment
            _ notDirect
          unfold MainlineCallGuardCompileDisplayedModel.JudgmentMeaning
          simp only [notDirect, sequentDecode, claimDecode]
          exact canonicalMeaning

/-- The exact empty-context generator rule is sound inside the complete
attached calculus. -/
theorem generated_canonicalNilApplication_sound
    (model : CarrierModel) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some ContextualInferenceCanonicalContext.nilRule)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    GeneratedJudgmentMeaning model conclusion := by
  rcases application with
    ⟨actualRule, actualLookup, argumentsValid, _sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  have actualRuleExact :
      actualRule = ContextualInferenceCanonicalContext.nilRule := by
    rw [actualLookup] at lookup
    exact Option.some.inj lookup
  subst actualRule
  have semantic := ContextualInferenceCanonicalContext.nil_instance_sound
    argumentsValid premisesInstantiate conclusionInstantiates
  exact canonicalMeaning_to_generated model semantic.2

/-- The no-metavariable universe row reconstructs its exact authored
conclusion inside any validated attachment that retains its lookup. -/
theorem universeApplication_conclusion_exact
    (carrier : CarrierSlot) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (CarrierTypingLanguageDef.universeAxiom (carrierName carrier)))
    (application : RuleApplication generated ruleInstance premises conclusion) :
    conclusion =
      (CarrierTypingLanguageDef.universeAxiom
        (carrierName carrier)).conclusion := by
  rcases application with
    ⟨actualRule, actualLookup, argumentsValid, _sideConditionsValid,
      _premisesInstantiate, conclusionInstantiates⟩
  have actualRuleExact : actualRule =
      CarrierTypingLanguageDef.universeAxiom (carrierName carrier) := by
    rw [actualLookup] at lookup
    exact Option.some.inj lookup
  subst actualRule
  have argumentsEmpty : ruleInstance.arguments = [] := by
    have lengthZero : ruleInstance.arguments.length = 0 := by
      simpa [CarrierTypingLanguageDef.universeAxiom] using
        (argumentsValidAt_length argumentsValid).symm
    exact List.eq_nil_of_length_eq_zero lengthZero
  rw [argumentsEmpty] at conclusionInstantiates
  have conclusionComputed :=
    instantiateSchemaAt?_complete conclusionInstantiates
  simpa [CarrierTypingLanguageDef.universeAxiom,
    instantiateSchemaAt?, instantiateSchemasAt?] using
    conclusionComputed.symm

/-- Every generated carrier-universe application preserves both independent
typing meaning and the ordinary-direct boundary. -/
theorem generated_universeApplication_sound
    (model : CarrierModel) {carrier : String}
    (membership : carrier ∈ carrierNames demand)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (CarrierTypingLanguageDef.universeAxiom carrier))
    (application : RuleApplication generated ruleInstance premises conclusion) :
    GeneratedJudgmentMeaning model conclusion := by
  obtain ⟨slot, nameExact⟩ := carrierSlot_of_name_mem membership
  have slotLookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (CarrierTypingLanguageDef.universeAxiom
        (carrierName slot)) := by
    simpa only [nameExact] using lookup
  have conclusionExact := universeApplication_conclusion_exact slot
    slotLookup application
  have wireExact : conclusion = (universeView slot).encode := by
    simpa [CarrierTypingLanguageDef.universeAxiom, universeView,
      CarrierTypingView.encode] using conclusionExact
  have semantic := universeAxiom_application_sound model demand slot
    slotLookup application
  refine ⟨?_, ?_⟩
  · rw [wireExact]
    apply (judgmentMeaning_carrierTyping model (universeView slot)).2
    have semanticMeaning := semantic.2
    rw [wireExact] at semanticMeaning
    simpa [CarrierTypingMeaning] using semanticMeaning
  · intro view decoded
    rw [wireExact, decodeCarrierTyping?_encode] at decoded
    have viewExact := Option.some.inj decoded
    subst view
    constructor <;> simp [universeView]

/-- The exact canonical context-extension row is sound in the complete
attached calculus.  Its one child is recovered in authored order before the
generic canonical theorem is applied. -/
theorem generated_canonicalConsApplication_sound
    (model : CarrierModel) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some ContextualInferenceCanonicalContext.consRule)
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      GeneratedJudgmentMeaning model premise) :
    GeneratedJudgmentMeaning model conclusion := by
  rcases application with
    ⟨actualRule, actualLookup, argumentsValid, _sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  have actualRuleExact :
      actualRule = ContextualInferenceCanonicalContext.consRule := by
    rw [actualLookup] at lookup
    exact Option.some.inj lookup
  subst actualRule
  have argumentsLength : ruleInstance.arguments.length = 2 := by
    simpa [ContextualInferenceCanonicalContext.consRule] using
      (argumentsValidAt_length argumentsValid).symm
  obtain ⟨formula, tail, argumentsExact⟩ :=
    List.length_eq_two.mp argumentsLength
  rw [argumentsExact] at argumentsValid premisesInstantiate conclusionInstantiates
  have premisesComputed :=
    instantiateSchemasAt?_complete premisesInstantiate
  have premisesExact : premises =
      [ContextualInference.lowerSequent
        (ContextualInferenceCanonicalContext.sequent tail)] := by
    have forward :
        [ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.sequent tail)] = premises := by
      simpa [ContextualInferenceCanonicalContext.consRule,
        ContextualInferenceCanonicalContext.premise,
        ContextualInferenceCanonicalContext.sequent,
        ContextualInferenceCanonicalContext.claim,
        ContextualInference.lowerSequent, ContextualInference.encodeContext,
        instantiateSchemas?, instantiateSchema?, instantiateSchemaAt?,
        instantiateSchemasAt?, lookupArgumentAt?] using premisesComputed
    exact forward.symm
  have tailMeaning := premisesMeaning
    (ContextualInference.lowerSequent
      (ContextualInferenceCanonicalContext.sequent tail)) (by
        rw [premisesExact]
        simp)
  have tailCanonical :
      ContextualInferenceCanonicalContext.Canonical tail :=
    (judgmentMeaning_canonicalContext model tail).mp tailMeaning.meaning
  have canonicalPremises : ∀ premise ∈ premises,
      ContextualInferenceCanonicalContext.Meaning premise := by
    intro premise member
    rw [premisesExact] at member
    simp only [List.mem_singleton] at member
    subst premise
    exact
      (ContextualInferenceCanonicalContext.meaning_lowerSequent tail).2
        tailCanonical
  have semantic := ContextualInferenceCanonicalContext.cons_instance_sound
    argumentsValid premisesInstantiate conclusionInstantiates
      canonicalPremises
  exact canonicalMeaning_to_generated model semantic

/-- The direct-to-contextual carrier bridge is sound exactly when its direct
child stays in the ordinary fragment.  The two ambient contexts are decoded
from their own canonical certificates, while all three children remain in one
checker application. -/
theorem generated_carrierBridgeApplication_sound
    (model : CarrierModel) {carrier : String}
    (membership : carrier ∈ carrierNames demand)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (ContextualCarrierClaims.liftTypingRule carrier))
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      GeneratedJudgmentMeaning model premise) :
    GeneratedJudgmentMeaning model conclusion := by
  obtain ⟨slot, nameExact⟩ := carrierSlot_of_name_mem membership
  obtain ⟨gammaWire, deltaWire, term, type, _argumentsExact,
      premisesExact, conclusionExact⟩ :=
    ContextualCarrierClaims.liftTypingRule_application_exact carrier
      lookup application
  have gammaChild := premisesMeaning
    (ContextualInference.lowerSequent
      (ContextualInferenceCanonicalContext.sequent gammaWire)) (by
        rw [premisesExact]
        simp)
  have deltaChild := premisesMeaning
    (ContextualInference.lowerSequent
      (ContextualInferenceCanonicalContext.sequent deltaWire)) (by
        rw [premisesExact]
        simp)
  obtain ⟨gammaContext, gammaEncoding⟩ :=
    (judgmentMeaning_canonicalContext model gammaWire).mp gammaChild.meaning
  obtain ⟨deltaContext, deltaEncoding⟩ :=
    (judgmentMeaning_canonicalContext model deltaWire).mp deltaChild.meaning
  let view : CarrierTypingView demand :=
    { carrier := slot, term := term, type := type }
  have viewWireExact : view.encode =
      .apply (CarrierTypingLanguageDef.typingHead carrier) [term, type] := by
    simp [view, CarrierTypingView.encode, nameExact]
  have directChild := premisesMeaning
    (.apply (CarrierTypingLanguageDef.typingHead carrier) [term, type]) (by
      rw [premisesExact]
      simp)
  have directDecoded :
      decodeCarrierTyping? demand
          (.apply (CarrierTypingLanguageDef.typingHead carrier) [term, type]) =
        some view := by
    rw [← viewWireExact]
    exact decodeCarrierTyping?_encode view
  have ordinary := directChild.directOrdinary view directDecoded
  have directMeaning : JudgmentMeaning model view.encode := by
    rw [viewWireExact]
    exact directChild.meaning
  have typed :=
    (judgmentMeaning_carrierTyping model view).mp directMeaning
  let sequent : ContextualInference.Sequent :=
    { variableContext := gammaContext
      relationContext := deltaContext
      conclusion := ContextualCarrierClaims.typingClaim carrier term type }
  have conclusionWireExact :
      conclusion = ContextualInference.lowerSequent sequent := by
    rw [conclusionExact]
    simp [sequent, ContextualInference.lowerSequent,
      gammaEncoding, deltaEncoding]
  rw [conclusionWireExact]
  apply GeneratedJudgmentMeaning.of_not_direct model
  · apply (judgmentMeaning_contextual model sequent _).2
    · intro environment
      refine ⟨?_⟩
      change FormulaEvidence model environment.world
        (ContextualCarrierClaims.typingClaim carrier term type)
      have evidence := FormulaEvidence.directTyping model environment.world
        view ordinary.1 ordinary.2 typed
      simpa [sequent, view, nameExact] using evidence
    · simp [sequent, ContextualCarrierClaims.typingClaim,
        ContextualInferenceCanonicalContext.decodeClaim?]
  · simp [decodeCarrierTyping?, ContextualInference.lowerSequent]

/-- Successful rule lookup records the queried identifier in the selected
schema. -/
theorem ruleId_eq_of_lookup {definition : CalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema}
    (lookup : definition.lookupRule? ruleInstance.ruleId = some rule) :
    ruleInstance.ruleId = rule.id := by
  unfold CalculusLanguageDef.lookupRule? at lookup
  have selected := List.find?_some lookup
  have ruleExact : rule.id = ruleInstance.ruleId := by
    simpa using selected
  exact ruleExact.symm

/-- A checker application of a rule with fixed contextual conclusion head
cannot produce a direct carrier-typing wire. -/
theorem application_not_direct_of_contextualConclusion
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern} {rule : RuleSchema} {schemas : List Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId = some rule)
    (conclusionShape : rule.conclusion =
      .apply ContextualInference.contextualJudgment.head schemas)
    (application : RuleApplication generated ruleInstance premises conclusion) :
    decodeCarrierTyping? demand conclusion = none := by
  rcases application with
    ⟨actualRule, actualLookup, _argumentsValid, _sideConditionsValid,
      _premisesInstantiate, conclusionInstantiates⟩
  have actualRuleExact : actualRule = rule := by
    rw [actualLookup] at lookup
    exact Option.some.inj lookup
  subst actualRule
  rw [conclusionShape] at conclusionInstantiates
  exact not_direct_of_contextual_instantiates conclusionInstantiates

/-- One generated occurrence-indexed Formation application preserves the
strengthened induction meaning. -/
theorem generated_formationApplication_strengthened
    (model : CarrierModel)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot)))
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      GeneratedJudgmentMeaning model premise) :
    GeneratedJudgmentMeaning model conclusion := by
  have ruleId := ruleId_eq_of_lookup lookup
  have meaning := generated_formationApplication_sound model slot ruleId
    application (fun premise member => (premisesMeaning premise member).meaning)
  apply GeneratedJudgmentMeaning.of_not_direct model conclusion meaning
  apply application_not_direct_of_contextualConclusion
    (schemas :=
      [ ContextualInference.encodeContext
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot).conclusion.variableContext
      , ContextualInference.encodeContext
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
            demand slot).conclusion.relationContext
      , (SelectedNativeTypeGuardedSourceIndexedIntroduction.formationRule
          demand slot).conclusion.conclusion ]) lookup _ application
  rfl

/-- One generated guarded M-Intro application preserves the strengthened
induction meaning. -/
theorem generated_introductionApplication_strengthened
    (model : CarrierModel)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : generated.1.lookupRule? ruleInstance.ruleId =
      some (ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot)))
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      GeneratedJudgmentMeaning model premise) :
    GeneratedJudgmentMeaning model conclusion := by
  have ruleId := ruleId_eq_of_lookup lookup
  have meaning := generated_introductionApplication_sound model slot ruleId
    application (fun premise member => (premisesMeaning premise member).meaning)
  apply GeneratedJudgmentMeaning.of_not_direct model conclusion meaning
  apply application_not_direct_of_contextualConclusion
    (schemas :=
      [ ContextualInference.encodeContext
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            guardProfile slot).conclusion.variableContext
      , ContextualInference.encodeContext
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
            guardProfile slot).conclusion.relationContext
      , (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          guardProfile slot).conclusion.conclusion ]) lookup _ application
  rfl

/-! ## Generator-family closure and arbitrary derivations -/

/-- Every checker application in the complete generated calculus preserves the
strengthened independent meaning.  Classification follows generator
provenance, never a handwritten enumeration of the emitted rule table. -/
theorem generated_ruleApplication_sound
    (model : CarrierModel) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication generated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      GeneratedJudgmentMeaning model premise) :
    GeneratedJudgmentMeaning model conclusion := by
  obtain ⟨rule, lookup, origin⟩ := application_has_origin demand
    supportSeparated guardProfile (definition := generated) (by rfl)
      application
  cases origin with
  | «universe» carrier membership =>
      exact generated_universeApplication_sound model membership lookup
        application
  | canonicalNil =>
      exact generated_canonicalNilApplication_sound model lookup application
  | canonicalCons =>
      exact generated_canonicalConsApplication_sound model lookup application
        premisesMeaning
  | carrierBridge carrier membership =>
      exact generated_carrierBridgeApplication_sound model membership lookup
        application premisesMeaning
  | formation slot =>
      exact generated_formationApplication_strengthened model slot lookup
        application premisesMeaning
  | introduction slot =>
      exact generated_introductionApplication_strengthened model slot lookup
        application premisesMeaning

/-- Arbitrary binder-free proof trees in the generated call-guard calculus
satisfy the strengthened induction meaning. -/
theorem generated_derivation_strengthened (model : CarrierModel)
    {goal : Pattern} (derivation : Derivation generated goal) :
    GeneratedJudgmentMeaning model goal :=
  derivation.sound_of_ruleApplications
    (GeneratedJudgmentMeaning model)
    (generated_ruleApplication_sound model)

/-- Public crown: every arbitrary binder-free generated derivation has the
independently defined displayed call-guard meaning. -/
theorem generated_derivation_sound (model : CarrierModel)
    {goal : Pattern} (derivation : Derivation generated goal) :
    JudgmentMeaning model goal :=
  (generated_derivation_strengthened model derivation).meaning

/-! ## Discriminating boundary control -/

namespace Canary

/-- A private occurrence-indexed modal type cannot masquerade as an ordinary
direct carrier-typing child.  This is the exact counterexample that requires
the strengthened induction invariant at the carrier bridge. -/
theorem privateModalType_not_strengthenedDirect
    (model : CarrierModel)
    (slot : SelectedNativeTypeContextualCalculus.Occurrence demand)
    (term family : Pattern) :
    ¬ GeneratedJudgmentMeaning model
      ({ carrier :=
          MainlineCallGuardCompileFormationSemantics.focusCarrier slot
         term := term
         type := modalType demand slot family } :
        CarrierTypingView demand).encode := by
  intro strengthened
  let view : CarrierTypingView demand :=
    { carrier := MainlineCallGuardCompileFormationSemantics.focusCarrier slot
      term := term
      type := modalType demand slot family }
  have ordinary := strengthened.directOrdinary view
    (decodeCarrierTyping?_encode view)
  have impossible : false = true := by
    simpa [view] using ordinary.2
  exact Bool.false_ne_true impossible

end Canary

#print axioms carrierSlot_of_name_mem
#print axioms ordinaryTypingTerm_carrierUniverse
#print axioms canonicalMeaning_to_generated
#print axioms generated_canonicalNilApplication_sound
#print axioms universeApplication_conclusion_exact
#print axioms generated_universeApplication_sound
#print axioms generated_canonicalConsApplication_sound
#print axioms generated_carrierBridgeApplication_sound
#print axioms ruleId_eq_of_lookup
#print axioms application_not_direct_of_contextualConclusion
#print axioms generated_formationApplication_strengthened
#print axioms generated_introductionApplication_strengthened
#print axioms generated_ruleApplication_sound
#print axioms generated_derivation_strengthened
#print axioms generated_derivation_sound
#print axioms Canary.privateModalType_not_strengthenedDirect

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedDerivationSoundness
