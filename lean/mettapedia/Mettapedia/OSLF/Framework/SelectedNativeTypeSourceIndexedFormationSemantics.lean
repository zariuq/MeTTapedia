import Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction

/-!
# Independent universe and formation semantics for selected native types

The generated selected-native calculus first contributes a carrier-indexed
universe axiom and then one formation rule for each selected authored rewrite
occurrence.  This module gives those two rule families an interpretation which
does not mention generated derivability or checker acceptance.

The boundary has three layers:

* an exact decoder for the generated carrier-typing judgment;
* interpretation of private universe codes through an independently supplied
  `CarrierModel`; and
* a source-indexed formation view whose meaning is the displayed
  `ModalFormer.WellFormed` predicate.

The formation theorem is stated for the whole generator family.  A separate
wire theorem shows that the actual generated conclusion is exactly the
encoding of that semantic view.  This leaves introduction and checker-wide
derivation soundness to later modules without allowing either to define the
meaning established here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding

abbrev CarrierSlot {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeSourceIndexedSemanticDecoding.CarrierSlot demand

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-! ## Exact carrier-typing decoding -/

/-- Semantic view of one generated carrier-indexed typing judgment.  The
carrier is a request-bound slot, so a private wire name never becomes a global
type name. -/
structure CarrierTypingView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  carrier : CarrierSlot demand
  term : Pattern
  type : Pattern
deriving DecidableEq

def CarrierTypingView.encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : CarrierTypingView demand) : Pattern :=
  .apply (CarrierTypingLanguageDef.typingHead (carrierName view.carrier))
    [view.term, view.type]

/-- Fail-closed decoder for the direct carrier-typing judgment.  Both the
judgment head and its carrier coordinate must belong to the exact augmented
source-indexed request. -/
def decodeCarrierTyping? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern →
      Option (CarrierTypingView demand)
  | .apply head [term, type] => do
      let rawCarrier ← CarrierTypingLanguageDef.typingCarrier? head
      let carrier ← carrierSlot? demand rawCarrier
      pure { carrier, term, type }
  | _ => none

@[simp] theorem decodeCarrierTyping?_encode
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : CarrierTypingView demand) :
    decodeCarrierTyping? demand view.encode = some view := by
  cases view
  simp [decodeCarrierTyping?, CarrierTypingView.encode,
    carrierName, carrierSlot?]

/-- Successful direct-typing decoding reconstructs the complete wire. -/
theorem encode_of_decodeCarrierTyping?_eq_some
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {pattern : Pattern} {view : CarrierTypingView demand}
    (decoded : decodeCarrierTyping? demand pattern = some view) :
    view.encode = pattern := by
  cases pattern with
  | apply head arguments =>
      cases arguments with
      | nil => simp [decodeCarrierTyping?] at decoded
      | cons term tail =>
          cases tail with
          | nil => simp [decodeCarrierTyping?] at decoded
          | cons type rest =>
              cases rest with
              | cons extra more => simp [decodeCarrierTyping?] at decoded
              | nil =>
                  change
                    (do
                      let rawCarrier ←
                        CarrierTypingLanguageDef.typingCarrier? head
                      let carrier ← carrierSlot? demand rawCarrier
                      pure
                        ({ carrier
                           term
                           type } : CarrierTypingView demand)) =
                      some view at decoded
                  cases typingDecode :
                      CarrierTypingLanguageDef.typingCarrier? head with
                  | none => simp [typingDecode] at decoded
                  | some rawCarrier =>
                      rw [typingDecode] at decoded
                      change
                        (do
                          let carrier ← carrierSlot? demand rawCarrier
                          pure
                            ({ carrier
                               term
                               type } : CarrierTypingView demand)) =
                          some view at decoded
                      cases carrierDecode : carrierSlot? demand rawCarrier with
                      | none => simp [carrierDecode] at decoded
                      | some carrier =>
                          rw [carrierDecode] at decoded
                          change some
                            ({ carrier := carrier
                               term := term
                               type := type } : CarrierTypingView demand) =
                              some view at decoded
                          have viewExact := Option.some.inj decoded
                          subst view
                          rw [CarrierTypingView.encode,
                            carrierName_of_carrierSlot?_eq_some carrierDecode]
                          congr 1
                          exact
                            CarrierTypingLanguageDef.typingHead_of_typingCarrier?_eq_some
                              typingDecode
  | _ => simp [decodeCarrierTyping?] at decoded

/-! ## Independent universe interpretation -/

/-- Exact decoding of a private universe term.  This lemma avoids asking the
elaborator to normalize the complete generated decoder at each semantic use. -/
theorem decodeApplication?_carrierUniverse
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (code : CarrierUniverseSignature.Code) (carrier : CarrierSlot demand) :
    decodeApplication? demand
        (.apply (CarrierUniverseSignature.label code (carrierName carrier)) []) =
      some
        ({ head := .carrierUniverse code carrier
           arguments := [] } : ApplicationView demand) := by
  unfold decodeApplication?
  change
    (match decodeHead? demand (encodeHead (.carrierUniverse code carrier)) with
    | some head =>
        if [].length = arity head then
          some ({ head, arguments := [] } : ApplicationView demand)
        else none
    | none => none) = _
  rw [decodeHead?_encodeHead]
  rfl

/-- Interpret only the private universe layer here.  Authored source terms and
later modal syntax remain unchanged until their own independently indexed
semantic clauses are selected. -/
def interpretUniverseTerm {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (term : Pattern) : Pattern :=
  match decodeApplication? demand term with
  | some { head := .carrierUniverse code carrier, arguments := [] } =>
      model.universeObject carrier.expression code
  | _ => term

@[simp] theorem interpretUniverseTerm_carrierUniverse
    {source : ValidatedLanguageDef}
    (model : CarrierModel) {demand : SelectedNativeTypeDemand source}
    (code : CarrierUniverseSignature.Code) (carrier : CarrierSlot demand) :
    interpretUniverseTerm model demand
        (.apply (CarrierUniverseSignature.label code (carrierName carrier)) []) =
      model.universeObject carrier.expression code := by
  rw [interpretUniverseTerm, decodeApplication?_carrierUniverse]

/-- Independent meaning of the direct carrier-typing fragment.  Generated
universe names are decoded through the request and interpreted by the model;
the proof calculus is not consulted. -/
def CarrierTypingMeaning {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (claim : Pattern) : Prop :=
  match decodeCarrierTyping? demand claim with
  | some view =>
      model.Typed view.carrier.expression
        (interpretUniverseTerm model demand view.term)
        (interpretUniverseTerm model demand view.type)
  | none => False

def universeView {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (carrier : CarrierSlot demand) : CarrierTypingView demand :=
  { carrier
    term := .apply
      (CarrierUniverseSignature.label .star (carrierName carrier)) []
    type := .apply
      (CarrierUniverseSignature.label .box (carrierName carrier)) [] }

/-- Every emitted carrier-universe axiom has the independent carrier-model
meaning. -/
theorem universeAxiom_semantic
    {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand) :
    CarrierTypingMeaning model demand
      (CarrierTypingLanguageDef.universeAxiom
        (carrierName carrier)).conclusion := by
  change CarrierTypingMeaning model demand (universeView carrier).encode
  rw [CarrierTypingMeaning, decodeCarrierTyping?_encode]
  change model.Typed carrier.expression
    (interpretUniverseTerm model demand (universeView carrier).term)
    (interpretUniverseTerm model demand (universeView carrier).type)
  rw [show (universeView carrier).term =
      .apply (CarrierUniverseSignature.label .star
        (carrierName carrier)) [] from rfl]
  rw [show (universeView carrier).type =
      .apply (CarrierUniverseSignature.label .box
        (carrierName carrier)) [] from rfl]
  rw [interpretUniverseTerm_carrierUniverse,
    interpretUniverseTerm_carrierUniverse]
  exact universe_axiom model carrier.expression

/-- The no-metavariable universe schema has no instantiated premises and its
instantiated conclusion retains the independent universe meaning. -/
theorem universeAxiom_instance_sound
    {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (argumentsValid :
      argumentsValidAt
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).metavariables arguments = true)
    (premisesInstantiate :
      InstantiatesList
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).metavariables arguments
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).premises premises)
    (conclusionInstantiates :
      Instantiates
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).metavariables arguments
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).conclusion conclusion) :
    premises = [] ∧ CarrierTypingMeaning model demand conclusion := by
  have argumentsEmpty : arguments = [] := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
        simp [CarrierTypingLanguageDef.universeAxiom,
          argumentsValidAt] at argumentsValid
  subst arguments
  have premisesComputed := instantiateSchemasAt?_complete premisesInstantiate
  have premisesEmpty : premises = [] := by
    simpa [CarrierTypingLanguageDef.universeAxiom,
      instantiateSchemasAt?] using premisesComputed.symm
  have conclusionComputed :=
    instantiateSchemaAt?_complete conclusionInstantiates
  have conclusionExact :
      conclusion =
        (CarrierTypingLanguageDef.universeAxiom
          (carrierName carrier)).conclusion := by
    simpa [CarrierTypingLanguageDef.universeAxiom,
      instantiateSchemaAt?, instantiateSchemasAt?] using
        conclusionComputed.symm
  exact ⟨premisesEmpty,
    conclusionExact ▸ universeAxiom_semantic model demand carrier⟩

/-- Rule-application form of universe soundness.  Lookup remains an explicit
premise so this theorem applies at every lawful attachment layer. -/
theorem universeAxiom_application_sound
    {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand)
    {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some (CarrierTypingLanguageDef.universeAxiom (carrierName carrier)))
    (application :
      RuleApplication definition ruleInstance premises conclusion) :
    premises = [] ∧ CarrierTypingMeaning model demand conclusion := by
  cases application with
  | intro actualRule actualLookup argumentsValid _sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have actualRuleExact :
          actualRule = CarrierTypingLanguageDef.universeAxiom
            (carrierName carrier) := by
        rw [actualLookup] at lookup
        exact Option.some.inj lookup
      subst actualRule
      exact universeAxiom_instance_sound model demand carrier
        argumentsValid premisesInstantiate conclusionInstantiates

/-! ## Source-indexed formation meaning -/

/-- Every carrier required by a selected modal occurrence remains in the
augmented source-indexed request. -/
theorem requiredCarrier_mem_augmented
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {object : TypeExpr}
    (required : object ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (typingAt demand slot)) :
    object ∈
      (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
        demand).objects := by
  exact
    (CarrierObjectClosure.Request.objects_prefix_append
      demand.foundation.carrierObjects
      (SelectedNativeTypeSourceIndexedCarrierSupport.authoredRequest
        demand)).subset
      (demand.foundation.requiredCarrier_mem_objects
        (SelectedNativeTypeSourceIndexedCarrierSupport.selectedTyping_mem_foundation
          demand slot) required)

/-- Request-bound slot of one carrier required by a selected occurrence. -/
def requiredCarrierSlot
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {object : TypeExpr}
    (required : object ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (typingAt demand slot)) : CarrierSlot demand :=
  CarrierObjectNameLookup.slotOf
    (requiredCarrier_mem_augmented demand slot required)

/-- The proof-relevant required slot carries exactly the resolver name used by
the generated source-indexed rule. -/
theorem carrierName_requiredCarrierSlot
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {object : TypeExpr}
    (required : object ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (typingAt demand slot)) :
    carrierName (requiredCarrierSlot demand slot required) =
      sourceCarrierAt demand object := by
  unfold carrierName requiredCarrierSlot sourceCarrierAt
    SelectedNativeTypeSourceIndexedCarrierSupport.resolve
    CarrierObjectNameLookup.indexed?
  rw [CarrierObjectNameLookup.lookup?_eq_some_of_mem
    (CarrierObjectLanguageDef.Naming.indexed
      (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest demand))
    (requiredCarrier_mem_augmented demand slot required)]
  rfl

/-- Every augmented request slot belongs to the exact combined carrier-name
inventory used by the source-indexed calculus. -/
theorem carrierName_mem_generatedCarrierNames
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand) :
    carrierName carrier ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation ++
        SelectedNativeTypeSourceIndexedCarrierSupport.additionalCarrierNames
          demand := by
  rw [SelectedNativeTypeSourceIndexedCarrierSupport.carrierNames_append]
  change CarrierObjectLanguageDef.Naming.indexedName carrier ∈
    (CarrierObjectLanguageDef.carrierSignature
      (CarrierObjectLanguageDef.Naming.indexed
        (SelectedNativeTypeSourceIndexedCarrierSupport.augmentedRequest
          demand))).typeNames
  rw [CarrierObjectLanguageDef.carrierTypeNames]
  exact List.mem_ofFn.mpr ⟨carrier, rfl⟩

/-- A foundation carrier's universe axiom remains in the chronological
contextual signature.  Constructor chronology may change, but proof rows do
not. -/
theorem foundationUniverseAxiom_mem_signature
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) {name : String}
    (membership : name ∈
      SelectedNativeTypeFoundation.stableCarrierNames demand.foundation) :
    CarrierTypingLanguageDef.universeAxiom name ∈
      (SelectedNativeTypeContextualCalculus.signature demand).rules := by
  rw [SelectedNativeTypeContextualCalculus.signature,
    ContextualCarrierClaims.apply_rules]
  apply List.mem_append_left
  rw [(ContextualModalSignatureCompiler.definition_constructorPermutation_grouped
    demand.foundation).rules,
    ContextualModalExtension.language_rules,
    SelectedNativeTypeFoundation.definition_rules]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨name, membership, rfl⟩)

/-- Every request-bound universe axiom is an actual row of the final
source-indexed definition, whether its carrier was allocated by the modal
foundation or by the authored-endpoint suffix. -/
theorem universeAxiom_mem_definition
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (carrier : CarrierSlot demand) :
    CarrierTypingLanguageDef.universeAxiom (carrierName carrier) ∈
      (SelectedNativeTypeSourceIndexedCalculus.definition
        demand separated).rules := by
  have membership := carrierName_mem_generatedCarrierNames demand carrier
  rw [List.mem_append] at membership
  rw [SelectedNativeTypeSourceIndexedCalculus.definition_rules]
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_append.mpr
  cases membership with
  | inl foundationMembership =>
      exact Or.inl
        (foundationUniverseAxiom_mem_signature demand foundationMembership)
  | inr suffixMembership =>
      apply Or.inr
      rw [SelectedNativeTypeSourceIndexedCarrierSupport.extension_rules]
      apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨carrierName carrier, suffixMembership, rfl⟩

/-- Semantic data classified by one generated formation rule. -/
structure FormationView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  occurrence : Occurrence demand
  relyTypes : RelyRow (typingAt demand occurrence)
  resultFamily : Pattern

def FormationView.former {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : FormationView demand) :
    ModalFormer (occurrenceAt demand view.occurrence) where
  relyTypes := view.relyTypes
  resultFamily := view.resultFamily

/-- Independent meanings of all formation premises. -/
def FormationView.PremisesMeaning {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (model : CarrierModel) (view : FormationView demand) : Prop :=
  RelyTypesSorted model (occurrenceAt demand view.occurrence)
      view.relyTypes ∧
    ResultFamilySorted model (occurrenceAt demand view.occurrence)
      view.relyTypes view.resultFamily

/-- Independent meaning of the corresponding formation conclusion. -/
def FormationView.ConclusionMeaning {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (model : CarrierModel) (view : FormationView demand) : Prop :=
  view.former.WellFormed model

/-- Generator-family formation soundness.  The premise semantics and modal
meaning are independently defined in the displayed model; generated proof
search appears on neither side. -/
theorem formation_family_sound
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (model : CarrierModel) (view : FormationView demand) :
    view.PremisesMeaning model → view.ConclusionMeaning model := by
  intro premises
  exact premises

/-- Wire representation of one semantic modal former.  Ordered rely types
are retained without quotienting duplicates or permutations. -/
def FormationView.modalWire {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : FormationView demand) : Pattern :=
  .apply (SelectedModalNaming.label view.occurrence.val)
    (rowList view.relyTypes ++ [view.resultFamily])

/-- Exact generated contextual conclusion representing a semantic formation
view. -/
def FormationView.conclusionWire {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (view : FormationView demand) : Pattern :=
  let slot := view.occurrence
  let carrier := sourceCarrierAt demand (typingAt demand slot).focusType
  ContextualInference.lowerSequent
    { variableContext := gamma
      relationContext := delta
      conclusion := ContextualCarrierClaims.typingClaim carrier
        view.modalWire
        (sortCode carrier
          (ContextualModalProfile.resultCode
            (occurrenceAt demand slot).profile)) }

/-- Open formation view emitted at one selected occurrence. -/
def schemaFormationView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    FormationView demand where
  occurrence := slot
  relyTypes := fun index => .fvar (relyTypeName index.val)
  resultFamily := .fvar "result-family"

theorem rowList_schemaFormationView
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    rowList (schemaFormationView demand slot).relyTypes =
      relyTypes demand slot := by
  apply List.ext_get
  · simp [rowList, schemaFormationView, relyTypes, bindingsAt]
  · intro index firstBound secondBound
    simp [rowList, schemaFormationView, relyTypes]

/-- The open semantic view uses exactly the modal constructor application
emitted by the source-indexed generator. -/
theorem modalWire_schemaFormationView
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (schemaFormationView demand slot).modalWire =
      modalType demand slot (.fvar "result-family") := by
  unfold FormationView.modalWire
  rw [rowList_schemaFormationView]
  rfl

/-- The actual source-indexed formation generator emits exactly the wire of
the source-indexed semantic view. -/
theorem schemaFormationConclusion_exact
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (schemaFormationView demand slot).conclusionWire =
      ContextualInference.lowerSequent
        (SelectedNativeTypeSourceIndexedIntroduction.formationRule
          demand slot).conclusion := by
  unfold FormationView.conclusionWire
  simp only [
    SelectedNativeTypeSourceIndexedIntroduction.formationRule,
    inferMetavariables_conclusion,
    SelectedNativeTypeSourceIndexedIntroduction.formationRuleCore]
  change
    ContextualInference.lowerSequent
      { variableContext := gamma
        relationContext := delta
        conclusion := ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).focusType)
          (schemaFormationView demand slot).modalWire
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).focusType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) } = _
  rw [modalWire_schemaFormationView]

/-- Every source-indexed formation schema is an actual rule of the final
flat definition.  The proof follows the generator family and therefore does
not enumerate emitted rows. -/
theorem formationRule_mem_definition
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (slot : Occurrence demand) :
    ContextualInference.lowerRule
        (SelectedNativeTypeSourceIndexedIntroduction.formationRule demand slot) ∈
      (SelectedNativeTypeSourceIndexedCalculus.definition
        demand separated).rules := by
  rw [SelectedNativeTypeSourceIndexedCalculus.definition_rules]
  apply List.mem_append.mpr
  apply Or.inr
  rw [SelectedNativeTypeSourceIndexedIntroduction.profiledRules]
  apply List.mem_flatten.mpr
  refine
    ⟨SelectedNativeTypeSourceIndexedIntroduction.rulesAt demand slot, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨slot, rfl⟩
  · simp [SelectedNativeTypeSourceIndexedIntroduction.rulesAt]

/-! ## Discriminating controls -/

namespace Canary

/-- A carrier model which distinguishes the two universe objects and admits
exactly the intended universe axiom. -/
def separatingModel : CarrierModel where
  universeObject := fun _ code =>
    match code with
    | .star => .apply "$oslf:formation-canary:star" []
    | .box => .apply "$oslf:formation-canary:box" []
  Typed := fun _ term type =>
    term = .apply "$oslf:formation-canary:star" [] ∧
      type = .apply "$oslf:formation-canary:box" []
  starTypedBox := by
    intro carrier
    exact ⟨rfl, rfl⟩

/-- Positive control: every request-bound carrier retains the independent
universe axiom in a model which distinguishes its two universe objects. -/
theorem separatingModel_accepts_universeAxiom
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand) :
    CarrierTypingMeaning separatingModel demand
      (CarrierTypingLanguageDef.universeAxiom
        (carrierName carrier)).conclusion :=
  universeAxiom_semantic separatingModel demand carrier

/-- Negative control: changing the codomain from box to star is not licensed
by the same independent model. -/
theorem separatingModel_rejects_star_typed_star
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (carrier : CarrierSlot demand) :
    ¬ CarrierTypingMeaning separatingModel demand
      (CarrierTypingView.encode
        { carrier
          term := .apply
            (CarrierUniverseSignature.label .star
              (carrierName carrier)) []
          type := .apply
            (CarrierUniverseSignature.label .star
              (carrierName carrier)) [] }) := by
  rw [CarrierTypingMeaning, decodeCarrierTyping?_encode]
  simp [interpretUniverseTerm_carrierUniverse, separatingModel]

/-- A well-shaped typing head with a carrier outside the exact request cannot
acquire source-indexed semantic meaning. -/
theorem foreignCarrier_rejected
    {source : ValidatedLanguageDef}
    (model : CarrierModel) (demand : SelectedNativeTypeDemand source)
    (foreign : String) (term type : Pattern)
    (outside : carrierSlot? demand foreign = none) :
    ¬ CarrierTypingMeaning model demand
      (.apply (CarrierTypingLanguageDef.typingHead foreign) [term, type]) := by
  simp [CarrierTypingMeaning, decodeCarrierTyping?, outside]

end Canary

#print axioms decodeCarrierTyping?_encode
#print axioms encode_of_decodeCarrierTyping?_eq_some
#print axioms decodeApplication?_carrierUniverse
#print axioms interpretUniverseTerm_carrierUniverse
#print axioms universeAxiom_semantic
#print axioms universeAxiom_instance_sound
#print axioms universeAxiom_application_sound
#print axioms requiredCarrier_mem_augmented
#print axioms carrierName_requiredCarrierSlot
#print axioms carrierName_mem_generatedCarrierNames
#print axioms foundationUniverseAxiom_mem_signature
#print axioms universeAxiom_mem_definition
#print axioms formation_family_sound
#print axioms rowList_schemaFormationView
#print axioms modalWire_schemaFormationView
#print axioms schemaFormationConclusion_exact
#print axioms formationRule_mem_definition
#print axioms Canary.separatingModel_accepts_universeAxiom
#print axioms Canary.separatingModel_rejects_star_typed_star
#print axioms Canary.foreignCarrier_rejected

end Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
