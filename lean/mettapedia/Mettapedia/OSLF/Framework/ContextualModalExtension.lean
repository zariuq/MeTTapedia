import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Indexes
import Mettapedia.GSLT.LanguageDef.ConstructorTermExtension
import Mettapedia.OSLF.Framework.CarrierObjectNameLookup
import Mettapedia.OSLF.Framework.ContextualModalSignature
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationValidation

/-!
# Contextual-modal extension of the sparse carrier foundation

This module compiles one contextual modal constructor for every selected,
typed rewrite occurrence.  Carrier lookup is fail-closed: an unretained
`TypeExpr` maps to the empty invalid category, while the demand's coverage
proof shows that every name actually emitted comes from a unique retained
carrier slot.

The compiler is expressed as a `CalculusLanguageExtension`, and `language`
applies that delta to the carrier foundation.  Thus callers receive one flat
`CalculusLanguageDef`; the factorization remains available only for proofs,
incremental compilation, and specialization.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace ContextualModalExtension

/-- Fail-closed carrier resolver used internally by contextual compilation.
Coverage theorems reduce every emitted use to a successful certified lookup. -/
def compiledCarrierName {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (object : TypeExpr) : String :=
  (CarrierObjectNameLookup.indexed? demand.carrierObjects object).getD ""

/-- A retained object compiles to its unique indexed carrier name. -/
theorem compiledCarrierName_of_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    {object : TypeExpr}
    (membership : object ∈ demand.carrierObjects.objects) :
    compiledCarrierName demand object =
      CarrierObjectNameLookup.nameOf
        (CarrierObjectLanguageDef.Naming.indexed demand.carrierObjects)
        membership := by
  simp [compiledCarrierName, CarrierObjectNameLookup.indexed?, membership]

/-- The typed occurrence selected at one exact authored-order slot. -/
def typingAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) : DisplayedRewriteTyping source :=
  demand.typings.get slot

/-- A positional selection always denotes an actually demanded typing. -/
theorem typingAt_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) :
    typingAt demand slot ∈ demand.typings := by
  exact List.get_mem demand.typings slot

/-- Every carrier used by a contextual modal argument is one of the carrier
roots retained by the sparse foundation. -/
theorem inputCarrier_mem_requiredCarrierRoots
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) {object : TypeExpr}
    (membership : object ∈ ContextualModalSignature.inputCarriers typing) :
    object ∈ SelectedNativeTypeFoundation.requiredCarrierRoots typing := by
  rw [ContextualModalSignature.inputCarriers, List.mem_append] at membership
  rcases membership with relyMembership | resultMembership
  · unfold SelectedNativeTypeFoundation.requiredCarrierRoots
    apply List.mem_append_right
    simpa [ContextualModalSignature.relyBindings,
      DisplayedContextProfile.carrierTypes] using relyMembership
  · simp only [List.mem_singleton] at resultMembership
    subst object
    simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-- The finite support of a modal declaration is contained in the exact
carrier-root demand of its selected typing. -/
theorem carrierSupport_mem_requiredCarrierRoots
    {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) {object : TypeExpr}
    (membership : object ∈ ContextualModalSignature.carrierSupport typing) :
    object ∈ SelectedNativeTypeFoundation.requiredCarrierRoots typing := by
  rw [ContextualModalSignature.carrierSupport, List.mem_cons] at membership
  rcases membership with rfl | inputMembership
  · simp [SelectedNativeTypeFoundation.requiredCarrierRoots]
  · exact inputCarrier_mem_requiredCarrierRoots typing inputMembership

/-- Every compiled name justified by one selected typing belongs to the flat
foundation's carrier namespace. -/
theorem compiledCarrierName_mem_typeNames
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    {typing : DisplayedRewriteTyping source}
    (typingMembership : typing ∈ demand.typings)
    {object : TypeExpr}
    (required : object ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots typing) :
    compiledCarrierName demand object ∈
      (SelectedNativeTypeFoundation.definition demand).toLanguageDef.typeNames := by
  have retained := demand.requiredCarrier_mem_objects typingMembership required
  rw [compiledCarrierName_of_mem demand retained,
    SelectedNativeTypeFoundation.definition_typeNames]
  simpa [SelectedNativeTypeFoundation.stableCarrierNames,
    SelectedNativeTypeFoundation.stableCarrierTypes,
    CarrierObjectLanguageDef.carrierSignature, LanguageDef.typeNames] using
    (CarrierObjectNameLookup.indexed_name_mem_typeNames
      (request := demand.carrierObjects) retained)

/-- Contextual modal declaration at one exact occurrence slot. -/
def modalRuleAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) : GrammarRule :=
  ContextualModalSignature.modalRule (compiledCarrierName demand) slot.val
    (typingAt demand slot)

/-- All contextual modal declarations in authored occurrence order. -/
def modalTerms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) : List GrammarRule :=
  List.ofFn (modalRuleAt demand)

/-- Equivalent indexed-map view used by the incremental compilation laws. -/
theorem modalTerms_eq_mapIdx {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    modalTerms demand = demand.typings.mapIdx fun slot typing =>
      ContextualModalSignature.modalRule (compiledCarrierName demand)
        slot typing := by
  rw [List.mapIdx_eq_ofFn]
  rfl

/-- Carrier names already allocated by an earlier demand are stable when a
later demand is appended. -/
theorem compiledCarrierName_append_of_mem
    {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeFoundation.Demand source)
    {object : TypeExpr}
    (membership : object ∈ earlier.carrierObjects.objects) :
    compiledCarrierName (earlier.append later) object =
      compiledCarrierName earlier object := by
  unfold compiledCarrierName
  rw [SelectedNativeTypeFoundation.Demand.carrierObjects_append,
    CarrierObjectNameLookup.indexed?_append_of_mem
      earlier.carrierObjects later.carrierObjects membership]

/-- New modal rows generated after an existing demand.  Labels use their
global authored-order offset and carrier lookup uses the combined inventory. -/
def appendedModalTerms {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeFoundation.Demand source) :
    List GrammarRule :=
  later.typings.mapIdx fun slot typing =>
    ContextualModalSignature.modalRule
      (compiledCarrierName (earlier.append later))
      (slot + earlier.typings.length) typing

/-- The old modal prefix is byte-for-byte stable under demand append. -/
theorem modalTerms_oldPrefix
    {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeFoundation.Demand source) :
    earlier.typings.mapIdx (fun slot typing =>
      ContextualModalSignature.modalRule
        (compiledCarrierName (earlier.append later)) slot typing) =
      modalTerms earlier := by
  rw [modalTerms_eq_mapIdx, List.mapIdx_eq_ofFn, List.mapIdx_eq_ofFn]
  apply congrArg List.ofFn
  funext slot
  apply ContextualModalSignature.modalRule_congr
  intro object supportMembership
  apply compiledCarrierName_append_of_mem earlier later
  apply earlier.requiredCarrier_mem_objects
    (List.get_mem earlier.typings slot)
  exact carrierSupport_mem_requiredCarrierRoots
    (earlier.typings.get slot) supportMembership

/-- Exact incremental law: compiling an appended demand is the stable old
prefix followed by the residual rows compiled against the combined carrier
inventory. -/
theorem modalTerms_append {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeFoundation.Demand source) :
    modalTerms (earlier.append later) =
      modalTerms earlier ++ appendedModalTerms earlier later := by
  rw [modalTerms_eq_mapIdx,
    SelectedNativeTypeFoundation.Demand.append_typings, List.mapIdx_append,
    modalTerms_oldPrefix]
  rfl

/-- Signature delta contributed by selected contextual occurrences. -/
def extension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    CalculusLanguageExtension :=
  ConstructorTermExtension.ofList (modalTerms demand)

/-- One flat carrier-and-contextual calculus language. -/
def language {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    CalculusLanguageDef :=
  (extension demand).apply (SelectedNativeTypeFoundation.definition demand)

@[simp]
theorem language_types {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (language demand).types =
      (SelectedNativeTypeFoundation.definition demand).types := by
  simp [language, extension, ConstructorTermExtension.ofList]

@[simp]
theorem language_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (language demand).terms =
      (SelectedNativeTypeFoundation.definition demand).terms ++
        modalTerms demand := by
  rfl

@[simp]
theorem language_judgments {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (language demand).judgments =
      (SelectedNativeTypeFoundation.definition demand).judgments := by
  simp [language, extension, ConstructorTermExtension.ofList]

@[simp]
theorem language_rules {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (language demand).rules =
      (SelectedNativeTypeFoundation.definition demand).rules := by
  simp [language, extension, ConstructorTermExtension.ofList]

@[simp]
theorem length_modalTerms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (modalTerms demand).length = demand.typings.length := by
  simp [modalTerms]

theorem modalTermLabels {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (modalTerms demand).map GrammarRule.label =
      List.ofFn fun slot : Fin demand.typings.length =>
        SelectedModalNaming.label slot.val := by
  simp [modalTerms, modalRuleAt, ContextualModalSignature.modalRule,
    List.map_ofFn, Function.comp_def]

theorem modalTermLabels_nodup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    ((modalTerms demand).map GrammarRule.label).Nodup := by
  rw [modalTermLabels]
  apply List.nodup_ofFn_ofInjective
  intro first second equality
  apply Fin.ext
  exact SelectedModalNaming.label_injective equality

/-- The result carrier of every generated modal declaration is present in the
flat carrier foundation. -/
theorem modalRuleAt_category_mem_typeNames
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) :
    (modalRuleAt demand slot).category ∈
      (SelectedNativeTypeFoundation.definition demand).toLanguageDef.typeNames := by
  apply compiledCarrierName_mem_typeNames demand (typingAt_mem demand slot)
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-- Every base sort named by a generated contextual parameter is present in
the same flat carrier foundation. -/
theorem modalRuleAt_parameter_baseName_mem_typeNames
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length)
    {parameter : TermParam}
    (parameterMembership : parameter ∈ (modalRuleAt demand slot).params)
    {typeName : String}
    (typeNameMembership :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    typeName ∈
      (SelectedNativeTypeFoundation.definition demand).toLanguageDef.typeNames := by
  obtain ⟨object, objectMembership, typeNameEquality⟩ :=
    ContextualModalSignature.parameter_baseName_origin
      (compiledCarrierName demand)
      (ContextualModalSignature.relyBindings (typingAt demand slot))
      (typingAt demand slot).rewriteType
      (by simpa [modalRuleAt, ContextualModalSignature.modalRule,
          ContextualModalSignature.parameters] using parameterMembership)
      typeNameMembership
  subst typeName
  apply compiledCarrierName_mem_typeNames demand (typingAt_mem demand slot)
  apply inputCarrier_mem_requiredCarrierRoots (typingAt demand slot)
  simpa [ContextualModalSignature.inputCarriers] using objectMembership

/-- Each generated contextual declaration passes the ordinary constructor
row validator against the carrier foundation. -/
theorem modalRuleAt_validateTerm
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) :
    LanguageDef.validateTerm
      (SelectedNativeTypeFoundation.definition demand).toLanguageDef
      (modalRuleAt demand slot) = [] := by
  simp only [LanguageDef.validateTerm,
    modalRuleAt_category_mem_typeNames, if_pos, List.nil_append,
    List.append_eq_nil_iff]
  constructor
  · apply List.flatMap_eq_nil_iff.mpr
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro typeName typeNameMembership
    exact modalRuleAt_parameter_baseName_mem_typeNames demand slot
      parameterMembership typeNameMembership
  · simp [modalRuleAt, ContextualModalSignature.modalRule]

/-- Carrier-universe constructors and contextual-modal constructors occupy
provably disjoint generated namespaces. -/
theorem foundation_modalTermLabels_disjoint
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    List.Disjoint
      ((SelectedNativeTypeFoundation.definition demand).terms.map (·.label))
      ((modalTerms demand).map (·.label)) := by
  rw [SelectedNativeTypeFoundation.definition_terms,
    CarrierUniverseSignature.termLabelsFor, modalTermLabels,
    List.disjoint_left]
  intro name universeMembership modalMembership
  obtain ⟨carrier, _, localMembership⟩ :=
    List.mem_flatMap.mp universeMembership
  have universeCases :
      name = CarrierUniverseSignature.label .star carrier ∨
      name = CarrierUniverseSignature.label .box carrier := by
    simpa using localMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp modalMembership
  rcases universeCases with starEquality | boxEquality
  · exact SelectedModalNaming.label_ne_carrierUniverseLabel
      slot.val .star carrier starEquality
  · exact SelectedModalNaming.label_ne_carrierUniverseLabel
      slot.val .box carrier boxEquality

/-- The complete flat constructor namespace remains duplicate-free. -/
theorem language_termLabels_nodup
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    ((language demand).terms.map (·.label)).Nodup := by
  rw [language_terms, List.map_append]
  exact List.Nodup.append
    (CarrierUniverseSignature.termLabelsFor_nodup
      (SelectedNativeTypeFoundation.stableCarrierNames demand)
      (SelectedNativeTypeFoundation.stableCarrierNames_nodup demand))
    (modalTermLabels_nodup demand)
    (foundation_modalTermLabels_disjoint demand)

/-- The contextual signature extension passes the structural language gate;
there is no intermediate public pair or unchecked merged representation. -/
theorem language_validate {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (language demand).toLanguageDef.validate = [] := by
  change ((ConstructorTermExtension.ofList (modalTerms demand)).apply
    (SelectedNativeTypeFoundation.definition demand)).toLanguageDef.validate = []
  apply ConstructorTermExtension.apply_language_validate
  · exact SelectedNativeTypeFoundation.definition_language_validate demand
  · rfl
  · rfl
  · exact modalTermLabels_nodup demand
  · exact foundation_modalTermLabels_disjoint demand
  · intro term termMembership
    change term ∈ List.ofFn (modalRuleAt demand) at termMembership
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp termMembership
    exact modalRuleAt_validateTerm demand slot

@[simp]
theorem modalRuleAt_parameter_count {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source)
    (slot : Fin demand.typings.length) :
    (modalRuleAt demand slot).params.length =
      (DisplayedContextProfile.bindings (typingAt demand slot)).length + 1 := by
  exact ContextualModalSignature.modalRule_parameter_count
    (compiledCarrierName demand) slot.val (typingAt demand slot)

/-! ## Positive and negative controls -/

namespace Canary

/-- Empty demand adds no hidden modal declaration. -/
theorem empty_has_no_modal_terms (source : ValidatedLanguageDef) :
    modalTerms (SelectedNativeTypeFoundation.Demand.empty source) = [] := by
  rfl

/-- Modal output cardinality reflects selected occurrence multiplicity. -/
theorem modalTerms_ne_of_typing_count_ne
    {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeFoundation.Demand source)
    (different : first.typings.length ≠ second.typings.length) :
    modalTerms first ≠ modalTerms second := by
  intro equality
  apply different
  rw [← length_modalTerms first, ← length_modalTerms second, equality]

end Canary

#print axioms compiledCarrierName_of_mem
#print axioms modalTermLabels_nodup
#print axioms modalTerms_append
#print axioms modalRuleAt_validateTerm
#print axioms foundation_modalTermLabels_disjoint
#print axioms language_validate
#print axioms modalRuleAt_parameter_count
#print axioms Canary.empty_has_no_modal_terms
#print axioms Canary.modalTerms_ne_of_typing_count_ne

end ContextualModalExtension

end Mettapedia.OSLF.Framework
