import Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompiler
import Mettapedia.OSLF.Framework.ContextualModalSignatureTransport

/-!
# Structural transport of profiled contextual calculus compilation

The existing atomic input transports its retained typing, grounded carriers,
and local profile together. These laws concern the actual chronological
compiler and its generated contextual rules. They do not assert a free
extension universal property or select a local modal profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace SelectedNativeTypeContextualCalculus

/-- Reindex an occurrence without changing its chronological position. -/
def mapSlot {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    Occurrence (demand.map morphism) :=
  ⟨slot.val, by simp [SelectedNativeTypeDemand.map]⟩

@[simp] theorem mapSlot_val {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (mapSlot morphism demand slot).val = slot.val := rfl

@[simp] theorem occurrenceAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    occurrenceAt (demand.map morphism) (mapSlot morphism demand slot) =
      (occurrenceAt demand slot).map morphism := by
  simp [occurrenceAt, SelectedNativeTypeDemand.map, mapSlot]

@[simp] theorem typingAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    typingAt (demand.map morphism) (mapSlot morphism demand slot) =
      (typingAt demand slot).map morphism := by
  simp [typingAt]

@[simp] theorem bindingsAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    bindingsAt (demand.map morphism) (mapSlot morphism demand slot) =
      (bindingsAt demand slot).map fun binding =>
        (binding.1, mapTypeExpr morphism.symbols binding.2) := by
  simp [bindingsAt, DisplayedContextProfile.bindings_map]

@[simp] theorem length_bindingsAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (bindingsAt (demand.map morphism) (mapSlot morphism demand slot)).length =
      (bindingsAt demand slot).length := by simp

private theorem typingAt_mem_foundation {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    typingAt demand slot ∈ demand.foundation.typings := by
  apply List.mem_map.mpr
  exact ⟨occurrenceAt demand slot, List.get_mem _ _, rfl⟩

/-- Resolve a retained carrier through the same certified private slot. -/
theorem carrierAt_map_of_mem {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) {object : TypeExpr}
    (retained : object ∈ demand.foundation.carrierObjects.objects) :
    carrierAt (demand.map morphism) (mapTypeExpr morphism.symbols object) =
      carrierAt demand object := by
  unfold carrierAt resolve
  rw [SelectedNativeTypeDemand.map_foundation]
  exact ContextualModalExtension.compiledCarrierName_map_of_mem
    morphism sortInjective demand.foundation retained

private theorem carrierAt_map_required {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {object : TypeExpr}
    (required : object ∈ SelectedNativeTypeFoundation.requiredCarrierRoots
      (typingAt demand slot)) :
    carrierAt (demand.map morphism) (mapTypeExpr morphism.symbols object) =
      carrierAt demand object :=
  carrierAt_map_of_mem morphism sortInjective demand
    (SelectedNativeTypeFoundation.Demand.requiredCarrier_mem_objects
      demand.foundation (typingAt_mem_foundation demand slot) required)

@[simp] theorem focusCarrier_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    carrierAt (demand.map morphism)
        (typingAt (demand.map morphism) (mapSlot morphism demand slot)).focusType =
      carrierAt demand (typingAt demand slot).focusType := by
  rw [typingAt_map]
  apply carrierAt_map_required morphism sortInjective demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

@[simp] theorem resultCarrier_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    carrierAt (demand.map morphism)
        (typingAt (demand.map morphism) (mapSlot morphism demand slot)).rewriteType =
      carrierAt demand (typingAt demand slot).rewriteType := by
  rw [typingAt_map]
  apply carrierAt_map_required morphism sortInjective demand slot
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

private theorem bindingCarrier_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : String × TypeExpr) (membership : binding ∈ bindingsAt demand slot) :
    carrierAt (demand.map morphism) (mapTypeExpr morphism.symbols binding.2) =
      carrierAt demand binding.2 := by
  apply carrierAt_map_required morphism sortInjective demand slot
  have retained : binding.2 ∈ DisplayedContextProfile.carrierTypes
      (typingAt demand slot) := List.mem_map.mpr ⟨binding, membership, rfl⟩
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots, retained]

private theorem profileCode_eq_of_choices_eq
    {source target : ValidatedLanguageDef}
    (first : ProfiledRewriteOccurrence source)
    (second : ProfiledRewriteOccurrence target)
    (choices : first.choices = second.choices)
    (firstIndex : ContextualModalProfile.Slot first.typing)
    (secondIndex : ContextualModalProfile.Slot second.typing)
    (indices : firstIndex.val = secondIndex.val) :
    first.profile firstIndex = second.profile secondIndex := by
  rcases firstIndex with ⟨index, firstBound⟩
  rcases secondIndex with ⟨secondIndex, secondBound⟩
  dsimp at indices
  subst secondIndex
  have read := congrArg (fun wire : List CarrierUniverseSignature.Code => wire[index]?)
    choices
  simpa only [ProfiledRewriteOccurrence.choices, ContextualModalProfile.choices,
    List.getElem?_ofFn, dif_pos firstBound, dif_pos secondBound,
    Option.some.injEq] using read

@[simp] theorem resultCode_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualModalProfile.resultCode
        (occurrenceAt (demand.map morphism) (mapSlot morphism demand slot)).profile =
      ContextualModalProfile.resultCode (occurrenceAt demand slot).profile := by
  apply profileCode_eq_of_choices_eq
  · simp only [occurrenceAt_map, ProfiledRewriteOccurrence.choices_map]
  · change (bindingsAt (demand.map morphism) (mapSlot morphism demand slot)).length =
      (bindingsAt demand slot).length
    exact length_bindingsAt_map morphism demand slot

@[simp] theorem relyTypes_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relyTypes (demand.map morphism) (mapSlot morphism demand slot) =
      relyTypes demand slot := by simp [relyTypes]

@[simp] theorem relyValues_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relyValues (demand.map morphism) (mapSlot morphism demand slot) =
      relyValues demand slot := by simp [relyValues]

@[simp] theorem modalType_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (result : Pattern) :
    modalType (demand.map morphism) (mapSlot morphism demand slot) result =
      modalType demand slot result := by simp [modalType]

@[simp] theorem familyApplication_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (result : Pattern) :
    familyApplication (demand.map morphism) (mapSlot morphism demand slot) result =
      familyApplication demand slot result := by simp [familyApplication]

@[simp] theorem contextPlug_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (focus : Pattern) :
    contextPlug (demand.map morphism) (mapSlot morphism demand slot) focus =
      contextPlug demand slot focus := by simp [contextPlug]

@[simp] theorem predicateApplication_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (predicate focus : Pattern) :
    predicateApplication (demand.map morphism) (mapSlot morphism demand slot)
        predicate focus = predicateApplication demand slot predicate focus := by
  simp [predicateApplication]

@[simp] theorem relyMetavariables_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relyMetavariables (demand.map morphism) (mapSlot morphism demand slot) =
      relyMetavariables demand slot := by simp [relyMetavariables]

private theorem ofFn_profileBindings_map {source target : ValidatedLanguageDef}
    {Result : Type} (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (family : Nat → String → String → CarrierUniverseSignature.Code → Result) :
    (List.ofFn fun index : Fin
        (bindingsAt (demand.map morphism) (mapSlot morphism demand slot)).length =>
      let binding := (bindingsAt (demand.map morphism)
        (mapSlot morphism demand slot)).get index
      family index.val binding.1 (carrierAt (demand.map morphism) binding.2)
        ((occurrenceAt (demand.map morphism) (mapSlot morphism demand slot)).profile
          (ContextualModalProfile.relySlot
            (typingAt (demand.map morphism) (mapSlot morphism demand slot)) index))) =
    (List.ofFn fun index : Fin (bindingsAt demand slot).length =>
      let binding := (bindingsAt demand slot).get index
      family index.val binding.1 (carrierAt demand binding.2)
        ((occurrenceAt demand slot).profile
          (ContextualModalProfile.relySlot (typingAt demand slot) index))) := by
  rw [List.ofFn_congr (length_bindingsAt_map morphism demand slot)]
  apply congrArg List.ofFn
  funext index
  simp only [bindingsAt_map, List.get_eq_getElem, List.getElem_map,
    Fin.val_cast, ContextualModalProfile.relySlot]
  rw [bindingCarrier_map morphism sortInjective demand slot _
    (List.getElem_mem index.isLt)]
  congr 1
  apply profileCode_eq_of_choices_eq
  · simp only [occurrenceAt_map, ProfiledRewriteOccurrence.choices_map]
  · rfl

@[simp] theorem relyVariableClaims_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relyVariableClaims (demand.map morphism) (mapSlot morphism demand slot) =
      relyVariableClaims demand slot := by
  exact ofFn_profileBindings_map morphism sortInjective demand slot
    (fun index _ carrier _ => ContextualCarrierClaims.variableClaim carrier
      (.fvar (relyValueName index)))

@[simp] theorem relyTypingClaims_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relyTypingClaims (demand.map morphism) (mapSlot morphism demand slot) =
      relyTypingClaims demand slot := by
  exact ofFn_profileBindings_map morphism sortInjective demand slot
    (fun index _ carrier _ => ContextualCarrierClaims.typingClaim carrier
      (.fvar (relyValueName index)) (.fvar (relyTypeName index)))

@[simp] theorem relySortPremises_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    relySortPremises (demand.map morphism) (mapSlot morphism demand slot) =
      relySortPremises demand slot := by
  exact ofFn_profileBindings_map (Result := ContextualInference.Sequent)
    morphism sortInjective demand slot
    (fun index _ carrier code =>
      { variableContext := .hole "Gamma"
        relationContext := .hole "Delta"
        conclusion := ContextualCarrierClaims.typingClaim carrier
          (.fvar (relyTypeName index)) (sortCode carrier code) })

@[simp] theorem resultSortPremise_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    resultSortPremise (demand.map morphism) (mapSlot morphism demand slot) =
      resultSortPremise demand slot := by
  simp only [resultSortPremise, resultCarrier_map morphism sortInjective,
    relyVariableClaims_map morphism sortInjective,
    relyTypingClaims_map morphism sortInjective, familyApplication_map,
    resultCode_map]

/-- Formation transports the exact ordered rely premises and profile codes. -/
@[simp] theorem formationRule_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    formationRule (demand.map morphism) (mapSlot morphism demand slot) =
      formationRule demand slot := by
  simp only [formationRule, mapSlot_val, relyMetavariables_map,
    relySortPremises_map morphism sortInjective,
    resultSortPremise_map morphism sortInjective,
    focusCarrier_map morphism sortInjective, modalType_map, resultCode_map]

/-- Introduction retains its actual generic reduction and typing premises. -/
@[simp] theorem introductionRule_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    introductionRule (demand.map morphism) (mapSlot morphism demand slot) =
      introductionRule demand slot := by
  simp only [introductionRule, mapSlot_val, relyMetavariables_map,
    relySortPremises_map morphism sortInjective,
    resultSortPremise_map morphism sortInjective,
    focusCarrier_map morphism sortInjective,
    resultCarrier_map morphism sortInjective,
    relyVariableClaims_map morphism sortInjective,
    relyTypingClaims_map morphism sortInjective,
    familyApplication_map, contextPlug_map, modalType_map]

/-- Elimination retains both ordered contexts and its arbitrary predicate. -/
@[simp] theorem eliminationRule_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    eliminationRule (demand.map morphism) (mapSlot morphism demand slot) =
      eliminationRule demand slot := by
  simp only [eliminationRule, mapSlot_val, relyMetavariables_map,
    relySortPremises_map morphism sortInjective,
    resultSortPremise_map morphism sortInjective,
    focusCarrier_map morphism sortInjective,
    resultCarrier_map morphism sortInjective,
    relyVariableClaims_map morphism sortInjective,
    relyTypingClaims_map morphism sortInjective,
    familyApplication_map, contextPlug_map, modalType_map, predicateApplication_map]

/-- The emitted, lowered formation/introduction/elimination rows transport,
not merely their ids or their number. -/
@[simp] theorem rulesAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    rulesAt (demand.map morphism) (mapSlot morphism demand slot) =
      rulesAt demand slot := by
  simp only [rulesAt, formationRule_map morphism sortInjective,
    introductionRule_map morphism sortInjective,
    eliminationRule_map morphism sortInjective]

/-- Reindexing preserves the entire emitted profile-rule stream, including
authored order, repeated occurrences, premises, and conclusions. -/
theorem profiledRules_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) :
    profiledRules (demand.map morphism) = profiledRules demand := by
  unfold profiledRules
  rw [List.ofFn_congr (show (demand.map morphism).occurrences.length =
      demand.occurrences.length by simp [SelectedNativeTypeDemand.map])]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext slot
  exact rulesAt_map morphism sortInjective demand slot

private theorem map_resolvedBindings {source target : ValidatedLanguageDef}
    {Result : Type} (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (family : String → String → Result) :
    (bindingsAt (demand.map morphism) (mapSlot morphism demand slot)).map
        (fun binding => family binding.1 (carrierAt (demand.map morphism) binding.2)) =
      (bindingsAt demand slot).map
        (fun binding => family binding.1 (carrierAt demand binding.2)) := by
  rw [bindingsAt_map, List.map_map]
  apply List.map_congr_left
  intro binding membership
  simp only [Function.comp_def]
  rw [bindingCarrier_map morphism sortInjective demand slot binding membership]

theorem resultFamilyType_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ContextualModalSignature.resultFamilyType (resolve (demand.map morphism))
        (typingAt (demand.map morphism) (mapSlot morphism demand slot)) =
      ContextualModalSignature.resultFamilyType (resolve demand)
        (typingAt demand slot) := by
  change ContextualModalSignature.curryType
      ((bindingsAt (demand.map morphism) (mapSlot morphism demand slot)).map
        fun binding => .base (carrierAt (demand.map morphism) binding.2))
      (.base (carrierAt (demand.map morphism)
        (typingAt (demand.map morphism) (mapSlot morphism demand slot)).rewriteType)) = _
  rw [resultCarrier_map morphism sortInjective]
  rw [map_resolvedBindings morphism sortInjective demand slot
    (fun _ carrier => TypeExpr.base carrier)]
  rfl

@[simp] theorem familyApplicationTerm_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    familyApplicationTerm (demand.map morphism) (mapSlot morphism demand slot) =
      familyApplicationTerm demand slot := by
  simp only [familyApplicationTerm, mapSlot_val,
    resultCarrier_map morphism sortInjective,
    resultFamilyType_map morphism sortInjective]
  rw [map_resolvedBindings morphism sortInjective demand slot
    (fun name carrier => TermParam.simple ("rely:" ++ name) (.base carrier))]

@[simp] theorem contextPlugTerm_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    contextPlugTerm (demand.map morphism) (mapSlot morphism demand slot) =
      contextPlugTerm demand slot := by
  simp only [contextPlugTerm, mapSlot_val,
    resultCarrier_map morphism sortInjective,
    focusCarrier_map morphism sortInjective]
  rw [map_resolvedBindings morphism sortInjective demand slot
    (fun name carrier => TermParam.simple ("rely:" ++ name) (.base carrier))]

@[simp] theorem predicateApplicationTerm_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    predicateApplicationTerm (demand.map morphism) (mapSlot morphism demand slot) =
      predicateApplicationTerm demand slot := by
  simp only [predicateApplicationTerm, mapSlot_val,
    focusCarrier_map morphism sortInjective]

/-- Every actual support constructor, including the curried result family,
uses the same certified carrier slots after structural reindexing. -/
@[simp] theorem supportTermsAt_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    supportTermsAt (demand.map morphism) (mapSlot morphism demand slot) =
      supportTermsAt demand slot := by
  simp only [supportTermsAt, familyApplicationTerm_map morphism sortInjective,
    contextPlugTerm_map morphism sortInjective,
    predicateApplicationTerm_map morphism sortInjective]

theorem supportTerms_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) :
    supportTerms (demand.map morphism) = supportTerms demand := by
  unfold supportTerms
  rw [List.ofFn_congr (show (demand.map morphism).occurrences.length =
      demand.occurrences.length by simp [SelectedNativeTypeDemand.map])]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext slot
  exact supportTermsAt_map morphism sortInjective demand slot

/-- The existing profile extension keeps its complete constructor and rule
rows; no profile-free projection replaces the authored input. -/
theorem profileExtension_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) :
    profileExtension (demand.map morphism) = profileExtension demand := by
  simp only [profileExtension, supportTerms_map morphism sortInjective,
    profiledRules_map morphism sortInjective]

theorem signature_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) :
    signature (demand.map morphism) =
      { signature demand with name :=
        (ContextualModalSignatureCompiler.base target).name } := by
  unfold signature
  rw [SelectedNativeTypeDemand.map_foundation,
    ContextualModalSignatureCompiler.definition_map morphism sortInjective,
    SelectedNativeTypeFoundation.Demand.stableCarrierNames_map morphism sortInjective]
  rfl

/-- All rows of the existing contextual profile calculus are preserved.
The authored-language name changes explicitly; carrier denotations are not
identified merely because their generated private names agree. -/
theorem definition_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sortInjective : Function.Injective morphism.symbols.sort)
    (demand : SelectedNativeTypeDemand source) :
    definition (demand.map morphism) =
      { definition demand with name :=
        (ContextualModalSignatureCompiler.base target).name } := by
  unfold definition
  rw [profileExtension_map morphism sortInjective, signature_map morphism sortInjective]
  rfl

end SelectedNativeTypeContextualCalculus

namespace SelectedNativeTypeCalculusCompiler

@[simp] theorem singleton_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (occurrence : Input source) :
    singleton (occurrence.map morphism) = (singleton occurrence).map morphism := by
  apply SelectedNativeTypeDemand.ext
  rfl

@[simp] theorem nextDemand_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (compiled : Demand source) (occurrence : Input source) :
    nextDemand (compiled.map morphism) (occurrence.map morphism) =
      (nextDemand compiled occurrence).map morphism := by
  simp [nextDemand, SelectedNativeTypeDemand.map_append]

/-- The actual chronological compiler transports its full profiled state,
not merely the carrier foundation or an unprofiled occurrence list. -/
theorem runFrom_state_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (compiled : Demand source) (occurrences : List (Input source)) :
    ((generator target).runFrom (compiled.map morphism)
        (occurrences.map (ProfiledRewriteOccurrence.map morphism))).1 =
      (((generator source).runFrom compiled occurrences).1).map morphism := by
  rw [runFrom_state, runFrom_state, SelectedNativeTypeDemand.map_append]
  rfl

end SelectedNativeTypeCalculusCompiler

/-! ## Nonidentity source reindexing and profile-sensitive controls -/

namespace ProfiledCalculusTransportCanary

open SelectedNativeTypeContextualCalculus
open ContextualModalSignature.Canary

private def symbols : LanguageDefSymbolMap where
  sort := fun name => "p:" ++ name
  constructor := fun name => "p:" ++ name
  relation := fun name => "p:" ++ name
  equation := fun name => "p:" ++ name
  rewrite := fun name => "p:" ++ name

private def targetLanguage : LanguageDef :=
  StructuralCoproduct.renameLanguage "profiled-calculus-transport-target"
    symbols sourceLanguage

private theorem target_valid : targetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hrewriteValid =>
    intro rewrite membership
    have selected : rewrite = mapRewriteRule symbols contextualRewrite := by
      simpa [targetLanguage, StructuralCoproduct.renameLanguage, sourceLanguage]
        using membership
    subst rewrite
    simp [LanguageDef.validateRewrite, targetLanguage,
      StructuralCoproduct.renameLanguage, sourceLanguage,
      mapRewriteRule, mapTypeContext, mapPattern, mapPatternList,
      mapTypeDecl, mapGrammarRule, mapTermParam, mapTypeExpr, symbols,
      contextualRewrite, ternaryTerm, termType,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name membership
    simpa [TypeExpr.baseNames] using membership

private def target : ValidatedLanguageDef := ⟨targetLanguage, target_valid⟩

private def morphism : StructuralMorphism source target where
  symbols := symbols
  mapsTypes _ membership := List.mem_map_of_mem membership
  mapsTerms _ membership := List.mem_map_of_mem membership
  mapsEquations _ membership := List.mem_map_of_mem membership
  mapsRewrites _ membership := List.mem_map_of_mem membership

private theorem sortInjective : Function.Injective morphism.symbols.sort := by
  intro first second same
  exact (String.append_right_inj "p:").mp same

/-- The source carrier really moves; the row-preservation test is not an
identity-map instance. -/
theorem source_carrier_changes :
    mapTypeExpr morphism.symbols middleTyping.focusType ≠ middleTyping.focusType := by
  decide +kernel

/-- Both local endpoints transport complete, lowered contextual rule rows. -/
theorem profile_rows_transport (code : CarrierUniverseSignature.Code) :
    profiledRules ((Canary.middleDemand code).map morphism) =
      profiledRules (Canary.middleDemand code) :=
  profiledRules_map morphism sortInjective _

/-- Reindexing cannot erase the distinction between star and box rules,
even though their profile-free generated signatures agree. -/
theorem different_profiles_remain_distinct :
    profiledRules ((Canary.middleDemand .star).map morphism) ≠
      profiledRules ((Canary.middleDemand .box).map morphism) := by
  rw [profiledRules_map morphism sortInjective,
    profiledRules_map morphism sortInjective]
  exact Canary.middle_endpoint_rules_distinct

/-- One real chronological run carries two differently profiled occurrences
and their exact order through the source namespace change. -/
theorem chronological_state_transport :
    ((SelectedNativeTypeCalculusCompiler.generator target).runFrom
        (SelectedNativeTypeDemand.empty target)
        [(Canary.middleOccurrence .star).map morphism,
          (Canary.middleOccurrence .box).map morphism]).1 =
      (((SelectedNativeTypeCalculusCompiler.generator source).runFrom
        (SelectedNativeTypeDemand.empty source)
        [Canary.middleOccurrence .star, Canary.middleOccurrence .box]).1).map morphism := by
  simpa only [SelectedNativeTypeDemand.map_empty, List.map_cons, List.map_nil] using
    (SelectedNativeTypeCalculusCompiler.runFrom_state_map morphism
      (SelectedNativeTypeDemand.empty source)
      [Canary.middleOccurrence .star, Canary.middleOccurrence .box])

end ProfiledCalculusTransportCanary

#print axioms SelectedNativeTypeContextualCalculus.formationRule_map
#print axioms SelectedNativeTypeContextualCalculus.introductionRule_map
#print axioms SelectedNativeTypeContextualCalculus.eliminationRule_map
#print axioms SelectedNativeTypeContextualCalculus.profiledRules_map
#print axioms SelectedNativeTypeContextualCalculus.supportTerms_map
#print axioms SelectedNativeTypeContextualCalculus.definition_map
#print axioms SelectedNativeTypeCalculusCompiler.runFrom_state_map
#print axioms ProfiledCalculusTransportCanary.source_carrier_changes
#print axioms ProfiledCalculusTransportCanary.different_profiles_remain_distinct
#print axioms ProfiledCalculusTransportCanary.chronological_state_transport

end Mettapedia.OSLF.Framework
