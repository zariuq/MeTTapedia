import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeCoherence
import Mettapedia.GSLT.Core.RelativeClosedSyntaxNativeTranslationControls

/-!
# Complete native coherence and raw-choice separators

The actual weak Boolean-order map retains negation through two independent
restrictions and the direct coded composite. Unit and association controls
instantiate the genuine whole-functor comparisons. A formed equalizer of
the supplied native terminal inverse has a different raw code after native
identity translation, while the earned identity comparison gives its actual
isomorphism. Coherence therefore retains choices rather than erasing them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedSyntaxNativeCoherenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.CategoryTheory
open GeneratedCategory Interpretation
open RelativeClosedWeakBaseControls RelativeClosedSyntaxTranslationBaseControls

private instance translated_base_lex : PreservesFiniteLimits translation.data.base := by
  change PreservesFiniteLimits weakBase
  infer_instance

private instance translated_base_closed : MonoidalClosedFunctor translation.data.base := by
  change MonoidalClosedFunctor weakBase
  infer_instance

private instance composite_base_lex : PreservesFiniteLimits (translation.compose translation).data.base :=
  comp_preservesFiniteLimits translation.data.base translation.data.base

private instance composite_base_closed : MonoidalClosedFunctor (translation.compose translation).data.base :=
  CartesianClosedFunctorCoherence.closed_composition translation.data.base translation.data.base

def twice : SemanticModels.Model augmented Type :=
  (Translation.NativeExtension.extended translation).precomposeModel
    ((Translation.NativeExtension.extended translation).precomposeModel independentAugmentedModel)

def composed : SemanticModels.Model augmented Type :=
  (Translation.NativeExtension.extended (translation.compose translation)).precomposeModel independentAugmentedModel

theorem complete_model_composition : twice = composed :=
  Translation.NativeModelAction.compose_model translation translation independentAugmentedModel

theorem full_negation_composed :
    composed.meanings.evaluateArrow (BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true)) =
      some (⟨ULift Bool, ULift Bool, negate⟩ : ArrowValue Type) := by
  let once := (Translation.NativeExtension.extended translation).precomposeModel independentAugmentedModel
  let code := BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true)
  have firstRead : once.meanings.evaluateArrow code = some (⟨ULift Bool, ULift Bool, negate⟩ : ArrowValue Type) :=
    ((Translation.NativeExtension.extended translation).evaluateArrow_precompose
      extended extended_realized code).symm.trans supplied_negation_read
  have secondRead : twice.meanings.evaluateArrow code = some (⟨ULift Bool, ULift Bool, negate⟩ : ArrowValue Type) :=
    ((Translation.NativeExtension.extended translation).evaluateArrow_precompose
      once.meanings once.realization code).symm.trans firstRead
  have same := congrArg
    (fun model : SemanticModels.Model augmented Type => model.meanings.evaluateArrow
      (BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true))) complete_model_composition
  exact same.symm.trans secondRead

def composedNegation : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom (objectValue_unique composed.meanings composed.realization dataObject (ULift Bool) rfl).symm ≫
    composed.diagram.map (classOf originalNegation) ≫
      eqToHom (objectValue_unique composed.meanings composed.realization dataObject (ULift Bool) rfl)

private theorem retained_loop {source target : Type} (before : source ⟶ source) (after : target ⟶ target)
    (objects : source = target)
    (value : (⟨source, source, before⟩ : ArrowValue Type) = ⟨target, target, after⟩) :
    eqToHom objects.symm ≫ before ≫ eqToHom objects = after := by
  cases objects
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ArrowValue.arrow_injective value

theorem composed_negation_readout : composedNegation = negate :=
  retained_loop (composed.diagram.map (classOf originalNegation)) negate
    (objectValue_unique composed.meanings composed.realization dataObject (ULift Bool) rfl)
    (Option.some.inj ((functor_complete_readout composed.meanings composed.realization originalNegation).symm.trans
      full_negation_composed))

theorem supplied_values_survive_composition :
    (composedNegation (ULift.up false)).down = true ∧
      (composedNegation (ULift.up true)).down = false := by
  rw [composed_negation_readout]
  exact ⟨rfl, rfl⟩

theorem constant_composite_rejected :
    composedNegation (ULift.up false) ≠ composedNegation (ULift.up true) := by
  intro same
  have read := congrArg ULift.down same
  rw [supplied_values_survive_composition.1, supplied_values_survive_composition.2] at read
  exact Bool.false_ne_true read.symm

theorem actual_left_unit :
    Translation.NativeCoherence.leftUnit translation headers headers =
      Functor.isoWhiskerRight (Translation.NativeComparison.identity headers)
          (Translation.NativeExtension.extended translation).functor ≪≫
        Functor.leftUnitor (Translation.NativeExtension.extended translation).functor :=
  Translation.NativeCoherence.left_unit_coherence translation headers headers

theorem actual_right_unit :
    Translation.NativeCoherence.rightUnit translation headers =
      Functor.isoWhiskerLeft (Translation.NativeExtension.extended translation).functor
          (Translation.NativeComparison.identity headers) ≪≫
        Functor.rightUnitor (Translation.NativeExtension.extended translation).functor :=
  Translation.NativeCoherence.right_unit_coherence translation headers

theorem actual_association :
    Translation.NativeCoherence.associateLeft translation translation translation headers headers =
      Translation.NativeCoherence.associateRight translation translation translation headers :=
  Translation.NativeCoherence.associativity_coherence translation translation translation headers headers

def inverseTyped : Derivation augmented
    (.arrow .terminal (.base (𝟙_ Bool)) (.name (.inl .terminal))) :=
  .arrowName (signature := augmented) (.inl .terminal) .terminalObject (.baseObject (𝟙_ Bool))

def chosenEqualizer : Object augmented :=
  ⟨.equalizer .terminal (.base (𝟙_ Bool)) (.name (.inl .terminal)) (.name (.inl .terminal)),
    ⟨.equalizerObject .terminalObject (.baseObject (𝟙_ Bool)) inverseTyped inverseTyped⟩⟩

theorem native_identity_keeps_distinct_raw_choice :
    (Translation.NativeExtension.extended (Translation.identity headers)).object chosenEqualizer ≠ chosenEqualizer := by
  intro same
  have codes := congrArg Object.code same
  let changed : ArrowCode Bool (BaseExtension.extendedSymbols Bool names) :=
    Translation.NativeData.inverseCode (Translation.identity headers) .terminal
  change ObjectCode.equalizer .terminal (.base (𝟙_ Bool)) changed changed =
    (ObjectCode.equalizer .terminal (.base (𝟙_ Bool)) (.name (.inl .terminal)) (.name (.inl .terminal)) :
      ObjectCode Bool (BaseExtension.extendedSymbols Bool names)) at codes
  have premises := ObjectCode.equalizer.inj codes
  have impossible := premises.2.2.1
  change (ArrowCode.compose (.name (.inl .terminal))
    (.base (inv (CartesianMonoidalCategory.terminalComparison (𝟭 Bool)))) :
      ArrowCode Bool (BaseExtension.extendedSymbols Bool names)) =
      (ArrowCode.name (.inl .terminal) : ArrowCode Bool (BaseExtension.extendedSymbols Bool names)) at impossible
  cases impossible

theorem literal_identity_functor_rejected :
    (Translation.NativeExtension.extended (Translation.identity headers)).functor ≠ 𝟭 (Object augmented) := by
  intro same
  exact native_identity_keeps_distinct_raw_choice (Functor.congr_obj same chosenEqualizer)

def chosenEqualizerComparison :
    (Translation.NativeExtension.extended (Translation.identity headers)).object chosenEqualizer ≅ chosenEqualizer :=
  (Translation.NativeComparison.identity headers).app chosenEqualizer

theorem actual_chosen_comparison_inverse :
    chosenEqualizerComparison.hom ≫ chosenEqualizerComparison.inv =
      𝟙 ((Translation.NativeExtension.extended (Translation.identity headers)).object chosenEqualizer) :=
  chosenEqualizerComparison.hom_inv_id

end Mettapedia.GSLT.Core.RelativeClosedSyntaxNativeCoherenceControls
