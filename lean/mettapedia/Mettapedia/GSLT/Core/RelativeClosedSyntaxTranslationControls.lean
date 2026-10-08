import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationComposition
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationModels
import Mettapedia.GSLT.Core.RelativeClosedFunctorReconstructionControls

/-!
# Complete context-expression translation controls

A declared object becomes a function object, and declared negation becomes
an abstraction whose body evaluates the supplied function and then negates
its result. The native readout retains the supplied function and argument.
The target's scalar negation name cannot inhabit the translated function
header. Identity and composition read the actual generated quotient functors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedSyntaxTranslationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation
open RelativeClosedInterpretationPreservationControls

abbrev headers := RelativeClosedFunctorReconstructionControls.headers

def functionCode : ObjectCode Base names := .exponential (.name ()) (.name ())

def actionCode : ArrowCode Base names :=
  .curry functionCode (.name ()) (.name ())
    (.compose (.evaluation (.name ()) (.name ())) (.name true))

def data : TranslationData (C := Base) (symbols := names) (D := Base) (nextSymbols := names) where
  base := 𝟭 Base
  objects _ := functionCode
  arrows origin := if origin then actionCode else .identity functionCode

def dataFormed : Derivation signature (.object (.name ())) :=
  .objectName (signature := signature) ()

def functionFormed : Derivation signature (.object functionCode) :=
  .exponentialObject dataFormed dataFormed

def translation : Translation signature signature where
  data := data
  objectTyped _ := functionFormed
  arrowTyped origin := by
    cases origin with
    | false => exact .identity functionFormed
    | true =>
      change Derivation signature (.arrow functionCode functionCode actionCode)
      exact .curry functionFormed dataFormed dataFormed
        (.compose (.evaluation dataFormed dataFormed)
          (.arrowName (signature := signature) true dataFormed dataFormed))
  equationTyped origin := origin.elim

theorem object_translation_is_not_a_name (origin : names.ObjectName) :
    translation.data.objects () ≠ .name origin := by
  intro same
  cases same

theorem scalar_name_cannot_supply_function_header :
    ¬ Nonempty (Derivation signature (.arrow functionCode functionCode (.name true))) := by
  rintro ⟨tree⟩
  cases tree

def nativeAction : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) :=
  Interpretation.abstraction (Interpretation.evaluation Bool Bool ≫ negate)

theorem nativeAction_readout (function : Bool ⟶ Bool) (input : Bool) :
    nativeAction function input = Bool.not (function input) := rfl

theorem function_evaluated : meanings.evaluateObject functionCode = some (Bool ⟶ Bool) :=
  meanings.evaluate_exponential (meanings.evaluate_object_name ()) (meanings.evaluate_object_name ())

theorem action_evaluated : meanings.evaluateArrow actionCode =
    some ⟨(Bool ⟶ Bool), (Bool ⟶ Bool), nativeAction⟩ :=
  meanings.evaluate_abstraction _ function_evaluated
    (meanings.evaluate_object_name ()) (meanings.evaluate_object_name ())
    (meanings.evaluate_compose _ _
      (meanings.evaluate_evaluation (meanings.evaluate_object_name ()) (meanings.evaluate_object_name ()))
      (meanings.evaluate_arrow_name true))

theorem complete_translated_action :
    HEq ((translation.functor ⋙ interpreted).map (declared true)) nativeAction :=
  functor_map_heq meanings realized (translation.rawArrow (namedRaw true)) nativeAction action_evaluated

theorem translated_object_readout :
    (translation.functor ⋙ interpreted).obj dataObject = (Bool ⟶ Bool) :=
  objectValue_unique meanings realized (translation.object dataObject) _ function_evaluated

def translatedAction : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) :=
  eqToHom translated_object_readout.symm ≫
    (translation.functor ⋙ interpreted).map (declared true) ≫ eqToHom translated_object_readout

theorem translatedAction_complete : translatedAction = nativeAction := by
  have actual := (conj_eqToHom_iff_heq _ _ translated_object_readout translated_object_readout).mpr
    complete_translated_action
  unfold translatedAction
  rw [actual]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem actual_supplied_function_and_argument (function : Bool ⟶ Bool) (input : Bool) :
    translatedAction function input = Bool.not (function input) := by
  rw [translatedAction_complete]
  exact nativeAction_readout function input

theorem second_argument_retained :
    translatedAction (𝟙 Bool) false = true ∧ translatedAction (𝟙 Bool) true = false :=
  ⟨actual_supplied_function_and_argument (𝟙 Bool) false,
    actual_supplied_function_and_argument (𝟙 Bool) true⟩

theorem supplied_function_retained :
    translatedAction negate false = false ∧ translatedAction (𝟙 Bool) false = true :=
  ⟨actual_supplied_function_and_argument negate false,
    actual_supplied_function_and_argument (𝟙 Bool) false⟩

theorem dropping_argument_rejected :
    translatedAction (𝟙 Bool) false ≠ translatedAction (𝟙 Bool) true := by
  rw [second_argument_retained.1, second_argument_retained.2]
  exact Bool.false_ne_true.symm

theorem dropping_function_rejected :
    translatedAction negate false ≠ translatedAction (𝟙 Bool) false := by
  rw [supplied_function_retained.1, supplied_function_retained.2]
  exact Bool.false_ne_true

theorem actual_identity_functor : (Translation.identity headers).functor = 𝟭 (Object signature) :=
  Translation.functor_identity headers

theorem actual_composite_functor :
    translation.functor ⋙ translation.functor = (translation.compose translation).functor :=
  Translation.functor_compose translation translation

theorem composed_object_has_two_function_layers :
    ((translation.compose translation).object dataObject).code =
      .exponential functionCode functionCode := rfl

theorem exact_semantic_restriction :
    translation.functor ⋙ interpreted =
      Interpretation.functor (translation.precompose meanings realized)
        (translation.realization_precompose meanings realized) :=
  translation.functor_precompose meanings realized

def targetModel : SemanticModels.Model signature Type := ⟨meanings, realized⟩

def restrictedModel : SemanticModels.Model signature Type :=
  translation.precomposeModels.obj targetModel

theorem restricted_model_complete_action :
    restrictedModel.meanings.evaluateArrow (.name true) =
      some ⟨(Bool ⟶ Bool), (Bool ⟶ Bool), nativeAction⟩ :=
  (translation.evaluateArrow_precompose meanings realized (.name true)).symm.trans action_evaluated

def complete_restricted_diagram :
    translation.functor ⋙ targetModel.diagram ≅ restrictedModel.diagram :=
  translation.precomposeComparison targetModel

theorem actual_finite_limits : PreservesFiniteLimits translation.functor := inferInstance

theorem actual_closed : MonoidalClosedFunctor translation.functor := inferInstance

end Mettapedia.GSLT.Core.RelativeClosedSyntaxTranslationControls
