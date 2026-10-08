import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationRealization
import Mettapedia.GSLT.Core.RelativeClosedFunctorNormalizationControls

/-!
# Complete reconstructed functions and independent arrow classes

A genuinely weak `ULift` presentation is reconstructed through the actual
independent evaluator. The annotated function body uses its supplied second
coordinate and the declared negation. Its complete curried function retains
both distinct argument values. Independent identity and negation origins also
give different generated quotient classes, not merely different raw codes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedFunctorReconstructionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation FunctorNormalization
open RelativeClosedInterpretationPreservationControls

abbrev weak := RelativeClosedFunctorNormalizationControls.weak

def headers : HeaderFormation signature where
  source _ := by
    change Derivation signature (.object (.name ()))
    exact .objectName (signature := signature) ()
  target _ := by
    change Derivation signature (.object (.name ()))
    exact .objectName (signature := signature) ()
  left origin := origin.elim
  right origin := origin.elim

abbrev reconstructedAssignment := assignment weak headers

theorem primitive_type_read : reconstructedAssignment.evaluateObject (.name ()) = some (ULift Bool) :=
  (object_reconstruction weak headers dataObject).trans
    (congrArg some RelativeClosedFunctorNormalizationControls.normalized_data_object)

theorem primitive_negation_read : reconstructedAssignment.evaluateArrow (.name true) =
    some (⟨ULift Bool, ULift Bool, RelativeClosedFunctorNormalizationControls.normalizedNegation⟩ : ArrowValue Type) :=
  (raw_arrow_reconstruction weak headers (namedRaw true)).trans
    (congrArg some (arrowValue_transport ((normalizedFunctor weak).map (declared true))
      RelativeClosedFunctorNormalizationControls.normalized_data_object
      RelativeClosedFunctorNormalizationControls.normalized_data_object))

def body : RawHom (product dataObject dataObject) dataObject :=
  RawHom.compose
    ⟨.second dataObject.code dataObject.code,
      ⟨.second dataObject.formed.some dataObject.formed.some⟩⟩ (namedRaw true)

def nativeBody : (ULift Bool ⊗ ULift Bool) ⟶ ULift Bool :=
  CartesianMonoidalCategory.snd (ULift Bool) (ULift Bool) ≫
    RelativeClosedFunctorNormalizationControls.normalizedNegation

theorem complete_body_read : reconstructedAssignment.evaluateArrow body.code =
    some (⟨ULift Bool ⊗ ULift Bool, ULift Bool, nativeBody⟩ : ArrowValue Type) :=
  reconstructedAssignment.evaluate_compose _ _
    (reconstructedAssignment.evaluate_second primitive_type_read primitive_type_read) primitive_negation_read

def curried : RawHom dataObject (exponentialObject dataObject dataObject) :=
  ⟨.curry dataObject.code dataObject.code dataObject.code body.code,
    ⟨.curry dataObject.formed.some dataObject.formed.some dataObject.formed.some body.admitted.some⟩⟩

def nativeCurried : ULift Bool ⟶ (ULift Bool ⟶ ULift Bool) := Interpretation.abstraction nativeBody

theorem complete_curried_read : reconstructedAssignment.evaluateArrow curried.code =
    some (⟨ULift Bool, ULift Bool ⟶[Type] ULift Bool, nativeCurried⟩ : ArrowValue Type) :=
  reconstructedAssignment.evaluate_abstraction nativeBody primitive_type_read primitive_type_read
    primitive_type_read complete_body_read

theorem complete_curried_functor_image : HEq ((normalizedFunctor weak).map (classOf curried)) nativeCurried :=
  ArrowValue.arrows_heq (Option.some.inj
    ((raw_arrow_reconstruction weak headers curried).symm.trans complete_curried_read))

theorem supplied_argument_readout (context argument : Bool) :
    nativeCurried (ULift.up context) (ULift.up argument) = ULift.up (Bool.not argument) := by
  change RelativeClosedFunctorNormalizationControls.normalizedNegation (ULift.up argument) = _
  exact RelativeClosedFunctorNormalizationControls.normalizedNegation_readout argument

theorem both_complete_argument_values_retained :
    (nativeCurried (ULift.up false) (ULift.up false)).down = true ∧
    (nativeCurried (ULift.up false) (ULift.up true)).down = false :=
  ⟨congrArg ULift.down (supplied_argument_readout false false),
    congrArg ULift.down (supplied_argument_readout false true)⟩

theorem omitted_second_argument_rejected :
    (nativeCurried (ULift.up false) (ULift.up false)).down ≠
      (nativeCurried (ULift.up false) (ULift.up true)).down := by
  rw [both_complete_argument_values_retained.1, both_complete_argument_values_retained.2]
  exact Ne.symm Bool.false_ne_true

theorem distinct_arrow_origins_give_distinct_classes : declared false ≠ declared true := by
  intro same
  have readout := congrArg (fun arrow : dataObject ⟶ dataObject =>
    weak.map arrow (ULift.up false)) same
  have identityRead : weak.map (declared false) (ULift.up false) = ULift.up false := by
    change ULift.up (interpreted.map (declared false) false) = _
    rw [actual_identity]
    rfl
  rw [identityRead, RelativeClosedFunctorNormalizationControls.wrapped_negation] at readout
  exact Bool.false_ne_true (congrArg ULift.down readout)

instance reconstructed_lex : PreservesFiniteLimits (reconstructedFunctor weak headers) :=
  preservesFiniteLimits_of_natIso (parserComparison weak headers)

theorem reconstructed_is_closed : MonoidalClosedFunctor (reconstructedFunctor weak headers) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_of_naturalIso
    (parserComparison weak headers).symm

def actualWeakParserComparison : weak ≅ reconstructedFunctor weak headers := parserComparison weak headers

end Mettapedia.GSLT.Core.RelativeClosedFunctorReconstructionControls
