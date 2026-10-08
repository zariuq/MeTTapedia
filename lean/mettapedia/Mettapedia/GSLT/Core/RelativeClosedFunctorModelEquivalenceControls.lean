import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorModelNaturality
import Mettapedia.GSLT.Core.RelativeClosedTheoryModelActionControls

/-!
# Independent function values in the coherent universal comparison

A supplied weak closed diagram has a genuinely wrapped Boolean carrier.
The inverse category equivalence reconstructs its primitive meanings and
complete curried function through the independent evaluator. The resulting
function retains its supplied second argument. The actual equivalence unit
and counit are also evaluated at the independently supplied model and map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedFunctorModelEquivalenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation SemanticModels ClosedModels
open RelativeClosedInterpretationPreservationControls
open RelativeClosedFunctorReconstructionControls

def supplied : Diagram signature Type :=
  ⟨weak, RelativeClosedFunctorNormalizationControls.weak_lex,
    RelativeClosedFunctorNormalizationControls.weak_closed⟩

def rebuilt : Model signature Type :=
  (FunctorModelEquivalence.equivalence headers).inverse.obj supplied

theorem actual_supplied_diagram_comparison :
    ((FunctorModelEquivalence.equivalence headers).counitIso.hom.app supplied) =
      (FunctorModelEquivalence.comparison headers supplied).inv := rfl

theorem actual_independent_model_recovered :
    (FunctorModelEquivalence.equivalence headers).inverse.obj
      ((FunctorModelEquivalence.equivalence headers).functor.obj
        RelativeClosedTheoryModelActionControls.model) = RelativeClosedTheoryModelActionControls.model :=
  FunctorModelEquivalence.complete_model_recovered headers _

theorem independent_primitive_readout : rebuilt.meanings.evaluateObject (.name ()) =
    some (ULift Bool) := primitive_type_read

theorem independent_function_readout : rebuilt.meanings.evaluateArrow curried.code =
    some (⟨ULift Bool, ULift Bool ⟶[Type] ULift Bool, nativeCurried⟩ : ArrowValue Type) :=
  complete_curried_read

theorem recovered_carrier : rebuilt.diagram.obj dataObject = ULift Bool :=
  objectValue_unique rebuilt.meanings rebuilt.realization dataObject _ independent_primitive_readout

theorem recovered_function_object : rebuilt.diagram.obj (exponentialObject dataObject dataObject) =
    ULift Bool ⟶[Type] ULift Bool :=
  objectValue_unique rebuilt.meanings rebuilt.realization (exponentialObject dataObject dataObject) _
    (rebuilt.meanings.evaluate_exponential independent_primitive_readout independent_primitive_readout)

def completeRecoveredFunction : ULift Bool ⟶ (ULift Bool ⟶ ULift Bool) :=
  eqToHom recovered_carrier.symm ≫ rebuilt.diagram.map (classOf curried) ≫
    eqToHom recovered_function_object

theorem completeRecoveredFunction_readout : completeRecoveredFunction = nativeCurried :=
  ((conj_eqToHom_iff_heq nativeCurried (rebuilt.diagram.map (classOf curried))
    recovered_carrier.symm recovered_function_object.symm).mpr
      (functor_map_heq rebuilt.meanings rebuilt.realization curried nativeCurried
        independent_function_readout).symm).symm

theorem both_supplied_arguments_retained (context argument : Bool) :
    completeRecoveredFunction (ULift.up context) (ULift.up argument) = ULift.up (Bool.not argument) :=
  (congrArg (fun arrow : ULift Bool ⟶ (ULift Bool ⟶ ULift Bool) =>
    arrow (ULift.up context) (ULift.up argument)) completeRecoveredFunction_readout).trans
      (supplied_argument_readout context argument)

theorem dropped_argument_rejected :
    completeRecoveredFunction (ULift.up false) (ULift.up false) ≠
      completeRecoveredFunction (ULift.up false) (ULift.up true) := by
  intro same
  have read := congrArg ULift.down same
  rw [both_supplied_arguments_retained, both_supplied_arguments_retained] at read
  exact Bool.false_ne_true read.symm

theorem supplied_diagram_triangle :
    (FunctorModelEquivalence.equivalence headers).functor.map
        ((FunctorModelEquivalence.equivalence headers).unitIso.hom.app rebuilt) ≫
      (FunctorModelEquivalence.equivalence headers).counitIso.hom.app
        ((FunctorModelEquivalence.equivalence headers).functor.obj rebuilt) =
          𝟙 ((FunctorModelEquivalence.equivalence headers).functor.obj rebuilt) :=
  (FunctorModelEquivalence.equivalence headers).functor_unitIso_comp rebuilt

def actual_weak_target_square :
    ClosedModels.interpretation ⋙ ClosedModels.postcompose RelativeClosedTheoryModelActionControls.raised ≅
      AssignmentTransportAction.action headers RelativeClosedTheoryModelActionControls.raised ⋙
        ClosedModels.interpretation :=
  FunctorModelEquivalence.interpretationComparison headers RelativeClosedTheoryModelActionControls.raised

end Mettapedia.GSLT.Core.RelativeClosedFunctorModelEquivalenceControls
