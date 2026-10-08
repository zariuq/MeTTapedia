import Mettapedia.GSLT.Core.RelativeClosedTheoryModelAction
import Mettapedia.GSLT.Core.RelativeClosedFunctorReconstructionControls

/-!
# Complete values through the coherent weak model action

The actual value-lift functor is applied twice to an independently supplied
Boolean model. A declared negation retains both argument values; the
composition comparison relates the independently transported diagrams.
The genuine lift-to-identity natural cell also retains the supplied value.
Replacing the complete result by a constant is independently rejected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedTheoryModelActionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation SemanticModels AssignmentTransportAction
open RelativeClosedInterpretationPreservationControls

abbrev headers := RelativeClosedFunctorReconstructionControls.headers

def model : Model signature Type := ⟨meanings, realized⟩

abbrev raised : Type ⥤ Type := uliftFunctor.{0,0}

private instance raised_lex : PreservesFiniteLimits raised :=
  preservesFiniteLimits_of_natIso uliftFunctorTrivial.symm

private instance raised_closed : MonoidalClosedFunctor raised :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_of_naturalIso uliftFunctorTrivial

private instance composite_lex : PreservesFiniteLimits (raised ⋙ raised) :=
  comp_preservesFiniteLimits raised raised

private instance composite_closed : MonoidalClosedFunctor (raised ⋙ raised) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition raised raised

def firstModel : Model signature Type := image headers raised model
def twiceModel : Model signature Type := image headers raised firstModel
def compositeModel : Model signature Type := image headers (raised ⋙ raised) model

def firstValue (value : Bool) : firstModel.diagram.obj dataObject :=
  (comparison headers raised model).hom.app dataObject (ULift.up value)

def twiceValue (value : Bool) : twiceModel.diagram.obj dataObject :=
  (comparison headers raised firstModel).hom.app dataObject (ULift.up (firstValue value))

def compositeValue (value : Bool) : compositeModel.diagram.obj dataObject :=
  (comparison headers (raised ⋙ raised) model).hom.app dataObject (ULift.up (ULift.up value))

def completeReadout (value : compositeModel.diagram.obj dataObject) : Bool :=
  ((comparison headers (raised ⋙ raised) model).inv.app dataObject value).down.down

theorem supplied_value_retained (value : Bool) : completeReadout (compositeValue value) = value := by
  exact congrArg (fun arrow : ULift (ULift Bool) ⟶ ULift (ULift Bool) =>
    (arrow (ULift.up (ULift.up value))).down.down)
      (Iso.hom_inv_id_app (comparison headers (raised ⋙ raised) model) dataObject)

theorem negation_value_retained (value : Bool) :
    compositeModel.diagram.map (declared true) (compositeValue value) = compositeValue (Bool.not value) := by
  have natural := (comparison headers (raised ⋙ raised) model).hom.naturality (declared true)
  have supplied := congrArg
    (fun arrow : ULift (ULift Bool) ⟶ compositeModel.diagram.obj dataObject =>
      arrow (ULift.up (ULift.up value))) natural
  change (comparison headers (raised ⋙ raised) model).hom.app dataObject
      (ULift.up (ULift.up (interpreted.map (declared true) value))) =
    compositeModel.diagram.map (declared true) (compositeValue value) at supplied
  rw [actual_negation] at supplied
  exact supplied.symm

theorem actual_composite_negation_readout (value : Bool) :
    completeReadout (compositeModel.diagram.map (declared true) (compositeValue value)) =
      Bool.not value :=
  (congrArg completeReadout (negation_value_retained value)).trans
    (supplied_value_retained (Bool.not value))

theorem composition_retains_complete_value (value : Bool) :
    (compositionAt headers raised raised model).hom.app dataObject (compositeValue value) =
      twiceValue value := by
  have cancellation := congrArg
    (fun arrow : ULift (ULift Bool) ⟶ ULift (ULift Bool) =>
      arrow (ULift.up (ULift.up value)))
    (Iso.hom_inv_id_app (comparison headers (raised ⋙ raised) model) dataObject)
  change (comparison headers raised firstModel).hom.app dataObject
      (ULift.up ((comparison headers raised model).hom.app dataObject
        (((comparison headers (raised ⋙ raised) model).inv.app dataObject
          (compositeValue value)).down))) = twiceValue value
  change (comparison headers (raised ⋙ raised) model).inv.app dataObject
      (compositeValue value) = ULift.up (ULift.up value) at cancellation
  rw [cancellation]
  rfl

theorem constant_composite_replacement_rejected :
    compositeModel.diagram.map (declared true) (compositeValue false) ≠
      compositeModel.diagram.map (declared true) (compositeValue true) := by
  intro same
  have read := congrArg completeReadout same
  rw [actual_composite_negation_readout, actual_composite_negation_readout] at read
  exact Bool.false_ne_true read.symm

def identityValue (value : Bool) : (image headers (𝟭 Type) model).diagram.obj dataObject :=
  (comparison headers (𝟭 Type) model).hom.app dataObject value

theorem target_cell_retains_supplied_value (value : Bool) :
    ((change headers uliftFunctorTrivial.hom).app model).app dataObject (firstValue value) =
      identityValue value := by
  have cancellation := congrArg (fun arrow : ULift Bool ⟶ ULift Bool => arrow (ULift.up value))
    (Iso.hom_inv_id_app (comparison headers raised model) dataObject)
  change (comparison headers (𝟭 Type) model).hom.app dataObject
      (((comparison headers raised model).inv.app dataObject (firstValue value)).down) = _
  change (comparison headers raised model).inv.app dataObject (firstValue value) = ULift.up value
    at cancellation
  rw [cancellation]
  rfl

theorem target_cell_complete_readout (value : Bool) :
    (comparison headers (𝟭 Type) model).inv.app dataObject
      (((change headers uliftFunctorTrivial.hom).app model).app dataObject (firstValue value)) = value := by
  rw [target_cell_retains_supplied_value]
  exact congrArg (fun arrow : Bool ⟶ Bool => arrow value)
    (Iso.hom_inv_id_app (comparison headers (𝟭 Type) model) dataObject)

theorem constant_target_cell_rejected :
    ((change headers uliftFunctorTrivial.hom).app model).app dataObject (firstValue false) ≠
      ((change headers uliftFunctorTrivial.hom).app model).app dataObject (firstValue true) := by
  intro same
  have read := congrArg ((comparison headers (𝟭 Type) model).inv.app dataObject) same
  rw [target_cell_complete_readout, target_cell_complete_readout] at read
  exact Bool.false_ne_true read

def nativeTheory : LambdaTheory.{1,0} := LambdaTheory.ofCategory Type

def raisedMap : LambdaTheoryMap nativeTheory nativeTheory where
  functor := raised
  preservesFiniteLimits := raised_lex
  preservesExponentials := raised_closed

def actualModelAction : Pseudofunctor LambdaTheory.{1,0} Cat.{0,1} :=
  RelativeClosedTheoryModelAction.action headers

theorem actual_theory_route : actualModelAction.map raisedMap =
    (AssignmentTransportAction.action headers raised).toCatHom := rfl

end Mettapedia.GSLT.Core.RelativeClosedTheoryModelActionControls
