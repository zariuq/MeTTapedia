import Mettapedia.TypeTheory.PresheafNativeLogicalCells
import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherenceControls

/-!
# Whole-function readouts through the native product cell

The incoming route has proved future-argument coverage. A multiplication
theory cell changes the future arrow at which an independently supplied ray
function is read. The complete native receipt is encoded, acted on by the
native product cell, decoded, and applied at a genuine future arrow. This
distinguishes both the theory cell and the supplied function witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeProductCellControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafPi
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation DisplayedPresheafTheoryTransformationCoherence
open DisplayedPresheafProductTransformationCoherence DependentProductNativeComparison
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open PresheafNativeLogicalCells
open DisplayedPresheafProductTransformationCoherenceControls.Covered

abbrev argument : NativeType scalarBase := LocalType.present scalarWitnesses
abbrev evidence : NativeType (totalSpace argument.decoded) := LocalType.present scalarResults

noncomputable instance nativeFutureCoverage :
    ∀ point, (DependentProductRestrictionCoverage.futureLift
      (Functor.Elements.precomp (𝟭 ScalarWorlds).op scalarBase) argument.decoded point).Initial := by
  intro point
  change (DependentProductRestrictionCoverage.futureLift
    (Functor.Elements.precomp (𝟭 ScalarWorlds).op scalarBase) scalarWitnesses point).Initial
  exact scalarFutureCoverage point

noncomputable def decoder :=
  productDecoderTotal ((𝟭 ScalarWorlds).op ⋙ scalarBase)
    (restrict (𝟭 ScalarWorlds) argument) (body (𝟭 ScalarWorlds) argument evidence)

def scalarWorld : ScalarWorldsᵒᵖ := Opposite.op (SingleObj.star Nat)

noncomputable def suppliedReceipt (parameter : Nat) :
    (totalSpace (piDisplayed scalarWitnesses scalarResults)).obj scalarWorld :=
  ⟨PUnit.unit, rayFunction parameter⟩

noncomputable def nativeReceipt (parameter : Nat) :=
  decoder.inv.app scalarWorld (suppliedReceipt parameter)

noncomputable def changedReceipt (factor parameter : Nat) :=
  (productCell (scale factor) scalarBase argument evidence).app scalarWorld
    (nativeReceipt parameter)

private theorem conjugated_readout {K : Type*} [Category K]
    {X A : K} (encoding : X ≅ A) (operation : A ⟶ A) :
    (encoding.hom ≫ operation ≫ encoding.inv) ≫ encoding.hom =
      encoding.hom ≫ operation := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] NativeLocalTypeFormers.pi

set_option backward.isDefEq.respectTransparency true in
/-- This equality tests the new native product cell on a supplied whole
function receipt, before selecting any one application readout. -/
theorem native_cell_decodes_supplied_receipt (factor parameter : Nat) :
    decoder.hom.app scalarWorld (changedReceipt factor parameter) =
      (((coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses).app
        scalarResults).app scalarWorld (suppliedReceipt parameter)) := by
  have square : productCell (scale factor) scalarBase argument evidence ≫ decoder.hom =
      decoder.hom ≫
        (coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses).app scalarResults :=
    conjugated_readout decoder
      ((coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses).app scalarResults)
  have value := ConcreteCategory.congr_hom (NatTrans.congr_app square scalarWorld)
    (nativeReceipt parameter)
  have inverse := ConcreteCategory.congr_hom
    (decoder.inv_hom_id_app scalarWorld) (suppliedReceipt parameter)
  change decoder.hom.app scalarWorld (nativeReceipt parameter) = suppliedReceipt parameter at inverse
  exact value.trans (congrArg
    (((coveredProductTotalTransformation (scale factor) scalarBase scalarWitnesses).app
      scalarResults).app scalarWorld) inverse)

def futureArrow (coefficient : Nat) : scalarPoint ⟶ scalarPoint :=
  ⟨Quiver.Hom.op (show SingleObj.star Nat ⟶ SingleObj.star Nat from coefficient), rfl⟩

noncomputable def functionReadout
    (receipt : (totalSpace (piDisplayed scalarWitnesses scalarResults)).obj scalarWorld)
    (coefficient : Nat) : Nat :=
  ((((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app scalarPoint receipt.2).app
      scalarPoint (futureArrow coefficient) (0 : Nat))

noncomputable def nativeScaleReadout (factor parameter coefficient : Nat) : Nat :=
  functionReadout (decoder.hom.app scalarWorld (changedReceipt factor parameter)) coefficient

set_option backward.isDefEq.respectTransparency false in
/-- Both the transformation's arrow and the supplied future arrow remain
in the actual native product-cell application. -/
theorem native_scale_future_readout (factor parameter coefficient : Nat) :
    nativeScaleReadout factor parameter coefficient = (factor * coefficient) * parameter := by
  unfold nativeScaleReadout
  rw [native_cell_decodes_supplied_receipt, covered_scale_is_actual_action]
  change ((((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).app scalarPoint
      ((piDisplayed scalarWitnesses scalarResults).map
        (elementArrow (scale factor) scalarBase scalarPoint) (rayFunction parameter))).app
          scalarPoint (futureArrow coefficient) (0 : Nat)) = _
  have natural := (((nativeIso scalarWitnesses).hom.app
    (displayedToTotalElements scalarWitnesses ⋙ scalarResults)).naturality_apply
      (elementArrow (scale factor) scalarBase scalarPoint) (rayFunction parameter))
  erw [natural]
  exact rayFunction_readout parameter scalarPoint
    (elementArrow (scale factor) scalarBase scalarPoint ≫ futureArrow coefficient)
      (show scalarWitnesses.obj scalarPoint from (0 : Nat))

theorem native_nonidentity_cells_are_distinguished :
    nativeScaleReadout 2 3 2 ≠ nativeScaleReadout 3 3 2 := by
  rw [native_scale_future_readout, native_scale_future_readout]
  decide

theorem native_action_retains_supplied_functions :
    nativeScaleReadout 2 3 2 ≠ nativeScaleReadout 2 4 2 := by
  rw [native_scale_future_readout, native_scale_future_readout]
  decide

theorem omitting_the_future_arrow_changes_the_readout :
    nativeScaleReadout 2 3 2 ≠ nativeScaleReadout 2 3 1 := by
  rw [native_scale_future_readout, native_scale_future_readout]
  decide

end Mettapedia.TypeTheory.PresheafNativeProductCellControls
