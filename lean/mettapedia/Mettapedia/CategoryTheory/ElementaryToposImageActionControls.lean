import Mettapedia.CategoryTheory.ElementaryToposImagePseudofunctor
import Mettapedia.CategoryTheory.ElementaryToposImageMate
import Mettapedia.CategoryTheory.MonoArrowImageControls
import Mettapedia.GSLT.Topos.ElementaryToposGeometricControls

/-!
# Geometric action on supplied dependent displays

The actual native action sends a varying receipt display through the
non-full diagonal and transports a nonidentity display square. Exchange
of diagram indices changes an independently supplied transition readout.
The independently computed adjunction mate commutes with image units and
universal elimination. Its value readout cannot recover distinct receipt
positions that the image has forgotten.

These are categorical controls, without a runtime execution claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageActionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Bicategory
open ElementaryToposImageComprehensionAction MonoArrowImageAdjunction
open MonoArrowImageControls
open Mettapedia.GSLT.Topos.ElementaryToposGeometricControls
open Mettapedia.GSLT.Core.LambdaTheoryClosedControls

local instance diagonal_finite : PreservesFiniteLimits diagonal.functor := diagonal.finite

local instance diagonal_leftAdjoint : diagonal.functor.IsLeftAdjoint := diagonal.leftAdjoint

local instance sets_images : HasImages sets := ElementaryTopos.hasImages sets

local instance diagrams_images : HasImages diagrams := ElementaryTopos.hasImages diagrams

def nativeDiagonal := normalizedAction.map diagonal

def nativeExchange := normalizedAction.map exchange

def receiptDisplay : Arrow sets := Arrow.mk readout

def mappedReceiptDisplay : Arrow diagrams :=
  nativeDiagonal.hom.right.square.left.toFunctor.obj receiptDisplay

theorem diagonal_display_readout (index : Bool) (receipt : Receipt) :
    mappedReceiptDisplay.hom.app ⟨index⟩ receipt = 2 * receipt.1 := rfl

theorem diagonal_advance_value (index : Bool) (receipt : Receipt) :
    (nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).left.app
      ⟨index⟩ receipt = advance receipt := rfl

theorem diagonal_advance_position (index : Bool) (receipt : Receipt) :
    ((nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).left.app
      ⟨index⟩ receipt).2.val = receipt.2.val := rfl

theorem diagonal_advance_base (index : Bool) (value : Nat) :
    (nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).right.app
      ⟨index⟩ value = value + 2 := rfl

theorem mapped_positions_remain_distinct (index : Bool) :
    (nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).left.app
        ⟨index⟩ firstReceipt ≠
      (nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).left.app
        ⟨index⟩ secondReceipt := by
  intro same
  have position := congrArg (fun receipt : Receipt => receipt.2.val) same
  change (0 : Nat) = 1 at position
  omega

theorem mapped_square_nonidentity (index : Bool) :
    (nativeDiagonal.hom.right.square.left.toFunctor.map advanceSquare).left.app
      ⟨index⟩ firstReceipt ≠ firstReceipt := advance_is_nonidentity

def shiftDisplay : Arrow diagrams := Arrow.mk shift

theorem native_exchange_readout :
    (nativeExchange.hom.right.square.left.toFunctor.obj shiftDisplay).hom.app
      ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem native_exchange_changes_readout :
    ((nativeExchange.hom.right.square.left.toFunctor.obj shiftDisplay).hom.app
        ⟨false⟩ (10 : Nat) : Nat) ≠
      shiftDisplay.hom.app ⟨false⟩ (10 : Nat) := component_values_differ

theorem native_exchange_twice_recovers_readout :
    ((nativeExchange ≫ nativeExchange).hom.right.square.left.toFunctor.obj
      shiftDisplay).hom.app ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem native_diagonal_not_full :
    ¬ nativeDiagonal.hom.right.square.right.toFunctor.Full := diagonal_not_full

theorem lex_power_excluded_from_geometric_action :
    ¬ ∃ route : ElementaryTopos.GeometricHom sets sets,
      route.functor = CartesianClosedPowerFunctor.power Bool := no_geometric_power_map

universe u v
variable {source target : ElementaryTopos.{max u v,v}}

/-- The comparison here is the actual mate calculated from the native
adjunction units and counits, rather than a freely supplied image map. -/
theorem computed_mate_unit (route : source ⟶ target) (arrow : Arrow source) :
    unitSquare (route.functor.mapArrow.obj arrow) ≫
        (comprehension target).map
          ((AdjunctionTwoCategory.leftMate (map route)).hom.left.toNatTrans.app arrow) =
      route.functor.mapArrow.map (unitSquare arrow) := by
  rw [leftMate_eq_imageComparison]
  exact imageComparison_unit route.functor arrow

theorem computed_mate_elimination (route : source ⟶ target)
    {arrow : Arrow source} {predicate : Predicate source}
    (authored : arrow ⟶ predicate.obj) :
    (AdjunctionTwoCategory.leftMate (map route)).hom.left.toNatTrans.app arrow ≫
        (MonoArrowImageAdjunction.map route.functor).map (descend authored) =
      descend (route.functor.mapArrow.map authored) := by
  rw [leftMate_eq_imageComparison]
  exact imageComparison_elimination route.functor authored

def diagonalEliminator :=
  (AdjunctionTwoCategory.leftMate nativeDiagonal).hom.left.toNatTrans.app receiptDisplay ≫
    (MonoArrowImageAdjunction.map diagonal.functor).map (descend authoredEvidence)

def nativeTargetImage :=
  (object diagrams).left.square.left.toFunctor.obj mappedReceiptDisplay

def nativeTargetUnit : mappedReceiptDisplay ⟶ nativeTargetImage.obj :=
  (object diagrams).adjunction.unit.hom.left.toNatTrans.app mappedReceiptDisplay

/-- The actual unit and computed native mate feed the universal
eliminator against the independently authored even predicate. -/
theorem diagonal_elimination_complete_square :
    nativeTargetUnit ≫
        (comprehension diagrams).map diagonalEliminator =
      diagonal.functor.mapArrow.map authoredEvidence := by
  rw [show nativeTargetUnit = unitSquare mappedReceiptDisplay from
    MonoArrowImageAdjunction.adjunction_unit mappedReceiptDisplay]
  change unitSquare (diagonal.functor.mapArrow.obj receiptDisplay) ≫
      (comprehension diagrams).map
        ((AdjunctionTwoCategory.leftMate (map diagonal)).hom.left.toNatTrans.app
          receiptDisplay ≫
            (MonoArrowImageAdjunction.map diagonal.functor).map (descend authoredEvidence)) = _
  rw [computed_mate_elimination]
  exact descend_factor
    (predicate := (MonoArrowImageAdjunction.map diagonal.functor).obj evenPredicate)
    (diagonal.functor.mapArrow.map authoredEvidence)

theorem diagonal_elimination_readout (index : Bool) (receipt : Receipt) :
    diagonalEliminator.hom.left.app ⟨index⟩
      (nativeTargetUnit.left.app ⟨index⟩ receipt) = receipt.1 := by
  exact congrArg (fun square => square.left.app ⟨index⟩ receipt)
    diagonal_elimination_complete_square

theorem native_unit_collapses_positions (index : Bool) :
    nativeTargetUnit.left.app ⟨index⟩ firstReceipt =
      nativeTargetUnit.left.app ⟨index⟩ secondReceipt := by
  let : Mono nativeTargetImage.obj.hom := nativeTargetImage.property
  apply (mono_iff_injective
    (nativeTargetImage.obj.hom.app ⟨index⟩)).mp inferInstance
  have first := congrArg (fun transformation => transformation.app ⟨index⟩ firstReceipt)
    (Arrow.w nativeTargetUnit)
  have second := congrArg (fun transformation => transformation.app ⟨index⟩ secondReceipt)
    (Arrow.w nativeTargetUnit)
  exact first.trans second.symm

/-- This separator uses the chosen native target image itself, after
actual geometric translation, rather than a different source image. -/
theorem diagonal_elimination_position_boundary (index : Bool) :
    ¬ ∃ decode : nativeTargetImage.obj.left.obj ⟨index⟩ → Receipt,
      ∀ receipt,
        decode (nativeTargetUnit.left.app ⟨index⟩ receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  apply receipt_positions_differ
  exact (recovers firstReceipt).symm.trans
    ((congrArg decode (native_unit_collapses_positions index)).trans (recovers secondReceipt))

end Mettapedia.CategoryTheory.ElementaryToposImageActionControls
