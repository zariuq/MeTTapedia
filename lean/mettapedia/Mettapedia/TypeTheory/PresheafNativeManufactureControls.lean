import Mettapedia.TypeTheory.PresheafNativeManufacture
import Mettapedia.GSLT.Topos.PresheafElementaryToposControls

/-!
# Complete observations through the native manufacture

The actual higher-order dependent action retains nonidentity geometric
maps, distinct ordinary comparison cells and complete dependent values.
Their base readouts do not recover positions forgotten by a comparison.
An independently sized authored closed theory exercises the composite
presheaf-to-native action on a nonconstant representable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafNativeManufactureControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
open Mettapedia.GSLT.Topos.PresheafElementaryToposControls
open ElementaryToposImageComprehensionAction

namespace ActualCells

open Parallel

def leftCell := ElementaryToposNativeLanguageAction.action.map₂ nativeLeft
def rightCell := ElementaryToposNativeLanguageAction.action.map₂ nativeRight

def leftRead :
    oneEvaluation.functor.obj display ⟶ zeroEvaluation.functor.obj display :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object Point)).map
      (leftCell.hom.hom.right.hom.right.toNatTrans.app
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object WalkingParallelPair)).obj display))

def rightRead :
    oneEvaluation.functor.obj display ⟶ zeroEvaluation.functor.obj display :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object Point)).map
      (rightCell.hom.hom.right.hom.right.toNatTrans.app
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object WalkingParallelPair)).obj display))

theorem left_complete : leftRead = nativeLeft.app display :=
  global_base_cell nativeLeft display

theorem right_complete : rightRead = nativeRight.app display :=
  global_base_cell nativeRight display

def translatedAdvance :
    oneEvaluation.functor.obj display ⟶ oneEvaluation.functor.obj display :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object Point)).map
      ((ElementaryToposNativeLanguageAction.action.map oneEvaluation).hom.hom.right.square.right.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object WalkingParallelPair)).map advanceDisplay))

theorem advance_complete : translatedAdvance = oneEvaluation.functor.map advanceDisplay :=
  global_base_arrow oneEvaluation advanceDisplay

theorem changed_index (receipt : Receipt) :
    (translatedAdvance.app (op ⟨PUnit.unit⟩) receipt).1 = receipt.1 + 1 := by
  rw [advance_complete]
  exact actual_evaluation_advance_value receipt

theorem retained_position (receipt : Receipt) :
    (translatedAdvance.app (op ⟨PUnit.unit⟩) receipt).2.val = receipt.2.val := by
  rw [advance_complete]
  exact actual_evaluation_retains_position receipt

theorem left_after_advance (receipt : Receipt) :
    leftRead.app (op ⟨PUnit.unit⟩)
      (translatedAdvance.app (op ⟨PUnit.unit⟩) receipt) = receipt.1 + 1 + 7 := by
  rw [left_complete, advance_complete]
  exact actual_cell_after_advance receipt

theorem different_actual_cells : leftCell ≠ rightCell := by
  intro same
  have values := congrArg (fun supplied :
    ElementaryToposNativeLanguageAction.action.map oneEvaluation ⟶
      ElementaryToposNativeLanguageAction.action.map zeroEvaluation =>
    ((ElementaryToposObjectUniverseLift.down
      (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object Point)).map
        (supplied.hom.hom.right.hom.right.toNatTrans.app
          ((ElementaryToposObjectUniverseLift.up
            (Mettapedia.GSLT.Topos.PresheafElementaryTopos.object WalkingParallelPair)).obj display))).app
      (op ⟨PUnit.unit⟩) firstReceipt) same
  change leftRead.app (op ⟨PUnit.unit⟩) firstReceipt =
    rightRead.app (op ⟨PUnit.unit⟩) firstReceipt at values
  rw [left_complete, right_complete, actual_left_cell_readout,
    actual_right_cell_readout] at values
  change (1 : Nat) + 7 = 1 + 9 at values
  omega

theorem no_receipt_decoder :
    ¬ ∃ decode : Nat → Receipt, ∀ receipt,
      decode (leftRead.app (op ⟨PUnit.unit⟩) receipt) = receipt := by
  rw [left_complete]
  exact cells_do_not_recover_positions

end ActualCells

namespace ActualTheory

open Mettapedia.GSLT.Core.LambdaTheoryClosedControls
open Mettapedia.GSLT.Topos.PresheafTheoryActionControls.Exchange
open IndependentSizes

def swapRestriction : Diagramsᵒᵖ ⥤ Type 1 :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory diagramsTheory))).obj
      ((PresheafNativeManufacture.action.map (route swapMap)).hom.hom.right.square.right.toFunctor.obj
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory diagramsTheory))).obj
          IndependentSizes.represented))

def twiceRestriction : Diagramsᵒᵖ ⥤ Type 1 :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory diagramsTheory))).obj
      ((PresheafNativeManufacture.action.map (route swapMap ≫ route swapMap)).hom.hom.right.square.right.toFunctor.obj
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos (theory diagramsTheory))).obj
          IndependentSizes.represented))

theorem actual_swap_readout :
    ((swapRestriction.map shift.op (ULift.up supplied)).down.app
      ⟨false⟩ (10 : Nat)) = (12 : Nat) := rfl

theorem omitted_theory_changes_readout :
    ((swapRestriction.map shift.op (ULift.up supplied)).down.app ⟨false⟩ (10 : Nat)) ≠
      ((IndependentSizes.represented.map shift.op (ULift.up supplied)).down.app
        ⟨false⟩ (10 : Nat)) := by
  rw [actual_swap_readout]
  change (12 : Nat) ≠ 11
  omega

theorem actual_composed_theory_readout :
    ((twiceRestriction.map shift.op (ULift.up supplied)).down.app
      ⟨false⟩ (10 : Nat)) = (11 : Nat) := rfl

end ActualTheory

end Mettapedia.TypeTheory.PresheafNativeManufactureControls
