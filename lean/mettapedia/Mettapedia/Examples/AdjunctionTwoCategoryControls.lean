import Mettapedia.CategoryTheory.AdjunctionTwoCategory
import Mettapedia.GSLT.Core.LambdaTheoryStructuredControls
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# Invertible right squares with noninvertible canonical mates

The Boolean bottom/top adjunction has a square whose right comparison
is invertible. Its canonical left mate sends bottom to top, and cannot
be inverted. Both the square and the mate are actual categorical maps.
Thus the ambient adjunction two-category has strictly more maps than its
strong profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Examples.AdjunctionTwoCategoryControls

open _root_.CategoryTheory
open _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

def bottomTop : _root_.CategoryTheory.Adjunction bottomFunctor topFunctor :=
  _root_.CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun _ => homOfLE le_top
      invFun := fun _ => homOfLE bot_le
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim }

def object : AdjunctionTwoCategory Cat.{0,0} :=
  ⟨Cat.of Bool, Cat.of Bool, bottomFunctor.toCatHom, topFunctor.toCatHom, bottomTop.toCat⟩

def route : object ⟶ object := InducedBicategory.mkHom {
  left := topFunctor.toCatHom
  right := (𝟭 Bool).toCatHom
  comm := eqToIso (by apply Cat.ext; rfl) }

theorem rightComparison_identity (value : Bool) :
    route.hom.comm.hom.toNatTrans.app value = 𝟙 true := by
  apply Subsingleton.elim

theorem leftMate_false :
    (AdjunctionTwoCategory.leftMate route).toNatTrans.app false =
      homOfLE (show false ≤ true from le_top) :=
  Subsingleton.elim _ _

theorem route_not_strong : ¬ AdjunctionTwoCategory.Strong route := by
  intro strong
  let : IsIso (AdjunctionTwoCategory.leftMate route) := strong
  let backward := (inv (AdjunctionTwoCategory.leftMate route)).toNatTrans.app false
  change (true : Bool) ⟶ false at backward
  exact (not_le_of_gt Bool.false_lt_true) backward.le

theorem actual_nonidentity_endpoint : route.hom.left.toFunctor.obj false = true := rfl

end Mettapedia.Examples.AdjunctionTwoCategoryControls
