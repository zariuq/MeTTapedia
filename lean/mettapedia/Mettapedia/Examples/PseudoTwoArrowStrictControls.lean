import Mettapedia.CategoryTheory.PseudoTwoArrowStrict
import Mettapedia.CategoryTheory.StrictTwoCategoryControls

/-!
# Stored comparison controls in the strict pseudo-arrow category

Two squares have the same identity endpoint maps, but their independent
invertible comparisons act differently on a supplied Boolean value.
Consequently their comparison cube cannot have two identity components.
Composition retains this distinction, including two and three successive
swaps. Strict unit and associativity equalities concern those complete
square morphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Examples.PseudoTwoArrowStrictControls

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory
open Mettapedia.CategoryTheory
open StrictTwoCategoryControls

def unchangedComparison : constantBool ⋙ 𝟭 Type ≅ 𝟭 Type ⋙ constantBool where
  hom := { app := fun _ => 𝟙 Bool, naturality := by intros; rfl }
  inv := { app := fun _ => 𝟙 Bool, naturality := by intros; rfl }
  hom_inv_id := by apply NatTrans.ext; funext object; rfl
  inv_hom_id := by apply NatTrans.ext; funext object; rfl

def swappedComparison : constantBool ⋙ 𝟭 Type ≅ 𝟭 Type ⋙ constantBool where
  hom := { app := fun _ => TypeCat.ofHom Bool.not, naturality := by intros; rfl }
  inv := { app := fun _ => TypeCat.ofHom Bool.not, naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext object
    apply ConcreteCategory.hom_ext
    intro value
    cases value <;> rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext object
    apply ConcreteCategory.hom_ext
    intro value
    cases value <;> rfl

def object : PseudoTwoArrow Cat.{0,1} :=
  ⟨Cat.of Type, Cat.of Type, constantBool.toCatHom⟩

def unchanged : object ⟶ object where
  left := (𝟭 Type).toCatHom
  right := (𝟭 Type).toCatHom
  comm := Cat.Hom.isoMk unchangedComparison

def swapped : object ⟶ object where
  left := (𝟭 Type).toCatHom
  right := (𝟭 Type).toCatHom
  comm := Cat.Hom.isoMk swappedComparison

theorem endpoint_maps_equal : unchanged.left = swapped.left ∧
    unchanged.right = swapped.right := ⟨rfl, rfl⟩

theorem swapped_readout : booleanReadout (swapped.comm.hom.toNatTrans.app Empty) = true := rfl

theorem unchanged_readout : booleanReadout (unchanged.comm.hom.toNatTrans.app Empty) = false := rfl

theorem no_identity_component_cube :
    ¬ ∃ change : unchanged ⟶ swapped,
      change.left = 𝟙 ((𝟭 Type).toCatHom) ∧
        change.right = 𝟙 ((𝟭 Type).toCatHom) := by
  rintro ⟨change, left, right⟩
  have cube := change.compatible
  rw [left, right] at cube
  have readout := congrArg (fun comparison =>
    booleanReadout (comparison.toNatTrans.app Empty)) cube
  change (true : Bool) = false at readout
  cases readout

theorem endpoint_equalities_do_not_determine_square : unchanged ≠ swapped := by
  intro same
  apply no_identity_component_cube
  refine ⟨eqToHom same, ?_, ?_⟩
  · rw [PseudoTwoArrow.eqToHom_left]
    rfl
  · rw [PseudoTwoArrow.eqToHom_right]
    rfl

theorem identity_keeps_swapped_readout :
    booleanReadout ((𝟙 object ≫ swapped).comm.hom.toNatTrans.app Empty) = true := rfl

theorem two_swaps_readout :
    booleanReadout ((swapped ≫ swapped).comm.hom.toNatTrans.app Empty) = false := rfl

theorem three_swaps_readout :
    booleanReadout (((swapped ≫ swapped) ≫ swapped).comm.hom.toNatTrans.app Empty) = true := rfl

theorem complete_associativity :
    (swapped ≫ swapped) ≫ swapped = swapped ≫ (swapped ≫ swapped) :=
  PseudoTwoArrow.assoc_hom swapped swapped swapped

end Mettapedia.Examples.PseudoTwoArrowStrictControls
