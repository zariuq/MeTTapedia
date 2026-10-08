import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# Reversing two-cells of an actual bicategory

Objects and one-cell directions remain unchanged. Every hom category is
replaced by its opposite; whiskering acts on the reversed two-cell and
associators and unitors use their actual opposite isomorphisms. Composing
this construction with the ordinary one-cell opposite gives the variance
needed for contravariant context and natural-transformation actions.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory
open _root_.CategoryTheory.Bicategory

universe u v w

structure TwoOpposite (B : Type u) where
  unco : B

namespace TwoOpposite

variable {B : Type u} [Bicategory.{w, v} B]

def co (object : B) : TwoOpposite B := ⟨object⟩

instance categoryStruct : CategoryStruct.{v} (TwoOpposite B) where
  Hom first second := (first.unco ⟶ second.unco)ᵒᵖ
  id object := Opposite.op (𝟙 object.unco)
  comp first second := Opposite.op (first.unop ≫ second.unop)

instance homCategory (first second : TwoOpposite B) : Category.{w} (first ⟶ second) :=
  inferInstanceAs (Category ((first.unco ⟶ second.unco)ᵒᵖ))

@[simp] theorem unco_identity (object : TwoOpposite B) :
    Opposite.unop (𝟙 object) = 𝟙 object.unco := rfl

@[simp] theorem unco_composition {first middle last : TwoOpposite B}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    Opposite.unop (earlier ≫ later) = Opposite.unop earlier ≫ Opposite.unop later := rfl

@[simp] theorem unco_vertical {first last : TwoOpposite B}
    {f g h : first ⟶ last} (earlier : f ⟶ g) (later : g ⟶ h) :
    (earlier ≫ later).unop = later.unop ≫ earlier.unop := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance bicategory : Bicategory.{w, v} (TwoOpposite B) where
  toCategoryStruct := categoryStruct
  homCategory := homCategory
  whiskerLeft := fun {_ _ _} first {_ _} change => ((Opposite.unop first) ◁ change.unop).op
  whiskerRight := fun {_ _ _} {_ _} change last => (change.unop ▷ (Opposite.unop last)).op
  associator first second third := (α_ (Opposite.unop first) (Opposite.unop second) (Opposite.unop third)).symm.op
  leftUnitor first := (λ_ (Opposite.unop first)).symm.op
  rightUnitor first := (ρ_ (Opposite.unop first)).symm.op
  whiskerLeft_id := by
    intro a b c first second
    apply Quiver.Hom.unop_inj
    exact Bicategory.whiskerLeft_id (Opposite.unop first) (Opposite.unop second)
  whiskerLeft_comp := by
    intro a b c first g h i change later
    apply Quiver.Hom.unop_inj
    exact Bicategory.whiskerLeft_comp (Opposite.unop first) later.unop change.unop
  id_whiskerLeft := by
    intro a b f g change
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using Bicategory.id_whiskerLeft change.unop
  comp_whiskerLeft := by
    intro a b c d first second h h' change
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using
      Bicategory.comp_whiskerLeft (Opposite.unop first) (Opposite.unop second) change.unop
  id_whiskerRight := by
    intro a b c first last
    apply Quiver.Hom.unop_inj
    exact Bicategory.id_whiskerRight (Opposite.unop first) (Opposite.unop last)
  comp_whiskerRight := by
    intro a b c f g h change later last
    apply Quiver.Hom.unop_inj
    exact Bicategory.comp_whiskerRight later.unop change.unop (Opposite.unop last)
  whiskerRight_id := by
    intro a b f g change
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using Bicategory.whiskerRight_id change.unop
  whiskerRight_comp := by
    intro a b c d f f' change second third
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using
      Bicategory.whiskerRight_comp change.unop (Opposite.unop second) (Opposite.unop third)
  whisker_assoc := by
    intro a b c d first g g' change last
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc] using
      Bicategory.whisker_assoc (Opposite.unop first) change.unop (Opposite.unop last)
  whisker_exchange := by
    intro a b c f g h i first second
    apply Quiver.Hom.unop_inj
    exact (Bicategory.whisker_exchange first.unop second.unop).symm
  pentagon := by
    intro a b c d e first second third fourth
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.symm_hom,
      Category.assoc] using
      Bicategory.pentagon_inv (Opposite.unop first) (Opposite.unop second)
        (Opposite.unop third) (Opposite.unop fourth)
  triangle := by
    intro a b c first second
    apply Quiver.Hom.unop_inj
    simpa only [unco_vertical, unco_identity, unco_composition, Quiver.Hom.unop_op, Iso.op_hom, Iso.symm_hom,
      Category.assoc] using
      Bicategory.triangle_assoc_comp_left_inv (Opposite.unop first) (Opposite.unop second)

end TwoOpposite
end Mettapedia.CategoryTheory
