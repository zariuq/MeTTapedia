import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Invertibly commuting squares in a bicategory

An arrow object retains its actual source, target and arrow. A morphism is
a square with an invertible comparison, and a two-cell is a compatible
pair of endpoint two-cells. The comparison is part of the morphism data;
it is neither erased nor replaced by equality of the endpoint arrows.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w,v} B]

structure PseudoTwoArrow where
  source : B
  target : B
  arrow : source ⟶ target

namespace PseudoTwoArrow

variable {B}

structure Hom (source target : PseudoTwoArrow B) where
  left : source.source ⟶ target.source
  right : source.target ⟶ target.target
  comm : source.arrow ≫ right ≅ left ≫ target.arrow

instance categoryStruct : CategoryStruct (PseudoTwoArrow B) where
  Hom := Hom
  id source := ⟨𝟙 source.source, 𝟙 source.target,
    (ρ_ source.arrow) ≪≫ (λ_ source.arrow).symm⟩
  comp {source middle target} first second := ⟨first.left ≫ second.left,
    first.right ≫ second.right,
    (α_ source.arrow first.right second.right).symm ≪≫
      whiskerRightIso first.comm second.right ≪≫
      (α_ first.left middle.arrow second.right) ≪≫
      whiskerLeftIso first.left second.comm ≪≫
      (α_ first.left second.left target.arrow).symm⟩

@[simp] theorem id_left (source : PseudoTwoArrow B) :
    (𝟙 source : source ⟶ source).left = 𝟙 source.source := rfl
@[simp] theorem id_right (source : PseudoTwoArrow B) :
    (𝟙 source : source ⟶ source).right = 𝟙 source.target := rfl
@[simp] theorem id_comm_hom (source : PseudoTwoArrow B) :
    (𝟙 source : source ⟶ source).comm.hom =
      (ρ_ source.arrow).hom ≫ (λ_ source.arrow).inv := rfl

@[simp] theorem comp_left {source middle target : PseudoTwoArrow B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).left = first.left ≫ second.left := rfl
@[simp] theorem comp_right {source middle target : PseudoTwoArrow B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).right = first.right ≫ second.right := rfl
@[simp] theorem comp_comm_hom {source middle target : PseudoTwoArrow B}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).comm.hom =
      rightAdjointSquare.vcomp first.comm.hom second.comm.hom := rfl

structure Cell {source target : PseudoTwoArrow B} (first second : source ⟶ target) where
  left : first.left ⟶ second.left
  right : first.right ⟶ second.right
  compatible : source.arrow ◁ right ≫ second.comm.hom =
    first.comm.hom ≫ left ▷ target.arrow

@[ext] theorem Cell.ext {source target : PseudoTwoArrow B}
    {first second : source ⟶ target} {earlier later : Cell first second}
    (left : earlier.left = later.left) (right : earlier.right = later.right) :
    earlier = later := by
  cases earlier
  cases later
  cases left
  cases right
  rfl

instance homCategory (source target : PseudoTwoArrow B) : Category (source ⟶ target) where
  Hom := Cell
  id first := ⟨𝟙 first.left, 𝟙 first.right, by simp⟩
  comp {first second third} earlier later :=
    ⟨earlier.left ≫ later.left, earlier.right ≫ later.right, by
      rw [whiskerLeft_comp, comp_whiskerRight, Category.assoc, later.compatible,
        ← Category.assoc, earlier.compatible, Category.assoc]⟩
  id_comp := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.id_comp _
  comp_id := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.comp_id _
  assoc := by intros; apply Cell.ext <;> exact _root_.CategoryTheory.Category.assoc _ _ _

@[simp] theorem cell_id_left {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    (𝟙 route : route ⟶ route).left = 𝟙 route.left := rfl
@[simp] theorem cell_id_right {source target : PseudoTwoArrow B} (route : source ⟶ target) :
    (𝟙 route : route ⟶ route).right = 𝟙 route.right := rfl
@[simp] theorem cell_comp_left {source target : PseudoTwoArrow B}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).left = earlier.left ≫ later.left := rfl
@[simp] theorem cell_comp_right {source target : PseudoTwoArrow B}
    {first second third : source ⟶ target} (earlier : first ⟶ second) (later : second ⟶ third) :
    (earlier ≫ later).right = earlier.right ≫ later.right := rfl

end PseudoTwoArrow
end Mettapedia.CategoryTheory
