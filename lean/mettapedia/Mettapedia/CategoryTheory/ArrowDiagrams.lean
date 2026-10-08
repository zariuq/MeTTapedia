import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Commuting squares as diagrams of length one

The arrow category and the functor category on the two-element ordered
category describe the same objects and morphisms. The equivalence retains
both components of every commuting square, with explicit readout laws.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.ArrowDiagrams

open _root_.CategoryTheory

universe u v
variable (C : Type u) [Category.{v} C]

def toArrows : ComposableArrows C 1 ⥤ Arrow C where
  obj diagram := Arrow.mk diagram.hom
  map square := Arrow.homMk (square.app 0) (square.app 1)
    (square.naturality (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).symm
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

def toDiagrams : Arrow C ⥤ ComposableArrows C 1 where
  obj arrow := ComposableArrows.mk₁ arrow.hom
  map square := ComposableArrows.homMk₁ square.left square.right square.w.symm
  map_id _ := by apply ComposableArrows.hom_ext₁ <;> rfl
  map_comp _ _ := by apply ComposableArrows.hom_ext₁ <;> rfl

def unit : 𝟭 (ComposableArrows C 1) ≅ toArrows C ⋙ toDiagrams C :=
  NatIso.ofComponents
    (fun diagram => ComposableArrows.isoMk₁ (Iso.refl diagram.left)
      (Iso.refl diagram.right) (by
        change diagram.hom ≫ 𝟙 _ = 𝟙 _ ≫ diagram.hom
        simp))
    (by
      intro first second square
      apply ComposableArrows.hom_ext₁
      · change square.app 0 ≫ 𝟙 _ = 𝟙 _ ≫ square.app 0
        simp
      · change square.app 1 ≫ 𝟙 _ = 𝟙 _ ≫ square.app 1
        simp)

def counit : toDiagrams C ⋙ toArrows C ≅ 𝟭 (Arrow C) :=
  NatIso.ofComponents (fun arrow => Iso.refl arrow)
    (by
      intro first second square
      ext
      · change square.left ≫ 𝟙 _ = 𝟙 _ ≫ square.left
        simp
      · change square.right ≫ 𝟙 _ = 𝟙 _ ≫ square.right
        simp)

def equivalence : ComposableArrows C 1 ≌ Arrow C where
  functor := toArrows C
  inverse := toDiagrams C
  unitIso := unit C
  counitIso := counit C
  functor_unitIso_comp diagram := by
    ext <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> simp

theorem toArrows_left (diagram : ComposableArrows C 1) :
    ((toArrows C).obj diagram).left = diagram.left := rfl

theorem toArrows_right (diagram : ComposableArrows C 1) :
    ((toArrows C).obj diagram).right = diagram.right := rfl

theorem toArrows_map_left {first second : ComposableArrows C 1}
    (square : first ⟶ second) : ((toArrows C).map square).left = square.app 0 := rfl

theorem toArrows_map_right {first second : ComposableArrows C 1}
    (square : first ⟶ second) : ((toArrows C).map square).right = square.app 1 := rfl

theorem toDiagrams_map_left {first second : Arrow C} (square : first ⟶ second) :
    ((toDiagrams C).map square).app 0 = square.left := rfl

theorem toDiagrams_map_right {first second : Arrow C} (square : first ⟶ second) :
    ((toDiagrams C).map square).app 1 = square.right := rfl

end Mettapedia.CategoryTheory.ArrowDiagrams
