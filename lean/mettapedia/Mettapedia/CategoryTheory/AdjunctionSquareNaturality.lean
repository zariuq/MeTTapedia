import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Endpoint naturality of adjunction mates

Changing either vertical side of an adjunction square commutes with taking
its actual mate. Consequently the compatibility cube for right adjoints
determines the compatibility cube for left adjoints, including the unit
and counit used by the chosen adjunctions.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.AdjunctionSquareNaturality

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u
variable {B : Type u} [Bicategory.{w,v} B]
variable {a b c d : B} {L : a ⟶ b} {R : b ⟶ a} {L' : c ⟶ d} {R' : d ⟶ c}
variable (first : L ⊣ R) (second : L' ⊣ R')

theorem mate_precompose {g g' : a ⟶ c} {h : b ⟶ d}
    (change : g ⟶ g') (square : g' ≫ L' ⟶ L ≫ h) :
    mateEquiv first second (change ▷ L' ≫ square) =
      R ◁ change ≫ mateEquiv first second square := by
  calc
    _ = 𝟙 _ ⊗≫
        R ◁ (g ◁ second.unit ≫ change ▷ (L' ≫ R')) ⊗≫
        R ◁ square ▷ R' ⊗≫ first.counit ▷ h ▷ R' ⊗≫ 𝟙 _ := by
      simp only [mateEquiv_apply', whiskerLeft_comp, comp_whiskerRight]
      bicategory
    _ = 𝟙 _ ⊗≫
        R ◁ (change ▷ (𝟙 c) ≫ g' ◁ second.unit) ⊗≫
        R ◁ square ▷ R' ⊗≫ first.counit ▷ h ▷ R' ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by simp only [mateEquiv_apply', whiskerLeft_comp]; bicategory

theorem mate_postcompose {g : a ⟶ c} {h h' : b ⟶ d}
    (square : g ≫ L' ⟶ L ≫ h) (change : h ⟶ h') :
    mateEquiv first second (square ≫ L ◁ change) =
      mateEquiv first second square ≫ change ▷ R' := by
  calc
    _ = 𝟙 _ ⊗≫ R ◁ g ◁ second.unit ⊗≫ R ◁ square ▷ R' ⊗≫
        (((R ≫ L) ◁ change ≫ first.counit ▷ h') ▷ R') ⊗≫ 𝟙 _ := by
      simp only [mateEquiv_apply', whiskerLeft_comp, comp_whiskerRight]
      bicategory
    _ = 𝟙 _ ⊗≫ R ◁ g ◁ second.unit ⊗≫ R ◁ square ▷ R' ⊗≫
        ((first.counit ▷ h ≫ (𝟙 b) ◁ change) ▷ R') ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by simp only [mateEquiv_apply', comp_whiskerRight]; bicategory

/-- A compatibility cube has the same content on either side of the
complete adjunction-mate equivalence. -/
theorem compatibility_iff {g g' : a ⟶ c} {h h' : b ⟶ d}
    (leftChange : g ⟶ g') (rightChange : h ⟶ h')
    (earlier : g ≫ L' ⟶ L ≫ h) (later : g' ≫ L' ⟶ L ≫ h') :
    leftChange ▷ L' ≫ later = earlier ≫ L ◁ rightChange ↔
      R ◁ leftChange ≫ mateEquiv first second later =
        mateEquiv first second earlier ≫ rightChange ▷ R' := by
  rw [← mate_precompose first second, ← mate_postcompose first second]
  exact (mateEquiv first second).injective.eq_iff.symm

end Mettapedia.CategoryTheory.AdjunctionSquareNaturality
