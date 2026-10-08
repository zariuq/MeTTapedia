import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Complete dependent-sum comparisons of a functor

Dependent sum in the actual slices is composition of display arrows.
The comparison is an isomorphism because a functor preserves composition;
it retains the entire mapped domain and every mapped domain morphism.
No dependent-product or classifier preservation is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.SliceFunctorSumComparison

open _root_.CategoryTheory

universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)
variable {X Y : C} (route : X ⟶ Y)

def component (display : Over X) :
    (Over.map route ⋙ Over.post F).obj display ≅
      (Over.post F ⋙ Over.map (F.map route)).obj display :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (F.obj display.left) ≫ (F.map display.hom ≫ F.map route) =
      F.map (display.hom ≫ route)
    rw [Category.id_comp, F.map_comp])

def comparison : Over.map route ⋙ Over.post F ≅
    Over.post F ⋙ Over.map (F.map route) :=
  NatIso.ofComponents (component F route) (by
    intro first second square
    apply Over.OverMorphism.ext
    change F.map square.left ≫ 𝟙 (F.obj second.left) =
      𝟙 (F.obj first.left) ≫ F.map square.left
    rw [Category.comp_id, Category.id_comp])

theorem complete_domain (display : Over X) :
    ((comparison F route).hom.app display).left = 𝟙 (F.obj display.left) := rfl

theorem complete_domain_inverse (display : Over X) :
    ((comparison F route).inv.app display).left = 𝟙 (F.obj display.left) := rfl

/-- The whole actual base equation is the functor's composition law. -/
theorem display_readout (display : Over X) :
    ((comparison F route).hom.app display).left ≫
        (F.map display.hom ≫ F.map route) = F.map (display.hom ≫ route) := by
  change 𝟙 (F.obj display.left) ≫ (F.map display.hom ≫ F.map route) = _
  rw [Category.id_comp, F.map_comp]

end Mettapedia.CategoryTheory.SliceFunctorSumComparison
