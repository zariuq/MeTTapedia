import Mettapedia.CategoryTheory.MonoArrowImageComparison

/-!
# Identity, counit and uniqueness of canonical image comparisons

The image comparison is the unique map extending the translated image unit.
This characterizes the canonical mate, supplies its identity law and proves
compatibility with the comprehension counit. The comparisons retain their
actual chosen image objects throughout.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [HasEqualizers C]
variable {D : Type u₂} [Category.{v₂} D] [StrongEpiCategory D]
variable [HasImages C] [HasImageMaps C] [HasImages D] [HasImageMaps D]
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable [PreservesColimitsOfShape WalkingSpan F]

theorem imageComparison_unique (object : Arrow C)
    (candidate : (image (C := D)).obj (F.mapArrow.obj object) ⟶
      (map F).obj (image.obj object))
    (factorization : unitSquare (F.mapArrow.obj object) ≫
      (comprehension D).map candidate = F.mapArrow.map (unitSquare object)) :
    candidate = (imageComparison F).hom.app object := by
  exact (descend_unique _ candidate factorization).trans
    (descend_unique _ ((imageComparison F).hom.app object)
      (imageComparison_unit F object)).symm

theorem imageComparison_counit (predicate : Predicate C) :
    (imageComparison F).hom.app predicate.obj ≫
      (map F).map (adjunction.counit.app predicate) =
    adjunction.counit.app ((map F).obj predicate) := by
  apply predicate_hom_ext
  change 𝟙 (F.obj predicate.obj.right) ≫
    F.map ((adjunction.counit.app predicate).hom.right) =
      (adjunction.counit.app ((map F).obj predicate)).hom.right
  rw [counit_over_identity, counit_over_identity, F.map_id, Category.id_comp]
  rfl

section Identity

variable [StrongEpiCategory C]

@[simp] theorem imageComparison_identity (object : Arrow C) :
    (imageComparison (𝟭 C)).hom.app object = 𝟙 (image.obj object) := by
  apply predicate_hom_ext
  rfl

end Identity

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
