import Mettapedia.CategoryTheory.MonoArrowFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Canonical image comparisons and their coherence

Finite-limit and pushout preservation earn the comparison between image
factorization before and after translation. Its complete predicate square
commutes with the adjunction unit and universal elimination. Naturality in
theory transformations and composition retain the actual image objects and
their canonical comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesColimitsOfShape

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] [HasEqualizers C]
variable {D : Type u₂} [Category.{v₂} D] [StrongEpiCategory D]
variable [HasImages C] [HasImageMaps C] [HasImages D] [HasImageMaps D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesColimitsOfShape WalkingSpan F]

def imageComparison : F.mapArrow ⋙ image (C := D) ≅ image (C := C) ⋙ map F :=
  NatIso.ofComponents
    (fun object => (monomorphismProperty D).isoMk (Arrow.isoMk
      (PreservesImage.iso F object.hom) (Iso.refl _) (by
        change (PreservesImage.iso F object.hom).hom ≫ F.map (Limits.image.ι object.hom) =
          Limits.image.ι (F.map object.hom) ≫ 𝟙 (F.obj object.right)
        rw [Category.comp_id]
        exact PreservesImage.hom_comp_map_image_ι F object.hom)))
    (by
      intro first second square
      apply predicate_hom_ext
      change F.map square.right ≫ 𝟙 (F.obj second.right) =
        𝟙 (F.obj first.right) ≫ F.map square.right
      rw [Category.comp_id, Category.id_comp])

@[simp] theorem imageComparison_left (object : Arrow C) :
    ((imageComparison F).hom.app object).hom.left =
      (PreservesImage.iso F object.hom).hom := rfl

@[simp] theorem imageComparison_right (object : Arrow C) :
    ((imageComparison F).hom.app object).hom.right = 𝟙 (F.obj object.right) := rfl

theorem imageComparison_unit (object : Arrow C) :
    unitSquare (F.mapArrow.obj object) ≫
        (comprehension D).map ((imageComparison F).hom.app object) =
      F.mapArrow.map (unitSquare object) := by
  apply square_into_predicate_ext
  change 𝟙 (F.obj object.right) ≫ 𝟙 (F.obj object.right) = F.map (𝟙 object.right)
  rw [Category.id_comp, F.map_id]

theorem imageComparison_elimination {object : Arrow C} {predicate : Predicate C}
    (square : object ⟶ predicate.obj) :
    (imageComparison F).hom.app object ≫ (map F).map (descend square) =
      descend (F.mapArrow.map square) := by
  apply predicate_hom_ext
  change 𝟙 (F.obj object.right) ≫ F.map square.right = F.map square.right
  exact Category.id_comp _

theorem imageComparison_transformation {G : C ⥤ D}
    [PreservesFiniteLimits G] [PreservesColimitsOfShape WalkingSpan G]
    (change : F ⟶ G) (object : Arrow C) :
    (image (C := D)).map (((Functor.mapArrowFunctor C D).map change).app object) ≫
        (imageComparison G).hom.app object =
      (imageComparison F).hom.app object ≫ (map₂ change).app (image.obj object) := by
  apply predicate_hom_ext
  change change.app object.right ≫ 𝟙 (G.obj object.right) =
    𝟙 (F.obj object.right) ≫ change.app object.right
  rw [Category.comp_id, Category.id_comp]

variable {E : Type u₃} [Category.{v₃} E] [StrongEpiCategory E]
variable [HasEqualizers D] [HasImages E] [HasImageMaps E]
variable (G : D ⥤ E) [PreservesFiniteLimits G] [PreservesColimitsOfShape WalkingSpan G]

theorem imageComparison_composition (object : Arrow C) :
    (imageComparison (F ⋙ G)).hom.app object =
      (imageComparison G).hom.app (F.mapArrow.obj object) ≫
        (map G).map ((imageComparison F).hom.app object) := by
  apply predicate_hom_ext
  change 𝟙 (G.obj (F.obj object.right)) =
    𝟙 (G.obj (F.obj object.right)) ≫ G.map (𝟙 (F.obj object.right))
  rw [G.map_id, Category.id_comp]

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
