import Mettapedia.CategoryTheory.FibrationCodomainAction

/-!+# Horizontal coherence of the actual fibration action

The total and base natural transformations paste through the same chosen
identity/composition comparisons. Full comprehension respects the complete
two-cell square. These laws involve the actual mapped displays and their
components, rather than only an equality of base functors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.FibrationTwoCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Bicategory

universe u v
variable {C D E : Type (max u v)} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable [HasPullbacks C] [HasPullbacks D] [HasPullbacks E]

attribute [local instance] comp_preservesFiniteLimits

theorem codomainCell_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (change : G ⟶ H) :
    codomainCell (Functor.whiskerLeft F change) ≫
        eqToHom (codomainMap_composition F H) =
      eqToHom (codomainMap_composition F G) ≫ (codomainMap F ◁ codomainCell change) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext <;> apply NatTrans.ext
  · funext object
    apply Arrow.hom_ext <;> simp [codomainCell, codomainMap, Functor.mapArrow]
  · funext object
    simp [codomainCell, codomainMap]

theorem codomainCell_whiskerRight {F G : C ⥤ D} (H : D ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (change : F ⟶ G) :
    codomainCell (Functor.whiskerRight change H) ≫
        eqToHom (codomainMap_composition G H) =
      eqToHom (codomainMap_composition F H) ≫ (codomainCell change ▷ codomainMap H) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext <;> apply NatTrans.ext
  · funext object
    apply Arrow.hom_ext <;> simp [codomainCell, codomainMap]
  · funext object
    simp [codomainCell, codomainMap]

theorem predicateCell_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (change : G ⟶ H) :
    predicateCell (Functor.whiskerLeft F change) ≫
        eqToHom (predicateMap_composition F H) =
      eqToHom (predicateMap_composition F G) ≫ (predicateMap F ◁ predicateCell change) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext <;> apply NatTrans.ext
  · funext object
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> simp [predicateCell, predicateMap, MonoArrowImageAdjunction.map₂,
      MonoArrowImageAdjunction.map, Functor.mapArrow]
  · funext object
    simp [predicateCell, predicateMap]

theorem predicateCell_whiskerRight {F G : C ⥤ D} (H : D ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (change : F ⟶ G) :
    predicateCell (Functor.whiskerRight change H) ≫
        eqToHom (predicateMap_composition G H) =
      eqToHom (predicateMap_composition F H) ≫ (predicateCell change ▷ predicateMap H) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext <;> apply NatTrans.ext
  · funext object
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> simp [predicateCell, predicateMap, MonoArrowImageAdjunction.map₂,
      MonoArrowImageAdjunction.map]
  · funext object
    simp [predicateCell, predicateMap]

theorem comprehensionCell_naturality {F G : C ⥤ D}
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (change : F ⟶ G) :
    (predicateCell change ▷ comprehensionMap D) ≫ eqToHom (comprehension_naturality G) =
      eqToHom (comprehension_naturality F) ≫ (comprehensionMap C ◁ codomainCell change) := by
  apply Fibration.Cell.ext
  apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext <;> apply NatTrans.ext
  · funext object
    apply Arrow.hom_ext <;> simp [predicateCell, codomainCell, comprehensionMap,
      MonoArrowImageAdjunction.map₂]
  · funext object
    simp [predicateCell, codomainCell, comprehensionMap]

end Mettapedia.CategoryTheory.FibrationTwoCategory
