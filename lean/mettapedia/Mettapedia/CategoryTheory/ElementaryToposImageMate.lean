import Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
import Mettapedia.CategoryTheory.FibrationTwoCellFaithfulness

/-!
# The actual image comparison in the fibration adjunction target

Finite-limit-preserving inverse-image maps preserve the complete image
factorization. The resulting comparison retains its actual total natural
isomorphism and both base components. Its inverse satisfies the same
complete projection square; invertibility is earned from these data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open FibrationTwoCategory FibrationAdjunctionTwoCategory MonoArrowImageAdjunction

universe u v
variable {source target : ElementaryTopos.{max u v,v}}

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

theorem imageComparison_inverse_base (route : source ⟶ target) (arrow : Arrow source) :
    ((imageComparison route.functor).inv.app arrow).hom.right =
      𝟙 (route.functor.obj arrow.right) := by
  have same := congrArg (fun transformation => (transformation.app arrow).hom.right)
    (imageComparison route.functor).inv_hom_id
  change ((imageComparison route.functor).inv.app arrow).hom.right ≫
    ((imageComparison route.functor).hom.app arrow).hom.right =
      𝟙 (route.functor.obj arrow.right) at same
  calc
    _ = ((imageComparison route.functor).inv.app arrow).hom.right ≫ 𝟙 _ :=
      (Category.comp_id _).symm
    _ = ((imageComparison route.functor).inv.app arrow).hom.right ≫
        ((imageComparison route.functor).hom.app arrow).hom.right :=
      congrArg (fun component =>
        ((imageComparison route.functor).inv.app arrow).hom.right ≫ component)
        (imageComparison_right route.functor arrow).symm
    _ = _ := same

def imageComparisonIso (route : source ⟶ target) :
    codomainMap route.functor ≫ imageMap target.classifier ≅
      imageMap source.classifier ≫ predicateMap route.functor where
  hom := {
    hom := {
      left := (imageComparison route.functor).hom.toCatHom₂
      right := ((Functor.rightUnitor route.functor) ≪≫
        (Functor.leftUnitor route.functor).symm).hom.toCatHom₂
      compatible := by
        apply heq_of_eq
        apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext arrow
        change 𝟙 _ ≫ 𝟙 _ = ((imageComparison route.functor).hom.app arrow).hom.right
        rw [imageComparison_right, Category.id_comp]
        rfl } }
  inv := {
    hom := {
      left := (imageComparison route.functor).inv.toCatHom₂
      right := ((Functor.rightUnitor route.functor) ≪≫
        (Functor.leftUnitor route.functor).symm).inv.toCatHom₂
      compatible := by
        apply heq_of_eq
        apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext arrow
        change 𝟙 _ ≫ 𝟙 _ = ((imageComparison route.functor).inv.app arrow).hom.right
        rw [imageComparison_inverse_base, Category.id_comp]
        rfl } }
  hom_inv_id := by
    apply Fibration.Cell.ext
    apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
    · exact (imageComparison route.functor).hom_inv_id
    · exact ((Functor.rightUnitor route.functor) ≪≫
        (Functor.leftUnitor route.functor).symm).hom_inv_id
  inv_hom_id := by
    apply Fibration.Cell.ext
    apply StrictTwoArrow.Cell.ext <;> apply Cat.Hom₂.ext
    · exact (imageComparison route.functor).inv_hom_id
    · exact ((Functor.rightUnitor route.functor) ≪≫
        (Functor.leftUnitor route.functor).symm).inv_hom_id

@[simp] theorem imageComparisonIso_total (route : source ⟶ target) (arrow : Arrow source) :
    (imageComparisonIso route).hom.hom.left.toNatTrans.app arrow =
      (imageComparison route.functor).hom.app arrow := rfl

@[simp] theorem imageComparisonIso_base (route : source ⟶ target) (base : source) :
    (imageComparisonIso route).hom.hom.right.toNatTrans.app base =
      𝟙 (route.functor.obj base) := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

/-- The mate is computed independently from the actual fibration
adjunctions. Faithfulness of predicate projection and the complete cube
identify it with the independently constructed image comparison. -/
theorem leftMate_eq_imageComparison (route : source ⟶ target) :
    AdjunctionTwoCategory.leftMate (map route) = (imageComparisonIso route).hom := by
  let : (predicates target).functor.Faithful :=
    inferInstanceAs ((MonoArrowImageAdjunction.projection target).Faithful)
  apply cell_ext_of_base (target := predicates target)
  change ((mateEquiv (imageAdjunction source.classifier)
    (imageAdjunction target.classifier)).symm
      (eqToIso (comprehension_naturality route.functor)).inv).hom.right =
        (imageComparisonIso route).hom.hom.right
  rw [Bicategory.mateEquiv_symm_apply, Bicategory.Adjunction.homEquiv₂_symm_apply,
    Bicategory.Adjunction.homEquiv₁_symm_apply]
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext base
  simp [imageAdjunction, imageUnit, imageCounit, imageMap, comprehensionMap,
    imageComparisonIso]
  rfl

/-- Invertibility is established for geometric inverse-image maps from
the actual complete image comparison, not from right-square invertibility. -/
theorem map_strong (route : source ⟶ target) :
    AdjunctionTwoCategory.Strong (map route) := by
  unfold AdjunctionTwoCategory.Strong
  rw [leftMate_eq_imageComparison]
  infer_instance

end Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
