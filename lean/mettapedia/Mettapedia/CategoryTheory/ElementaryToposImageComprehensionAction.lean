import Mettapedia.CategoryTheory.ElementaryToposGeometric
import Mettapedia.CategoryTheory.FibrationAdjunctionTwoCategory
import Mettapedia.CategoryTheory.MonoArrowImageComparisonCoherence

/-!
# Elementary-topos action on actual image-comprehension adjunctions

Every supplied elementary topos gives an adjunction object in the
two-category of fibrations. Its inverse-image maps act on the actual
predicate and codomain fibrations, retaining the invertible comprehension
square. Natural transformations retain both endpoint components and the
complete compatibility cube. Higher-order object profiles are assembled
separately from this ambient adjunction action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open FibrationTwoCategory

universe u v

def object (topos : ElementaryTopos.{max u v,v}) :
    FibrationAdjunctionTwoCategory.{max u v,v} :=
  FibrationAdjunctionTwoCategory.ofElementaryTopos topos

variable {source target : ElementaryTopos.{max u v,v}}

def map (route : source ⟶ target) : object source ⟶ object target :=
  InducedBicategory.mkHom {
    left := predicateMap route.functor
    right := codomainMap route.functor
    comm := (eqToIso (comprehension_naturality route.functor)).symm }

def map₂ {first second : source ⟶ target} (change : first ⟶ second) :
    map first ⟶ map second :=
  InducedBicategory.mkHom₂ {
    left := predicateCell change
    right := codomainCell change
    compatible := by
      change (comprehensionMap source ◁ codomainCell change) ≫
          (eqToIso (comprehension_naturality second.functor)).inv =
        (eqToIso (comprehension_naturality first.functor)).inv ≫
          (predicateCell change ▷ comprehensionMap target)
      apply (Iso.comp_inv_eq (eqToIso (comprehension_naturality second.functor))).mpr
      have same := congrArg
        (fun cell => (eqToIso (comprehension_naturality first.functor)).inv ≫ cell)
        (comprehensionCell_naturality change)
      simpa only [eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.id_comp] using same.symm }

theorem map₂_identity (route : source ⟶ target) :
    map₂ (𝟙 route) = 𝟙 (map route) := by
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · exact predicateCell_identity route.functor
  · exact codomainCell_identity route.functor

theorem map₂_composition {first second third : source ⟶ target}
    (earlier : first ⟶ second) (later : second ⟶ third) :
    map₂ (earlier ≫ later) = map₂ earlier ≫ map₂ later := by
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · exact predicateCell_composition earlier later
  · exact codomainCell_composition earlier later

@[simp] theorem map_predicate (route : source ⟶ target) :
    (map route).hom.left = predicateMap route.functor := rfl

@[simp] theorem map_codomain (route : source ⟶ target) :
    (map route).hom.right = codomainMap route.functor := rfl

@[simp] theorem map₂_predicate {first second : source ⟶ target}
    (change : first ⟶ second) :
    (map₂ change).hom.left = predicateCell change := rfl

@[simp] theorem map₂_codomain {first second : source ⟶ target}
    (change : first ⟶ second) :
    (map₂ change).hom.right = codomainCell change := rfl

end Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
