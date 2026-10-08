import Mettapedia.CategoryTheory.ElementaryToposImageActionCoherence
import Mettapedia.CategoryTheory.FibrationTwoCellFaithfulness
import Mettapedia.CategoryTheory.PseudoTwoArrowStrict

/-!
# Horizontal coherence of the image-comprehension action

Horizontal substitution respects the actual identity and composition
isomorphisms at both endpoints. The chosen comparisons retain the same
predicate displays, arrow displays and complete base transformations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Bicategory
open FibrationTwoCategory

universe u v

attribute [local instance] comp_preservesFiniteLimits

theorem map_identity (source : ElementaryTopos.{max u v,v}) :
    map (𝟙 source) = 𝟙 (object source) := by
  apply InducedBicategory.hom_ext
  apply PseudoTwoArrow.Hom.ext_of_cell
    predicateMap_identity.{u,v} codomainMap_identity.{u,v}
    (mapIdentity source).hom.hom <;> rfl

theorem map_composition {source middle target : ElementaryTopos.{max u v,v}}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    map (first ≫ second) = map first ≫ map second := by
  apply InducedBicategory.hom_ext
  apply PseudoTwoArrow.Hom.ext_of_cell
    (predicateMap_composition.{u,v} first.functor second.functor)
    (codomainMap_composition.{u,v} first.functor second.functor)
    (mapComposition first second).hom.hom <;> rfl

theorem mapIdentity_eq (source : ElementaryTopos.{max u v,v}) :
    mapIdentity source = eqToIso (map_identity source) := by
  apply Iso.ext
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · change (eqToIso predicateMap_identity.{u,v}).hom =
      (eqToHom (map_identity source)).hom.left
    rw [InducedBicategory.eqToHom_hom, PseudoTwoArrow.eqToHom_left]
    rfl
  · change (eqToIso codomainMap_identity.{u,v}).hom =
      (eqToHom (map_identity source)).hom.right
    rw [InducedBicategory.eqToHom_hom, PseudoTwoArrow.eqToHom_right]
    rfl

theorem mapComposition_eq {source middle target : ElementaryTopos.{max u v,v}}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    mapComposition first second = eqToIso (map_composition first second) := by
  apply Iso.ext
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · change (eqToIso (predicateMap_composition.{u,v} first.functor second.functor)).hom =
      (eqToHom (map_composition first second)).hom.left
    rw [InducedBicategory.eqToHom_hom, PseudoTwoArrow.eqToHom_left]
    rfl
  · change (eqToIso (codomainMap_composition.{u,v} first.functor second.functor)).hom =
      (eqToHom (map_composition first second)).hom.right
    rw [InducedBicategory.eqToHom_hom, PseudoTwoArrow.eqToHom_right]
    rfl

theorem map₂_whiskerLeft {source middle target : ElementaryTopos.{max u v,v}}
    (first : source ⟶ middle) {earlier later : middle ⟶ target}
    (change : earlier ⟶ later) :
    map₂ (first ◁ change) = (mapComposition first earlier).hom ≫
      map first ◁ map₂ change ≫ (mapComposition first later).inv := by
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · change predicateCell (Functor.whiskerLeft first.functor change) =
      eqToHom (predicateMap_composition.{u,v} first.functor earlier.functor) ≫
        (predicateMap first.functor ◁ predicateCell change) ≫
          eqToHom (predicateMap_composition.{u,v} first.functor later.functor).symm
    simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
      (Iso.eq_comp_inv (eqToIso (predicateMap_composition.{u,v} first.functor later.functor))).mpr
        (predicateCell_whiskerLeft.{u,v} first.functor change)
  · change codomainCell (Functor.whiskerLeft first.functor change) =
      eqToHom (codomainMap_composition.{u,v} first.functor earlier.functor) ≫
        (codomainMap first.functor ◁ codomainCell change) ≫
          eqToHom (codomainMap_composition.{u,v} first.functor later.functor).symm
    simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
      (Iso.eq_comp_inv (eqToIso (codomainMap_composition.{u,v} first.functor later.functor))).mpr
        (codomainCell_whiskerLeft.{u,v} first.functor change)

theorem map₂_whiskerRight {source middle target : ElementaryTopos.{max u v,v}}
    {earlier later : source ⟶ middle} (change : earlier ⟶ later)
    (last : middle ⟶ target) :
    map₂ (change ▷ last) = (mapComposition earlier last).hom ≫
      map₂ change ▷ map last ≫ (mapComposition later last).inv := by
  apply InducedBicategory.hom₂_ext
  apply PseudoTwoArrow.Cell.ext
  · change predicateCell (Functor.whiskerRight change last.functor) =
      eqToHom (predicateMap_composition.{u,v} earlier.functor last.functor) ≫
        (predicateCell change ▷ predicateMap last.functor) ≫
          eqToHom (predicateMap_composition.{u,v} later.functor last.functor).symm
    simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
      (Iso.eq_comp_inv (eqToIso (predicateMap_composition.{u,v} later.functor last.functor))).mpr
        (predicateCell_whiskerRight.{u,v} last.functor change)
  · change codomainCell (Functor.whiskerRight change last.functor) =
      eqToHom (codomainMap_composition.{u,v} earlier.functor last.functor) ≫
        (codomainCell change ▷ codomainMap last.functor) ≫
          eqToHom (codomainMap_composition.{u,v} later.functor last.functor).symm
    simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
      (Iso.eq_comp_inv (eqToIso (codomainMap_composition.{u,v} later.functor last.functor))).mpr
        (codomainCell_whiskerRight.{u,v} last.functor change)

/-- The complete ambient adjunction action. Higher-order and closed
profiles are additional object structure of its eventual restricted target. -/
def normalizedAction : StrictPseudofunctor ElementaryTopos.{max u v,v}
    FibrationAdjunctionTwoCategory.{max u v,v} :=
  StrictPseudofunctor.mk'' {
    obj := object
    map := map
    map₂ := map₂
    map₂_id := map₂_identity
    map₂_comp := map₂_composition
    map_id := map_identity
    map_comp := map_composition
    map₂_whisker_left := by
      intro source middle target first earlier later change
      simpa only [mapComposition_eq.{u,v}, eqToIso.hom, eqToIso.inv] using
        map₂_whiskerLeft.{u,v} first change
    map₂_whisker_right := by
      intro source middle target earlier later change last
      simpa only [mapComposition_eq.{u,v}, eqToIso.hom, eqToIso.inv] using
        map₂_whiskerRight.{u,v} change last }

end Mettapedia.CategoryTheory.ElementaryToposImageComprehensionAction
