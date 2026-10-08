import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# Restriction of a strict action to a full object sub-bicategory

An earned profile for every image object restricts the target objects.
Every actual ambient map and cell is retained. The complete functor laws
are inherited through the fully faithful induced hom categories.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.InducedBicategoryPseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe u₁ u₂ v₁ v₂ w₁ w₂
variable {B : Type u₁} [Bicategory.{w₁,v₁} B] [Strict B]
variable {C : Type u₂} [Bicategory.{w₂,v₂} C] [Strict C]

abbrev Target (property : C → Prop) :=
  InducedBicategory C (fun object : {object : C // property object} => object.val)

def restrict (F : StrictPseudofunctor B C) (property : C → Prop)
    (member : ∀ object, property (F.obj object)) :
    StrictPseudofunctor B (Target property) :=
  StrictPseudofunctor.mk'' {
    obj := fun object => ⟨F.obj object, member object⟩
    map := fun route => InducedBicategory.mkHom (F.map route)
    map₂ := fun change => InducedBicategory.mkHom₂ (F.map₂ change)
    map₂_id := by
      intros
      apply InducedBicategory.hom₂_ext
      exact F.map₂_id _
    map₂_comp := by
      intros
      apply InducedBicategory.hom₂_ext
      exact F.map₂_comp _ _
    map_id := by
      intro object
      apply InducedBicategory.hom_ext
      exact F.map_id object
    map_comp := by
      intro first middle last earlier later
      apply InducedBicategory.hom_ext
      exact F.map_comp earlier later
    map₂_whisker_left := by
      intro first middle last earlier later alternate change
      apply InducedBicategory.hom₂_ext
      simp only [InducedBicategory.Hom.category_comp_hom, InducedBicategory.eqToHom_hom]
      change F.map₂ (earlier ◁ change) =
        eqToHom (F.map_comp earlier later) ≫
          F.map earlier ◁ F.map₂ change ≫ eqToHom (F.map_comp earlier alternate).symm
      simpa only [StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
        F.map₂_whisker_left earlier change
    map₂_whisker_right := by
      intro first middle last earlier alternate change later
      apply InducedBicategory.hom₂_ext
      simp only [InducedBicategory.Hom.category_comp_hom, InducedBicategory.eqToHom_hom]
      change F.map₂ (change ▷ later) =
        eqToHom (F.map_comp earlier later) ≫
          F.map₂ change ▷ F.map later ≫ eqToHom (F.map_comp alternate later).symm
      simpa only [StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
        F.map₂_whisker_right change later }

@[simp] theorem restrict_map (F : StrictPseudofunctor B C) (property : C → Prop)
    (member : ∀ object, property (F.obj object)) {first last : B} (route : first ⟶ last) :
    ((restrict F property member).map route).hom = F.map route := rfl

@[simp] theorem restrict_cell (F : StrictPseudofunctor B C) (property : C → Prop)
    (member : ∀ object, property (F.obj object)) {first last : B}
    {earlier later : first ⟶ last} (change : earlier ⟶ later) :
    ((restrict F property member).map₂ change).hom = F.map₂ change := rfl

end Mettapedia.CategoryTheory.InducedBicategoryPseudofunctor
