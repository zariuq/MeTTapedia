import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions
import Mathlib.CategoryTheory.Elements

/-!
# Dependent-product comparison under change of worlds

Restriction of a dependent function remembers the mapped substitution arrow,
the argument and its evidence. Every functor gives a comparison in this
direction. This does not assert that the comparison is invertible.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductRestriction

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]

abbrev restrictedFamily (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) : (F ⋙ A).Elements ⥤ Type u :=
  Functor.Elements.precomp F A ⋙ B

/-- The component of the dependent-product mate, with no choice of a
representative arrow or inhabitant of an evidence fibre. -/
def restrictSection (F : C ⥤ D) (A : D ⥤ Type u) (B : A.Elements ⥤ Type u)
    {X : C} (value : DependentSection A B (F.obj X)) :
    DependentSection (F ⋙ A) (restrictedFamily F A B) X where
  app Y arrow argument := value.app (F.obj Y) (F.map arrow) argument
  naturality {Y Z} step arrow argument := by
    change B.map (argumentMap A (F.map step) argument)
      (value.app (F.obj Y) (F.map arrow) argument) = _
    rw [F.map_comp]
    exact value.naturality (F.map step) (F.map arrow) argument

/-- Restriction commutes with all later substitutions. -/
theorem restrictSection_natural (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) {X Y : C} (step : X ⟶ Y)
    (value : DependentSection A B (F.obj X)) :
    restrictSection F A B (DependentSection.restrict A B (F.map step) value) =
      DependentSection.restrict (F ⋙ A) (restrictedFamily F A B) step
        (restrictSection F A B value) := by
  apply DependentSection.ext
  intro Z arrow argument
  change value.app (F.obj Z) (F.map step ≫ F.map arrow) argument =
    value.app (F.obj Z) (F.map (step ≫ arrow)) argument
  rw [F.map_comp]

/-- The canonical colax Π comparison as an actual natural transformation. -/
def comparison (F : C ⥤ D) (A : D ⥤ Type u) (B : A.Elements ⥤ Type u) :
    F ⋙ dependentFunctions A B ⟶
      dependentFunctions (F ⋙ A) (restrictedFamily F A B) where
  app X := TypeCat.ofHom (restrictSection F A B)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro value
    exact restrictSection_natural F A B step value

theorem comparison_evaluation (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) {X : C}
    (value : DependentSection A B (F.obj X)) (argument : A.obj (F.obj X)) :
    (restrictSection F A B value).app X (𝟙 X) argument =
      value.app (F.obj X) (𝟙 (F.obj X)) argument := by
  change value.app (F.obj X) (F.map (𝟙 X)) argument = _
  rw [F.map_id]

theorem restrictSection_id (A : C ⥤ Type u) (B : A.Elements ⥤ Type u)
    {X : C} (value : DependentSection A B X) :
    restrictSection (𝟭 C) A B value = value := by
  apply DependentSection.ext
  intro Y arrow argument
  rfl

/-- Composition retains the same arrow and evidence, not just the same
truth value of an inhabited product. -/
theorem restrictSection_comp (F : C ⥤ D) (G : D ⥤ E)
    (A : E ⥤ Type u) (B : A.Elements ⥤ Type u) {X : C}
    (value : DependentSection A B (G.obj (F.obj X))) :
    restrictSection (F ⋙ G) A B value =
      restrictSection F (G ⋙ A) (restrictedFamily G A B)
        (restrictSection G A B value) := by
  apply DependentSection.ext
  intro Y arrow argument
  rfl

/-- The comparison also respects maps between dependent evidence families. -/
theorem comparison_family (F : C ⥤ D) (A : D ⥤ Type u)
    {B B' : A.Elements ⥤ Type u} (map : B ⟶ B') {X : C}
    (value : DependentSection A B (F.obj X)) :
    restrictSection F A B' ((mapFamily map).app (F.obj X) value) =
      (mapFamily (Functor.whiskerLeft (Functor.Elements.precomp F A) map)).app X
        (restrictSection F A B value) := by
  apply DependentSection.ext
  intro Y arrow argument
  rfl

end Mettapedia.TypeTheory.DependentProductRestriction
