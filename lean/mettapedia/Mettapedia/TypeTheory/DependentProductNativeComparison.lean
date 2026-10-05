import Mettapedia.TypeTheory.DependentProductRestriction
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Concrete dependent sections and the chosen native product

The arrow-sensitive dependent-section construction and the existing right-Kan
product are right adjoints to the same category-of-elements substitution.
Their canonical comparison commutes with evaluation and abstraction. Thus
change-of-world comparisons apply to the existing native model, rather than
selecting a second dependent-product interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductNativeComparison

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

universe u
variable {C : Type u} [Category.{u} C]

def sectionProduct (A : C ⥤ Type u) : (A.Elements ⥤ Type u) ⥤ (C ⥤ Type u) where
  obj B := dependentFunctions A B
  map f := mapFamily f
  map_id B := by
    ext X value
    apply DependentSection.ext
    intro Y arrow argument
    rfl
  map_comp f g := by
    ext X value
    apply DependentSection.ext
    intro Y arrow argument
    rfl

def sectionAdjunction (A : C ⥤ Type u) :
    (Functor.whiskeringLeft _ _ (Type u)).obj (CategoryOfElements.π A) ⊣
      sectionProduct A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun H B => dependentHomEquiv A B H
      homEquiv_naturality_left_symm := by
        intro H H' B first operation
        ext X value
        rfl
      homEquiv_naturality_right := by
        intro H B B' operation later
        ext X parameter
        apply DependentSection.ext
        intro Y arrow argument
        rfl }

/-- Uniqueness of the actual right adjoint compares the two constructions. -/
noncomputable def nativeIso (A : C ⥤ Type u) :
    (CategoryOfElements.π A).ran ≅ sectionProduct A :=
  Adjunction.rightAdjointUniq
    (generalPiAdjunction (context := Cat.of C) A) (sectionAdjunction A)

theorem nativeIso_evaluation (A : C ⥤ Type u) (B : A.Elements ⥤ Type u) :
    Functor.whiskerLeft (CategoryOfElements.π A) ((nativeIso A).hom.app B) ≫
      (sectionAdjunction A).counit.app B =
        generalPiEvaluation (context := Cat.of C) A B :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ B

set_option backward.isDefEq.respectTransparency false in
theorem nativeIso_abstraction (A : C ⥤ Type u)
    {H : C ⥤ Type u} {B : A.Elements ⥤ Type u}
    (body : CategoryOfElements.π A ⋙ H ⟶ B) :
    generalPiTranspose (context := Cat.of C) A body ≫ (nativeIso A).hom.app B =
      (sectionAdjunction A).homEquiv H B body := by
  apply ((sectionAdjunction A).homEquiv H B).symm.injective
  rw [Equiv.symm_apply_apply]
  change Functor.whiskerLeft (CategoryOfElements.π A)
    (generalPiTranspose (context := Cat.of C) A body ≫ (nativeIso A).hom.app B) ≫
      (sectionAdjunction A).counit.app B = body
  rw [Functor.whiskerLeft_comp, Category.assoc, nativeIso_evaluation]
  exact generalPi_beta (context := Cat.of C) (source := H) A body

/-- Change of worlds for the already selected native dependent product. -/
noncomputable def nativeRestriction {D : Type u} [Category.{u} D]
    (F : C ⥤ D) (A : D ⥤ Type u) (B : A.Elements ⥤ Type u) :
    F ⋙ generalPiFamily (context := Cat.of D) A B ⟶
      generalPiFamily (context := Cat.of C) (F ⋙ A)
        (DependentProductRestriction.restrictedFamily F A B) :=
  Functor.whiskerLeft F ((nativeIso A).hom.app B) ≫
    DependentProductRestriction.comparison F A B ≫
      (nativeIso (F ⋙ A)).inv.app _

end Mettapedia.TypeTheory.DependentProductNativeComparison
