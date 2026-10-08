import Mettapedia.TypeTheory.DependentProductNativeComparison

/-!
# The dependent-product comparison is natural in evidence families

Restriction of a dependent function acts on its actual proof-valued
codomain. Naturality is established before conjugating by the canonical
right-adjoint comparison. This gives the colax action on the chosen native
product functors, rather than only unrelated component maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductRestrictionAction

open CategoryTheory
open DependentProductNativeComparison DependentProductRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

abbrev precomposition (F : C ⥤ D) : (D ⥤ Type u) ⥤ (C ⥤ Type u) :=
  (Functor.whiskeringLeft C D (Type u)).obj F

def sectionComparison (F : C ⥤ D) (A : D ⥤ Type u) :
    sectionProduct A ⋙ precomposition F ⟶
      precomposition (Functor.Elements.precomp F A) ⋙ sectionProduct (F ⋙ A) where
  app B := comparison F A B
  naturality B B' evidenceMap := by
    ext X value
    exact comparison_family F A evidenceMap value

/-- The canonical mate assembled as a natural transformation between
the actual evidence-family functors. -/
noncomputable def nativeComparison (F : C ⥤ D) (A : D ⥤ Type u) :
    (CategoryOfElements.π A).ran ⋙ precomposition F ⟶
      precomposition (Functor.Elements.precomp F A) ⋙ (CategoryOfElements.π (F ⋙ A)).ran :=
  (Functor.isoWhiskerRight (nativeIso A) (precomposition F)).hom ≫
    sectionComparison F A ≫
      (Functor.isoWhiskerLeft (precomposition (Functor.Elements.precomp F A))
        (nativeIso (F ⋙ A))).inv

theorem nativeComparison_app (F : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) :
    (nativeComparison F A).app B = nativeRestriction F A B := rfl

end Mettapedia.TypeTheory.DependentProductRestrictionAction
