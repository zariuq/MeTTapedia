import Mettapedia.TypeTheory.PresheafDependentAdjunction
import Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge

/-!
# The existing indexed-family product in slice semantics

The dependent product already constructed along the category-of-elements
projection agrees with product along the total-presheaf projection. The
comparison uses the existing equivalence between their element categories
and uniqueness of right adjoints. Its counit law compares evaluation, so
the result identifies the function operations as well as their objects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSlicePi

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice DisplayedPresheafSliceSubstitution
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open PresheafDependentAdjunction

universe u
variable {C : Type u} [Category.{u} C]
variable {P : Face.{u, u, u} C}

/-- Regroup the elements of an extended presheaf context, then apply
the existing indexed-family right-Kan product. -/
noncomputable def displayedProductFunctor
    (A : DisplayedFamily.{u, u, u, u} P) :
    DisplayedFamily.{u, u, u, u} (totalSpace A) ⥤
      DisplayedFamily.{u, u, u, u} P :=
  (totalElementsEquivalence A).congrLeft.functor ⋙
    (CategoryOfElements.π A).ran

/-- The indexed-family product has the same left adjoint as the product
along the total-presheaf projection. -/
noncomputable def displayedProductAdjunction
    (A : DisplayedFamily.{u, u, u, u} P) :
    reindexFunctor (totalProjection A) ⊣ displayedProductFunctor A :=
  ((generalPiAdjunction (context := Cat.of P.Elements) A).comp
    ((totalElementsEquivalence A).congrLeft (E := Type u)).symm.toAdjunction).ofNatIsoLeft
      ((Functor.whiskeringLeft _ _ (Type u)).mapIso
        (eqToIso (totalElementsEquivalence_over_base A)))

/-- Natural comparison with the existing category-indexed family product. -/
noncomputable def familyProductComparison
    (A : DisplayedFamily.{u, u, u, u} P) :
    (totalProjection A).mapElements.ran ≅ displayedProductFunctor A :=
  Adjunction.rightAdjointUniq
    (familyAdjunction (totalProjection A)) (displayedProductAdjunction A)

/-- The product comparison preserves application to dependent arguments. -/
theorem familyProductComparison_evaluation
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    (reindexFunctor (totalProjection A)).map
        ((familyProductComparison A).hom.app B) ≫
      (displayedProductAdjunction A).counit.app B =
        (familyAdjunction (totalProjection A)).counit.app B :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ B

/-- On an actual displayed codomain, slice Pi is the total space of the
existing indexed-family Pi, up to its canonical natural comparison. -/
noncomputable def piSliceIso
    (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A)) :
    (dependentProduct (totalProjection A)).obj
        ((totalFunctor (totalSpace A)).obj B) ≅
      (totalFunctor P).obj
        (generalPiFamily (context := Cat.of P.Elements) A
          (displayedToTotalElements A ⋙ B)) :=
  (totalFunctor P).mapIso
    (((totalProjection A).mapElements.ran).mapIso (projectionFibreIso B).symm ≪≫
      (familyProductComparison A).app B)

end Mettapedia.TypeTheory.DisplayedPresheafSlicePi
