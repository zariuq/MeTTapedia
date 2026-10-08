import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestriction
import Mettapedia.TypeTheory.DisplayedPresheafSigmaFunctor
import Mettapedia.TypeTheory.DependentProductRestrictionAction

/-!
# Natural dependent-type comparisons for theory restriction

Theory precomposition acts on categories of dependent evidence families.
Comprehension reassociation identifies the restricted dependent codomain.
The sum comparison is invertible and the product comparison is colax; both
are natural in the supplied maps of evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionAction

open CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafSlicePi
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafTheoryRestriction
open DisplayedPresheafSigmaFunctor DependentProductRestrictionAction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

abbrev restrictionFunctor (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    DisplayedFamily P ⥤ DisplayedFamily (F.op ⋙ P) :=
  precomposition (Functor.Elements.precomp F.op P)

abbrev codomainFunctor (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    DisplayedFamily (totalSpace A) ⥤ DisplayedFamily (totalSpace (restrictFamily F P A)) :=
  restrictionFunctor F (totalSpace A) ⋙ reindexFunctor (totalComparison F P A).hom

set_option backward.isDefEq.respectTransparency false in
/-- Comprehension reassociation is natural in the evidence codomain. -/
def codomainIso (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    precomposition (displayedToTotalElements A) ⋙
        precomposition (Functor.Elements.precomp (Functor.Elements.precomp F.op P) A) ≅
      codomainFunctor F P A ⋙ precomposition (displayedToTotalElements (restrictFamily F P A)) :=
  NatIso.ofComponents (codomainComparison F P A) (by
    intro B B' operation
    ext point value
    change ((codomainComparison F P A B').hom.app point)
        (operation.app ((Functor.Elements.precomp
          (Functor.Elements.precomp F.op P) A ⋙ displayedToTotalElements A).obj point) value) =
      operation.app ((displayedToTotalElements (restrictFamily F P A) ⋙
        (totalComparison F P A).hom.mapElements ⋙
          Functor.Elements.precomp F.op (totalSpace A)).obj point)
        ((codomainComparison F P A B).hom.app point value)
    erw [codomainComparison_app, codomainComparison_app]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The sum comparison is a natural isomorphism of evidence-family functors. -/
def sumIso (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    sumFunctor A ⋙ restrictionFunctor F P ≅
      codomainFunctor F P A ⋙ sumFunctor (restrictFamily F P A) :=
  NatIso.ofComponents (sumComparison F P A) (by
    intro B B' operation
    ext point value
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The chosen native dependent products have a natural colax comparison. -/
noncomputable def productMap (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P) :
    displayedProductFunctor A ⋙ restrictionFunctor F P ⟶
      codomainFunctor F P A ⋙ displayedProductFunctor (restrictFamily F P A) :=
  Functor.whiskerLeft (precomposition (displayedToTotalElements A))
      (nativeComparison (Functor.Elements.precomp F.op P) A) ≫
    (Functor.isoWhiskerRight (codomainIso F P A)
      (CategoryOfElements.π (restrictFamily F P A)).ran).hom

/-- The natural comparison uses the already established native component. -/
theorem productMap_app (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (productMap F P A).app B = productComparison F P A B := rfl

end Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionAction
