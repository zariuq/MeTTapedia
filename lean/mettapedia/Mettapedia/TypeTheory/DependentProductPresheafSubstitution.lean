import Mettapedia.TypeTheory.DependentProductRestrictionEvaluation
import Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge

/-!
# The chosen product comparison for a presheaf substitution

The canonical colax comparison along the actual map of element categories
is the inverse of the selected presheaf product base-change isomorphism.
Equality is earned by the full evaluation counit and its adjunction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductPresheafSubstitution

open _root_.CategoryTheory
open CategoryIndexedFamilyGeneralPi DependentProductNativeComparison
open PresheafPiIndexedCwfBridge

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : C ⥤ Type u}

set_option backward.isDefEq.respectTransparency false in
/-- This identifies the actual native map, rather than an unrelated
objectwise equivalence of function carriers. -/
theorem comparison_inverse (substitution : Q ⟶ P) (A : P.Elements ⥤ Type u)
    (B : A.Elements ⥤ Type u) :
    nativeRestriction substitution.mapElements A B =
      (presheafGeneralPi_formation_baseChangeIso substitution A B).inv := by
  let comparison := presheafGeneralPi_formation_baseChangeIso substitution A B
  let projection := CategoryOfElements.π (substitution.mapElements ⋙ A)
  have inverse : Functor.whiskerLeft projection comparison.inv ≫
      generalPiEvaluation (context := Cat.of Q.Elements)
        (substitution.mapElements ⋙ A)
        (DependentProductRestriction.restrictedFamily substitution.mapElements A B) =
      Functor.whiskerLeft (CategoryOfElementsBaseChange.mapPrecompElements substitution.mapElements A)
        (generalPiEvaluation (context := Cat.of P.Elements) A B) := by
    have forward := presheafGeneralPi_evaluation_baseChange substitution A B
    exact ((Functor.isoWhiskerLeft projection comparison).inv_comp_eq).2 forward.symm
  apply ((generalPiAdjunction (context := Cat.of Q.Elements)
    (substitution.mapElements ⋙ A)).homEquiv
      (substitution.mapElements ⋙ generalPiFamily (context := Cat.of P.Elements) A B)
      (DependentProductRestriction.restrictedFamily substitution.mapElements A B)).symm.injective
  change Functor.whiskerLeft projection (nativeRestriction substitution.mapElements A B) ≫
      generalPiEvaluation (context := Cat.of Q.Elements)
        (substitution.mapElements ⋙ A)
        (DependentProductRestriction.restrictedFamily substitution.mapElements A B) =
    Functor.whiskerLeft projection comparison.inv ≫
      generalPiEvaluation (context := Cat.of Q.Elements)
        (substitution.mapElements ⋙ A)
        (DependentProductRestriction.restrictedFamily substitution.mapElements A B)
  exact (DependentProductRestrictionEvaluation.evaluation substitution.mapElements A B).trans inverse.symm

end Mettapedia.TypeTheory.DependentProductPresheafSubstitution
