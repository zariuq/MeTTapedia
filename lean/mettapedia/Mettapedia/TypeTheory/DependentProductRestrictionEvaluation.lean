import Mettapedia.TypeTheory.DependentProductRestrictionAction

/-!
# Evaluation and abstraction under change of theory

The canonical dependent-product comparison is the mate of restriction of
the actual evaluation map. Consequently restriction commutes with lambda
abstraction. These laws concern the chosen native right adjoint, including
its maps of evidence; they do not assume an invertible product comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductRestrictionEvaluation

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open CategoryIndexedFamilyGeneralPi DependentProductNativeComparison
open DependentProductRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

set_option backward.isDefEq.respectTransparency false in
/-- The colax product comparison transports the supplied function's
evaluation to the same dependent evidence in the changed theory. -/
theorem evaluation (F : C ⥤ D) (A : D ⥤ Type u) (B : A.Elements ⥤ Type u) :
    Functor.whiskerLeft (CategoryOfElements.π (F ⋙ A)) (nativeRestriction F A B) ≫
        generalPiEvaluation (context := Cat.of C) (F ⋙ A) (restrictedFamily F A B) =
      Functor.whiskerLeft (Functor.Elements.precomp F A)
        (generalPiEvaluation (context := Cat.of D) A B) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  have sourceEvaluation := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun map => map.app ((Functor.Elements.precomp F A).obj point))
      (nativeIso_evaluation A B)) value
  have targetEvaluation := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun map => map.app point)
      (nativeIso_evaluation (F ⋙ A) (restrictedFamily F A B)))
    ((nativeRestriction F A B).app point.1 value)
  have sectionSquare := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun map => map.app point.1) (nativeRestriction_section F A B)) value
  change
    (generalPiEvaluation (context := Cat.of C) (F ⋙ A) (restrictedFamily F A B)).app point
      ((nativeRestriction F A B).app point.1 value) =
    (generalPiEvaluation (context := Cat.of D) A B).app
      ((Functor.Elements.precomp F A).obj point) value
  erw [← targetEvaluation]
  change (((nativeIso (F ⋙ A)).hom.app (restrictedFamily F A B)).app point.1
    ((nativeRestriction F A B).app point.1 value)).app point.1 (𝟙 point.1) point.2 = _
  erw [sectionSquare]
  erw [comparison_evaluation]
  exact sourceEvaluation

set_option backward.isDefEq.respectTransparency false in
/-- Changing a theory and abstracting a supplied dependent body commute
through the canonical product comparison. -/
theorem abstraction (F : C ⥤ D) (A : D ⥤ Type u)
    {H : D ⥤ Type u} {B : A.Elements ⥤ Type u}
    (body : CategoryOfElements.π A ⋙ H ⟶ B) :
    Functor.whiskerLeft F (generalPiTranspose (context := Cat.of D) A body) ≫
        nativeRestriction F A B =
      generalPiTranspose (context := Cat.of C) (F ⋙ A)
        (Functor.whiskerLeft (Functor.Elements.precomp F A) body) := by
  apply ((generalPiAdjunction (context := Cat.of C) (F ⋙ A)).homEquiv
    (F ⋙ H) (restrictedFamily F A B)).symm.injective
  erw [Equiv.symm_apply_apply]
  change Functor.whiskerLeft (CategoryOfElements.π (F ⋙ A))
      (Functor.whiskerLeft F (generalPiTranspose (context := Cat.of D) A body) ≫
        nativeRestriction F A B) ≫
      generalPiEvaluation (context := Cat.of C) (F ⋙ A) (restrictedFamily F A B) = _
  erw [Functor.whiskerLeft_comp, Category.assoc, evaluation]
  change Functor.whiskerLeft (Functor.Elements.precomp F A)
    (Functor.whiskerLeft (CategoryOfElements.π A)
      (generalPiTranspose (context := Cat.of D) A body)) ≫
    Functor.whiskerLeft (Functor.Elements.precomp F A)
      (generalPiEvaluation (context := Cat.of D) A B) = _
  rw [← Functor.whiskerLeft_comp]
  exact congrArg (Functor.whiskerLeft (Functor.Elements.precomp F A))
    (generalPi_beta (context := Cat.of D) (source := H) A body)

set_option backward.isDefEq.respectTransparency false in
/-- The selected canonical product comparison preserves identity routes. -/
theorem restriction_identity (A : C ⥤ Type u) (B : A.Elements ⥤ Type u) :
    nativeRestriction (𝟭 C) A B = 𝟙 (generalPiFamily (context := Cat.of C) A B) := by
  apply (cancel_mono ((nativeIso A).hom.app B)).mp
  erw [nativeRestriction_id_section]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Sequential restriction has the same canonical comparison as the
composite theory route. -/
theorem restriction_composition {E : Type u} [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (A : E ⥤ Type u) (B : A.Elements ⥤ Type u) :
    nativeRestriction (F ⋙ G) A B =
      Functor.whiskerLeft F (nativeRestriction G A B) ≫
        nativeRestriction F (G ⋙ A) (restrictedFamily G A B) := by
  apply (cancel_mono ((nativeIso ((F ⋙ G) ⋙ A)).hom.app
    (restrictedFamily (F ⋙ G) A B))).mp
  exact (nativeRestriction_section (F ⋙ G) A B).trans
    (nativeRestriction_comp_section F G A B).symm

end Mettapedia.TypeTheory.DependentProductRestrictionEvaluation
