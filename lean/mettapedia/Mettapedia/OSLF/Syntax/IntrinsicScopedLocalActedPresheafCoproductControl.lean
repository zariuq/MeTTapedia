import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafMultiplicityControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafExtension
import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Two retained event alternatives under presheaf extension

The actual coproduct of generic event presheaves contains two separately tagged
authored beta witnesses. The left Kan extension interprets both injections,
and density determines its maps on the whole coproduct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheafCoproductControl

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheafMultiplicityControl
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

abbrev eventPresheaf := event.{0} sourceRules noEquations [] ()

/-- Two independently tagged alternatives over the actual event carrier. -/
abbrev alternatives := eventPresheaf ⨿ eventPresheaf

def generalAlternative : alternatives.obj (Opposite.op sourceStage) :=
  (coprod.inl : eventPresheaf ⟶ alternatives).app _ generalSection

def identityAlternative : alternatives.obj (Opposite.op sourceStage) :=
  (coprod.inr : eventPresheaf ⟶ alternatives).app _ identitySection

/-- Both actual beta histories occur, in different summands of the colimit. -/
theorem alternatives_distinct : generalAlternative ≠ identityAlternative := by
  intro same
  have tagged := congrArg
    ((FunctorToTypes.binaryCoproductIso eventPresheaf eventPresheaf).hom.app
      (Opposite.op sourceStage)) same
  simp only [generalAlternative, identityAlternative,
    FunctorToTypes.inl_comp_binaryCoproductIso_hom_apply,
    FunctorToTypes.inr_comp_binaryCoproductIso_hom_apply] at tagged
  cases tagged

universe u
variable {D : Type u} [Category.{0} D] [CartesianMonoidalCategory D]
variable [HasPullbacks D] [HasColimitsOfSize.{0, 0} D]

/-- The actual extension of this two-event colimit is the coproduct of
the model's two generic event meanings. -/
def extensionAlternativesIso (model : CategoricalModel sourceRules noEquations (D := D)) :
    ((Mettapedia.CategoryTheory.PresheafStructuredExtension.embedding.{0, 0, 0, 0}).lan.obj model.classifyingFunctor).obj alternatives ≅
      model.classifyingFunctor.obj (eventObject sourceRules noEquations [] ()) ⨿
        model.classifyingFunctor.obj (eventObject sourceRules noEquations [] ()) :=
  Mettapedia.CategoryTheory.PresheafStructuredExtension.extensionCoproductIso model.classifyingFunctor
    (eventObject sourceRules noEquations [] ()) (eventObject sourceRules noEquations [] ())

/-- The general rule's summand is interpreted using its own injection. -/
theorem extension_inl (model : CategoricalModel sourceRules noEquations (D := D)) :
    ((Mettapedia.CategoryTheory.PresheafStructuredExtension.embedding.{0, 0, 0, 0}).lan.obj model.classifyingFunctor).map
        (coprod.inl : eventPresheaf ⟶ alternatives) ≫
      (extensionAlternativesIso model).hom =
        ((Mettapedia.CategoryTheory.PresheafStructuredExtension.unitIso.{0, 0, 0, 0, u}).app model.classifyingFunctor).inv.app
          (eventObject sourceRules noEquations [] ()) ≫ coprod.inl :=
  Mettapedia.CategoryTheory.PresheafStructuredExtension.extensionCoproductIso_inl model.classifyingFunctor
    (eventObject sourceRules noEquations [] ()) (eventObject sourceRules noEquations [] ())

/-- The specialized rule's summand is interpreted using the other injection. -/
theorem extension_inr (model : CategoricalModel sourceRules noEquations (D := D)) :
    ((Mettapedia.CategoryTheory.PresheafStructuredExtension.embedding.{0, 0, 0, 0}).lan.obj model.classifyingFunctor).map
        (coprod.inr : eventPresheaf ⟶ alternatives) ≫
      (extensionAlternativesIso model).hom =
        ((Mettapedia.CategoryTheory.PresheafStructuredExtension.unitIso.{0, 0, 0, 0, u}).app model.classifyingFunctor).inv.app
          (eventObject sourceRules noEquations [] ()) ≫ coprod.inr :=
  Mettapedia.CategoryTheory.PresheafStructuredExtension.extensionCoproductIso_inr model.classifyingFunctor
    (eventObject sourceRules noEquations [] ()) (eventObject sourceRules noEquations [] ())

omit [CartesianMonoidalCategory D] [HasPullbacks D] in
/-- Restriction determines maps on this actual colimit, including both
retained event alternatives. -/
theorem maps_determined_on_alternatives
    {L K : Mettapedia.CategoryTheory.PresheafStructuredExtension.CocontinuousFunctors.{0, 0, 0, 0, u}
      (C := Classifier sourceRules noEquations) (D := D)} (α β : L ⟶ K)
    (same : (Mettapedia.CategoryTheory.PresheafStructuredExtension.restrict.{0, 0, 0, 0, u}).map α =
      (Mettapedia.CategoryTheory.PresheafStructuredExtension.restrict.{0, 0, 0, 0, u}).map β) :
    α.hom.app alternatives = β.hom.app alternatives :=
  Mettapedia.CategoryTheory.PresheafStructuredExtension.extension_maps_equal_on_coproduct α β same
    (eventObject sourceRules noEquations [] ()) (eventObject sourceRules noEquations [] ())

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheafCoproductControl
