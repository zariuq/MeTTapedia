import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasSemantics

/-!
# Complete application beneath a schema reference binder

The curried reference-body application is compared with the independently
formed continuation operation. Precomposition by the actual unit insertion
and naturality of currying preserve every supplied metavariable function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations NamePassingBindingClosedOperations

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (primitives : Operations C)

def appliedBody : primitives.boundBodyObject ⊗ primitives.names ⟶ primitives.boundBodyObject :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (lift (call (fst (primitives.boundBodyObject ⊗ primitives.names) primitives.names ≫
      fst primitives.boundBodyObject primitives.names)
      (snd (primitives.boundBodyObject ⊗ primitives.names) primitives.names))
      (fst (primitives.boundBodyObject ⊗ primitives.names) primitives.names ≫
        snd primitives.boundBodyObject primitives.names) ≫ primitives.application)

theorem call_as_evaluation {X A B : C} (function : X ⟶ (A ⟶[C] B)) (argument : X ⟶ A) :
    call function argument = lift argument function ≫ (ihom.ev A).app B := by
  unfold call Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.evaluation
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange
  rw [← Category.assoc, comp_lift]
  simp only [lift_snd, lift_fst]

theorem appliedBody_read {Z : C} (body : Z ⟶ primitives.boundBodyObject) (argument : Z ⟶ primitives.names) :
    MonoidalClosed.curry
      (lift (MonoidalClosed.uncurry body) (snd primitives.names Z ≫ argument) ≫ primitives.application) =
        lift body argument ≫ appliedBody primitives := by
  unfold appliedBody Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange
  rw [← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  rw [call_as_evaluation]
  simp only [comp_lift_assoc, lift_fst_assoc,
    lift_fst, lift_snd, whiskerLeft_fst, whiskerLeft_snd_assoc]
  congr 2
  rw [MonoidalClosed.uncurry_eq]
  congr 1
  apply hom_ext <;> simp

/-- The canonical unit conversion commutes with application beneath the
reference binder. The supplied function is unrestricted. -/
theorem appliedBody_unit_read {Z : C}
    (body : Z ⟶ (ihom (primitives.names ⊗ 𝟙_ C)).obj primitives.termObject)
    (argument : Z ⟶ primitives.names) :
    MonoidalClosed.curry
      (lift (MonoidalClosed.uncurry body) (snd (primitives.names ⊗ 𝟙_ C) Z ≫ argument) ≫
        primitives.application) ≫ boundValue primitives =
      lift (body ≫ boundValue primitives) argument ≫ appliedBody primitives := by
  unfold boundValue
  rw [MonoidalClosed.curry_pre_app]
  rw [← appliedBody_read]
  apply congrArg MonoidalClosed.curry
  rw [MonoidalClosed.uncurry_pre_app, ← Category.assoc, comp_lift]
  simp only [whiskerRight_snd_assoc]

theorem reference_application_curry {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredEquations.metas)
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.tm, .nm]) :
    MonoidalClosed.curry
      (((generated primitives).model.interp NamePassing.AuthoredEquations.metas
        (NamePassing.AuthoredEquations.schemaApplication
          (NamePassing.AuthoredEquations.boundBody (.var .zero)) (.var (.succ (.succ .zero))))).value
            ((primitives.names ⊗ 𝟙_ C) ⊗ Z) (snd _ _ ≫ parameters)
            ((generated primitives).model.extendEnv [.nm] environment)) ≫ boundValue primitives =
      lift (parameters ≫ fst _ _ ≫ boundValue primitives)
        (environment .nm (.succ .zero)) ≫ appliedBody primitives := by
  have bodyValue := congrArg MonoidalClosed.uncurry
    (reference_body_curry primitives parameters environment)
  rw [MonoidalClosed.uncurry_curry] at bodyValue
  erw [schema_application_value, bodyValue, Model.interp_var]
  simp only [Model.extendEnv, lift_snd_assoc]
  dsimp only [Model.ctx, ClosedPresentation.Operations.model, ofClosed,
    generated, contextOf, NamePassingConstructorInterpretation.sortValue, familyOf]
  simpa only [Category.assoc] using
    (appliedBody_unit_read primitives
      (parameters ≫ fst ((ihom (primitives.names ⊗ 𝟙_ C)).obj primitives.termObject) (𝟙_ C))
      (environment .nm (.succ .zero)))

theorem definition_left_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredEquations.metas)
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.tm, .nm]) :
    ((generated primitives).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.lhs).value Z parameters environment =
      lift (lift (environment .tm .zero) ((parameters ≫ fst _ _) ≫ boundValue primitives) ≫
        primitives.definition) (environment .nm (.succ .zero)) ≫ primitives.application := by
  erw [schema_application_value, schema_definition_value, reference_body_curry]
  simp only [Model.interp_var]

theorem definition_right_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredEquations.metas)
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.tm, .nm]) :
    ((generated primitives).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.rhs).value Z parameters environment =
      lift (environment .tm .zero)
        (lift (parameters ≫ fst _ _ ≫ boundValue primitives) (environment .nm (.succ .zero)) ≫
          appliedBody primitives) ≫ primitives.definition := by
  erw [schema_definition_value, reference_application_curry]
  simp only [Model.interp_var]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
