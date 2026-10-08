import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations
import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredEquations
import Mettapedia.OSLF.Syntax.BindingClosedAuthoredPresentation

/-!
# Whole categorical readings of the authored scope schemas

The generated binding model is evaluated with arbitrary supplied metavariable
families and ambient environments. Empty binder arguments recover their whole
readings by naturality and the unit comparison; reference-bound arguments keep
their complete curried functions.
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
variable {metas : List (MetaArity NamePassing.Presentation.signature)}
variable {context : Ctx NamePassing.Presentation.signature}
variable {Z : C} (parameters : Z ⟶ (generated primitives).model.family metas)
variable (environment : (generated primitives).model.Env Z context)

theorem empty_argument {sort : NamePassing.Presentation.Srt}
    (term : Term (withMetas NamePassing.Presentation.signature metas) context sort) :
    MonoidalClosed.curry
        (((generated primitives).model.interp metas term).value (𝟙_ C ⊗ Z)
          (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)) ≫
      emptyValue ((generated primitives).sort sort) =
        ((generated primitives).model.interp metas term).value Z parameters environment := by
  have natural := ((generated primitives).model.interp metas term).natural
    (snd (𝟙_ C) Z) parameters environment
  change ((generated primitives).model.interp metas term).value (𝟙_ C ⊗ Z)
    (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment) =
      snd _ _ ≫ ((generated primitives).model.interp metas term).value Z parameters environment at natural
  rw [natural]
  exact empty_curry _

theorem schema_application_value
    (function : Term (withMetas NamePassing.Presentation.signature metas) context .tm)
    (argument : Term (withMetas NamePassing.Presentation.signature metas) context .nm) :
    ((generated primitives).model.interp metas
      (.op (.inl .application) (.cons function (.cons argument .nil)))).value Z parameters environment =
      lift (((generated primitives).model.interp metas function).value Z parameters environment)
        (((generated primitives).model.interp metas argument).value Z parameters environment) ≫
          primitives.application := by
  change lift
    (MonoidalClosed.curry (((generated primitives).model.interp metas function).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)))
    (lift (MonoidalClosed.curry (((generated primitives).model.interp metas argument).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment))) (toUnit Z)) ≫
        (lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.names) ≫ primitives.application) = _
  rw [← Category.assoc, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc]
  erw [empty_argument, empty_argument]

theorem schema_definition_value
    (value : Term (withMetas NamePassing.Presentation.signature metas) context .tm)
    (body : Term (withMetas NamePassing.Presentation.signature metas) (.nm :: context) .tm) :
    ((generated primitives).model.interp metas
      (.op (.inl .definition) (.cons value (.cons body .nil)))).value Z parameters environment =
      lift (((generated primitives).model.interp metas value).value Z parameters environment)
        (MonoidalClosed.curry
          (((generated primitives).model.interp metas body).value
            ((primitives.names ⊗ 𝟙_ C) ⊗ Z) (snd _ _ ≫ parameters)
            ((generated primitives).model.extendEnv [.nm] environment)) ≫ boundValue primitives) ≫
          primitives.definition := by
  change lift
    (MonoidalClosed.curry (((generated primitives).model.interp metas value).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)))
    (lift (MonoidalClosed.curry
      (((generated primitives).model.interp metas body).value ((primitives.names ⊗ 𝟙_ C) ⊗ Z)
        (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [.nm] environment))) (toUnit Z)) ≫
        (lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ boundValue primitives) ≫ primitives.definition) = _
  rw [← Category.assoc, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc]
  erw [empty_argument]

theorem schema_carrier_value
    (name : Term (withMetas NamePassing.Presentation.signature metas) context .nm)
    (value body : Term (withMetas NamePassing.Presentation.signature metas) context .tm) :
    ((generated primitives).model.interp metas
      (.op (.inl .carrier) (.cons name (.cons value (.cons body .nil))))).value Z parameters environment =
      lift (((generated primitives).model.interp metas name).value Z parameters environment)
        (lift (((generated primitives).model.interp metas value).value Z parameters environment)
          (((generated primitives).model.interp metas body).value Z parameters environment)) ≫
            primitives.carrier := by
  change lift
    (MonoidalClosed.curry (((generated primitives).model.interp metas name).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)))
    (lift (MonoidalClosed.curry (((generated primitives).model.interp metas value).value (𝟙_ C ⊗ Z)
      (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)))
      (lift (MonoidalClosed.curry (((generated primitives).model.interp metas body).value (𝟙_ C ⊗ Z)
        (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment))) (toUnit Z))) ≫
        (lift (fst _ _ ≫ emptyValue primitives.names)
          (lift (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)
            (snd _ _ ≫ snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)) ≫ primitives.carrier) = _
  rw [← Category.assoc, comp_lift, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc]
  erw [empty_argument, empty_argument, empty_argument]

theorem schema_metavariable_value {context : Ctx NamePassing.Presentation.signature}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredEquations.metas)
    (environment : (generated primitives).model.Env Z context)
    (argument : Term NamePassing.AuthoredEquations.schemaSig context .nm) :
    ((generated primitives).model.interp NamePassing.AuthoredEquations.metas
      (NamePassing.AuthoredEquations.boundBody argument)).value Z parameters environment =
      lift (lift (((generated primitives).model.interp NamePassing.AuthoredEquations.metas argument).value
        Z parameters environment) (toUnit Z)) (parameters ≫ fst _ _) ≫
          (ihom.ev (primitives.names ⊗ 𝟙_ C)).app primitives.termObject := by
  rfl

/-- The complete function of the freshly bound reference is precisely the
supplied metavariable section; no representability of syntactic instances is
assumed. -/
theorem reference_body_curry {context : Ctx NamePassing.Presentation.signature}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredEquations.metas)
    (environment : (generated primitives).model.Env Z context) :
    MonoidalClosed.curry
      (((generated primitives).model.interp NamePassing.AuthoredEquations.metas
        (NamePassing.AuthoredEquations.boundBody (.var .zero :
          Term NamePassing.AuthoredEquations.schemaSig (.nm :: context) .nm))).value
            ((primitives.names ⊗ 𝟙_ C) ⊗ Z) (snd _ _ ≫ parameters)
            ((generated primitives).model.extendEnv [.nm] environment)) = parameters ≫ fst _ _ := by
  rw [schema_metavariable_value]
  rw [Model.interp_var]
  simp only [Model.extendEnv, Category.assoc]
  change MonoidalClosed.curry
    (lift (lift (fst (primitives.names ⊗ 𝟙_ C) Z ≫ fst primitives.names (𝟙_ C)) (toUnit _))
      (snd (primitives.names ⊗ 𝟙_ C) Z ≫ parameters ≫ fst _ _) ≫
        (ihom.ev (primitives.names ⊗ 𝟙_ C)).app primitives.termObject) = _
  have argument : lift (fst (primitives.names ⊗ 𝟙_ C) Z ≫ fst primitives.names (𝟙_ C))
      (toUnit ((primitives.names ⊗ 𝟙_ C) ⊗ Z)) = fst (primitives.names ⊗ 𝟙_ C) Z := by
    apply hom_ext
    · simp only [lift_fst]
    · exact (lift_snd _ _).trans (toUnit_unique _ _)
  rw [argument]
  have paired : lift (fst (primitives.names ⊗ 𝟙_ C) Z)
      (snd (primitives.names ⊗ 𝟙_ C) Z ≫ parameters ≫ fst _ _) =
        (primitives.names ⊗ 𝟙_ C) ◁ (parameters ≫ fst _ _) := by
    apply hom_ext <;> simp
  rw [paired]
  exact (generated primitives).model.curry_uncurry
    (Γ := [NamePassing.Presentation.Srt.nm]) (s := .tm) (parameters ≫ fst _ _)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
