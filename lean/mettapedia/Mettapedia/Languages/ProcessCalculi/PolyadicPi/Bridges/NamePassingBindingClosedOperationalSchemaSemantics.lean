import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasBinderSemantics
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalPresentation

/-!
# Complete categorical readings of the authored root reduction schemas

Both sides are evaluated independently from their raw binding syntax. The
beta body is an arbitrary supplied function section. The canonical unit
conversion commutes with evaluation, so no syntactic representability or
selected-current-value assumption is needed for either endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalSchemaSemantics

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations NamePassingBindingClosedOperations NamePassingBindingClosedSchemas

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (primitives : Operations C)

theorem schema_reference_value {metas : List (MetaArity NamePassing.Presentation.signature)}
    {context : Ctx NamePassing.Presentation.signature} {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family metas)
    (environment : (generated primitives).model.Env Z context)
    (name : Term (withMetas NamePassing.Presentation.signature metas) context .nm) :
    ((generated primitives).model.interp metas
      (.op (.inl .reference) (.cons name .nil))).value Z parameters environment =
        ((generated primitives).model.interp metas name).value Z parameters environment ≫
          primitives.reference := by
  change lift (MonoidalClosed.curry
      (((generated primitives).model.interp metas name).value (𝟙_ C ⊗ Z)
        (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment))) (toUnit Z) ≫
      (fst _ _ ≫ emptyValue primitives.names ≫ primitives.reference) = _
  erw [lift_fst_assoc]
  have reading := empty_argument primitives parameters environment name
  change MonoidalClosed.curry
      (((generated primitives).model.interp metas name).value (𝟙_ C ⊗ Z)
        (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [] environment)) ≫
      emptyValue primitives.names =
        ((generated primitives).model.interp metas name).value Z parameters environment at reading
  simpa only [Category.assoc] using
    congrArg (fun value => value ≫ primitives.reference) reading

theorem schema_abstraction_value {metas : List (MetaArity NamePassing.Presentation.signature)}
    {context : Ctx NamePassing.Presentation.signature} {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family metas)
    (environment : (generated primitives).model.Env Z context)
    (body : Term (withMetas NamePassing.Presentation.signature metas) (.nm :: context) .tm) :
    ((generated primitives).model.interp metas
      (.op (.inl .abstraction) (.cons body .nil))).value Z parameters environment =
        MonoidalClosed.curry
          (((generated primitives).model.interp metas body).value ((primitives.names ⊗ 𝟙_ C) ⊗ Z)
            (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [.nm] environment)) ≫
          boundValue primitives ≫ primitives.abstraction := by
  change lift (MonoidalClosed.curry
      (((generated primitives).model.interp metas body).value ((primitives.names ⊗ 𝟙_ C) ⊗ Z)
        (snd _ _ ≫ parameters) ((generated primitives).model.extendEnv [.nm] environment))) (toUnit Z) ≫
      (fst _ _ ≫ boundValue primitives ≫ primitives.abstraction) = _
  rw [lift_fst_assoc]

/-- Evaluation retains the complete supplied function through unit insertion. -/
theorem bound_call {Z : C}
    (function : Z ⟶ (ihom (primitives.names ⊗ 𝟙_ C)).obj primitives.termObject)
    (argument : Z ⟶ primitives.names) :
    call (function ≫ boundValue primitives) argument =
      lift (lift argument (toUnit Z)) function ≫
        (ihom.ev (primitives.names ⊗ 𝟙_ C)).app primitives.termObject := by
  rw [call_as_evaluation]
  unfold boundValue
  have converted : lift argument (function ≫
      (MonoidalClosed.pre (ρ_ primitives.names).inv).app primitives.termObject) =
      lift argument function ≫ primitives.names ◁
        (MonoidalClosed.pre (ρ_ primitives.names).inv).app primitives.termObject := by
    apply hom_ext <;> simp
  rw [converted,Category.assoc,MonoidalClosed.id_tensor_pre_app_comp_ev,← Category.assoc]
  congr 1
  apply hom_ext
  · apply hom_ext <;> simp
  · simp

theorem beta_before_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredOperationalProfile.betaMetas)
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.nm]) :
    ((generated primitives).model.interp NamePassing.AuthoredOperationalProfile.betaMetas
      NamePassing.AuthoredOperationalProfile.beta.conclusion.lhs).value Z parameters environment =
      lift (parameters ≫ fst _ _ ≫ boundValue primitives ≫ primitives.abstraction)
        (environment .nm .zero) ≫ primitives.application := by
  change ((generated primitives).model.interp NamePassing.AuthoredEquations.metas
    (.op (.inl .application)
      (.cons (.op (.inl .abstraction)
        (.cons (NamePassing.AuthoredEquations.boundBody (.var .zero)) .nil))
        (.cons (.var .zero) .nil)))).value Z parameters environment = _
  erw [schema_application_value,schema_abstraction_value,reference_body_curry,Model.interp_var]
  simp only [Category.assoc]

theorem beta_after_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family NamePassing.AuthoredOperationalProfile.betaMetas)
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.nm]) :
    ((generated primitives).model.interp NamePassing.AuthoredOperationalProfile.betaMetas
      NamePassing.AuthoredOperationalProfile.beta.conclusion.rhs).value Z parameters environment =
        call (parameters ≫ fst _ _ ≫ boundValue primitives) (environment .nm .zero) := by
  change ((generated primitives).model.interp NamePassing.AuthoredEquations.metas
    (NamePassing.AuthoredEquations.boundBody (.var .zero))).value Z parameters environment = _
  rw [schema_metavariable_value,Model.interp_var]
  simpa only [Category.assoc] using
    (bound_call primitives (parameters ≫ fst _ _) (environment .nm .zero)).symm

theorem fetch_before_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family [])
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.nm,.tm]) :
    ((generated primitives).model.interp [] NamePassing.AuthoredOperationalProfile.fetch.conclusion.lhs).value
      Z parameters environment =
        lift (environment .nm .zero)
          (lift (environment .tm (.succ .zero)) (environment .nm .zero ≫ primitives.reference)) ≫
            primitives.carrier := by
  change ((generated primitives).model.interp []
    (.op (.inl .carrier) (.cons (.var .zero) (.cons (.var (.succ .zero))
      (.cons (.op (.inl .reference) (.cons (.var .zero) .nil)) .nil))))).value
        Z parameters environment = _
  erw [schema_carrier_value,schema_reference_value]
  rfl

theorem fetch_after_value {Z : C}
    (parameters : Z ⟶ (generated primitives).model.family [])
    (environment : (generated primitives).model.Env Z [NamePassing.Presentation.Srt.nm,.tm]) :
    ((generated primitives).model.interp [] NamePassing.AuthoredOperationalProfile.fetch.conclusion.rhs).value
      Z parameters environment = environment .tm (.succ .zero) := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalSchemaSemantics
