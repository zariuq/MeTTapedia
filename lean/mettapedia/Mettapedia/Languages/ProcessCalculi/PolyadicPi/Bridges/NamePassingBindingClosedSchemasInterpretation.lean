import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasBinderSemantics

/-!
# Admission of the complete authored scope schemas in the native pi model

Both schema equations hold on arbitrary categorical metavariable function
families, at every stage and ambient environment. The independently generated
closed equation presentation therefore has a genuine finite-limit and closed
interpretation into the authored pi equation model. Its constructor restriction
is the previously qualified categorical continuation map.
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
open NamePassingCategoricalCompiler NamePassingContinuationOperations NamePassingBindingClosedOperations

attribute [local irreducible] Operations.application Operations.definition Operations.carrier applicationBody

theorem appliedBody_native : appliedBody operations = applicationBody := by
  unfold appliedBody applicationBody
  rfl

theorem application_definition_arrow :
    lift (fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫ operations.definition)
      (snd (operations.termObject ⊗ operations.boundBodyObject) operations.names) ≫ operations.application =
      lift (fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
        fst operations.termObject operations.boundBodyObject)
        (lift (fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
          snd operations.termObject operations.boundBodyObject)
          (snd (operations.termObject ⊗ operations.boundBodyObject) operations.names) ≫ applicationBody) ≫
            operations.definition := by
  apply NatTrans.ext
  funext world
  rw [← world_stage world]
  apply ConcreteCategory.hom_ext
  intro supplied
  exact application_definition_section supplied.1.1 supplied.1.2 supplied.2

theorem application_carrier_arrow :
    lift (fst (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names ≫
      operations.carrier) (snd (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names) ≫
        operations.application =
      lift (fst (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names ≫
        fst operations.names (operations.termObject ⊗ operations.termObject))
        (lift (fst (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names ≫
          snd operations.names (operations.termObject ⊗ operations.termObject) ≫
            fst operations.termObject operations.termObject)
          (lift (fst (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names ≫
            snd operations.names (operations.termObject ⊗ operations.termObject) ≫
              snd operations.termObject operations.termObject)
            (snd (operations.names ⊗ (operations.termObject ⊗ operations.termObject)) operations.names) ≫
              operations.application)) ≫ operations.carrier := by
  apply NatTrans.ext
  funext world
  rw [← world_stage world]
  apply ConcreteCategory.hom_ext
  intro supplied
  exact application_carrier_section supplied.1.1 supplied.2 supplied.1.2.1 supplied.1.2.2

theorem application_definition_arrows {Z : Ambient}
    (value : Z ⟶ operations.termObject) (body : Z ⟶ operations.boundBodyObject)
    (argument : Z ⟶ operations.names) :
    lift (lift value body ≫ operations.definition) argument ≫ operations.application =
      lift value (lift body argument ≫ appliedBody operations) ≫ operations.definition := by
  have law := congrArg (fun arrow => lift (lift value body) argument ≫ arrow) application_definition_arrow
  simpa only [appliedBody_native, comp_lift_assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd,
    Category.assoc] using law

theorem application_carrier_arrows {Z : Ambient}
    (name argument : Z ⟶ operations.names) (value body : Z ⟶ operations.termObject) :
    lift (lift name (lift value body) ≫ operations.carrier) argument ≫ operations.application =
      lift name (lift value (lift body argument ≫ operations.application)) ≫ operations.carrier := by
  have law := congrArg (fun arrow => lift (lift name (lift value body)) argument ≫ arrow) application_carrier_arrow
  simpa only [comp_lift_assoc, comp_lift, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, Category.assoc] using law

theorem definition_schema_satisfied :
    NamePassingBindingClosedOperations.Native.operations.model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.lhs =
    NamePassingBindingClosedOperations.Native.operations.model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.rhs := by
  apply Model.ElemOver.ext
  funext Z parameters environment
  erw [schema_application_value, schema_definition_value, reference_body_curry,
    schema_definition_value, reference_application_curry]
  simp only [Model.interp_var]
  exact application_definition_arrows _ _ _

theorem carrier_schema_satisfied :
    NamePassingBindingClosedOperations.Native.operations.model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appCarrier.lhs =
    NamePassingBindingClosedOperations.Native.operations.model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appCarrier.rhs := by
  apply Model.ElemOver.ext
  funext Z parameters environment
  erw [schema_application_value, schema_carrier_value, schema_carrier_value, schema_application_value]
  simp only [Model.interp_var]
  exact application_carrier_arrows _ _ _ _

theorem schema_family_satisfied :
    NamePassingBindingClosedOperations.Native.operations.model.SchemaFamilySatisfaction
      NamePassing.AuthoredEquations.equations := by
  intro origin
  rcases origin with ⟨index, bound⟩
  cases index with
  | zero => exact definition_schema_satisfied
  | succ index =>
      cases index with
      | zero => exact carrier_schema_satisfied
      | succ index => simp [NamePassing.AuthoredEquations.equations] at bound

/-- The native model satisfies the existing global contextual contract,
including captured ambient instances and all second-order contexts. -/
theorem contextual_satisfied :
    NamePassingBindingClosedOperations.Native.operations.model.Satisfies
      (SecondOrderContext.authoredEquationPresentation NamePassing.Presentation.signature
        NamePassing.AuthoredEquations.equations) :=
  (NamePassingBindingClosedOperations.Native.operations.model.schema_family_iff_contextual
    NamePassing.AuthoredEquations.equations).mp schema_family_satisfied

theorem generated_model_admitted :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.Realization
      (ClosedPresentation.AuthoredPresentation.signature.{0} NamePassing.AuthoredEquations.equations)
      (ClosedPresentation.SchemaEquations.assignment
        (Index := ULift.{0} (Fin NamePassing.AuthoredEquations.equations.length))
        NamePassingBindingClosedOperations.Native.operations) :=
  (ClosedPresentation.AuthoredPresentation.admission_iff_contextual
    NamePassing.AuthoredEquations.equations NamePassingBindingClosedOperations.Native.operations).mpr
      contextual_satisfied

def interpretation :=
  ClosedPresentation.AuthoredPresentation.interpretation NamePassing.AuthoredEquations.equations
    NamePassingBindingClosedOperations.Native.operations contextual_satisfied

theorem complete_restriction :
    (ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor ⋙
      interpretation.functor = NamePassingBindingClosedOperations.Native.operations.interpretation.functor :=
  ClosedPresentation.AuthoredPresentation.complete_restriction NamePassing.AuthoredEquations.equations
    NamePassingBindingClosedOperations.Native.operations contextual_satisfied

/-- A supplied schema tree is read through the actual equation-extended
closed functor, including its complete context and function-family domain. -/
theorem generated_schema_readout {context : Ctx NamePassing.Presentation.signature}
    {sort : NamePassing.Presentation.Srt} (term : Term NamePassing.AuthoredEquations.schemaSig context sort) :
    (⟨interpretation.functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.SchemaExpressions.genericStage NamePassing.Presentation.signature
            NamePassing.AuthoredEquations.metas context)),
      interpretation.functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.sortObject NamePassing.Presentation.signature sort)),
      interpretation.functor.map
        ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.map
          (Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
            (ClosedPresentation.SchemaExpressions.expression NamePassing.Presentation.signature term)))⟩ :
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue Ambient) =
      ⟨NamePassingBindingClosedOperations.Native.operations.context context ⊗
          NamePassingBindingClosedOperations.Native.operations.family NamePassing.AuthoredEquations.metas,
        NamePassingBindingClosedOperations.Native.operations.sort sort,
        NamePassingBindingClosedOperations.Native.operations.model.generic NamePassing.AuthoredEquations.metas term⟩ := by
  have reading := NamePassingBindingClosedOperations.Native.operations.schema_complete_readout term
  rw [← complete_restriction] at reading
  exact reading

def equationContextInterpretation :=
  ClosedPresentation.AuthoredPresentation.equationContextInterpretation NamePassing.AuthoredEquations.equations
    NamePassingBindingClosedOperations.Native.operations contextual_satisfied

theorem equation_context_restriction :
    (SecondOrderContext.authoredEquationPresentation NamePassing.Presentation.signature
      NamePassing.AuthoredEquations.equations).quotientFunctor ⋙ equationContextInterpretation =
        NamePassingBindingClosedOperations.Native.operations.model.classifyingFunctor :=
  ClosedPresentation.AuthoredPresentation.equation_context_restriction NamePassing.AuthoredEquations.equations
    NamePassingBindingClosedOperations.Native.operations contextual_satisfied

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
