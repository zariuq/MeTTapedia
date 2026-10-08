import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedComparison

/-!
# A closed compiler between the independently generated static guests

The target's actual structural declarations earn the complete source scope
schemas, including arbitrary function metadata and every ambient environment.
Their generated finite-limit and closed presentations therefore admit the
categorical continuation compiler. Its complete constructor restriction and
open-term readings use the same earned interpretation.

The source operational evidence declarations and their images are separate
obligations. Static equation admission does not identify a rewrite with an
equation or supply unrestricted reflective observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStatic

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel SecondOrderContext
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations NamePassingBindingClosedOperations
open BindingClosedPrimitiveOperations
open NamePassingBindingClosedSchemas

universe u v k

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)

def operations : ClosedPresentation.Operations NamePassing.Presentation.signature C :=
  generated (continuation binding)

theorem definition_schema_satisfied
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (operations binding).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.lhs =
    (operations binding).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appDefinition.rhs := by
  apply Model.ElemOver.ext
  funext Z parameters environment
  dsimp only [operations] at parameters environment
  change ((generated (continuation binding)).model.interp _ _).value Z parameters environment =
    ((generated (continuation binding)).model.interp _ _).value Z parameters environment
  erw [definition_left_value, definition_right_value]
  simpa only [Category.assoc] using NamePassingGeneratedScopeEquations.application_definition binding satisfied
    (environment NamePassing.Presentation.Srt.tm .zero)
    (parameters ≫ fst _ _ ≫ boundValue (continuation binding))
    (environment NamePassing.Presentation.Srt.nm (.succ .zero))

theorem carrier_schema_satisfied
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (operations binding).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appCarrier.lhs =
    (operations binding).model.interp NamePassing.AuthoredEquations.metas
      NamePassing.AuthoredEquations.appCarrier.rhs := by
  apply Model.ElemOver.ext
  funext Z parameters environment
  change ((generated (continuation binding)).model.interp _ _).value Z parameters environment =
    ((generated (continuation binding)).model.interp _ _).value Z parameters environment
  erw [schema_application_value, schema_carrier_value, schema_carrier_value, schema_application_value]
  simp only [Model.interp_var]
  exact NamePassingGeneratedScopeEquations.application_carrier binding satisfied _ _ _ _

theorem schema_family_satisfied
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (operations binding).model.SchemaFamilySatisfaction NamePassing.AuthoredEquations.equations := by
  intro origin
  rcases origin with ⟨index, bound⟩
  cases index with
  | zero => exact definition_schema_satisfied binding satisfied
  | succ index =>
      cases index with
      | zero => exact carrier_schema_satisfied binding satisfied
      | succ index => simp [NamePassing.AuthoredEquations.equations] at bound

theorem contextual_satisfied
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (operations binding).model.Satisfies
      (authoredEquationPresentation NamePassing.Presentation.signature NamePassing.AuthoredEquations.equations) :=
  ((operations binding).model.schema_family_iff_contextual NamePassing.AuthoredEquations.equations).mp
    (schema_family_satisfied binding satisfied)

variable [HasFiniteLimits C]

def interpretation (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :=
  ClosedPresentation.AuthoredPresentation.interpretation NamePassing.AuthoredEquations.equations
    (operations binding) (contextual_satisfied binding satisfied)

theorem complete_restriction (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor ⋙
      (interpretation binding satisfied).functor = (operations binding).interpretation.functor :=
  ClosedPresentation.AuthoredPresentation.complete_restriction NamePassing.AuthoredEquations.equations
    (operations binding) (contextual_satisfied binding satisfied)

theorem complete_open_term (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {context : Ctx NamePassing.Presentation.signature} (term : NamePassing.Presentation.Program context) :
    (⟨(interpretation binding satisfied).functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.contextObject.{v} NamePassing.Presentation.signature context)),
      (interpretation binding satisfied).functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm)),
      (interpretation binding satisfied).functor.map
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.map
          (ClosedPresentation.termArrow NamePassing.Presentation.signature term))⟩ :
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue C) =
    ⟨(operations binding).context context, (continuation binding).termObject,
      contextMap (continuation binding) context ≫
        NamePassingConstructorInterpretation.meaning (continuation binding) term⟩ := by
  have read := generated_arrow_comparison (continuation binding) term
  have restriction := complete_restriction binding satisfied
  dsimp only [operations] at restriction
  rw [← restriction] at read
  exact read

/-- The generated arrow retains its whole metavariable-function domain,
ordinary context and independent natural-family reading. -/
theorem complete_schema_readout (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {context : Ctx NamePassing.Presentation.signature} {sort : NamePassing.Presentation.Srt}
    (term : Term NamePassing.AuthoredEquations.schemaSig context sort) :
    (⟨(interpretation binding satisfied).functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.SchemaExpressions.genericStage.{v} NamePassing.Presentation.signature
            NamePassing.AuthoredEquations.metas context)),
      (interpretation binding satisfied).functor.obj
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.obj
          (ClosedPresentation.sortObject NamePassing.Presentation.signature sort)),
      (interpretation binding satisfied).functor.map
        ((ClosedPresentation.AuthoredPresentation.inclusion.{v} NamePassing.AuthoredEquations.equations).functor.map
          (Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
            (ClosedPresentation.SchemaExpressions.expression.{v} NamePassing.Presentation.signature term)))⟩ :
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue C) =
      ⟨(operations binding).context context ⊗
          (operations binding).family NamePassing.AuthoredEquations.metas,
        (operations binding).sort sort, (operations binding).model.generic NamePassing.AuthoredEquations.metas term⟩ := by
  have read := (operations binding).schema_complete_readout term
  rw [← complete_restriction binding satisfied] at read
  exact read

def equationContextInterpretation (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :=
  ClosedPresentation.AuthoredPresentation.equationContextInterpretation NamePassing.AuthoredEquations.equations
    (operations binding) (contextual_satisfied binding satisfied)

omit [HasFiniteLimits C] in
theorem equation_context_restriction (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations) :
    (authoredEquationPresentation NamePassing.Presentation.signature NamePassing.AuthoredEquations.equations).quotientFunctor ⋙
      equationContextInterpretation binding satisfied = (operations binding).model.classifyingFunctor :=
  ClosedPresentation.AuthoredPresentation.equation_context_restriction NamePassing.AuthoredEquations.equations
    (operations binding) (contextual_satisfied binding satisfied)

namespace FreeTarget

def compiler := interpretation BindingClosedGenerated.operations.{k}
  BindingClosedGenerated.equations_satisfied

theorem source_schemas :
    (operations BindingClosedGenerated.operations.{k}).model.SchemaFamilySatisfaction
      NamePassing.AuthoredEquations.equations :=
  schema_family_satisfied BindingClosedGenerated.operations BindingClosedGenerated.equations_satisfied

theorem constructor_restriction :
    (ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor ⋙
      compiler.{k}.functor = (operations BindingClosedGenerated.operations).interpretation.functor :=
  complete_restriction BindingClosedGenerated.operations BindingClosedGenerated.equations_satisfied

end FreeTarget

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStatic
