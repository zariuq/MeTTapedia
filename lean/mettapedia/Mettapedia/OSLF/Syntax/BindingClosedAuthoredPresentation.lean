import Mettapedia.OSLF.Syntax.BindingClosedSchemaInstances

/-!
# Generated closed presentations of authored binding equation lists

Every list occurrence supplies its own equation declaration in the generated
closed category. The exact admission contract is the existing global contextual
model contract, including arbitrary ambient capture and every second-order
stage. The interpretation retains its complete constructor restriction and
interprets the existing equation-context category from the same admitted model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.AuthoredPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open CategoricalBindingModel SecondOrderContext

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature} {schema : List (MetaArity binding)}
variable (equations : List (EqAxiom binding schema))

def schemaAt (_ : ULift.{v} (Fin equations.length)) := schema
def equationAt (origin : ULift.{v} (Fin equations.length)) := equations.get origin.down

def signature := SchemaEquations.signature binding (schemaAt.{v} equations) (equationAt equations)
def theory := SchemaEquations.theory binding (schemaAt.{v} equations) (equationAt equations)
def inclusion := SchemaEquations.inclusion binding (schemaAt.{v} equations) (equationAt equations)

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasFiniteLimits C] (operations : Operations binding C)

omit [HasFiniteLimits C] in
theorem satisfaction_iff :
    SchemaEquations.Satisfies (schemaAt.{v} equations) (equationAt equations) operations ↔
      operations.model.SchemaFamilySatisfaction equations := by
  constructor
  · intro satisfied origin
    exact satisfied ⟨origin⟩
  · intro satisfied origin
    exact satisfied origin.down

theorem admission_iff_contextual :
    Interpretation.Realization (signature.{v} equations)
      (SchemaEquations.assignment (Index := ULift.{v} (Fin equations.length)) operations) ↔
      operations.model.Satisfies (authoredEquationPresentation binding equations) :=
  (SchemaEquations.admission_iff (schemaAt equations) (equationAt equations) operations).trans
    ((satisfaction_iff equations operations).trans (operations.model.schema_family_iff_contextual equations))

def interpretation
    (admitted : operations.model.Satisfies (authoredEquationPresentation binding equations)) :
    Mettapedia.GSLT.Core.LambdaTheoryMap (theory.{v} equations)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) :=
  SchemaEquations.interpretation (schemaAt equations) (equationAt equations) operations
    ((satisfaction_iff equations operations).mpr
      ((operations.model.schema_family_iff_contextual equations).mpr admitted))

theorem complete_restriction
    (admitted : operations.model.Satisfies (authoredEquationPresentation binding equations)) :
    (inclusion.{v} equations).functor ⋙ (interpretation equations operations admitted).functor =
      operations.interpretation.functor :=
  SchemaEquations.complete_restriction (schemaAt equations) (equationAt equations) operations
    ((satisfaction_iff equations operations).mpr
      ((operations.model.schema_family_iff_contextual equations).mpr admitted))

def equationContextInterpretation
    (admitted : operations.model.Satisfies (authoredEquationPresentation binding equations)) :
    EquationContexts (authoredEquationPresentation binding equations) ⥤ C :=
  operations.model.equationClassifyingFunctor (authoredEquationPresentation binding equations) admitted

omit [HasFiniteLimits C] in
theorem equation_context_restriction
    (admitted : operations.model.Satisfies (authoredEquationPresentation binding equations)) :
    (authoredEquationPresentation binding equations).quotientFunctor ⋙
        equationContextInterpretation equations operations admitted = operations.model.classifyingFunctor :=
  operations.model.quotient_comp_equationClassifyingFunctor (authoredEquationPresentation binding equations) admitted

end Mettapedia.OSLF.Binding.ClosedPresentation.AuthoredPresentation
