import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModel
import Mettapedia.OSLF.Syntax.BindingClosedSchemaClassification

/-!
# The generated equation guest's own binding model

The actual constructor inclusion determines all primitive operations inside
the generated equation category. Each independently authored equation is
proved there by its genuine generated declaration. The complete schema
comparison then earns equality at arbitrary stages and complete metavariable
function inputs, including those that are not images of raw term bodies.

No target-model satisfaction is supplied to construct this model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedEquations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory CategoricalBindingModel

universe k

variable {binding : Mettapedia.OSLF.Binding.Signature} {Index : Type k}
variable (metavariables : Index → List (MetaArity binding))
variable (equations : (origin : Index) → EqAxiom binding (metavariables origin))

def inclusion := (SchemaEquations.inclusion.{k} binding metavariables equations).functor

instance inclusion_finite : PreservesFiniteLimits (inclusion metavariables equations) :=
  (SchemaEquations.inclusion binding metavariables equations).preservesFiniteLimits

instance inclusion_closed : MonoidalClosedFunctor (inclusion metavariables equations) :=
  (SchemaEquations.inclusion binding metavariables equations).preservesExponentials

def operations : Operations binding (Object (SchemaEquations.signature binding metavariables equations)) := by
  letI : PreservesFiniteLimits (inclusion metavariables equations) := inclusion_finite metavariables equations
  letI : MonoidalClosedFunctor (inclusion metavariables equations) := inclusion_closed metavariables equations
  exact GeneratedModel.operations (binding := binding) (inclusion metavariables equations)

def constructorComparison : inclusion metavariables equations ≅
    (operations metavariables equations).interpretation.functor := by
  letI : PreservesFiniteLimits (inclusion metavariables equations) := inclusion_finite metavariables equations
  letI : MonoidalClosedFunctor (inclusion metavariables equations) := inclusion_closed metavariables equations
  exact GeneratedModel.comparison (binding := binding) (inclusion metavariables equations)

theorem satisfied : SchemaEquations.Satisfies metavariables equations (operations metavariables equations) := by
  let _ : PreservesFiniteLimits (inclusion metavariables equations) := inclusion_finite metavariables equations
  let _ : MonoidalClosedFunctor (inclusion metavariables equations) := inclusion_closed metavariables equations
  intro origin
  apply (GeneratedModel.schema_eq_iff (binding := binding) (inclusion metavariables equations)
    (equations origin).lhs (equations origin).rhs).mp
  exact SchemaEquations.authored_equation binding metavariables equations origin

theorem complete_values (origin : Index)
    (stage : Object (SchemaEquations.signature binding metavariables equations))
    (parameters : stage ⟶ (operations metavariables equations).family (metavariables origin))
    (environment : (operations metavariables equations).model.Env stage (equations origin).ctx) :
    ((operations metavariables equations).model.interp (metavariables origin) (equations origin).lhs).value
        stage parameters environment =
      ((operations metavariables equations).model.interp (metavariables origin) (equations origin).rhs).value
        stage parameters environment :=
  SchemaEquations.complete_schema_values metavariables equations (operations metavariables equations)
    (satisfied metavariables equations) origin stage parameters environment

def interpretation := SchemaEquations.interpretation metavariables equations (operations metavariables equations)
  (satisfied metavariables equations)

theorem complete_constructor_restriction : inclusion metavariables equations ⋙
    (interpretation metavariables equations).functor =
      (operations metavariables equations).interpretation.functor :=
  SchemaEquations.complete_restriction metavariables equations (operations metavariables equations)
    (satisfied metavariables equations)

end Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedEquations
