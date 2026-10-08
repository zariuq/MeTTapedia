import Mettapedia.OSLF.Syntax.BindingClosedSchemaGeneric
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationCoherent

/-!
# Actual equation-schema extensions of generated binding presentations

Each authored equation has its own ordinary context and complete metavariable
function family. Its two independent encodings supply the parallel arrows of
an actual equation declaration. A target interpretation extends exactly when
the corresponding complete natural families agree. Restriction recovers the
entire original constructor interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.SchemaEquations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory

universe u v

variable (binding : Mettapedia.OSLF.Binding.Signature)
variable {Index : Type v} (metavariables : Index → List (MetaArity binding))
variable (equations : (origin : Index) → EqAxiom binding (metavariables origin))

def declaration (origin : Index) : EquationExtension.Declaration (ClosedPresentation.signature.{v} binding) where
  source := SchemaExpressions.genericStage binding (metavariables origin) (equations origin).ctx
  target := sortObject binding (equations origin).sort
  left := SchemaExpressions.expression binding (equations origin).lhs
  right := SchemaExpressions.expression binding (equations origin).rhs

def signature := EquationExtension.extend (ClosedPresentation.signature.{v} binding)
  (declaration binding metavariables equations)

def headers : HeaderFormation (signature binding metavariables equations) :=
  EquationExtension.headers (ClosedPresentation.signature binding) (declaration binding metavariables equations)
    (ClosedPresentation.headers binding)

def theory := EquationExtension.theory (ClosedPresentation.signature.{v} binding)
  (declaration binding metavariables equations)

def inclusion := EquationExtension.theoryMap (ClosedPresentation.signature.{v} binding)
  (declaration binding metavariables equations)

theorem authored_equation (origin : Index) :
    (inclusion binding metavariables equations).functor.map (classOf (declaration binding metavariables equations origin).left) =
      (inclusion binding metavariables equations).functor.map (classOf (declaration binding metavariables equations origin).right) :=
  EquationExtension.equation_class (ClosedPresentation.signature binding)
    (declaration binding metavariables equations) origin

variable {binding}
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasFiniteLimits C] (operations : Operations binding C)

def Satisfies : Prop := ∀ origin,
  operations.model.interp (metavariables origin) (equations origin).lhs =
    operations.model.interp (metavariables origin) (equations origin).rhs

theorem satisfaction_iff :
    EquationExtension.Satisfies (ClosedPresentation.signature binding)
      (declaration binding metavariables equations) operations.assignment operations.realization ↔
      Satisfies metavariables equations operations := by
  apply forall_congr'
  intro origin
  exact operations.schema_arrow_eq_iff (equations origin).lhs (equations origin).rhs

theorem admission_iff :
    Interpretation.Realization (signature binding metavariables equations)
      (EquationExtension.extendAssignment (Index := Index) operations.assignment) ↔
      Satisfies metavariables equations operations :=
  (EquationExtension.realization_iff_satisfaction (ClosedPresentation.signature binding)
    (declaration binding metavariables equations) operations.assignment operations.realization).trans
      (satisfaction_iff metavariables equations operations)

def assignment := EquationExtension.extendAssignment (Index := Index) operations.assignment

theorem realization (satisfied : Satisfies metavariables equations operations) :
    Interpretation.Realization (signature binding metavariables equations)
      (assignment operations) :=
  EquationExtension.extended_realization (ClosedPresentation.signature binding)
    (declaration binding metavariables equations) operations.assignment operations.realization
    ((satisfaction_iff metavariables equations operations).mpr satisfied)

def interpretation (satisfied : Satisfies metavariables equations operations) :
    Mettapedia.GSLT.Core.LambdaTheoryMap (theory binding metavariables equations)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory C) where
  functor := Interpretation.functor (assignment operations)
    (realization metavariables equations operations satisfied)
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits (assignment operations)
    (realization metavariables equations operations satisfied)
  preservesExponentials := Interpretation.functor_closed (assignment operations)
    (realization metavariables equations operations satisfied)

theorem complete_restriction (satisfied : Satisfies metavariables equations operations) :
    (inclusion binding metavariables equations).functor ⋙
        (interpretation metavariables equations operations satisfied).functor =
      operations.interpretation.functor :=
  EquationExtension.complete_restriction (ClosedPresentation.signature binding)
    (declaration binding metavariables equations) operations.assignment operations.realization
    ((satisfaction_iff metavariables equations operations).mpr satisfied)

omit [HasFiniteLimits C] in
theorem complete_schema_values (satisfied : Satisfies metavariables equations operations)
    (origin : Index) (Z : C) (metas : Z ⟶ operations.family (metavariables origin))
    (environment : operations.model.Env Z (equations origin).ctx) :
    (operations.model.interp (metavariables origin) (equations origin).lhs).value Z metas environment =
      (operations.model.interp (metavariables origin) (equations origin).rhs).value Z metas environment :=
  congrArg (fun value => value.value Z metas environment) (satisfied origin)

end Mettapedia.OSLF.Binding.ClosedPresentation.SchemaEquations
