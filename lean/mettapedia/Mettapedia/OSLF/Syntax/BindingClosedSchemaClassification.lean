import Mettapedia.OSLF.Syntax.BindingClosedSchemaEquations

/-!
# Coherent classification of genuine binding equation-schema models

An independently supplied closed finite-limit functor carries only sort
isomorphisms and complete primitive operator readings. These readings force
the actual schema-family equations and determine a comparison on the entire
generated equation category. The comparison is unique among natural cells
with the supplied primitive components; raw context objects are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.SchemaEquations.Coherent

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {Index : Type v} (metavariables : Index → List (MetaArity binding))
variable (equations : (origin : Index) → EqAxiom binding (metavariables origin))
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasFiniteLimits C] (operations : Operations binding C)
variable (candidate : Object (signature binding metavariables equations) ⥤ C)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate (assignment operations))
variable (readings : CoherentExtension.ArrowImages candidate (assignment operations) images
  (headers binding metavariables equations))

include readings in
theorem schema_satisfaction : Satisfies metavariables equations operations :=
  (satisfaction_iff metavariables equations operations).mp
    (EquationExtension.Coherent.satisfies (declaration binding metavariables equations)
      operations.assignment operations.realization (ClosedPresentation.headers binding)
      candidate images readings)

def comparison : candidate ≅
    (interpretation metavariables equations operations
      (schema_satisfaction metavariables equations operations candidate images readings)).functor :=
  EquationExtension.Coherent.comparison (declaration binding metavariables equations)
    operations.assignment operations.realization (ClosedPresentation.headers binding)
    candidate images readings

abbrev CellAdmission
    (cell : candidate ⟶ (interpretation metavariables equations operations
      (schema_satisfaction metavariables equations operations candidate images readings)).functor) : Prop :=
  CoherentExtension.CellAdmission candidate (assignment operations) images
    (realization metavariables equations operations
      (schema_satisfaction metavariables equations operations candidate images readings)) cell

theorem comparison_admitted : CellAdmission metavariables equations operations candidate images readings
    (comparison metavariables equations operations candidate images readings).hom :=
  EquationExtension.Coherent.comparison_admitted (declaration binding metavariables equations)
    operations.assignment operations.realization (ClosedPresentation.headers binding)
    candidate images readings

theorem admitted_cell_unique
    (cell : candidate ⟶ (interpretation metavariables equations operations
      (schema_satisfaction metavariables equations operations candidate images readings)).functor)
    (admitted : CellAdmission metavariables equations operations candidate images readings cell) :
    cell = (comparison metavariables equations operations candidate images readings).hom :=
  EquationExtension.Coherent.admitted_cell_unique (declaration binding metavariables equations)
    operations.assignment operations.realization (ClosedPresentation.headers binding)
    candidate images readings cell admitted

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ (interpretation metavariables equations operations
      (schema_satisfaction metavariables equations operations candidate images readings)).functor //
      CellAdmission metavariables equations operations candidate images readings iso.hom} :=
  EquationExtension.Coherent.admittedIsoUnique (declaration binding metavariables equations)
    operations.assignment operations.realization (ClosedPresentation.headers binding)
    candidate images readings

def originalComparison : (inclusion binding metavariables equations).functor ⋙ candidate ≅
    operations.interpretation.functor :=
  Functor.isoWhiskerLeft (inclusion binding metavariables equations).functor
    (comparison metavariables equations operations candidate images readings) ≪≫
      eqToIso (complete_restriction metavariables equations operations
        (schema_satisfaction metavariables equations operations candidate images readings))

end Mettapedia.OSLF.Binding.ClosedPresentation.SchemaEquations.Coherent
