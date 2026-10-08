import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent classification from four primitive operation readings

An arbitrary finite-limit closed candidate is compared on the original base
and the independently supplied evidence object. The four complete local
operation readings determine its normalized assignment. Every generated
equation, the independently interpreted category and the whole natural
comparison follow. Admitted comparison cells are unique from their primitive
components; raw object presentations need not be identified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Universal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning.Operations (base.obj vertex))
variable (candidate : Object (Presentation.signature vertex) ⥤ D)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate (CategoryInterpretation.assignment vertex base meaning))

abbrev extracted := FunctorNormalization.assignment
  (CoherentExtension.presented candidate (CategoryInterpretation.assignment vertex base meaning) images)
    (Presentation.headers vertex)

structure OperationReadings : Prop where
  source : (extracted vertex base meaning candidate images).arrow (ULift.up Operation.source) =
    (⟨meaning.edge,base.obj vertex,meaning.source⟩ : ArrowValue D)
  target : (extracted vertex base meaning candidate images).arrow (ULift.up Operation.target) =
    (⟨meaning.edge,base.obj vertex,meaning.target⟩ : ArrowValue D)
  unit : (extracted vertex base meaning candidate images).arrow (ULift.up Operation.unit) =
    (⟨base.obj vertex,meaning.edge,meaning.unit⟩ : ArrowValue D)
  composition : (extracted vertex base meaning candidate images).arrow (ULift.up Operation.composition) =
    (⟨meaning.toGraph.composable,meaning.edge,meaning.composition⟩ : ArrowValue D)

variable (readings : OperationReadings vertex base meaning candidate images)

include readings in
theorem primitive_arrow_readings : CoherentExtension.ArrowImages candidate
    (CategoryInterpretation.assignment vertex base meaning) images (Presentation.headers vertex) where
  arrow origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact readings.source
      | target => exact readings.target
      | unit => exact readings.unit
      | composition => exact readings.composition

include readings in
theorem locally_realized : Realization (Presentation.signature vertex)
    (CategoryInterpretation.assignment vertex base meaning) := by
  have realized := FunctorNormalization.reconstruction_realization
    (CoherentExtension.presented candidate (CategoryInterpretation.assignment vertex base meaning) images)
      (Presentation.headers vertex)
  exact (CoherentExtension.assignment_equal candidate (CategoryInterpretation.assignment vertex base meaning)
    images (Presentation.headers vertex) (primitive_arrow_readings vertex base meaning candidate images readings)) ▸ realized

include readings in
theorem seven_diagrams : ∃ endpointLaws : Meaning.EndpointLaws vertex base meaning,
    ModelDiagrams.LocalLaws vertex base meaning endpointLaws :=
  (CategoryInterpretation.seven_diagram_admission_iff vertex base meaning).mp
    (locally_realized vertex base meaning candidate images readings)

include readings in
theorem endpointLaws : Meaning.EndpointLaws vertex base meaning :=
  (seven_diagrams vertex base meaning candidate images readings).choose

include readings in
theorem categoryLaws : ModelDiagrams.LocalLaws vertex base meaning
    (endpointLaws vertex base meaning candidate images readings) :=
  (seven_diagrams vertex base meaning candidate images readings).choose_spec

def category : InternalCategory D := ModelDiagrams.category vertex base meaning
  (endpointLaws vertex base meaning candidate images readings)
  (categoryLaws vertex base meaning candidate images readings)

def comparison : candidate ≅ CategoryInterpretation.functor vertex base meaning
    (endpointLaws vertex base meaning candidate images readings)
    (categoryLaws vertex base meaning candidate images readings) :=
  CoherentExtension.comparison candidate (CategoryInterpretation.assignment vertex base meaning)
    images (Presentation.headers vertex) (primitive_arrow_readings vertex base meaning candidate images readings)
      (CategoryInterpretation.realization vertex base meaning
        (endpointLaws vertex base meaning candidate images readings)
        (categoryLaws vertex base meaning candidate images readings))

abbrev CellAdmission := CoherentExtension.CellAdmission candidate
  (CategoryInterpretation.assignment vertex base meaning) images
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))

theorem comparison_admitted : CellAdmission vertex base meaning candidate images readings
    (comparison vertex base meaning candidate images readings).hom :=
  CoherentExtension.comparison_admitted candidate (CategoryInterpretation.assignment vertex base meaning)
    images (Presentation.headers vertex) (primitive_arrow_readings vertex base meaning candidate images readings)
      (CategoryInterpretation.realization vertex base meaning
        (endpointLaws vertex base meaning candidate images readings)
        (categoryLaws vertex base meaning candidate images readings))

theorem admitted_cell_unique
    (cell : candidate ⟶ CategoryInterpretation.functor vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
    (localComponents : CellAdmission vertex base meaning candidate images readings cell) :
    cell = (comparison vertex base meaning candidate images readings).hom :=
  CoherentExtension.admitted_cell_unique candidate (CategoryInterpretation.assignment vertex base meaning)
    images (Presentation.headers vertex) (primitive_arrow_readings vertex base meaning candidate images readings)
      (CategoryInterpretation.realization vertex base meaning
        (endpointLaws vertex base meaning candidate images readings)
        (categoryLaws vertex base meaning candidate images readings)) cell localComponents

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ CategoryInterpretation.functor vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings) //
        CellAdmission vertex base meaning candidate images readings iso.hom} :=
  CoherentExtension.admittedIsoUnique candidate (CategoryInterpretation.assignment vertex base meaning)
    images (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
        (Presentation.headers vertex) (primitive_arrow_readings vertex base meaning candidate images readings)

theorem category_composition_read {stage : D} (first second : stage ⟶ meaning.edge)
    (matching : first ≫ meaning.target = second ≫ meaning.source) :
    (category vertex base meaning candidate images readings).compose first second matching =
      CartesianEqualizerPullback.lift meaning.target meaning.source first second matching ≫ meaning.composition :=
  ModelDiagrams.category_compose_read vertex base meaning
    (endpointLaws vertex base meaning candidate images readings)
    (categoryLaws vertex base meaning candidate images readings) first second matching

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Universal
