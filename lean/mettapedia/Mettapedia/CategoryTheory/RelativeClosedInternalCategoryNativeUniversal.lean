import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryUniversal
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionCoherent

/-!
# Native base extension of the category-model universal comparison

The original base is independently finite-limit and closed. Four local
primitive readings suffice: the added native comparison arrows are forced
by their inverse equations. The seven target diagrams and the unique whole
comparison are earned without a target realization or category-law field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.NativeUniversal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasFiniteLimits C] (vertex : C)
variable {D : Type w} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
variable (meaning : Meaning.Operations (base.obj vertex))

abbrev oldMeanings := CategoryInterpretation.assignment vertex base meaning

instance oldMeanings_lex : PreservesFiniteLimits (oldMeanings vertex base meaning).base := by
  change PreservesFiniteLimits base
  infer_instance

instance oldMeanings_closed : MonoidalClosedFunctor (oldMeanings vertex base meaning).base := by
  change MonoidalClosedFunctor base
  infer_instance

abbrev assignment := BaseExtension.WeakExtension.assignment (oldMeanings vertex base meaning)

variable (candidate : Object (Presentation.nativeSignature vertex) ⥤ D)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate (assignment vertex base meaning))

abbrev extracted := BaseExtension.Coherent.extracted (oldMeanings vertex base meaning)
  (Presentation.headers vertex) candidate images

structure OperationReadings : Prop where
  source : (extracted vertex base meaning candidate images).arrow
    (BaseExtension.originalArrows (ULift.up Operation.source)) =
      (⟨meaning.edge,base.obj vertex,meaning.source⟩ : ArrowValue D)
  target : (extracted vertex base meaning candidate images).arrow
    (BaseExtension.originalArrows (ULift.up Operation.target)) =
      (⟨meaning.edge,base.obj vertex,meaning.target⟩ : ArrowValue D)
  unit : (extracted vertex base meaning candidate images).arrow
    (BaseExtension.originalArrows (ULift.up Operation.unit)) =
      (⟨base.obj vertex,meaning.edge,meaning.unit⟩ : ArrowValue D)
  composition : (extracted vertex base meaning candidate images).arrow
    (BaseExtension.originalArrows (ULift.up Operation.composition)) =
      (⟨meaning.toGraph.composable,meaning.edge,meaning.composition⟩ : ArrowValue D)

variable (readings : OperationReadings vertex base meaning candidate images)

include readings in
theorem old_arrow_readings : BaseExtension.Coherent.OldArrowImages (oldMeanings vertex base meaning)
    (Presentation.headers vertex) candidate images where
  arrow origin := by
    cases origin with
    | up origin =>
      cases origin with
      | source => exact readings.source
      | target => exact readings.target
      | unit => exact readings.unit
      | composition => exact readings.composition

include readings in
theorem all_arrow_readings : CoherentExtension.ArrowImages candidate (assignment vertex base meaning)
    images (Presentation.nativeHeaders vertex) :=
  BaseExtension.Coherent.all_arrow_images (oldMeanings vertex base meaning)
    (Presentation.headers vertex) candidate images (old_arrow_readings vertex base meaning candidate images readings)

include readings in
theorem native_realized : Realization (Presentation.nativeSignature vertex) (assignment vertex base meaning) := by
  have realized := FunctorNormalization.reconstruction_realization
    (CoherentExtension.presented candidate (assignment vertex base meaning) images)
      (Presentation.nativeHeaders vertex)
  exact (CoherentExtension.assignment_equal candidate (assignment vertex base meaning)
    images (Presentation.nativeHeaders vertex) (all_arrow_readings vertex base meaning candidate images readings)) ▸ realized

include readings in
theorem old_realized : Realization (Presentation.signature vertex) (oldMeanings vertex base meaning) := by
  have restricted := (Presentation.nativeInclusion vertex).realization_precompose
    (assignment vertex base meaning) (native_realized vertex base meaning candidate images readings)
  simpa only [Presentation.nativeInclusion, assignment, BaseExtension.WeakExtension.original_precompose] using restricted

include readings in
theorem endpointLaws : Meaning.EndpointLaws vertex base meaning :=
  ((CategoryInterpretation.seven_diagram_admission_iff vertex base meaning).mp
    (old_realized vertex base meaning candidate images readings)).choose

include readings in
theorem categoryLaws : ModelDiagrams.LocalLaws vertex base meaning
    (endpointLaws vertex base meaning candidate images readings) :=
  ((CategoryInterpretation.seven_diagram_admission_iff vertex base meaning).mp
    (old_realized vertex base meaning candidate images readings)).choose_spec

def interpreted : Object (Presentation.nativeSignature vertex) ⥤ D :=
  Interpretation.functor (assignment vertex base meaning)
    (BaseExtension.WeakExtension.realization (oldMeanings vertex base meaning)
      (CategoryInterpretation.realization vertex base meaning
        (endpointLaws vertex base meaning candidate images readings)
        (categoryLaws vertex base meaning candidate images readings)))

def comparison : candidate ≅ interpreted vertex base meaning candidate images readings :=
  BaseExtension.Coherent.comparison (oldMeanings vertex base meaning)
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
    (Presentation.headers vertex) candidate images (old_arrow_readings vertex base meaning candidate images readings)

abbrev CellAdmission := BaseExtension.Coherent.CellAdmission (oldMeanings vertex base meaning)
  (CategoryInterpretation.realization vertex base meaning
    (endpointLaws vertex base meaning candidate images readings)
    (categoryLaws vertex base meaning candidate images readings)) candidate images

theorem comparison_admitted : CellAdmission vertex base meaning candidate images readings
    (comparison vertex base meaning candidate images readings).hom :=
  BaseExtension.Coherent.comparison_admitted (oldMeanings vertex base meaning)
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
    (Presentation.headers vertex) candidate images (old_arrow_readings vertex base meaning candidate images readings)

theorem admitted_cell_unique (cell : candidate ⟶ interpreted vertex base meaning candidate images readings)
    (components : CellAdmission vertex base meaning candidate images readings cell) :
    cell = (comparison vertex base meaning candidate images readings).hom :=
  BaseExtension.Coherent.admitted_cell_unique (oldMeanings vertex base meaning)
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
    (Presentation.headers vertex) candidate images (old_arrow_readings vertex base meaning candidate images readings)
      cell components

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ interpreted vertex base meaning candidate images readings //
      CellAdmission vertex base meaning candidate images readings iso.hom} :=
  BaseExtension.Coherent.admittedIsoUnique (oldMeanings vertex base meaning)
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))
    (Presentation.headers vertex) candidate images (old_arrow_readings vertex base meaning candidate images readings)

theorem complete_old_restriction : (Presentation.nativeInclusion vertex).functor ⋙
    interpreted vertex base meaning candidate images readings =
      CategoryInterpretation.functor vertex base meaning
        (endpointLaws vertex base meaning candidate images readings)
        (categoryLaws vertex base meaning candidate images readings) :=
  BaseExtension.WeakExtension.original_diagram_readback (oldMeanings vertex base meaning)
    (CategoryInterpretation.realization vertex base meaning
      (endpointLaws vertex base meaning candidate images readings)
      (categoryLaws vertex base meaning candidate images readings))

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.NativeUniversal
