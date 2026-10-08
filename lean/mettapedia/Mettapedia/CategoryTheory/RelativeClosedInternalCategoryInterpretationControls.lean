import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryUniversal
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryNativeUniversal
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryCategoryControls
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension

/-!
# Complete generated evidence readings and rejected category models

The independently interpreted generated composition is applied to arbitrary
matching evidence, retaining both outer endpoints and the complete summed
weight. Its local primitive admission earns the whole unique comparison.
Endpoint-correct extra-weight operations and an incorrect unit are rejected
by the complete generated category presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.InterpretationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation
open Controls CategoryControls

abbrev supplied := CategoryInterpretation.assignment vertex base weighted
abbrev suppliedRealization := CategoryInterpretation.realization vertex base weighted
  weighted_endpoint_laws weighted_category_laws
abbrev interpreted := CategoryInterpretation.functor vertex base weighted
  weighted_endpoint_laws weighted_category_laws

instance interpreted_lex : PreservesFiniteLimits interpreted := by
  change PreservesFiniteLimits (Interpretation.functor supplied suppliedRealization)
  infer_instance

instance interpreted_closed : MonoidalClosedFunctor interpreted := by
  change MonoidalClosedFunctor (Interpretation.functor supplied suppliedRealization)
  infer_instance

def compositionSource := (Presentation.inclusion vertex).object (Endpoints.composable vertex)
def compositionTarget := (Presentation.inclusion vertex).object (Endpoints.edgeObject vertex)
def compositionCode := (Presentation.inclusion vertex).rawArrow (Endpoints.composition vertex)

theorem generated_composition_read :
    (⟨interpreted.obj compositionSource,interpreted.obj compositionTarget,
      interpreted.map (classOf compositionCode)⟩ : ArrowValue Type) =
        ⟨graph.composable,Evidence,weighted.composition⟩ := by
  have complete := Interpretation.functor_complete_readout supplied suppliedRealization compositionCode
  have read := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex) (EquationReadout.assignment vertex base weighted)
      (Endpoints.composition vertex).code).trans (EquationReadout.composition_read vertex base weighted)
  exact Option.some.inj (complete.symm.trans read)

def readGeneratedComposition : Option (graph.composable ⟶ Evidence) :=
  ArrowValue.readAt (some ⟨interpreted.obj compositionSource,interpreted.obj compositionTarget,
    interpreted.map (classOf compositionCode)⟩) graph.composable Evidence

theorem generated_composition_function : readGeneratedComposition = some weighted.composition := by
  unfold readGeneratedComposition
  rw [generated_composition_read]
  exact ArrowValue.readAt_supplied _

theorem whole_generated_composition (pair : graph.composable) :
    readGeneratedComposition.map (fun operation => operation pair) =
      some ((graph.first pair).1,(graph.second pair).2.1,
        (graph.first pair).2.2 + (graph.second pair).2.2) := by
  rw [generated_composition_function]
  rfl

def sampleFirst : PUnit ⟶ Evidence := TypeCat.ofHom (fun _ => (false,true,3))
def sampleSecond : PUnit ⟶ Evidence := TypeCat.ofHom (fun _ => (true,false,7))

theorem sample_matching : sampleFirst ≫ graph.target = sampleSecond ≫ graph.source := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  rfl

def samplePair : graph.composable :=
  CartesianEqualizerPullback.lift graph.target graph.source sampleFirst sampleSecond sample_matching PUnit.unit

theorem generated_value_retains_endpoints_and_weight :
    readGeneratedComposition.map (fun operation => operation samplePair) =
      some ((false,false,10) : Evidence) := by
  rw [whole_generated_composition]
  have first := congrArg (fun arrow : PUnit ⟶ Evidence => arrow PUnit.unit)
    (CartesianEqualizerPullback.lift_first graph.target graph.source
      sampleFirst sampleSecond sample_matching)
  have second := congrArg (fun arrow : PUnit ⟶ Evidence => arrow PUnit.unit)
    (CartesianEqualizerPullback.lift_second graph.target graph.source
      sampleFirst sampleSecond sample_matching)
  change graph.first samplePair = (false,true,3) at first
  change graph.second samplePair = (true,false,7) at second
  rw [first,second]
  rfl

theorem weighted_seven_diagrams_admitted : Realization (Presentation.signature vertex) supplied :=
  (CategoryInterpretation.seven_diagram_admission_iff vertex base weighted).mpr
    ⟨weighted_endpoint_laws,weighted_category_laws⟩

def primitiveImages := CanonicalExtension.images supplied suppliedRealization

theorem primitive_readings : Universal.OperationReadings vertex base weighted interpreted primitiveImages where
  source := (CanonicalExtension.arrow_images supplied suppliedRealization
    (Presentation.headers vertex)).arrow (ULift.up Operation.source)
  target := (CanonicalExtension.arrow_images supplied suppliedRealization
    (Presentation.headers vertex)).arrow (ULift.up Operation.target)
  unit := (CanonicalExtension.arrow_images supplied suppliedRealization
    (Presentation.headers vertex)).arrow (ULift.up Operation.unit)
  composition := (CanonicalExtension.arrow_images supplied suppliedRealization
    (Presentation.headers vertex)).arrow (ULift.up Operation.composition)

abbrev generatedUniqueComparison :
    Unique {iso : interpreted ≅ CategoryInterpretation.functor vertex base weighted
      (Universal.endpointLaws vertex base weighted interpreted primitiveImages primitive_readings)
      (Universal.categoryLaws vertex base weighted interpreted primitiveImages primitive_readings) //
        Universal.CellAdmission vertex base weighted interpreted primitiveImages primitive_readings iso.hom} :=
  Universal.admittedIsoUnique vertex base weighted interpreted primitiveImages primitive_readings

theorem endpoint_correct_offset_not_generated :
    ¬ Realization (Presentation.signature vertex) (CategoryInterpretation.assignment vertex base offset) := by
  intro admitted
  obtain ⟨endpoints,laws⟩ := (CategoryInterpretation.seven_diagram_admission_iff vertex base offset).mp admitted
  have same := Subsingleton.elim endpoints offset_endpoint_laws
  cases same
  exact offset_category_rejected laws

theorem incorrect_unit_not_generated :
    ¬ Realization (Presentation.signature vertex) (CategoryInterpretation.assignment vertex base incorrectUnit) := by
  intro admitted
  exact incorrect_unit_rejected
    ((CategoryInterpretation.seven_diagram_admission_iff vertex base incorrectUnit).mp admitted).choose

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.InterpretationControls
