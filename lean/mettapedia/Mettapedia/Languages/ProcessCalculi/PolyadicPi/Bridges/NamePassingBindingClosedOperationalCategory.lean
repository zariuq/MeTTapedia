import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasInterpretation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalCategory
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelRealization
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation

/-!
# Generated operational categories over the authored closed binding theory

The existing static equation presentation supplies the source program object
and its independently earned closed interpretation. Its program comparison
and the actual continuation-path category derive all seven new diagrams.
The native base extension retains the complete original finite-limit and
closed theory. Every generated endpoint, unit and composition has a whole
arrow-value readout. No selected operational-rule interpretation is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingCategoricalCompiler

abbrev staticSignature :=
  ClosedPresentation.AuthoredPresentation.signature.{0} NamePassing.AuthoredEquations.equations

abbrev Static := Object staticSignature

abbrev staticInterpretation := NamePassingBindingClosedSchemas.interpretation
abbrev base : Static ⥤ Ambient := staticInterpretation.functor

def vertex : Static :=
  (ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.obj
    (ClosedPresentation.sortObject.{0} NamePassing.Presentation.signature .tm)

abbrev actualCategory := CategoricalOperationalContinuations.category

/-- Original constructor restriction earns the actual complete program object. -/
theorem program_object : base.obj vertex = actualCategory.vertex := by
  have original := congrArg
    (fun map : Object (ClosedPresentation.signature.{0} NamePassing.Presentation.signature) ⥤ Ambient =>
      map.obj (ClosedPresentation.sortObject.{0} NamePassing.Presentation.signature .tm))
    NamePassingBindingClosedSchemas.complete_restriction
  exact original.trans
    (NamePassingBindingClosedOperations.Native.operations.sort_object_readout .tm)

def programComparison : base.obj vertex ≅ actualCategory.vertex := eqToIso program_object

instance base_lex : PreservesFiniteLimits base := staticInterpretation.preservesFiniteLimits
instance base_closed : MonoidalClosedFunctor base := staticInterpretation.preservesExponentials

abbrev meanings := RelativeClosedInternalCategory.ModelRealization.assignment
  vertex base actualCategory programComparison

abbrev evidenceOperations := RelativeClosedInternalCategory.ModelRealization.operations
  vertex base actualCategory programComparison

abbrev endpointLaws := RelativeClosedInternalCategory.ModelRealization.endpointLaws
  vertex base actualCategory programComparison

abbrev evidenceEndpoints := RelativeClosedInternalCategory.ModelDiagrams.endpoints
  vertex base evidenceOperations endpointLaws

theorem all_seven_diagrams :
    Realization (RelativeClosedInternalCategory.Presentation.signature vertex) meanings :=
  RelativeClosedInternalCategory.ModelRealization.realization vertex base actualCategory programComparison

def categoryInterpretation :=
  RelativeClosedInternalCategory.ModelRealization.functor vertex base actualCategory programComparison

instance meanings_lex : PreservesFiniteLimits meanings.base := by
  change PreservesFiniteLimits base
  infer_instance

instance meanings_closed : MonoidalClosedFunctor meanings.base := by
  change MonoidalClosedFunctor base
  infer_instance

abbrev nativeMeanings := BaseExtension.WeakExtension.assignment meanings

theorem native_all_seven_diagrams :
    Realization (RelativeClosedInternalCategory.Presentation.nativeSignature vertex) nativeMeanings :=
  BaseExtension.WeakExtension.realization meanings all_seven_diagrams

/-- The actual finite-limit and closed interpretation of the native guest. -/
def nativeInterpretation :
    Mettapedia.GSLT.Core.LambdaTheoryMap (RelativeClosedInternalCategory.Presentation.theory vertex)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory Ambient) where
  functor := Interpretation.functor nativeMeanings native_all_seven_diagrams
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits nativeMeanings native_all_seven_diagrams
  preservesExponentials := Interpretation.functor_closed nativeMeanings native_all_seven_diagrams

/-- Every original static object and arrow retains the supplied interpretation. -/
theorem complete_static_restriction :
    (RelativeClosedInternalCategory.Presentation.baseMap vertex).functor ⋙
      nativeInterpretation.functor = base :=
  Interpretation.functor_base nativeMeanings native_all_seven_diagrams

/-- Native base comparisons leave the whole independently generated category unchanged. -/
theorem complete_category_restriction :
    (RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
      nativeInterpretation.functor = categoryInterpretation :=
  BaseExtension.WeakExtension.original_diagram_readback meanings all_seven_diagrams

def sourceCode := RelativeClosedInternalCategory.ModelRealization.sourceCode vertex
def targetCode := RelativeClosedInternalCategory.ModelRealization.targetCode vertex
def unitCode := RelativeClosedInternalCategory.ModelRealization.unitCode vertex
def compositionCode := RelativeClosedInternalCategory.ModelRealization.compositionCode vertex

def value {first second : Object (RelativeClosedInternalCategory.Presentation.signature vertex)}
    (code : RawHom first second) : ArrowValue Ambient :=
  ⟨categoryInterpretation.obj first,categoryInterpretation.obj second,
    categoryInterpretation.map (classOf code)⟩

theorem source_readout : value sourceCode =
    ⟨actualCategory.edge,base.obj vertex,actualCategory.source ≫ programComparison.inv⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_source
    vertex base actualCategory programComparison

theorem target_readout : value targetCode =
    ⟨actualCategory.edge,base.obj vertex,actualCategory.target ≫ programComparison.inv⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_target
    vertex base actualCategory programComparison

theorem unit_readout : value unitCode =
    ⟨base.obj vertex,actualCategory.edge,programComparison.hom ≫ actualCategory.unit⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_unit
    vertex base actualCategory programComparison

theorem composition_readout : value compositionCode =
    ⟨evidenceOperations.toGraph.composable,actualCategory.edge,evidenceOperations.composition⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_composition
    vertex base actualCategory programComparison

/-- All native generated arrows have the same complete values, not just endpoints. -/
theorem native_value_readout
    {first second : Object (RelativeClosedInternalCategory.Presentation.signature vertex)}
    (code : RawHom first second) :
    (⟨((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
        nativeInterpretation.functor).obj first,
      ((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
        nativeInterpretation.functor).obj second,
      ((RelativeClosedInternalCategory.Presentation.nativeInclusion vertex).functor ⋙
        nativeInterpretation.functor).map (classOf code)⟩ : ArrowValue Ambient) = value code :=
  congrArg (fun map : Object (RelativeClosedInternalCategory.Presentation.signature vertex) ⥤ Ambient =>
    (⟨map.obj first,map.obj second,map.map (classOf code)⟩ : ArrowValue Ambient))
      complete_category_restriction

/-- Chosen generated composition reads the full two retained paths at every parameter. -/
theorem complete_composition {parameter : Ambient}
    (first second : parameter ⟶ actualCategory.edge)
    (matching : first ≫ evidenceOperations.target = second ≫ evidenceOperations.source) :
    InternalCategoryPresentedDiagrams.compose evidenceEndpoints first second matching =
      actualCategory.compose first second
        (InternalCategoryVertexIso.matching actualCategory programComparison first second matching) :=
  RelativeClosedInternalCategory.ModelRealization.complete_compose_read
    vertex base actualCategory programComparison first second matching

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperationalCategory
