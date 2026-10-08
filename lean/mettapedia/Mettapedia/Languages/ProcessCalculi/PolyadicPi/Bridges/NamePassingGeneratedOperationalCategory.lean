import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalModel
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStaticInterpretation
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelRealization
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation

/-!
# The source category guest interpreted in the generated operational target

The complete return-indexed category is transported from the actual target
internal category by the right adjoint for names. The independently generated
source static compiler supplies the vertex comparison. All seven category
diagrams, including composition on the actual composable-edge pullback,
therefore follow from that category's universal constructions.

This construction does not yet interpret the source primitive beta/fetch or
active-closure declarations. Those need target operational evidence arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

universe k

abbrev Target := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev binding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev ordinary := BindingClosedGeneratedOperationalModel.ordinary.{k}
abbrev staticSignature := ClosedPresentation.AuthoredPresentation.signature.{k}
  NamePassing.AuthoredEquations.equations
abbrev Static := Object staticSignature.{k}
abbrev staticInclusion := ClosedPresentation.AuthoredPresentation.inclusion.{k}
  NamePassing.AuthoredEquations.equations

def staticCompiler := NamePassingGeneratedStatic.interpretation binding.{k}
  BindingClosedGeneratedOperationalModel.structural_schemas

abbrev base : Static.{k} ⥤ Target.{k} := staticCompiler.functor

instance base_lex : PreservesFiniteLimits base.{k} := staticCompiler.preservesFiniteLimits
instance base_closed : MonoidalClosedFunctor base.{k} := staticCompiler.preservesExponentials

def vertex : Static.{k} :=
  staticInclusion.functor.obj (ClosedPresentation.sortObject.{k} NamePassing.Presentation.signature .tm)

def actualCategory : InternalCategory Target.{k} :=
  InternalCategoryFiniteLimitTransport.category (ihom ordinary.names)
    BindingClosedGeneratedOperationalModel.category

theorem program_object : base.obj vertex.{k} = ordinary.termObject := by
  have original := congrArg
    (fun map : Object (ClosedPresentation.signature.{k} NamePassing.Presentation.signature) ⥤ Target =>
      map.obj (ClosedPresentation.sortObject.{k} NamePassing.Presentation.signature .tm))
    (NamePassingGeneratedStatic.complete_restriction binding
      BindingClosedGeneratedOperationalModel.structural_schemas)
  exact original.trans ((NamePassingGeneratedStatic.operations binding).sort_object_readout .tm)

def programComparison : base.obj vertex.{k} ≅ actualCategory.vertex :=
  (eqToIso program_object).trans
    ((ihom ordinary.names).mapIso BindingClosedGeneratedOperationalModel.processComparison)

abbrev meanings := RelativeClosedInternalCategory.ModelRealization.assignment
  vertex.{k} base actualCategory programComparison

abbrev evidenceOperations := RelativeClosedInternalCategory.ModelRealization.operations
  vertex.{k} base actualCategory programComparison

theorem all_seven_diagrams :
    Realization (RelativeClosedInternalCategory.Presentation.signature vertex.{k}) meanings :=
  RelativeClosedInternalCategory.ModelRealization.realization vertex base actualCategory programComparison

def categoryInterpretation : Object (RelativeClosedInternalCategory.Presentation.signature vertex.{k}) ⥤ Target :=
  RelativeClosedInternalCategory.ModelRealization.functor vertex base actualCategory programComparison

instance meanings_lex : PreservesFiniteLimits meanings.{k}.base := by
  change PreservesFiniteLimits base
  exact staticCompiler.preservesFiniteLimits

instance meanings_closed : MonoidalClosedFunctor meanings.{k}.base := by
  change MonoidalClosedFunctor base
  exact staticCompiler.preservesExponentials

abbrev nativeMeanings := BaseExtension.WeakExtension.assignment meanings.{k}

theorem native_all_seven_diagrams :
    Realization (RelativeClosedInternalCategory.Presentation.nativeSignature vertex.{k}) nativeMeanings :=
  BaseExtension.WeakExtension.realization meanings all_seven_diagrams

def nativeInterpretation :
    Mettapedia.GSLT.Core.LambdaTheoryMap (RelativeClosedInternalCategory.Presentation.theory vertex.{k})
      BindingClosedGeneratedOperational.theory where
  functor := Interpretation.functor nativeMeanings native_all_seven_diagrams
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits nativeMeanings native_all_seven_diagrams
  preservesExponentials := Interpretation.functor_closed nativeMeanings native_all_seven_diagrams

theorem complete_static_restriction :
    (RelativeClosedInternalCategory.Presentation.baseMap vertex.{k}).functor ⋙
      nativeInterpretation.functor = base :=
  Interpretation.functor_base nativeMeanings native_all_seven_diagrams

theorem complete_category_restriction :
    (RelativeClosedInternalCategory.Presentation.nativeInclusion vertex.{k}).functor ⋙
      nativeInterpretation.functor = categoryInterpretation :=
  BaseExtension.WeakExtension.original_diagram_readback meanings all_seven_diagrams

def value {first second : Object (RelativeClosedInternalCategory.Presentation.signature vertex.{k})}
    (code : RawHom first second) : ArrowValue Target :=
  ⟨categoryInterpretation.obj first,categoryInterpretation.obj second,categoryInterpretation.map (classOf code)⟩

theorem source_readout : value (RelativeClosedInternalCategory.ModelRealization.sourceCode vertex.{k}) =
    ⟨actualCategory.edge,base.obj vertex,actualCategory.source ≫ programComparison.inv⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_source
    vertex base actualCategory programComparison

theorem target_readout : value (RelativeClosedInternalCategory.ModelRealization.targetCode vertex.{k}) =
    ⟨actualCategory.edge,base.obj vertex,actualCategory.target ≫ programComparison.inv⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_target
    vertex base actualCategory programComparison

theorem unit_readout : value (RelativeClosedInternalCategory.ModelRealization.unitCode vertex.{k}) =
    ⟨base.obj vertex,actualCategory.edge,programComparison.hom ≫ actualCategory.unit⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_unit
    vertex base actualCategory programComparison

theorem composition_readout : value (RelativeClosedInternalCategory.ModelRealization.compositionCode vertex.{k}) =
    ⟨evidenceOperations.toGraph.composable,actualCategory.edge,evidenceOperations.composition⟩ :=
  RelativeClosedInternalCategory.ModelRealization.complete_generated_composition
    vertex base actualCategory programComparison

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategory
