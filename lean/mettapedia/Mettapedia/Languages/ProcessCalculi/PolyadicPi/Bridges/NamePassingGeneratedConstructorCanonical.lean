import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorNaturality
import Mettapedia.CategoryTheory.ClosedFunctorNativeReadout

/-!
# Canonical native constructor squares

The complete ordinary source readings and independent target readings are
joined through the actual constructor natural isomorphism. Their native
product and full function domains use the compiler's canonical comparisons,
including the contravariant function argument and padded-context readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonical

open _root_.CategoryTheory MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingGeneratedConstructorComparison

universe k

abbrev names := NamePassingBindingClosedConstructorExpressions.names.{k}
abbrev terms := NamePassingBindingClosedConstructorExpressions.terms.{k}
abbrev bodies := NamePassingBindingClosedConstructorExpressions.bodies.{k}
abbrev last : Object (ClosedPresentation.signature.{k} NamePassing.Presentation.signature) ⥤ Target.{k} :=
  targetOperations.interpretation.functor
abbrev square := NamePassingGeneratedConstructorNaturality.comparison.{k}

instance sourceNative_finite : _root_.CategoryTheory.Limits.PreservesFiniteLimits sourceNative.{k} := by
  change _root_.CategoryTheory.Limits.PreservesFiniteLimits (FunctorNormalization.normalizedFunctor constructors)
  infer_instance
instance sourceNative_closed : MonoidalClosedFunctor sourceNative.{k} := by
  change MonoidalClosedFunctor (FunctorNormalization.normalizedFunctor constructors)
  infer_instance
instance compiler_finite : _root_.CategoryTheory.Limits.PreservesFiniteLimits compiler.{k} :=
  NamePassingGeneratedOperationalCategory.nativeInterpretation.preservesFiniteLimits
instance compiler_closed : MonoidalClosedFunctor compiler.{k} :=
  NamePassingGeneratedOperationalCategory.nativeInterpretation.preservesExponentials
instance last_finite : _root_.CategoryTheory.Limits.PreservesFiniteLimits last.{k} :=
  Interpretation.functor_preservesFiniteLimits targetOperations.assignment targetOperations.realization
instance last_closed : MonoidalClosedFunctor last.{k} :=
  Interpretation.functor_closed targetOperations.assignment targetOperations.realization

theorem source_sort (sort : NamePassing.Presentation.Srt) :
    sourceNative.{k}.obj (ClosedPresentation.sortObject NamePassing.Presentation.signature sort) =
      sourceOperations.sort sort :=
  ClosedPresentation.GeneratedModel.sort_native constructors sort

theorem target_sort (sort : NamePassing.Presentation.Srt) :
    last.{k}.obj (ClosedPresentation.sortObject NamePassing.Presentation.signature sort) =
      targetOperations.sort sort := targetOperations.sort_object_readout sort

def nameComparison : compiler.obj (NamePassingBindingPrimitiveOperations.names sourceOperations.{k}) ≅
    NamePassingGeneratedOperationalCategory.ordinary.names :=
  ClosedFunctorNativeReadout.objectChange sourceNative compiler last square names _ _
    (source_sort .nm) (target_sort .nm)

def termComparison : compiler.obj (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k}) ≅
    NamePassingGeneratedOperationalCategory.ordinary.termObject :=
  ClosedFunctorNativeReadout.objectChange sourceNative compiler last square terms _ _
    (source_sort .tm) (target_sort .tm)

def applicationComparison : compiler.obj (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.names sourceOperations) ≅
    NamePassingGeneratedOperationalCategory.ordinary.termObject ⊗ NamePassingGeneratedOperationalCategory.ordinary.names :=
  ClosedFunctorNativeReadout.productChange sourceNative compiler last square
    (source_sort .tm) (source_sort .nm) (target_sort .tm) (target_sort .nm)

def abstractionComparison : compiler.obj (NamePassingBindingPrimitiveOperations.bodies sourceOperations.{k}) ≅
    NamePassingGeneratedOperationalCategory.ordinary.boundBodyObject :=
  ClosedFunctorNativeReadout.functionChange sourceNative compiler last square
    (source_sort .nm) (source_sort .tm) (target_sort .nm) (target_sort .tm)

private theorem source_application_read :
    (⟨sourceNative.{k}.obj terms ⊗ sourceNative.obj names,sourceNative.obj terms,
      inv (CartesianMonoidalCategory.prodComparison sourceNative terms names) ≫
        sourceNative.map (classOf NamePassingBindingClosedConstructorExpressions.application)⟩ : ArrowValue Source) =
      ⟨NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗ NamePassingBindingPrimitiveOperations.names sourceOperations,
        NamePassingBindingPrimitiveOperations.terms sourceOperations,
        NamePassingBindingPrimitiveOperations.application sourceOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (FunctorNormalization.normalized_product_object constructors terms names)
    (FunctorNormalization.normalized_productComparison constructors terms names) _
    (whole_source_constructor .application)

private theorem target_application_read :
    (⟨last.{k}.obj terms ⊗ last.obj names,last.obj terms,
      inv (CartesianMonoidalCategory.prodComparison last terms names) ≫
        last.map (classOf NamePassingBindingClosedConstructorExpressions.application)⟩ : ArrowValue Target) =
      ⟨NamePassingBindingPrimitiveOperations.terms targetOperations ⊗ NamePassingBindingPrimitiveOperations.names targetOperations,
        NamePassingBindingPrimitiveOperations.terms targetOperations,
        NamePassingBindingPrimitiveOperations.application targetOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (functor_product_object targetOperations.assignment targetOperations.realization terms names)
    (functor_productComparison targetOperations.assignment targetOperations.realization terms names) _
    (NamePassingBindingClosedConstructorReadout.complete_readout targetOperations .application)

theorem complete_application : applicationComparison.{k}.inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.application sourceOperations) ≫ termComparison.hom =
      NamePassingGeneratedOperationalCategory.ordinary.application := by
  have actual := ClosedFunctorNativeReadout.complete_product_arrow sourceNative compiler last square
    (classOf NamePassingBindingClosedConstructorExpressions.application)
    (source_sort .tm) (source_sort .nm) (source_sort .tm)
    (target_sort .tm) (target_sort .nm) (target_sort .tm)
    _ _ source_application_read target_application_read
  exact actual.trans application_readout

private theorem source_abstraction_read :
    (⟨(sourceNative.{k}.obj names ⟶[Source] sourceNative.obj terms),sourceNative.obj terms,
      inv ((expComparison sourceNative names).natTrans.app terms) ≫
        sourceNative.map (classOf NamePassingBindingClosedConstructorExpressions.abstraction)⟩ : ArrowValue Source) =
      ⟨NamePassingBindingPrimitiveOperations.bodies sourceOperations,
        NamePassingBindingPrimitiveOperations.terms sourceOperations,
        NamePassingBindingPrimitiveOperations.abstraction sourceOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (FunctorNormalization.normalized_exponential_object constructors names terms)
    (FunctorNormalization.normalized_expComparison constructors names terms) _
    (whole_source_constructor .abstraction)

private theorem target_abstraction_read :
    (⟨(last.{k}.obj names ⟶[Target] last.obj terms),last.obj terms,
      inv ((expComparison last names).natTrans.app terms) ≫
        last.map (classOf NamePassingBindingClosedConstructorExpressions.abstraction)⟩ : ArrowValue Target) =
      ⟨NamePassingBindingPrimitiveOperations.bodies targetOperations,
        NamePassingBindingPrimitiveOperations.terms targetOperations,
        NamePassingBindingPrimitiveOperations.abstraction targetOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (functor_exponential_object targetOperations.assignment targetOperations.realization names terms)
    (functor_expComparison targetOperations.assignment targetOperations.realization names terms) _
    (NamePassingBindingClosedConstructorReadout.complete_readout targetOperations .abstraction)

theorem complete_abstraction : abstractionComparison.{k}.inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.abstraction sourceOperations) ≫ termComparison.hom =
      NamePassingGeneratedOperationalCategory.ordinary.abstraction := by
  have actual := ClosedFunctorNativeReadout.complete_function_arrow sourceNative compiler last square
    (classOf NamePassingBindingClosedConstructorExpressions.abstraction)
    (source_sort .nm) (source_sort .tm) (source_sort .tm)
    (target_sort .nm) (target_sort .tm) (target_sort .tm)
    _ _ source_abstraction_read target_abstraction_read
  exact actual.trans abstraction_readout

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonical
