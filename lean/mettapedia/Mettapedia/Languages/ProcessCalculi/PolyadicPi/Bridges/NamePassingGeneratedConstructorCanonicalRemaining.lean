import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalDomains
import Mettapedia.CategoryTheory.ClosedFunctorProductComponentCalibration

/-!
# Reference and carrier through canonical native domains

The carrier's nested pair retains its stored and active positions separately.
Its complete raw product comparison agrees with the compiler's canonical
inner product comparison. Together with the ordinary reference square these
complete the five chosen native binding-constructor comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalRemaining

open _root_.CategoryTheory MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingGeneratedConstructorComparison NamePassingGeneratedConstructorCanonical
open NamePassingGeneratedConstructorCanonicalDomains

universe k

theorem complete_reference : nameComparison.{k}.inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.reference sourceOperations) ≫ termComparison.hom =
      NamePassingGeneratedOperationalCategory.ordinary.reference := by
  have actual := ClosedFunctorProductComponentCalibration.complete_object_arrow
    sourceNative compiler last square (classOf NamePassingBindingClosedConstructorExpressions.reference)
    (source_sort .nm) (source_sort .tm) (target_sort .nm) (target_sort .tm)
    _ _ (whole_source_constructor .reference)
    (NamePassingBindingClosedConstructorReadout.complete_readout targetOperations .reference)
  exact actual.trans reference_readout

def pairTerms : Object (ClosedPresentation.signature.{k} NamePassing.Presentation.signature) :=
  product terms terms

theorem sourcePairSame : sourceNative.{k}.obj pairTerms =
    NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
      NamePassingBindingPrimitiveOperations.terms sourceOperations :=
  (FunctorNormalization.normalized_product_object constructors terms terms).trans
    (congrArg₂ (fun first second : Source => first ⊗ second) (source_sort .tm) (source_sort .tm))

theorem targetPairSame : last.{k}.obj pairTerms =
    NamePassingBindingPrimitiveOperations.terms targetOperations ⊗
      NamePassingBindingPrimitiveOperations.terms targetOperations :=
  (functor_product_object targetOperations.assignment targetOperations.realization terms terms).trans
    (congrArg₂ (fun first second : Target => first ⊗ second) (target_sort .tm) (target_sort .tm))

private theorem source_calibrated : CartesianMonoidalCategory.prodComparison sourceNative.{k} terms terms ≫
    (tensorIso (eqToIso (source_sort .tm)) (eqToIso (source_sort .tm))).hom = eqToHom sourcePairSame := by
  rw [ClosedFunctorProductComponentCalibration.tensorIso_cast]
  change CartesianMonoidalCategory.prodComparison sourceNative terms terms ≫
    eqToHom (congrArg₂ (fun first second : Source => first ⊗ second) (source_sort .tm) (source_sort .tm)) = _
  erw [FunctorNormalization.normalized_productComparison constructors, eqToHom_trans]

private theorem target_calibrated : CartesianMonoidalCategory.prodComparison last.{k} terms terms ≫
    (tensorIso (eqToIso (target_sort .tm)) (eqToIso (target_sort .tm))).hom = eqToHom targetPairSame := by
  rw [ClosedFunctorProductComponentCalibration.tensorIso_cast]
  change CartesianMonoidalCategory.prodComparison last terms terms ≫
    eqToHom (congrArg₂ (fun first second : Target => first ⊗ second) (target_sort .tm) (target_sort .tm)) = _
  erw [functor_productComparison targetOperations.assignment targetOperations.realization, eqToHom_trans]

def pairObjectComparison : compiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.terms sourceOperations) ≅
    NamePassingGeneratedOperationalCategory.ordinary.termObject ⊗
      NamePassingGeneratedOperationalCategory.ordinary.termObject :=
  ClosedFunctorNativeReadout.objectChange sourceNative compiler last square pairTerms _ _
    sourcePairSame targetPairSame

def pairComparison : compiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.terms sourceOperations) ≅
    NamePassingGeneratedOperationalCategory.ordinary.termObject ⊗
      NamePassingGeneratedOperationalCategory.ordinary.termObject :=
  ClosedFunctorNativeReadout.productChange sourceNative compiler last square
    (source_sort .tm) (source_sort .tm) (target_sort .tm) (target_sort .tm)

theorem pairObjectComparison_eq : pairObjectComparison.{k} = pairComparison :=
  ClosedFunctorProductComponentCalibration.product_component_calibrated sourceNative compiler last square
    (source_sort .tm) (source_sort .tm) (target_sort .tm) (target_sort .tm)
    sourcePairSame targetPairSame source_calibrated target_calibrated

def carrierComparison : compiler.obj
    (NamePassingBindingPrimitiveOperations.names sourceOperations.{k} ⊗
      (NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
        NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≅
    NamePassingGeneratedOperationalCategory.ordinary.names ⊗
      (NamePassingGeneratedOperationalCategory.ordinary.termObject ⊗
        NamePassingGeneratedOperationalCategory.ordinary.termObject) :=
  ClosedFunctorNativeReadout.productChange sourceNative compiler last square
    (source_sort .nm) sourcePairSame (target_sort .nm) targetPairSame

theorem carrierComparison_canonical : carrierComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison compiler
      (NamePassingBindingPrimitiveOperations.names sourceOperations)
      (NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
        NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≪≫
      tensorIso nameComparison pairComparison := by
  unfold carrierComparison ClosedFunctorNativeReadout.productChange
  change _ ≪≫ tensorIso nameComparison pairObjectComparison = _
  rw [pairObjectComparison_eq]

private theorem source_carrier_read :
    (⟨sourceNative.{k}.obj names ⊗ sourceNative.obj pairTerms,sourceNative.obj terms,
      inv (CartesianMonoidalCategory.prodComparison sourceNative names pairTerms) ≫
        sourceNative.map (classOf NamePassingBindingClosedConstructorExpressions.carrier)⟩ : ArrowValue Source) =
      ⟨NamePassingBindingPrimitiveOperations.names sourceOperations ⊗
          (NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
            NamePassingBindingPrimitiveOperations.terms sourceOperations),
        NamePassingBindingPrimitiveOperations.terms sourceOperations,
        NamePassingBindingPrimitiveOperations.carrier sourceOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (FunctorNormalization.normalized_product_object constructors names pairTerms)
    (FunctorNormalization.normalized_productComparison constructors names pairTerms) _
    (whole_source_constructor .carrier)

private theorem target_carrier_read :
    (⟨last.{k}.obj names ⊗ last.obj pairTerms,last.obj terms,
      inv (CartesianMonoidalCategory.prodComparison last names pairTerms) ≫
        last.map (classOf NamePassingBindingClosedConstructorExpressions.carrier)⟩ : ArrowValue Target) =
      ⟨NamePassingBindingPrimitiveOperations.names targetOperations ⊗
          (NamePassingBindingPrimitiveOperations.terms targetOperations ⊗
            NamePassingBindingPrimitiveOperations.terms targetOperations),
        NamePassingBindingPrimitiveOperations.terms targetOperations,
        NamePassingBindingPrimitiveOperations.carrier targetOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (functor_product_object targetOperations.assignment targetOperations.realization names pairTerms)
    (functor_productComparison targetOperations.assignment targetOperations.realization names pairTerms) _
    (NamePassingBindingClosedConstructorReadout.complete_readout targetOperations .carrier)

theorem complete_carrier : carrierComparison.{k}.inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.carrier sourceOperations) ≫ termComparison.hom =
      NamePassingGeneratedOperationalCategory.ordinary.carrier := by
  have actual := ClosedFunctorNativeReadout.complete_product_arrow sourceNative compiler last square
    (classOf NamePassingBindingClosedConstructorExpressions.carrier)
    (source_sort .nm) sourcePairSame (source_sort .tm)
    (target_sort .nm) targetPairSame (target_sort .tm)
    _ _ source_carrier_read target_carrier_read
  exact actual.trans carrier_readout

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalRemaining
