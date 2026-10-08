import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonical

/-!
# Chosen complete body comparison

The raw function object, its ordinary binding interpretation and the
compiler's canonical function comparison agree. Both independently chosen
closed interpretations calibrate their exponential comparisons before the
constructor square is pasted. This retains every function argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalDomains

open _root_.CategoryTheory MonoidalCategory MonoidalClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingGeneratedConstructorComparison
open NamePassingGeneratedConstructorCanonical

universe k

theorem sourceBodySame : sourceNative.{k}.obj bodies =
    NamePassingBindingPrimitiveOperations.bodies sourceOperations :=
  (FunctorNormalization.normalized_exponential_object constructors names terms).trans
    (congrArg₂ (fun input output : Source => input ⟶[Source] output)
      (source_sort .nm) (source_sort .tm))

theorem targetBodySame : last.{k}.obj bodies =
    NamePassingBindingPrimitiveOperations.bodies targetOperations :=
  (functor_exponential_object targetOperations.assignment targetOperations.realization names terms).trans
    (congrArg₂ (fun input output : Target => input ⟶[Target] output)
      (target_sort .nm) (target_sort .tm))

private theorem source_calibrated : (expComparison sourceNative.{k} names).natTrans.app terms ≫
    (FunctorNormalization.functionIso (eqToIso (source_sort .nm)) (eqToIso (source_sort .tm))).hom =
      eqToHom sourceBodySame := by
  rw [ClosedFunctorNativeReadout.functionIso_cast]
  change (expComparison sourceNative names).natTrans.app terms ≫
      eqToHom (congrArg₂ (fun input output : Source => input ⟶[Source] output)
        (source_sort .nm) (source_sort .tm)) = _
  erw [FunctorNormalization.normalized_expComparison constructors, eqToHom_trans]

private theorem target_calibrated : (expComparison last.{k} names).natTrans.app terms ≫
    (FunctorNormalization.functionIso (eqToIso (target_sort .nm)) (eqToIso (target_sort .tm))).hom =
      eqToHom targetBodySame := by
  rw [ClosedFunctorNativeReadout.functionIso_cast]
  change (expComparison last names).natTrans.app terms ≫
      eqToHom (congrArg₂ (fun input output : Target => input ⟶[Target] output)
        (target_sort .nm) (target_sort .tm)) = _
  erw [functor_expComparison targetOperations.assignment targetOperations.realization, eqToHom_trans]

def bodyObjectComparison : compiler.obj (NamePassingBindingPrimitiveOperations.bodies sourceOperations.{k}) ≅
    NamePassingGeneratedOperationalCategory.ordinary.boundBodyObject :=
  ClosedFunctorNativeReadout.objectChange sourceNative compiler last square bodies _ _
    sourceBodySame targetBodySame

theorem bodyObjectComparison_eq : bodyObjectComparison.{k} = abstractionComparison :=
  ClosedFunctorNativeReadout.function_component_calibrated sourceNative compiler last square
    (source_sort .nm) (source_sort .tm) (target_sort .nm) (target_sort .tm)
    sourceBodySame targetBodySame source_calibrated target_calibrated

def definitionComparison : compiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.bodies sourceOperations) ≅
    NamePassingGeneratedOperationalCategory.ordinary.termObject ⊗
      NamePassingGeneratedOperationalCategory.ordinary.boundBodyObject :=
  ClosedFunctorNativeReadout.productChange sourceNative compiler last square
    (source_sort .tm) sourceBodySame (target_sort .tm) targetBodySame

theorem definitionComparison_canonical : definitionComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison compiler
      (NamePassingBindingPrimitiveOperations.terms sourceOperations)
      (NamePassingBindingPrimitiveOperations.bodies sourceOperations)) ≪≫
        tensorIso termComparison abstractionComparison := by
  unfold definitionComparison ClosedFunctorNativeReadout.productChange
  change _ ≪≫ tensorIso termComparison bodyObjectComparison = _
  rw [bodyObjectComparison_eq]

private theorem source_definition_read :
    (⟨sourceNative.{k}.obj terms ⊗ sourceNative.obj bodies,sourceNative.obj terms,
      inv (CartesianMonoidalCategory.prodComparison sourceNative terms bodies) ≫
        sourceNative.map (classOf NamePassingBindingClosedConstructorExpressions.definition)⟩ : ArrowValue Source) =
      ⟨NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
          NamePassingBindingPrimitiveOperations.bodies sourceOperations,
        NamePassingBindingPrimitiveOperations.terms sourceOperations,
        NamePassingBindingPrimitiveOperations.definition sourceOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (FunctorNormalization.normalized_product_object constructors terms bodies)
    (FunctorNormalization.normalized_productComparison constructors terms bodies) _
    (whole_source_constructor .definition)

private theorem target_definition_read :
    (⟨last.{k}.obj terms ⊗ last.obj bodies,last.obj terms,
      inv (CartesianMonoidalCategory.prodComparison last terms bodies) ≫
        last.map (classOf NamePassingBindingClosedConstructorExpressions.definition)⟩ : ArrowValue Target) =
      ⟨NamePassingBindingPrimitiveOperations.terms targetOperations ⊗
          NamePassingBindingPrimitiveOperations.bodies targetOperations,
        NamePassingBindingPrimitiveOperations.terms targetOperations,
        NamePassingBindingPrimitiveOperations.definition targetOperations⟩ :=
  ClosedFunctorNativeReadout.canonical_source_read _ _
    (functor_product_object targetOperations.assignment targetOperations.realization terms bodies)
    (functor_productComparison targetOperations.assignment targetOperations.realization terms bodies) _
    (NamePassingBindingClosedConstructorReadout.complete_readout targetOperations .definition)

theorem complete_definition : definitionComparison.{k}.inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.definition sourceOperations) ≫ termComparison.hom =
      NamePassingGeneratedOperationalCategory.ordinary.definition := by
  have actual := ClosedFunctorNativeReadout.complete_product_arrow sourceNative compiler last square
    (classOf NamePassingBindingClosedConstructorExpressions.definition)
    (source_sort .tm) sourceBodySame (source_sort .tm)
    (target_sort .tm) targetBodySame (target_sort .tm)
    _ _ source_definition_read target_definition_read
  exact actual.trans definition_readout

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalDomains
