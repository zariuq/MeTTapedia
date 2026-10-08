import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorComparison
import Mathlib.CategoryTheory.Whiskering

/-!
# The coherent whole-source constructor comparison

The actual normalization comparison and complete constructor restriction
assemble a natural isomorphism on the entire generated constructor theory.
Its squares apply to every arrow, not just the five primitive expressions.
The independent ordinary source readings then give the comparison directly
on the source guest's chosen binding constructors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorNaturality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingGeneratedConstructorComparison

universe k

def comparison : sourceNative.{k} ⋙ compiler ≅ targetOperations.interpretation.functor :=
  (Functor.isoWhiskerRight (FunctorNormalization.comparison constructors) compiler).symm ≪≫
    eqToIso complete_constructor_restriction

theorem whole_arrow_square {before after : Object
    (ClosedPresentation.signature.{k} NamePassing.Presentation.signature)} (arrow : before ⟶ after) :
    compiler.map (sourceNative.map arrow) ≫ comparison.hom.app after =
      comparison.hom.app before ≫ targetOperations.interpretation.functor.map arrow :=
  comparison.hom.naturality arrow

theorem whole_inverse_square {before after : Object
    (ClosedPresentation.signature.{k} NamePassing.Presentation.signature)} (arrow : before ⟶ after) :
    targetOperations.interpretation.functor.map arrow ≫ comparison.inv.app after =
      comparison.inv.app before ≫ compiler.map (sourceNative.map arrow) :=
  comparison.inv.naturality arrow

theorem actual_source_binding : sourceOperations.{k} =
    NamePassingGeneratedOperationalPresentation.binding := rfl

def nativeDomainComparison (operator : NamePassing.Presentation.Operator .tm) :
    compiler.obj (NamePassingBindingClosedConstructorReadout.domain sourceOperations.{k} operator) ≅
      (targetValue operator).source :=
  (compiler.mapIso (eqToIso (congrArg ArrowValue.source (whole_source_constructor operator)))).symm ≪≫
    domainComparison operator

def nativeProgramComparison (operator : NamePassing.Presentation.Operator .tm) :
    compiler.obj (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k}) ≅
      (targetValue operator).target :=
  (compiler.mapIso (eqToIso (congrArg ArrowValue.target (whole_source_constructor operator)))).symm ≪≫
    programComparison operator

private theorem value_transport {C D : Type k} [Category.{k} C] [Category.{k} D]
    (mapping : C ⥤ D) (first second : ArrowValue C) (same : first = second)
    {before after : D} (input : mapping.obj first.source ≅ before)
    (output : mapping.obj first.target ≅ after) (target : before ⟶ after)
    (read : input.inv ≫ mapping.map first.arrow ≫ output.hom = target) :
    ((mapping.mapIso (eqToIso (congrArg ArrowValue.source same))).symm ≪≫ input).inv ≫
      mapping.map second.arrow ≫
        ((mapping.mapIso (eqToIso (congrArg ArrowValue.target same))).symm ≪≫ output).hom = target := by
  cases same
  simpa only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans] using read

theorem complete_native_constructor (operator : NamePassing.Presentation.Operator .tm) :
    (nativeDomainComparison.{k} operator).inv ≫
      compiler.map (NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator) ≫
        (nativeProgramComparison operator).hom = (targetValue operator).arrow :=
  value_transport compiler _ _ (whole_source_constructor operator)
    (domainComparison operator) (programComparison operator) _ (complete_compiled_constructor operator)

theorem complete_reference : (nativeDomainComparison.{k} .reference).inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.reference sourceOperations) ≫
      (nativeProgramComparison .reference).hom = NamePassingGeneratedOperationalCategory.ordinary.reference :=
  (complete_native_constructor .reference).trans reference_readout

theorem complete_abstraction : (nativeDomainComparison.{k} .abstraction).inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.abstraction sourceOperations) ≫
      (nativeProgramComparison .abstraction).hom = NamePassingGeneratedOperationalCategory.ordinary.abstraction :=
  (complete_native_constructor .abstraction).trans abstraction_readout

theorem complete_application : (nativeDomainComparison.{k} .application).inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.application sourceOperations) ≫
      (nativeProgramComparison .application).hom = NamePassingGeneratedOperationalCategory.ordinary.application :=
  (complete_native_constructor .application).trans application_readout

theorem complete_definition : (nativeDomainComparison.{k} .definition).inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.definition sourceOperations) ≫
      (nativeProgramComparison .definition).hom = NamePassingGeneratedOperationalCategory.ordinary.definition :=
  (complete_native_constructor .definition).trans definition_readout

theorem complete_carrier : (nativeDomainComparison.{k} .carrier).inv ≫
    compiler.map (NamePassingBindingPrimitiveOperations.carrier sourceOperations) ≫
      (nativeProgramComparison .carrier).hom = NamePassingGeneratedOperationalCategory.ordinary.carrier :=
  (complete_native_constructor .carrier).trans carrier_readout

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorNaturality
