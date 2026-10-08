import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCarrierComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalRootReadout
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRuleInterpretation

/-!
# Interpretation of the independently authored five operational rules

Actual unary and binary communication evidence interprets beta and fetch.
Actual parallel and restriction evidence interprets the three active source
positions. The complete source endpoint comparisons prove rule admission;
the generated rule guest then gives a finite-limit and closed compiler with
the original category interpretation recovered on restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingGeneratedConstructorComparison NamePassingGeneratedConstructorCanonical
open NamePassingGeneratedConstructorLeafComparisons NamePassingGeneratedOperationalActiveComparison
open NamePassingGeneratedOperationalReadout

universe k

abbrev meanings := NamePassingGeneratedOperationalCategory.nativeMeanings.{k}
abbrev realized := NamePassingGeneratedOperationalCategory.native_all_seven_diagrams.{k}

theorem rootDomainSame (fetch : Bool) : compiler.obj
    (NamePassingGeneratedOperationalPresentation.rootDeclaration.{k} fetch).domain =
      NamePassingGeneratedOperationalRootReadout.domain fetch :=
  congrArg ArrowValue.source (NamePassingGeneratedOperationalRootReadout.whole_before_readout fetch)

def rootComparison (fetch : Bool) : compiler.obj
    (NamePassingGeneratedOperationalPresentation.rootDeclaration.{k} fetch).domain ≅
      NamePassingGeneratedOperationalRootReadout.domain fetch := eqToIso (rootDomainSame fetch)

theorem root_before_post (fetch : Bool) : compiler.map
    (classOf (NamePassingGeneratedOperationalPresentation.rootDeclaration.{k} fetch).before) ≫ termComparison.hom =
      (rootComparison fetch).hom ≫ NamePassingGeneratedOperationalRootReadout.before fetch := by
  have whole := (conj_eqToHom_iff_heq _ _ (rootDomainSame fetch) complete_program_object).mpr
    (ArrowValue.arrows_heq (NamePassingGeneratedOperationalRootReadout.whole_before_readout fetch))
  rw [termComparison_eq, whole]
  simp only [rootComparison, eqToIso, Category.assoc, eqToHom_refl]
  erw [Category.comp_id, Category.comp_id]

theorem root_after_post (fetch : Bool) : compiler.map
    (classOf (NamePassingGeneratedOperationalPresentation.rootDeclaration.{k} fetch).after) ≫ termComparison.hom =
      (rootComparison fetch).hom ≫ NamePassingGeneratedOperationalRootReadout.after fetch := by
  have whole := (conj_eqToHom_iff_heq _ _ (rootDomainSame fetch) complete_program_object).mpr
    (ArrowValue.arrows_heq (NamePassingGeneratedOperationalRootReadout.whole_after_readout fetch))
  rw [termComparison_eq, whole]
  simp only [rootComparison, eqToIso, Category.assoc, eqToHom_refl]
  erw [Category.comp_id, Category.comp_id]

def firing (origin : ULift.{k} NamePassingGeneratedOperationalPresentation.Origin) :
    RelativeClosedInternalCategory.RuleInterpretation.premise
      NamePassingGeneratedOperationalPresentation.vertex
      NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
      meanings realized origin ⟶
    RelativeClosedInternalCategory.RuleInterpretation.edges
      NamePassingGeneratedOperationalPresentation.vertex
      NamePassingGeneratedOperationalPresentation.categoryMap meanings realized :=
  match origin with
  | ⟨.beta⟩ => (rootComparison false).hom ≫ NamePassingGeneratedOperationalRootReadout.firing false ≫ edgeComparison.inv
  | ⟨.fetch⟩ => (rootComparison true).hom ≫ NamePassingGeneratedOperationalRootReadout.firing true ≫ edgeComparison.inv
  | ⟨.application⟩ => applicationPremiseComparison.hom ≫ NamePassingGeneratedOperational.application ≫ edgeComparison.inv
  | ⟨.definition⟩ => definitionPremiseComparison.hom ≫ NamePassingGeneratedOperational.definition ≫ edgeComparison.inv
  | ⟨.carrier⟩ => NamePassingGeneratedOperationalCarrierComparison.premiseComparison.hom ≫
      NamePassingGeneratedOperational.carrier ≫ edgeComparison.inv

private theorem transported_firing {A : Source.{k}} {B : Target.{k}} (input : compiler.obj A ≅ B)
    (operation : B ⟶ targetEdges) (sourceReading : A ⟶ sourceTerms)
    (targetReading : B ⟶ targetTerms) (side : Bool)
    (targetEndpoint : operation ≫ NamePassingGeneratedOperational.functionEndpoint side = targetReading)
    (sourceEndpoint : compiler.map sourceReading ≫ termComparison.hom = input.hom ≫ targetReading) :
    (input.hom ≫ operation ≫ edgeComparison.inv) ≫ compiler.map (sourcePort side) = compiler.map sourceReading := by
  apply (cancel_mono termComparison.hom).mp
  simp only [Category.assoc]
  erw [whole_port_square side]
  rw [targetEndpoint, sourceEndpoint]

theorem firing_source (origin : ULift.{k} NamePassingGeneratedOperationalPresentation.Origin) : firing origin ≫
    compiler.map NamePassingGeneratedOperationalPresentation.edgeSource =
      compiler.map (classOf (NamePassingGeneratedOperationalPresentation.declaration origin).before) := by
  cases origin with
  | up origin =>
      cases origin with
      | beta =>
          exact transported_firing (rootComparison false) _ _ _ false
            (NamePassingGeneratedOperationalRootReadout.firing_before false) (root_before_post false)
      | fetch =>
          exact transported_firing (rootComparison true) _ _ _ false
            (NamePassingGeneratedOperationalRootReadout.firing_before true) (root_before_post true)
      | application =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (applicationPremiseComparison.hom ≫ NamePassingGeneratedOperational.application ≫
            edgeComparison.inv) ≫ compiler.map (sourcePort false) = _
          exact transported_firing applicationPremiseComparison NamePassingGeneratedOperational.application
              (NamePassingGeneratedOperationalPresentation.applicationEndpoint false)
              (NamePassingGeneratedOperational.applicationEndpoint false) false
              (NamePassingGeneratedOperational.application_endpoint false) (application_endpoint_post false)
      | definition =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (definitionPremiseComparison.hom ≫ NamePassingGeneratedOperational.definition ≫
            edgeComparison.inv) ≫ compiler.map (sourcePort false) = _
          exact transported_firing definitionPremiseComparison NamePassingGeneratedOperational.definition
              (NamePassingGeneratedOperationalPresentation.definitionEndpoint false)
              (NamePassingGeneratedOperational.definitionEndpoint false) false
              (NamePassingGeneratedOperational.definition_endpoint false) (definition_endpoint_post false)
      | carrier =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (NamePassingGeneratedOperationalCarrierComparison.premiseComparison.hom ≫
            NamePassingGeneratedOperational.carrier ≫ edgeComparison.inv) ≫ compiler.map (sourcePort false) = _
          exact transported_firing NamePassingGeneratedOperationalCarrierComparison.premiseComparison
              NamePassingGeneratedOperational.carrier (NamePassingGeneratedOperationalPresentation.carrierEndpoint false)
              (NamePassingGeneratedOperational.carrierEndpoint false) false
              (NamePassingGeneratedOperational.carrier_endpoint false)
              (NamePassingGeneratedOperationalCarrierComparison.endpoint_post false)

theorem firing_target (origin : ULift.{k} NamePassingGeneratedOperationalPresentation.Origin) : firing origin ≫
    compiler.map NamePassingGeneratedOperationalPresentation.edgeTarget =
      compiler.map (classOf (NamePassingGeneratedOperationalPresentation.declaration origin).after) := by
  cases origin with
  | up origin =>
      cases origin with
      | beta =>
          exact transported_firing (rootComparison false) _ _ _ true
            (NamePassingGeneratedOperationalRootReadout.firing_after false) (root_after_post false)
      | fetch =>
          exact transported_firing (rootComparison true) _ _ _ true
            (NamePassingGeneratedOperationalRootReadout.firing_after true) (root_after_post true)
      | application =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (applicationPremiseComparison.hom ≫ NamePassingGeneratedOperational.application ≫
            edgeComparison.inv) ≫ compiler.map (sourcePort true) = _
          exact transported_firing applicationPremiseComparison NamePassingGeneratedOperational.application
              (NamePassingGeneratedOperationalPresentation.applicationEndpoint true)
              (NamePassingGeneratedOperational.applicationEndpoint true) true
              (NamePassingGeneratedOperational.application_endpoint true) (application_endpoint_post true)
      | definition =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (definitionPremiseComparison.hom ≫ NamePassingGeneratedOperational.definition ≫
            edgeComparison.inv) ≫ compiler.map (sourcePort true) = _
          exact transported_firing definitionPremiseComparison NamePassingGeneratedOperational.definition
              (NamePassingGeneratedOperationalPresentation.definitionEndpoint true)
              (NamePassingGeneratedOperational.definitionEndpoint true) true
              (NamePassingGeneratedOperational.definition_endpoint true) (definition_endpoint_post true)
      | carrier =>
          simp only [NamePassingGeneratedOperationalPresentation.declaration, classOf_representative]
          change (NamePassingGeneratedOperationalCarrierComparison.premiseComparison.hom ≫
            NamePassingGeneratedOperational.carrier ≫ edgeComparison.inv) ≫ compiler.map (sourcePort true) = _
          exact transported_firing NamePassingGeneratedOperationalCarrierComparison.premiseComparison
              NamePassingGeneratedOperational.carrier (NamePassingGeneratedOperationalPresentation.carrierEndpoint true)
              (NamePassingGeneratedOperational.carrierEndpoint true) true
              (NamePassingGeneratedOperational.carrier_endpoint true)
              (NamePassingGeneratedOperationalCarrierComparison.endpoint_post true)

theorem all_endpoint_laws : RelativeClosedInternalCategory.RuleInterpretation.LocalLaws
    NamePassingGeneratedOperationalPresentation.vertex.{k}
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
    meanings realized firing where
  source := firing_source
  target := firing_target

abbrev assignment := RelativeClosedInternalCategory.RuleInterpretation.assignment
  NamePassingGeneratedOperationalPresentation.vertex.{k}
  NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
  meanings realized firing

theorem realization : Realization NamePassingGeneratedOperationalPresentation.signature.{k} assignment :=
  RelativeClosedInternalCategory.RuleInterpretation.realization
    NamePassingGeneratedOperationalPresentation.vertex
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
    meanings realized firing all_endpoint_laws

def interpretation : Mettapedia.GSLT.Core.LambdaTheoryMap
    NamePassingGeneratedOperationalPresentation.theory.{k} BindingClosedGeneratedOperational.theory where
  functor := Interpretation.functor assignment realization
  preservesFiniteLimits := Interpretation.functor_preservesFiniteLimits assignment realization
  preservesExponentials := Interpretation.functor_closed assignment realization

theorem complete_original_restriction :
    (RelativeClosedInternalCategory.RulePresentation.arrowInclusion
      NamePassingGeneratedOperationalPresentation.vertex.{k}
      NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration).functor ⋙
    (RelativeClosedInternalCategory.RulePresentation.equationInclusion
      NamePassingGeneratedOperationalPresentation.vertex
      NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration).functor ⋙
        interpretation.functor = compiler :=
  RelativeClosedInternalCategory.RuleInterpretation.complete_original_restriction
    NamePassingGeneratedOperationalPresentation.vertex
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
    meanings realized firing all_endpoint_laws

theorem whole_firing_readout (origin : ULift.{k} NamePassingGeneratedOperationalPresentation.Origin) :
    (⟨interpretation.functor.obj (RelativeClosedInternalCategory.RulePresentation.ruleDomain
        NamePassingGeneratedOperationalPresentation.vertex
        NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration origin),
      interpretation.functor.obj (RelativeClosedInternalCategory.RulePresentation.edges
        NamePassingGeneratedOperationalPresentation.vertex
        NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration),
      interpretation.functor.map (classOf (NamePassingGeneratedOperationalPresentation.fire origin))⟩ : ArrowValue Target) =
      RelativeClosedInternalCategory.RuleInterpretation.arrowValue
        NamePassingGeneratedOperationalPresentation.vertex
        NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
        meanings realized firing origin :=
  RelativeClosedInternalCategory.RuleInterpretation.fire_complete_read
    NamePassingGeneratedOperationalPresentation.vertex
    NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration
    meanings realized firing all_endpoint_laws origin

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalInterpretation
