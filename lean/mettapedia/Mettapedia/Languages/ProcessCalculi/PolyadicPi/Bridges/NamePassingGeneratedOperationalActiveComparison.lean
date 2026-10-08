import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorLeafComparisons
import Mettapedia.CategoryTheory.ClosedFunctorNativeSquares

/-!
# Whole active-premise endpoint squares

The independently authored source active positions map through the actual
category compiler. Product and complete function comparisons preserve each
evidence argument and passive source separately. Their endpoints agree with
the actual parallel/restriction evidence constructions in the target guest.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalActiveComparison

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingGeneratedConstructorComparison NamePassingGeneratedConstructorCanonical
open NamePassingGeneratedConstructorCanonicalDomains NamePassingGeneratedConstructorLeafComparisons

universe k

abbrev sourceNames := NamePassingGeneratedOperationalPresentation.names.{k}
abbrev sourceTerms := NamePassingGeneratedOperationalPresentation.programs.{k}
abbrev sourceEdges := NamePassingGeneratedOperationalPresentation.edges.{k}
abbrev targetNames := NamePassingGeneratedOperationalCategory.ordinary.{k}.names
abbrev targetTerms := NamePassingGeneratedOperationalCategory.ordinary.{k}.termObject
abbrev targetEdges := NamePassingGeneratedOperational.continuations.{k}

def sourcePort (side : Bool) : sourceEdges.{k} ⟶ sourceTerms :=
  if side then NamePassingGeneratedOperationalPresentation.edgeTarget else
    NamePassingGeneratedOperationalPresentation.edgeSource

theorem port_post (side : Bool) : compiler.map (sourcePort.{k} side) ≫ termComparison.hom =
    edgeComparison.hom ≫ NamePassingGeneratedOperational.functionEndpoint side := by
  apply (cancel_epi edgeComparison.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact whole_port_square side

def boundEdgeComparison : compiler.obj (sourceNames.{k} ⟶[Source] sourceEdges) ≅
    (targetNames ⟶[Target] targetEdges) :=
  ClosedFunctorNativeSquares.function compiler nameComparison edgeComparison

theorem bound_port_post (side : Bool) :
    compiler.map ((ihom sourceNames).map (sourcePort.{k} side)) ≫ abstractionComparison.hom =
      boundEdgeComparison.hom ≫ (ihom targetNames).map (NamePassingGeneratedOperational.functionEndpoint side) :=
  ClosedFunctorNativeSquares.function_postcomposition compiler nameComparison edgeComparison termComparison
    (sourcePort side) (NamePassingGeneratedOperational.functionEndpoint side) (port_post side)

def applicationPremiseComparison : compiler.obj (sourceEdges.{k} ⊗ sourceNames) ≅
    targetEdges ⊗ targetNames :=
  ClosedFunctorNativeSquares.product compiler edgeComparison nameComparison

private theorem application_post : compiler.map NamePassingGeneratedOperationalPresentation.application.{k} ≫
    termComparison.hom = applicationComparison.hom ≫ NamePassingGeneratedOperationalCategory.ordinary.application := by
  apply (cancel_epi applicationComparison.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact NamePassingGeneratedConstructorCanonical.complete_application

theorem application_endpoint_post (side : Bool) :
    compiler.map (NamePassingGeneratedOperationalPresentation.applicationEndpoint.{k} side) ≫ termComparison.hom =
      applicationPremiseComparison.hom ≫ NamePassingGeneratedOperational.applicationEndpoint side := by
  have inputs : compiler.map (lift (fst sourceEdges sourceNames ≫ sourcePort side) (snd sourceEdges sourceNames)) ≫
      applicationComparison.hom = applicationPremiseComparison.hom ≫
        lift (fst targetEdges targetNames ≫ NamePassingGeneratedOperational.functionEndpoint side)
          (snd targetEdges targetNames) := by
    have actual := ClosedFunctorNativeSquares.product_arrow_square compiler
      edgeComparison nameComparison termComparison nameComparison
      (sourcePort side) (𝟙 sourceNames) (NamePassingGeneratedOperational.functionEndpoint side) (𝟙 targetNames)
      (port_post side) (by erw [compiler.map_id, Category.id_comp, Category.comp_id])
    erw [Category.comp_id, Category.comp_id] at actual
    exact actual
  change compiler.map (lift (fst sourceEdges sourceNames ≫ sourcePort side) (snd sourceEdges sourceNames) ≫
    NamePassingGeneratedOperationalPresentation.application) ≫ termComparison.hom = _
  rw [compiler.map_comp, Category.assoc, application_post, ← Category.assoc, inputs]
  exact Category.assoc _ _ _

theorem application_endpoint (side : Bool) : applicationPremiseComparison.{k}.inv ≫
    compiler.map (NamePassingGeneratedOperationalPresentation.applicationEndpoint side) ≫ termComparison.hom =
      NamePassingGeneratedOperational.applicationEndpoint side := by
  rw [application_endpoint_post, Iso.inv_hom_id_assoc]

def definitionPremiseComparison : compiler.obj (sourceTerms.{k} ⊗ (sourceNames ⟶[Source] sourceEdges)) ≅
    targetTerms ⊗ (targetNames ⟶[Target] targetEdges) :=
  ClosedFunctorNativeSquares.product compiler termComparison boundEdgeComparison

private theorem definition_post : compiler.map NamePassingGeneratedOperationalPresentation.definition.{k} ≫
    termComparison.hom = definitionComparison.hom ≫ NamePassingGeneratedOperationalCategory.ordinary.definition := by
  apply (cancel_epi definitionComparison.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact NamePassingGeneratedConstructorCanonicalDomains.complete_definition

theorem definition_endpoint_post (side : Bool) :
    compiler.map (NamePassingGeneratedOperationalPresentation.definitionEndpoint.{k} side) ≫ termComparison.hom =
      definitionPremiseComparison.hom ≫ NamePassingGeneratedOperational.definitionEndpoint side := by
  have inputs : compiler.map (lift (fst sourceTerms (sourceNames ⟶[Source] sourceEdges))
      (snd sourceTerms (sourceNames ⟶[Source] sourceEdges) ≫ (ihom sourceNames).map (sourcePort side))) ≫
        definitionComparison.hom = definitionPremiseComparison.hom ≫
          lift (fst targetTerms (targetNames ⟶[Target] targetEdges))
            (snd targetTerms (targetNames ⟶[Target] targetEdges) ≫
              (ihom targetNames).map (NamePassingGeneratedOperational.functionEndpoint side)) := by
    have actual := ClosedFunctorNativeSquares.product_arrow_square compiler
      termComparison boundEdgeComparison termComparison abstractionComparison
      (𝟙 sourceTerms) ((ihom sourceNames).map (sourcePort side))
      (𝟙 targetTerms) ((ihom targetNames).map (NamePassingGeneratedOperational.functionEndpoint side))
      (by erw [compiler.map_id, Category.id_comp, Category.comp_id]) (bound_port_post side)
    rw [NamePassingGeneratedConstructorCanonicalDomains.definitionComparison_canonical]
    erw [Category.comp_id, Category.comp_id] at actual
    exact actual
  change compiler.map (lift (fst sourceTerms (sourceNames ⟶[Source] sourceEdges))
      (snd sourceTerms (sourceNames ⟶[Source] sourceEdges) ≫ (ihom sourceNames).map (sourcePort side)) ≫
        NamePassingGeneratedOperationalPresentation.definition) ≫ termComparison.hom = _
  rw [compiler.map_comp, Category.assoc, definition_post, ← Category.assoc, inputs]
  exact Category.assoc _ _ _

theorem definition_endpoint (side : Bool) : definitionPremiseComparison.{k}.inv ≫
    compiler.map (NamePassingGeneratedOperationalPresentation.definitionEndpoint side) ≫ termComparison.hom =
      NamePassingGeneratedOperational.definitionEndpoint side := by
  rw [definition_endpoint_post, Iso.inv_hom_id_assoc]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalActiveComparison
