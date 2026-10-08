import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalActiveComparison

/-!
# Whole carrier premise and endpoint comparison

The reference and stored term stay passive while the supplied active evidence
is transformed. The inner pair and outer product squares are independently
pasted through their canonical comparisons before applying the complete
carrier constructor square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCarrierComparison

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open NamePassingGeneratedConstructorComparison NamePassingGeneratedConstructorCanonical
open NamePassingGeneratedConstructorCanonicalRemaining NamePassingGeneratedConstructorLeafComparisons
open NamePassingGeneratedOperationalActiveComparison

universe k

def innerPremiseComparison : compiler.obj (sourceTerms.{k} ⊗ sourceEdges) ≅ targetTerms ⊗ targetEdges :=
  ClosedFunctorNativeSquares.product compiler termComparison edgeComparison

def premiseComparison : compiler.obj (sourceNames.{k} ⊗ (sourceTerms ⊗ sourceEdges)) ≅
    targetNames ⊗ (targetTerms ⊗ targetEdges) :=
  ClosedFunctorNativeSquares.product compiler nameComparison innerPremiseComparison

def sourceInner (side : Bool) : sourceTerms.{k} ⊗ sourceEdges ⟶ sourceTerms ⊗ sourceTerms :=
  lift (fst sourceTerms sourceEdges) (snd sourceTerms sourceEdges ≫ sourcePort side)

def targetInner (side : Bool) : targetTerms.{k} ⊗ targetEdges ⟶ targetTerms ⊗ targetTerms :=
  lift (fst targetTerms targetEdges)
    (snd targetTerms targetEdges ≫ NamePassingGeneratedOperational.functionEndpoint side)

theorem inner_endpoint_post (side : Bool) : compiler.map (sourceInner.{k} side) ≫ pairComparison.hom =
    innerPremiseComparison.hom ≫ targetInner side := by
  have actual := ClosedFunctorNativeSquares.product_arrow_square compiler
    termComparison edgeComparison termComparison termComparison
    (𝟙 sourceTerms) (sourcePort side) (𝟙 targetTerms) (NamePassingGeneratedOperational.functionEndpoint side)
    (by erw [compiler.map_id, Category.id_comp, Category.comp_id]) (port_post side)
  erw [Category.comp_id, Category.comp_id] at actual
  exact actual

private theorem carrier_post : compiler.map NamePassingGeneratedOperationalPresentation.carrier.{k} ≫
    termComparison.hom = carrierComparison.hom ≫ NamePassingGeneratedOperationalCategory.ordinary.carrier := by
  apply (cancel_epi carrierComparison.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact NamePassingGeneratedConstructorCanonicalRemaining.complete_carrier

theorem endpoint_post (side : Bool) :
    compiler.map (NamePassingGeneratedOperationalPresentation.carrierEndpoint.{k} side) ≫ termComparison.hom =
      premiseComparison.hom ≫ NamePassingGeneratedOperational.carrierEndpoint side := by
  have inputs : compiler.map
      (lift (fst sourceNames (sourceTerms ⊗ sourceEdges))
        (lift (snd sourceNames (sourceTerms ⊗ sourceEdges) ≫ fst sourceTerms sourceEdges)
          (snd sourceNames (sourceTerms ⊗ sourceEdges) ≫ snd sourceTerms sourceEdges ≫ sourcePort side))) ≫
        carrierComparison.hom = premiseComparison.hom ≫
          lift (fst targetNames (targetTerms ⊗ targetEdges))
            (lift (snd targetNames (targetTerms ⊗ targetEdges) ≫ fst targetTerms targetEdges)
              (snd targetNames (targetTerms ⊗ targetEdges) ≫ snd targetTerms targetEdges ≫
                NamePassingGeneratedOperational.functionEndpoint side)) := by
    have actual := ClosedFunctorNativeSquares.product_arrow_square compiler
      nameComparison innerPremiseComparison nameComparison pairComparison
      (𝟙 sourceNames) (sourceInner side) (𝟙 targetNames) (targetInner side)
      (by erw [compiler.map_id, Category.id_comp, Category.comp_id]) (inner_endpoint_post side)
    rw [NamePassingGeneratedConstructorCanonicalRemaining.carrierComparison_canonical]
    erw [Category.comp_id, Category.comp_id] at actual
    simp only [sourceInner, targetInner, comp_lift] at actual ⊢
    exact actual
  change compiler.map
    (lift (fst sourceNames (sourceTerms ⊗ sourceEdges))
      (lift (snd sourceNames (sourceTerms ⊗ sourceEdges) ≫ fst sourceTerms sourceEdges)
        (snd sourceNames (sourceTerms ⊗ sourceEdges) ≫ snd sourceTerms sourceEdges ≫ sourcePort side)) ≫
          NamePassingGeneratedOperationalPresentation.carrier) ≫ termComparison.hom = _
  rw [compiler.map_comp, Category.assoc, carrier_post, ← Category.assoc, inputs]
  exact Category.assoc _ _ _

theorem endpoint (side : Bool) : premiseComparison.{k}.inv ≫
    compiler.map (NamePassingGeneratedOperationalPresentation.carrierEndpoint side) ≫ termComparison.hom =
      NamePassingGeneratedOperational.carrierEndpoint side := by
  rw [endpoint_post, Iso.inv_hom_id_assoc]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCarrierComparison
