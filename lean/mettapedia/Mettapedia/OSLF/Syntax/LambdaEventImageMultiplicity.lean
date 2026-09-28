import Mettapedia.OSLF.Syntax.EventGraphImageMorphism
import Mettapedia.OSLF.Syntax.LambdaDerivationGraph

/-!
# Endpoint coverage without event surjectivity

Duplicating the authored lambda derivation graph adds a second copy of every
firing while leaving its reduction predicate unchanged. The inclusion of the
first copy therefore has exact endpoint image, but it is not surjective on
events. This separates the exact endpoint-cover criterion from the stronger
condition that every target event have its own source preimage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaEventImageMultiplicity

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph
open Mettapedia.OSLF.Binding.EventGraphImageMorphism
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaDerivationGraph

/-- The authored lambda graph, viewed in the variable-vertex graph category. -/
def sourceGraph : EventGraph Base := variableGraph graph

/-- Two tagged copies of every authored firing over the same programs. -/
def doubledGraph : EventGraph Base :=
  variableGraph (graphSum graph graph)

/-- Include the first occurrence of each authored firing. -/
def firstCopy : EventGraphHom sourceGraph doubledGraph where
  vertexMap := 𝟙 Programs
  edgeMap := inlEdge graph.edge graph.edge
  source_comm := by ext X event; rfl
  target_comm := by ext X event; rfl

/-- The first copy already covers every reduction endpoint in the doubled
graph. The second copy contributes new history, not new endpoint pairs. -/
theorem firstCopy_image_eq :
    (reductionImage sourceGraph).image
        (pairMap firstCopy.vertexMap) =
      reductionImage doubledGraph := by
  apply (reductionImage_map_eq_iff_endpointCover firstCopy).2
  intro X event
  cases event with
  | inl oldEvent => exact ⟨oldEvent, rfl⟩
  | inr oldEvent => exact ⟨oldEvent, rfl⟩

/-- The right-hand authored Ω firing has no preimage in the first copy. -/
theorem firstCopy_not_event_surjective :
    ¬ Function.Surjective
      (firstCopy.edgeMap.app
        (Opposite.op ⟨([] : Ctx sig)⟩)) := by
  intro surjective
  obtain ⟨event, impossible⟩ :=
    surjective (Sum.inr leftOmegaEvent)
  cases impossible

/-- Endpoint-image equality does not imply surjectivity on proof-relevant
firings, even for the actual authored lambda graph. -/
theorem image_equality_without_event_surjectivity :
    (reductionImage sourceGraph).image
        (pairMap firstCopy.vertexMap) =
      reductionImage doubledGraph ∧
    ¬ Function.Surjective
      (firstCopy.edgeMap.app
        (Opposite.op ⟨([] : Ctx sig)⟩)) :=
  ⟨firstCopy_image_eq, firstCopy_not_event_surjective⟩

end Mettapedia.OSLF.Binding.LambdaEventImageMultiplicity
