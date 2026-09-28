import Mettapedia.OSLF.Syntax.EquationExtensionEventGraph
import Mettapedia.OSLF.Syntax.RhoEquationEventComparison
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport

/-!
# Endpoint images along operational graph morphisms

A map of program states and firing events induces a directional comparison
between endpoint images. It need not reflect target reductions: target events
may be absent from the source. Pointwise coverage of target events upgrades
the comparison to equality. Equation extension is an important instance:
it identifies some state classes while retaining every firing occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphImageMorphism

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph
open Mettapedia.OSLF.Binding.BindingEquationExtension
open Mettapedia.OSLF.Binding.RuleListEventEmbedding

variable {base : Type*} [Category base]

/-- Read a variable-vertex event graph in the fixed-vertex graph interface. -/
def asFixed (G : EventGraph base) : Graph G.vertex where
  edge := G.edge
  source := G.source
  target := G.target

/-- Read a fixed-vertex graph in the category of graphs whose state object
may vary. This is the comparison used by authored operational morphisms. -/
def variableGraph {vertex : base ⥤ Type} (G : Graph vertex) :
    EventGraph base where
  vertex := vertex
  edge := G.edge
  source := G.source
  target := G.target

theorem asFixed_variableGraph {vertex : base ⥤ Type}
    (G : Graph vertex) :
    asFixed (variableGraph G) = G := rfl

/-- The subfunctor of endpoint pairs for which at least one firing exists. -/
def reductionImage (G : EventGraph base) :
    Subfunctor (FunctorToTypes.prod G.vertex G.vertex) :=
  endpointImage (asFixed G)

/-- The endpoint-pair arrow commutes with both components of a morphism of
retained graphs, without assuming either component is injective. -/
theorem endpointMap_morphism {G H : EventGraph base}
    (f : EventGraphHom G H) :
    endpointMap (asFixed G) ≫ pairMap f.vertexMap =
      f.edgeMap ≫ endpointMap (asFixed H) := by
  ext X event
  · change f.vertexMap.app X (G.source.app X event) =
      H.source.app X (f.edgeMap.app X event)
    exact (congrArg
      (fun arrow : G.edge ⟶ H.vertex => arrow.app X event)
      f.source_comm).symm
  · change f.vertexMap.app X (G.target.app X event) =
      H.target.app X (f.edgeMap.app X event)
    exact (congrArg
      (fun arrow : G.edge ⟶ H.vertex => arrow.app X event)
      f.target_comm).symm

/-- Every source firing maps to a target firing at the translated pair of
endpoints. This is the lax direction available for every graph morphism. -/
theorem reductionImage_map_le {G H : EventGraph base}
    (f : EventGraphHom G H) :
    (reductionImage G).image (pairMap f.vertexMap) ≤
      reductionImage H := by
  intro X pair h
  rcases h with ⟨oldPair, ⟨event, rfl⟩, rfl⟩
  refine ⟨f.edgeMap.app X event, ?_⟩
  exact (congrArg
    (fun arrow : G.edge ⟶
        FunctorToTypes.prod H.vertex H.vertex =>
      arrow.app X event)
    (endpointMap_morphism f)).symm

/-- Endpoint coverage asks only that every target firing endpoint pair have
some source firing over a pair translating to it. It does not require a
preimage of the target firing itself. -/
def EndpointCover {G H : EventGraph base}
    (f : EventGraphHom G H) : Prop :=
  ∀ X (event : H.edge.obj X),
    ∃ oldEvent : G.edge.obj X,
      (pairMap f.vertexMap).app X
        ((endpointMap (asFixed G)).app X oldEvent) =
      (endpointMap (asFixed H)).app X event

/-- Exact equality of endpoint images is equivalent to endpoint coverage.
This is weaker than surjectivity on events: different events may have the
same endpoints and the image predicate forgets their identity. -/
theorem reductionImage_map_eq_iff_endpointCover
    {G H : EventGraph base} (f : EventGraphHom G H) :
    (reductionImage G).image (pairMap f.vertexMap) =
        reductionImage H ↔ EndpointCover f := by
  constructor
  · intro equality X event
    have targetMem :
        (endpointMap (asFixed H)).app X event ∈
          (reductionImage H).obj X := ⟨event, rfl⟩
    rw [← equality] at targetMem
    rcases targetMem with ⟨oldPair, ⟨oldEvent, oldEq⟩, pairEq⟩
    refine ⟨oldEvent, ?_⟩
    rw [oldEq]
    exact pairEq
  · intro coverage
    apply le_antisymm (reductionImage_map_le f)
    intro X pair targetMem
    rcases targetMem with ⟨event, rfl⟩
    obtain ⟨oldEvent, endpointEq⟩ := coverage X event
    exact ⟨(endpointMap (asFixed G)).app X oldEvent,
      ⟨oldEvent, rfl⟩, endpointEq⟩

/-- If every target firing has a source preimage at each context, the
translated source image is exactly the target image. This is an event-level
coverage condition; surjectivity of the program map is unnecessary. -/
theorem reductionImage_map_eq_of_event_surjective
    {G H : EventGraph base} (f : EventGraphHom G H)
    (covers : ∀ X, Function.Surjective (f.edgeMap.app X)) :
    (reductionImage G).image (pairMap f.vertexMap) =
      reductionImage H := by
  apply (reductionImage_map_eq_iff_endpointCover f).2
  intro X event
  obtain ⟨oldEvent, imageEq⟩ := covers X event
  refine ⟨oldEvent, ?_⟩
  have natural := congrArg
    (fun arrow : G.edge ⟶
        FunctorToTypes.prod H.vertex H.vertex =>
      arrow.app X oldEvent)
    (endpointMap_morphism f)
  change (pairMap f.vertexMap).app X
      ((endpointMap (asFixed G)).app X oldEvent) =
    (endpointMap (asFixed H)).app X
      (f.edgeMap.app X oldEvent) at natural
  rw [imageEq] at natural
  exact natural

variable {S : Signature} {M : List (MetaArity S)}

/-- Adding authored equations quotients program states but leaves the
operational image exactly the direct image of the old endpoint relation. -/
theorem equationExtension_reductionImage
    {E F : List (EqAxiom S M)} (inclusion : AxiomInclusion E F)
    (rules : RuleList S M) (sort : S.Srt) :
    (reductionImage (presentedGraph E rules sort)).image
        (pairMap (compareStates inclusion sort)) =
      reductionImage (presentedGraph F rules sort) := by
  exact reductionImage_map_eq_of_event_surjective
    (equationGraphMap inclusion rules sort)
    (by intro X event; exact ⟨event, rfl⟩)

end Mettapedia.OSLF.Binding.EventGraphImageMorphism

namespace Mettapedia.OSLF.Binding.EventGraphImageMorphism.RhoExample

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEquationModel
open Mettapedia.OSLF.Binding.RhoEquationEventComparison
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph

/-- The authored COMM/Drop presentation satisfies the general image law
when its ACU states are quotiented by the source reflection equation. -/
theorem acu_source_image (sort : Srt) :
    (reductionImage
        (presentedGraph rhoE
          rhoSourceWithDrop.toUnpositioned.rules sort)).image
      (pairMap (compareStates acu_in_source sort)) =
    reductionImage
      (presentedGraph rhoSourceE
        rhoSourceWithDrop.toUnpositioned.rules sort) :=
  equationExtension_reductionImage acu_in_source _ sort

/-- Exact transport of rho's endpoint image does not require injective
state translation: the source reflection equation identifies name states. -/
theorem exact_image_with_noninjective_states :
    (reductionImage
        (presentedGraph rhoE
          rhoSourceWithDrop.toUnpositioned.rules Srt.nm)).image
      (pairMap (compareStates acu_in_source Srt.nm)) =
      reductionImage
        (presentedGraph rhoSourceE
          rhoSourceWithDrop.toUnpositioned.rules Srt.nm) ∧
    ¬ Function.Injective
      ((acuToSourceGraph Srt.nm).vertexMap.app
        (Opposite.op ⟨[Srt.nm]⟩)) :=
  ⟨acu_source_image Srt.nm, name_state_map_not_injective⟩

end Mettapedia.OSLF.Binding.EventGraphImageMorphism.RhoExample
