import Mettapedia.OSLF.Syntax.LambdaEventImageMultiplicity
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Reflecting reductions through operational graph maps

An endpoint-preserving map of firing events always preserves the existence of
a step. Exact coverage of target endpoint pairs is stable under composition.
To reflect a target step at a *specified source pair*, the program map must
also distinguish those two source programs. The small counterexample below
shows why endpoint coverage alone cannot supply that reflection.

These are strict operational comparison laws. They provide the graph-level
part of a context-sensitive theory morphism; preserving redex labels and
observer structure requires additional data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.OperationalImageReflection

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.EquationExtensionEventGraph
open Mettapedia.OSLF.Binding.EventGraphImageMorphism
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.RuleListEventEmbedding
open Mettapedia.OSLF.Binding.BindingEquationExtension

variable {base : Type*} [Category base]

/-- Identity graph maps cover every target firing endpoint pair. -/
theorem endpointCover_id (G : EventGraph base) :
    EndpointCover (EventGraphHom.id G) := by
  intro X event
  exact ⟨event, rfl⟩

/-- Endpoint coverage composes along strict graph maps. Thus exact transport
of the reduction image is coherent across consecutive interpretations. -/
theorem endpointCover_comp {G H K : EventGraph base}
    (f : EventGraphHom G H) (g : EventGraphHom H K)
    (hf : EndpointCover f) (hg : EndpointCover g) :
    EndpointCover (EventGraphHom.comp f g) := by
  intro X event
  obtain ⟨middle, hm⟩ := hg X event
  obtain ⟨first, hf'⟩ := hf X middle
  refine ⟨first, ?_⟩
  calc
    (pairMap (EventGraphHom.comp f g).vertexMap).app X
        ((endpointMap (asFixed G)).app X first) =
      (pairMap g.vertexMap).app X
        ((pairMap f.vertexMap).app X
          ((endpointMap (asFixed G)).app X first)) := rfl
    _ = (pairMap g.vertexMap).app X
          ((endpointMap (asFixed H)).app X middle) :=
      congrArg ((pairMap g.vertexMap).app X) hf'
    _ = (endpointMap (asFixed K)).app X event := hm

/-- The same presheaf event graphs, with only maps that preserve the
endpoint-image predicate exactly. This is the strict comparison category
needed when a target interpretation treats reduction as a predicate. -/
structure ExactImageGraph (base : Type*) [Category base] where
  graph : EventGraph base

/-- A graph map that covers every target endpoint pair. It may still forget
which of several firings at that pair occurred. -/
structure ExactImageGraphHom {base : Type*} [Category base]
    (G H : ExactImageGraph base) where
  hom : EventGraphHom G.graph H.graph
  covers : EndpointCover hom

namespace ExactImageGraphHom

@[ext] theorem ext {G H : ExactImageGraph base}
    {f g : ExactImageGraphHom G H} (same : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases same
  rfl

end ExactImageGraphHom

instance exactImageGraphCategory (base : Type*) [Category base] :
    Category (ExactImageGraph base) where
  Hom G H := ExactImageGraphHom G H
  id G := ⟨EventGraphHom.id G.graph, endpointCover_id G.graph⟩
  comp f g := ⟨EventGraphHom.comp f.hom g.hom,
    endpointCover_comp f.hom g.hom f.covers g.covers⟩
  id_comp := by
    intro G H f
    apply ExactImageGraphHom.ext
    apply EventGraphHom.ext <;>
      simp [EventGraphHom.comp, EventGraphHom.id]
  comp_id := by
    intro G H f
    apply ExactImageGraphHom.ext
    apply EventGraphHom.ext <;>
      simp [EventGraphHom.comp, EventGraphHom.id]
  assoc := by
    intro G H K L f g h
    apply ExactImageGraphHom.ext
    apply EventGraphHom.ext <;>
      simp [EventGraphHom.comp, Category.assoc]

/-- Forget exact endpoint coverage but retain the program and firing maps. -/
def exactImageGraphForget (base : Type*) [Category base] :
    ExactImageGraph base ⥤ EventGraph base where
  obj G := G.graph
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

variable {S : Signature} {M : List (MetaArity S)}

/-- An authored equation presentation, retaining its located firing graph,
viewed in the category whose maps preserve reduction images exactly. -/
def presentedExactGraph (E : List (EqAxiom S M))
    (rules : RuleList S M) (sort : S.Srt) :
    ExactImageGraph ((Syntactic.Ctxt S)ᵒᵖ) :=
  ⟨presentedGraph E rules sort⟩

/-- Adding equations is an exact-image map even when it identifies program
states: its firing events are retained individually. -/
def equationExtensionExactMap {E F : List (EqAxiom S M)}
    (inclusion : AxiomInclusion E F)
    (rules : RuleList S M) (sort : S.Srt) :
    presentedExactGraph E rules sort ⟶
      presentedExactGraph F rules sort :=
  ⟨equationGraphMap inclusion rules sort,
    (reductionImage_map_eq_iff_endpointCover _).mp
      (equationExtension_reductionImage inclusion rules sort)⟩

/-- The exact-image comparisons of equation presentations form a functor.
It composes on both state classes and retained firing occurrences. -/
def equationExactImageFunctor (rules : RuleList S M) (sort : S.Srt) :
    EquationCatalogue S M ⥤
      ExactImageGraph ((Syntactic.Ctxt S)ᵒᵖ) where
  obj catalogue := presentedExactGraph catalogue.equations rules sort
  map inclusion := equationExtensionExactMap inclusion.included rules sort
  map_id catalogue := by
    apply ExactImageGraphHom.ext
    exact equationGraphMap_id catalogue.equations rules sort
  map_comp first later := by
    apply ExactImageGraphHom.ext
    exact equationGraphMap_comp first.included later.included rules sort

/-- Forgetting exactness recovers the existing equation-extension graph
interpretation, so the stricter interface does not change its event map. -/
theorem equationExactImageFunctor_forget
    (rules : RuleList S M) (sort : S.Srt) :
    equationExactImageFunctor rules sort ⋙
      exactImageGraphForget ((Syntactic.Ctxt S)ᵒᵖ) =
        equationEventGraphFunctor rules sort := by
  rfl

/-- Endpoint coverage plus an injective program translation reflects a
target reduction at each specified source pair. Coverage alone only says
that *some* source pair maps to the target endpoints. -/
theorem reflects_reduction_of_endpointCover_of_vertex_injective
    {G H : EventGraph base} (f : EventGraphHom G H)
    (covers : EndpointCover f)
    (injective : ∀ X, Function.Injective (f.vertexMap.app X))
    (X : base) (pair : G.vertex.obj X × G.vertex.obj X)
    (step : (pairMap f.vertexMap).app X pair ∈
      (reductionImage H).obj X) :
    pair ∈ (reductionImage G).obj X := by
  obtain ⟨targetEvent, targetEq⟩ := step
  obtain ⟨sourceEvent, coveredEq⟩ := covers X targetEvent
  have mappedEq :
      (pairMap f.vertexMap).app X
          ((endpointMap (asFixed G)).app X sourceEvent) =
        (pairMap f.vertexMap).app X pair :=
    coveredEq.trans targetEq
  have sourceEq :
      ((endpointMap (asFixed G)).app X sourceEvent).1 = pair.1 := by
    apply injective X
    exact congrArg Prod.fst mappedEq
  have targetEq' :
      ((endpointMap (asFixed G)).app X sourceEvent).2 = pair.2 := by
    apply injective X
    exact congrArg Prod.snd mappedEq
  exact ⟨sourceEvent, Prod.ext sourceEq targetEq'⟩

namespace RhoControl

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEquationModel
open Mettapedia.OSLF.Binding.RhoEquationEventComparison

/-- Rho's source-reflection equation extends its ACU presentation through
an exact-image map, without discarding any of its authored firing events. -/
def acuToSourceExact :
    presentedExactGraph rhoE
        rhoSourceWithDrop.toUnpositioned.rules Srt.nm ⟶
      presentedExactGraph rhoSourceE
        rhoSourceWithDrop.toUnpositioned.rules Srt.nm :=
  equationExtensionExactMap acu_in_source _ _

/-- Exact preservation of the reduction image does not require the map on
name states to be injective. Pointwise reflection therefore needs a
separate condition from exactness of the direct image. -/
theorem acuToSourceExact_not_vertex_injective :
    ¬ Function.Injective
      (acuToSourceExact.hom.vertexMap.app
        (Opposite.op ⟨[Srt.nm]⟩)) :=
  name_state_map_not_injective

end RhoControl

namespace LambdaControl

open Mettapedia.OSLF.Binding.LambdaEventImageMultiplicity

/-- For the authored lambda firing graph, inclusion into two tagged copies
both preserves and reflects its reduction predicate on programs. The extra
copy remains a distinct event even though it adds no endpoint pair. -/
theorem firstCopy_reflects (X : Base)
    (pair : sourceGraph.vertex.obj X × sourceGraph.vertex.obj X)
    (step : (pairMap firstCopy.vertexMap).app X pair ∈
      (reductionImage doubledGraph).obj X) :
    pair ∈ (reductionImage sourceGraph).obj X := by
  apply reflects_reduction_of_endpointCover_of_vertex_injective firstCopy
    ((reductionImage_map_eq_iff_endpointCover firstCopy).mp firstCopy_image_eq)
    (by intro stage first last equal; exact equal) X pair step

end LambdaControl

namespace NoninjectiveControl

/-- A one-stage indexing category keeps the counterexample independent of
binding, equations and implementation details. -/
abbrev Index : Type := Discrete PUnit

private abbrev boolStates : Index ⥤ Type :=
  (Functor.const Index).obj Bool

private abbrev unitStates : Index ⥤ Type :=
  (Functor.const Index).obj PUnit

private abbrev oneEvent : Index ⥤ Type :=
  (Functor.const Index).obj PUnit

private def falseEndpoint : oneEvent ⟶ boolStates where
  app _ := TypeCat.ofHom (fun _ => false)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

private def unitEndpoint : oneEvent ⟶ unitStates where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro event
    rfl

private def collapseStates : boolStates ⟶ unitStates where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro state
    rfl

/-- The source graph has only one step, from false to false. -/
def source : EventGraph Index where
  vertex := boolStates
  edge := oneEvent
  source := falseEndpoint
  target := falseEndpoint

/-- The target identifies both source states and retains the event. -/
def target : EventGraph Index where
  vertex := unitStates
  edge := oneEvent
  source := unitEndpoint
  target := unitEndpoint

def collapse : EventGraphHom source target where
  vertexMap := collapseStates
  edgeMap := 𝟙 oneEvent
  source_comm := by ext X event; rfl
  target_comm := by ext X event; rfl

/-- Every target event, not just its endpoints, has a source preimage. -/
theorem collapse_event_surjective (X : Index) :
    Function.Surjective (collapse.edgeMap.app X) := by
  intro event
  exact ⟨event, rfl⟩

theorem collapse_endpointCover : EndpointCover collapse := by
  intro X event
  exact ⟨event, rfl⟩

private def stage : Index := Discrete.mk PUnit.unit

/-- The target has the sole possible pair as a reduction. -/
theorem target_step :
    (pairMap collapse.vertexMap).app stage (true, true) ∈
      (reductionImage target).obj stage := by
  exact ⟨PUnit.unit, rfl⟩

/-- The source pair true,true has no firing. -/
theorem source_no_step :
    (true, true) ∉ (reductionImage source).obj stage := by
  rintro ⟨event, equal⟩
  cases event
  have impossible : false = true := congrArg Prod.fst equal
  cases impossible

/-- Even surjectivity on events does not reflect reduction if the state map
collapses a source pair that has no step onto one that does. -/
theorem event_surjective_without_step_reflection :
    (∀ X, Function.Surjective (collapse.edgeMap.app X)) ∧
    EndpointCover collapse ∧
    (pairMap collapse.vertexMap).app stage (true, true) ∈
      (reductionImage target).obj stage ∧
    (true, true) ∉ (reductionImage source).obj stage :=
  ⟨collapse_event_surjective, collapse_endpointCover,
    target_step, source_no_step⟩

end NoninjectiveControl

end Mettapedia.OSLF.Binding.OperationalImageReflection

#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.endpointCover_comp
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.exactImageGraphCategory
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.equationExactImageFunctor
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.equationExactImageFunctor_forget
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.reflects_reduction_of_endpointCover_of_vertex_injective
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.RhoControl.acuToSourceExact_not_vertex_injective
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.LambdaControl.firstCopy_reflects
#print axioms Mettapedia.OSLF.Binding.OperationalImageReflection.NoninjectiveControl.event_surjective_without_step_reflection
