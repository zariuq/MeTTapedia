import Mettapedia.OSLF.Syntax.FreePresheafEventImage
import Mettapedia.OSLF.Syntax.RhoSourceEquationLexClassification
import Mettapedia.OSLF.Syntax.RhoEventQuotientDescentBoundary

/-!
# Reindexing event graphs along context and program comparisons

The finite-limit classifier compares program objects over an equation
context category, while authored firings are initially indexed by raw
substitution contexts. Reindexing and transport along a program-object
isomorphism carry the full event graph across that comparison. Their
endpoint images obey the corresponding pointwise image laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.PresheafEventGraphTransport

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventImage

universe u u' v v' w

variable {C : Type u} [Category.{v} C]
variable {B : Type u'} [Category.{v'} B]
variable {V W : C ⥤ Type w}

/-- Change the indexing category of an event graph by precomposition. -/
def reindex (H : B ⥤ C) (G : Graph V) : Graph (H ⋙ V) where
  edge := H ⋙ G.edge
  source := Functor.whiskerLeft H G.source
  target := Functor.whiskerLeft H G.target

/-- Reindex a map of retained event graphs, including its endpoint laws. -/
def reindexHom (H : B ⥤ C) {G K : Graph V}
    (f : Hom G K) : Hom (reindex H G) (reindex H K) where
  edgeMap := Functor.whiskerLeft H f.edgeMap
  source_comm := by
    ext X event
    exact congrArg
      (fun t : G.edge ⟶ V => t.app (H.obj X) event) f.source_comm
  target_comm := by
    ext X event
    exact congrArg
      (fun t : G.edge ⟶ V => t.app (H.obj X) event) f.target_comm

/-- Base change acts on graphs and their endpoint-preserving morphisms. -/
def reindexFunctor (H : B ⥤ C) : Graph V ⥤ Graph (H ⋙ V) where
  obj := reindex H
  map := reindexHom H
  map_id := by
    intro G
    apply Hom.ext
    rfl
  map_comp := by
    intro G K L f g
    apply Hom.ext
    rfl

/-- Precomposition preserves the pointwise disjoint sum of event presheaves.
The comparison is the identity on each event at each stage, but is a natural
isomorphism rather than definitional equality of functors. -/
def reindex_edgeSum_iso (H : B ⥤ C) (F G : C ⥤ Type w) :
    H ⋙ edgeSum F G ≅ edgeSum (H ⋙ F) (H ⋙ G) where
  hom :=
    { app := fun _ => TypeCat.ofHom id
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro event
        cases event <;> rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom id
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro event
        cases event <;> rfl }
  hom_inv_id := by ext X event; rfl
  inv_hom_id := by ext X event; rfl

/-- Context base change preserves the freely adjoined disjoint sum of
events. The comparison keeps each event in its original summand. -/
def reindex_graphSum_iso (H : B ⥤ C) (G K : Graph V) :
    reindex H (graphSum G K) ≅
      graphSum (reindex H G) (reindex H K) where
  hom :=
    { edgeMap := (reindex_edgeSum_iso H G.edge K.edge).hom
      source_comm := by
        ext X event
        cases event <;> rfl
      target_comm := by
        ext X event
        cases event <;> rfl }
  inv :=
    { edgeMap := (reindex_edgeSum_iso H G.edge K.edge).inv
      source_comm := by
        ext X event
        cases event <;> rfl
      target_comm := by
        ext X event
        cases event <;> rfl }
  hom_inv_id := by apply Hom.ext; exact (reindex_edgeSum_iso H G.edge K.edge).hom_inv_id
  inv_hom_id := by apply Hom.ext; exact (reindex_edgeSum_iso H G.edge K.edge).inv_hom_id

/-- Base change identifies the original-event injection with the original
summand after reindexing. -/
theorem reindex_graphInl (H : B ⥤ C) (G K : Graph V) :
    Hom.comp (reindexHom H (graphInl G K))
      (reindex_graphSum_iso H G K).hom =
        graphInl (reindex H G) (reindex H K) := by
  apply Hom.ext
  ext X event
  rfl

/-- Base change identifies the authored-generator injection with the new
summand after reindexing. -/
theorem reindex_graphInr (H : B ⥤ C) (G K : Graph V) :
    Hom.comp (reindexHom H (graphInr G K))
      (reindex_graphSum_iso H G K).hom =
        graphInr (reindex H G) (reindex H K) := by
  apply Hom.ext
  ext X event
  rfl

/-- The coproduct extension of two graph maps commutes with base change,
including its universal map on event occurrences. -/
theorem reindex_graphCopair (H : B ⥤ C)
    {G K T : Graph V} (f : Hom G T) (g : Hom K T) :
    Hom.comp (reindex_graphSum_iso H G K).hom
      (graphCopair (reindexHom H f) (reindexHom H g)) =
        reindexHom H (graphCopair f g) := by
  apply Hom.ext
  ext X event
  cases event <;> rfl

/-- A program-object isomorphism changes the endpoints of a graph without
changing or identifying any of its events. -/
def changeVertex (i : V ≅ W) (G : Graph V) : Graph W where
  edge := G.edge
  source := G.source ≫ i.hom
  target := G.target ≫ i.hom

/-- A program-object isomorphism also transports maps of event graphs. -/
def changeVertexHom (i : V ≅ W) {G K : Graph V}
    (f : Hom G K) : Hom (changeVertex i G) (changeVertex i K) where
  edgeMap := f.edgeMap
  source_comm := by
    simpa only [changeVertex, Category.assoc] using
      congrArg (fun t : G.edge ⟶ V => t ≫ i.hom) f.source_comm
  target_comm := by
    simpa only [changeVertex, Category.assoc] using
      congrArg (fun t : G.edge ⟶ V => t ≫ i.hom) f.target_comm

/-- State isomorphisms act functorially without changing the event carrier. -/
def changeVertexFunctor (i : V ≅ W) : Graph V ⥤ Graph W where
  obj := changeVertex i
  map := changeVertexHom i
  map_id := by
    intro G
    apply Hom.ext
    rfl
  map_comp := by
    intro G K L f g
    apply Hom.ext
    rfl

/-- Transporting program states along an isomorphism and back gives the
original event graph, with the identity map on every firing event. -/
def changeVertexRoundtrip (i : V ≅ W) (G : Graph V) :
    changeVertex i.symm (changeVertex i G) ≅ G where
  hom :=
    { edgeMap := 𝟙 G.edge
      source_comm := by simp [changeVertex, Category.assoc]
      target_comm := by simp [changeVertex, Category.assoc] }
  inv :=
    { edgeMap := 𝟙 G.edge
      source_comm := by simp [changeVertex, Category.assoc]
      target_comm := by simp [changeVertex, Category.assoc] }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- State isomorphisms induce equivalences of the corresponding categories
of event graphs. Both directions act as the identity on firing carriers. -/
def changeVertexEquivalence (i : V ≅ W) : Graph V ≌ Graph W where
  functor := changeVertexFunctor i
  inverse := changeVertexFunctor i.symm
  unitIso := NatIso.ofComponents (fun G => (changeVertexRoundtrip i G).symm)
    (by intro G K f; apply Hom.ext; rfl)
  counitIso := NatIso.ofComponents (changeVertexRoundtrip i.symm)
    (by intro G K f; apply Hom.ext; rfl)
  functor_unitIso_comp := by
    intro G
    apply Hom.ext
    rfl

/-- Transporting program states preserves the disjoint adjoining of firing
events, with the identity on both event summands. -/
def changeVertex_graphSum_iso (i : V ≅ W) (G K : Graph V) :
    changeVertex i (graphSum G K) ≅
      graphSum (changeVertex i G) (changeVertex i K) where
  hom :=
    { edgeMap := 𝟙 _
      source_comm := by
        ext X event
        cases event <;> rfl
      target_comm := by
        ext X event
        cases event <;> rfl }
  inv :=
    { edgeMap := 𝟙 _
      source_comm := by
        ext X event
        cases event <;> rfl
      target_comm := by
        ext X event
        cases event <;> rfl }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- The old-event injection is coherent with transport of the free sum. -/
theorem changeVertex_graphInl (i : V ≅ W) (G K : Graph V) :
    Hom.comp (changeVertexHom i (graphInl G K))
      (changeVertex_graphSum_iso i G K).hom =
        graphInl (changeVertex i G) (changeVertex i K) := by
  apply Hom.ext
  rfl

/-- The authored-generator injection is coherent with transport of the
free sum, so the identity of every firing occurrence is preserved. -/
theorem changeVertex_graphInr (i : V ≅ W) (G K : Graph V) :
    Hom.comp (changeVertexHom i (graphInr G K))
      (changeVertex_graphSum_iso i G K).hom =
        graphInr (changeVertex i G) (changeVertex i K) := by
  apply Hom.ext
  rfl

/-- Apply a map of state presheaves to each endpoint of a pair. -/
def pairMap (i : V ⟶ W) :
    FunctorToTypes.prod V V ⟶ FunctorToTypes.prod W W :=
  FunctorToTypes.prod.lift
    (FunctorToTypes.prod.fst ≫ i)
    (FunctorToTypes.prod.snd ≫ i)

/-- The paired endpoint arrow itself commutes with changing the program
object. Image transport is a consequence of this map-level equality. -/
theorem endpointMap_changeVertex (i : V ≅ W) (G : Graph V) :
    endpointMap (changeVertex i G) =
      endpointMap G ≫ pairMap i.hom := by
  ext X event <;> rfl

/-- Reindexing computes the endpoint image pointwise. No new image-preservation
axiom is needed because presheaf images are formed at each context. -/
theorem mem_endpointImage_reindex (H : B ⥤ C) (G : Graph V)
    (X : B) (pair : V.obj (H.obj X) × V.obj (H.obj X)) :
    pair ∈ (endpointImage (reindex H G)).obj X ↔
      pair ∈ (endpointImage G).obj (H.obj X) := by
  simp only [mem_endpointImage_iff]
  rfl

/-- Changing the program object pushes the endpoint predicate forward
along the induced product isomorphism. -/
theorem endpointImage_changeVertex (i : V ≅ W) (G : Graph V) :
    endpointImage (changeVertex i G) =
      (endpointImage G).image (pairMap i.hom) := by
  ext X pair
  constructor
  · rintro ⟨event, rfl⟩
    exact ⟨(endpointMap G).app X event, ⟨event, rfl⟩, rfl⟩
  · rintro ⟨oldPair, ⟨event, rfl⟩, rfl⟩
    exact ⟨event, rfl⟩

/-- A component of a presheaf isomorphism is injective. -/
theorem componentInjective (i : V ≅ W) (X : C) :
    Function.Injective (i.hom.app X) :=
  (i.app X).toEquiv.injective

/-- Transport across a program-object isomorphism preserves and reflects
the reduction predicate on corresponding endpoint pairs. -/
theorem mem_endpointImage_changeVertex (i : V ≅ W) (G : Graph V)
    (X : C) (pair : V.obj X × V.obj X) :
    (pairMap i.hom).app X pair ∈
      (endpointImage (changeVertex i G)).obj X ↔
        pair ∈ (endpointImage G).obj X := by
  change (i.hom.app X pair.1, i.hom.app X pair.2) ∈
    (endpointImage (changeVertex i G)).obj X ↔
      pair ∈ (endpointImage G).obj X
  rw [mem_endpointImage_iff, mem_endpointImage_iff]
  change (∃ event : G.edge.obj X,
    i.hom.app X (G.source.app X event) = i.hom.app X pair.1 ∧
    i.hom.app X (G.target.app X event) = i.hom.app X pair.2) ↔
    (∃ event : G.edge.obj X,
      G.source.app X event = pair.1 ∧
      G.target.app X event = pair.2)
  constructor
  · rintro ⟨event, sourceEq, targetEq⟩
    exact ⟨event,
      componentInjective i X sourceEq,
      componentInjective i X targetEq⟩
  · rintro ⟨event, sourceEq, targetEq⟩
    exact ⟨event, congrArg (i.hom.app X) sourceEq,
      congrArg (i.hom.app X) targetEq⟩

end Mettapedia.OSLF.Binding.PresheafEventGraphTransport

namespace Mettapedia.OSLF.Binding.PresheafEventGraphTransport.RhoExample

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
open Mettapedia.OSLF.Binding.FreePresheafEventImage
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

/-- Read raw substitution contexts as clone contexts before passing to the
complete rho source-equation quotient. -/
noncomputable def rawCloneIndex := (cloneContextToSyntactic sig).op

/-- The generated finite-limit interpretation's program object, pulled
back to the clone contexts where intrinsic firing events are compared. -/
noncomputable def generatedStates :=
  (termCloneToSemanticContextFunctor sig ⋙
    quotientContextFunctor rhoSourceE).op ⋙
      sourceYonedaExtension.1.obj
        ((authoredContext SourceContexts).obj program)

/-- The actual COMM/Drop event graph, with its full firing witnesses, now
over the program object of the source-equation finite-limit classifier. -/
noncomputable def generatedEventGraph :
    FreePresheafEventExtension.Graph generatedStates :=
  changeVertex generatedProgramAsOperationalStatesIso
    (reindex rawCloneIndex sourceEvents)

/-- The generated program comparison induces an equivalence of all
proof-relevant event graphs over the raw clone contexts, not merely a
comparison of the chosen rho generator graph. -/
noncomputable def sourceGeneratedGraphEquivalence :
    FreePresheafEventExtension.Graph (rawCloneIndex ⋙ states) ≌
      FreePresheafEventExtension.Graph generatedStates :=
  changeVertexEquivalence generatedProgramAsOperationalStatesIso

/-- The actual rho generators are the image of the authored graph under the
equivalence of graph categories. -/
theorem generatedEventGraph_is_equivalence_image :
    sourceGeneratedGraphEquivalence.functor.obj
      (reindex rawCloneIndex sourceEvents) = generatedEventGraph := rfl

/-- For any prior event graph over the authored state object, freely
adjoining the rho events commutes with interpreting states as the generated
program object. The comparison preserves each old and each authored event. -/
noncomputable def authoredFreeEventsTransportIso
    (prior : FreePresheafEventExtension.Graph (rawCloneIndex ⋙ states)) :
    changeVertex generatedProgramAsOperationalStatesIso
        (graphSum prior (reindex rawCloneIndex sourceEvents)) ≅
      graphSum (changeVertex generatedProgramAsOperationalStatesIso prior)
        generatedEventGraph :=
  changeVertex_graphSum_iso generatedProgramAsOperationalStatesIso
    prior (reindex rawCloneIndex sourceEvents)

/-- The generated graph keeps the authored event object, including distinct
firing witnesses with identical endpoints. -/
theorem generated_events_unchanged :
    generatedEventGraph.edge = rawCloneIndex ⋙ sourceEvents.edge := rfl

/-- The complete source equation quotient identifies substitutions that
still act differently on retained firing occurrences. Thus the generated
program comparison does not imply that its event object descends to the
quotient context base. -/
theorem generated_events_do_not_descend :
    ¬ ∃ (events : SourceContextsᵒᵖ ⥤ Type),
      Nonempty (generatedEventGraph.edge ≅
        (termCloneToSemanticContextFunctor sig ⋙
          quotientContextFunctor rhoSourceE).op ⋙ events) := by
  exact RhoEventQuotientDescentBoundary.raw_events_do_not_descend

/-- Before transport, the graph's endpoint image is exactly the authored
rho reduction subobject at each raw substitution context. -/
theorem reindexed_image_iff_source_reduction
    (X : (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject
      (termClone sig))ᵒᵖ)
    (pair : states.obj (rawCloneIndex.obj X) ×
      states.obj (rawCloneIndex.obj X)) :
    pair ∈ (endpointImage (reindex rawCloneIndex sourceEvents)).obj X ↔
      pair ∈ sourceReduction.obj (rawCloneIndex.obj X) := by
  rw [mem_endpointImage_reindex]
  rw [FreePresheafEventImage.RhoExample.source_image_eq_reduction]
  exact Iff.rfl

/-- The endpoint predicate of the generated-program graph is the image of
the source predicate under the proven program-object isomorphism. The
events themselves are unchanged by this transport. -/
theorem generated_image_transport :
    endpointImage generatedEventGraph =
      (endpointImage (reindex rawCloneIndex sourceEvents)).image
        (pairMap generatedProgramAsOperationalStatesIso.hom) :=
  endpointImage_changeVertex generatedProgramAsOperationalStatesIso
    (reindex rawCloneIndex sourceEvents)

/-- The generated interpretation has a firing at the transported endpoints
exactly when the original authored rho source has a reduction there. This
holds in every open clone context, not just for closed process terms. -/
theorem generated_image_iff_source_reduction
    (X : (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject
      (termClone sig))ᵒᵖ)
    (pair : states.obj (rawCloneIndex.obj X) ×
      states.obj (rawCloneIndex.obj X)) :
    (pairMap generatedProgramAsOperationalStatesIso.hom).app X pair ∈
      (endpointImage generatedEventGraph).obj X ↔
        pair ∈ sourceReduction.obj (rawCloneIndex.obj X) := by
  exact (mem_endpointImage_changeVertex
    generatedProgramAsOperationalStatesIso
    (reindex rawCloneIndex sourceEvents) X pair).trans
      (reindexed_image_iff_source_reduction X pair)

end Mettapedia.OSLF.Binding.PresheafEventGraphTransport.RhoExample
