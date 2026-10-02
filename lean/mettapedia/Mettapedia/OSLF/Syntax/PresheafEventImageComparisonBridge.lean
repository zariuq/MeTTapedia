import Mettapedia.OSLF.Syntax.PresheafEventImageComparison
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport
import Mettapedia.GSLT.Topos.PresheafPredicateProjection

/-!
# Shared event, image and predicate interfaces

The fixed-vertex operational graph and the constructive modal graph have the
same retained event presheaf and endpoint maps. The common endpoint-image
construction agrees with the older operational range, and reindexing computes
that image at each stage. At a small presheaf base, the reduction is an object
of the existing predicate total category with its actual cartesian lifts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.PresheafEventImageComparison

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open Mettapedia.GSLT.Topos.ConstructivePresheaf (EventGraph)
open Mettapedia.GSLT.Topos.PresheafEventModalities
open Mettapedia.OSLF.Binding.FreePresheafEventExtension (Graph Hom)
open Mettapedia.GSLT.Topos

universe u v w uB vB

variable {C : Type u} [Category.{v} C]

/-- Read the modal graph in the existing fixed-vertex operational interface. -/
def fixedGraph (G : EventGraph.{u, v, w} C) : Graph G.vertex where
  edge := G.edge
  source := G.source
  target := G.target

/-- Read an existing operational graph in the shared predicate/modal interface. -/
def modalGraph {V : C ⥤ Type w} (G : Graph V) : EventGraph C where
  vertex := V
  edge := G.edge
  source := G.source
  target := G.target

theorem fixed_modalGraph {V : C ⥤ Type w} (G : Graph V) :
    fixedGraph (modalGraph G) = G := rfl

theorem modal_fixedGraph (G : EventGraph.{u, v, w} C) :
    modalGraph (fixedGraph G) = G := rfl

theorem endpointMap_fixedGraph (G : EventGraph.{u, v, w} C) :
    FreePresheafEventImage.endpointMap (fixedGraph G) = endpointMap G := rfl

theorem reduction_fixedGraph (G : EventGraph.{u, v, w} C) :
    FreePresheafEventImage.endpointImage (fixedGraph G) = reduction G := rfl

variable {B : Type uB} [Category.{vB} B]

/-- A change of indexing category carries the actual event and program
presheaves by precomposition, retaining their endpoint natural maps. -/
def reindexGraph (H : B ⥤ C) (G : EventGraph.{u, v, w} C) : EventGraph B where
  vertex := H ⋙ G.vertex
  edge := H ⋙ G.edge
  source := Functor.whiskerLeft H G.source
  target := Functor.whiskerLeft H G.target

theorem fixedGraph_reindex (H : B ⥤ C) (G : EventGraph.{u, v, w} C) :
    fixedGraph (reindexGraph H G) =
      PresheafEventGraphTransport.reindex H (fixedGraph G) := rfl

/-- Endpoint image commutes with base reindexing. This section-level law
compares the actual old and new range constructions without any assumed
image-preservation property of a semantic interpretation. -/
theorem reduction_reindex (H : B ⥤ C) (G : EventGraph.{u, v, w} C)
    (X : B) (pair : G.vertex.obj (H.obj X) × G.vertex.obj (H.obj X)) :
    pair ∈ (reduction (reindexGraph H G)).obj X ↔
      pair ∈ (reduction G).obj (H.obj X) := by
  exact PresheafEventGraphTransport.mem_endpointImage_reindex H (fixedGraph G) X pair

/-- An ordinary endpoint-preserving operational graph map carries may-step
facts forward. Exact backward transport is an additional coverage property. -/
theorem diamond_le_of_graphHom {V : C ⥤ Type w} {G K : Graph V}
    (f : Hom G K) (predicate : Subfunctor V) :
    diamond (modalGraph G) predicate ≤ diamond (modalGraph K) predicate := by
  intro X x holds
  obtain ⟨event, target, source⟩ := (diamond_spec _ _ _ _).1 holds
  have sourceEq := congrArg (fun arrow => arrow.app X event) f.source_comm
  have targetEq := congrArg (fun arrow => arrow.app X event) f.target_comm
  exact (diamond_spec _ _ _ _).2
    ⟨f.edgeMap.app X event, targetEq.symm ▸ target, sourceEq.trans source⟩

section PredicateProjection

variable {A : Type u} [Category.{u} A]
variable (G : EventGraph.{u, u, u} Aᵒᵖ)

/-- The endpoint image is an actual object of the shared predicate category,
over the full presheaf of program pairs. -/
abbrev reductionPredicate : PresheafPredicateTotal A :=
  ⟨FunctorToTypes.prod G.vertex G.vertex, reduction G⟩

theorem reductionPredicate_base :
    (presheafPredicateProjection A).obj (reductionPredicate G) =
      FunctorToTypes.prod G.vertex G.vertex := rfl

/-- Predicate substitution at this image is exactly the shared constructive
preimage operation, rather than a present-stage-only test. -/
theorem reductionPredicate_pullback {F : Aᵒᵖ ⥤ Type u}
    (k : F ⟶ FunctorToTypes.prod G.vertex G.vertex) :
    (predicateLiftDomain (reduction G) k).fiber =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.preimage k (reduction G) := rfl

theorem reductionPredicate_cartesian {F : Aᵒᵖ ⥤ Type u}
    (k : F ⟶ FunctorToTypes.prod G.vertex G.vertex) :
    IsStronglyCartesian (presheafPredicateProjection A) k
      (predicateLift (reduction G) k) :=
  predicateLift_stronglyCartesian (reduction G) k

/-- Every preceding predicate arrow has a unique factorization through the
reduction's cartesian predicate lift. -/
theorem reductionPredicate_factorization {F : Aᵒᵖ ⥤ Type u}
    (k : F ⟶ FunctorToTypes.prod G.vertex G.vertex)
    (a : PresheafPredicateTotal A) (g : a.base ⟶ F)
    (arrow : a ⟶ reductionPredicate G)
    [IsHomLift (presheafPredicateProjection A) (g ≫ k) arrow] :
    ∃! factor : a ⟶ predicateLiftDomain (reduction G) k,
      IsHomLift (presheafPredicateProjection A) g factor ∧
        factor ≫ predicateLift (reduction G) k = arrow :=
  predicateLift_factorization (reduction G) k a g arrow

end PredicateProjection

end Mettapedia.OSLF.Binding.PresheafEventImageComparison

end
