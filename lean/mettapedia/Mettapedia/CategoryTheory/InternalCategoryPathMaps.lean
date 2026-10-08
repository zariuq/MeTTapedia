import Mettapedia.CategoryTheory.InternalCategoryPathDiagram
import Mettapedia.CategoryTheory.InternalCategoryDiagramMaps

/-!
# Internal path functors from full event-graph maps

Both endpoint equations of a graph map earn its quiver map. Its complete
stage naturality then gives a category-valued diagram transformation. The
resulting internal functor maps every singleton occurrence to its supplied
edge image, and composes arbitrary retained paths on the actual pullback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPathMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryPathDiagram

universe u v w

variable {B : Type u} [Category.{v} B]
variable {first second : InternalGraph (B ⥤ Type w)} (map : InternalGraph.Hom first second)

theorem source_readout (X : B) (edge : first.edge.obj X) :
    second.source.app X (map.edge.app X edge) = map.vertex.app X (first.source.app X edge) :=
  congrArg (fun (arrow : first.edge ⟶ second.vertex) => arrow.app X edge) map.source

theorem target_readout (X : B) (edge : first.edge.obj X) :
    second.target.app X (map.edge.app X edge) = map.vertex.app X (first.target.app X edge) :=
  congrArg (fun (arrow : first.edge ⟶ second.vertex) => arrow.app X edge) map.target

def quiverMap (X : B) : Vertex first X ⥤q Vertex second X where
  obj := fun object => map.vertex.app X object
  map edge := ⟨map.edge.app X edge.1,
    (source_readout map X edge.1).trans (congrArg (map.vertex.app X) edge.2.1),
    (target_readout map X edge.1).trans (congrArg (map.vertex.app X) edge.2.2)⟩

def quiverDiagramMap : quiverDiagram first ⟶ quiverDiagram second where
  app X := quiverMap map X
  naturality X Y change := by
    refine Prefunctor.ext'
      (fun object => NatTrans.naturality_apply map.vertex change object) ?_
    intro source target edge
    apply Subtype.ext
    rw [transported_edge_readout]
    exact NatTrans.naturality_apply map.edge change edge.1

def diagramMap : diagram first ⟶ diagram second :=
  Functor.whiskerRight (quiverDiagramMap map) Cat.free

/-- The full internal path functor, with no operational law supplied as a field. -/
def internalFunctor : InternalCategory.Hom (category first) (category second) :=
  InternalCategoryDiagramMaps.internalFunctor (diagramMap map)

theorem path_readout (X : B) (path : InternalCategoryDiagram.Arrow ((diagram first).obj X)) :
    (internalFunctor map).edge.app X path =
      ⟨map.vertex.app X path.1, map.vertex.app X path.2.1,
        (quiverMap map X).mapPath path.2.2⟩ := rfl

theorem edge_readout (X : B) (supplied : first.edge.obj X) :
    (internalFunctor map).edge.app X (edge first X supplied) =
      edge second X (map.edge.app X supplied) := by
  change (⟨map.vertex.app X (first.source.app X supplied),
    map.vertex.app X (first.target.app X supplied),
    (quiverMap map X).mapPath
      (@Quiver.Hom.toPath (Vertex first X) (quiver first X) _ _
        ⟨supplied, rfl, rfl⟩)⟩ :
      InternalCategoryDiagram.Arrow ((diagram second).obj X)) = _
  rw [Prefunctor.mapPath_toPath]
  exact singleton_eq_edge second X (map.edge.app X supplied) _ _
    (source_readout map X supplied) (target_readout map X supplied)

end Mettapedia.CategoryTheory.InternalCategoryPathMaps
