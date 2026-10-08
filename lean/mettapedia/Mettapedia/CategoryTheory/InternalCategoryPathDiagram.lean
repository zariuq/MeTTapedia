import Mettapedia.CategoryTheory.InternalCategoryDiagram
import Mathlib.CategoryTheory.Category.Quiv

/-!
# The internal category of retained event paths

An independently supplied graph diagram gives a quiver at every stage.
Restriction maps every particular edge with its two endpoints. The actual
free-category functor constructs the category-valued path diagram, and the
chosen-pullback construction makes it an internal presheaf category.
Operational edges remain distinct from identities and from their endpoint
pair; no edge is identified with equality of vertices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryPathDiagram

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {B : Type u} [Category.{v} B]

def Vertex (graph : InternalGraph (B ⥤ Type w)) (X : B) := graph.vertex.obj X

instance quiver (graph : InternalGraph (B ⥤ Type w)) (X : B) : Quiver (Vertex graph X) where
  Hom first last := {edge : graph.edge.obj X //
    graph.source.app X edge = first ∧ graph.target.app X edge = last}

def restriction (graph : InternalGraph (B ⥤ Type w)) {X Y : B} (change : X ⟶ Y) :
    Vertex graph X ⥤q Vertex graph Y where
  obj := fun object => graph.vertex.map change object
  map edge := ⟨graph.edge.map change edge.1, by
    constructor
    · exact (NatTrans.naturality_apply graph.source change edge.1).trans
        (congrArg (graph.vertex.map change) edge.2.1)
    · exact (NatTrans.naturality_apply graph.target change edge.1).trans
        (congrArg (graph.vertex.map change) edge.2.2)⟩

theorem transported_edge_readout (graph : InternalGraph (B ⥤ Type w)) (X : B)
    {first last first' last' : Vertex graph X} (edge : first ⟶ last)
    (firstEq : first = first') (lastEq : last = last') :
    (Quiver.homOfEq edge firstEq lastEq).1 = edge.1 := by
  subst first'
  subst last'
  rfl

theorem restriction_id (graph : InternalGraph (B ⥤ Type w)) (X : B) :
    restriction graph (𝟙 X) = 𝟭q (Vertex graph X) := by
  refine Prefunctor.ext'
    (fun object => ConcreteCategory.congr_hom (graph.vertex.map_id X) object) ?_
  intro first last edge
  apply Subtype.ext
  rw [transported_edge_readout]
  exact graph.edge.map_id_apply X edge.1

theorem restriction_comp (graph : InternalGraph (B ⥤ Type w))
    {X Y Z : B} (first : X ⟶ Y) (second : Y ⟶ Z) :
    restriction graph (first ≫ second) = restriction graph first ⋙q restriction graph second := by
  refine Prefunctor.ext'
    (fun object => ConcreteCategory.congr_hom (graph.vertex.map_comp first second) object) ?_
  intro firstObject lastObject edge
  apply Subtype.ext
  rw [transported_edge_readout]
  exact graph.edge.map_comp_apply first second edge.1

def quiverDiagram (graph : InternalGraph (B ⥤ Type w)) : B ⥤ Quiv.{w,w} where
  obj X := Quiv.of (Vertex graph X)
  map := restriction graph
  map_id := restriction_id graph
  map_comp := restriction_comp graph

def diagram (graph : InternalGraph (B ⥤ Type w)) : B ⥤ Cat.{w,w} :=
  quiverDiagram graph ⋙ Cat.free

def category (graph : InternalGraph (B ⥤ Type w)) : InternalCategory (B ⥤ Type w) :=
  InternalCategoryDiagram.category (diagram graph)

abbrev Path (graph : InternalGraph (B ⥤ Type w)) (X : B)
    (first last : Vertex graph X) := @Quiver.Path (Vertex graph X) (quiver graph X) first last

def edge (graph : InternalGraph (B ⥤ Type w)) (X : B) (supplied : graph.edge.obj X) :
    InternalCategoryDiagram.Arrow ((diagram graph).obj X) :=
  ⟨graph.source.app X supplied, graph.target.app X supplied,
    @Quiver.Hom.toPath (Vertex graph X) (quiver graph X) _ _ ⟨supplied, rfl, rfl⟩⟩

theorem singleton_eq_edge (graph : InternalGraph (B ⥤ Type w)) (X : B)
    (supplied : graph.edge.obj X) (first last : Vertex graph X)
    (sourceRead : graph.source.app X supplied = first)
    (targetRead : graph.target.app X supplied = last) :
    (⟨first, last, @Quiver.Hom.toPath (Vertex graph X) (quiver graph X) _ _
      ⟨supplied, sourceRead, targetRead⟩⟩ :
        InternalCategoryDiagram.Arrow ((diagram graph).obj X)) = edge graph X supplied := by
  cases sourceRead
  cases targetRead
  rfl

theorem edge_source (graph : InternalGraph (B ⥤ Type w)) (X : B) (supplied : graph.edge.obj X) :
    (category graph).source.app X (edge graph X supplied) = graph.source.app X supplied := rfl

theorem edge_target (graph : InternalGraph (B ⥤ Type w)) (X : B) (supplied : graph.edge.obj X) :
    (category graph).target.app X (edge graph X supplied) = graph.target.app X supplied := rfl

theorem edge_restriction (graph : InternalGraph (B ⥤ Type w)) {X Y : B}
    (change : X ⟶ Y) (supplied : graph.edge.obj X) :
    (category graph).edge.map change (edge graph X supplied) =
      edge graph Y (graph.edge.map change supplied) := by
  have sourceRead := NatTrans.naturality_apply graph.source change supplied
  have targetRead := NatTrans.naturality_apply graph.target change supplied
  change (⟨graph.vertex.map change (graph.source.app X supplied),
    graph.vertex.map change (graph.target.app X supplied),
    (restriction graph change).mapPath
      (@Quiver.Hom.toPath (Vertex graph X) (quiver graph X) _ _
        ⟨supplied, rfl, rfl⟩)⟩ :
      InternalCategoryDiagram.Arrow ((diagram graph).obj Y)) = _
  rw [Prefunctor.mapPath_toPath]
  exact singleton_eq_edge graph Y (graph.edge.map change supplied) _ _ sourceRead targetRead

/-- Every supplied event is naturally included as its one-edge path. -/
def edgeInclusion (graph : InternalGraph (B ⥤ Type w)) : graph.edge ⟶ (category graph).edge where
  app X := TypeCat.ofHom (edge graph X)
  naturality X Y change := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact (edge_restriction graph change supplied).symm

@[reassoc] theorem edgeInclusion_source (graph : InternalGraph (B ⥤ Type w)) :
    edgeInclusion graph ≫ (category graph).source = graph.source := by
  ext X supplied
  rfl

@[reassoc] theorem edgeInclusion_target (graph : InternalGraph (B ⥤ Type w)) :
    edgeInclusion graph ≫ (category graph).target = graph.target := by
  ext X supplied
  rfl

end Mettapedia.CategoryTheory.InternalCategoryPathDiagram
