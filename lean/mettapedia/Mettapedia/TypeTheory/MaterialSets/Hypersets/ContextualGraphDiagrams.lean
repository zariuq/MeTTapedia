import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization
import Mettapedia.TypeTheory.ContextualWitnessCover

/-!
# Small contextual graphs and their actual rooted-value universe

Nodes vary over the context category. Every context map transports actual
nodes and preserves an authored edge. A rooted value retains its whole
diagram and current node; transport keeps the diagram and applies its
node functor. Parallel context arrows are retained individually.

The carrier of each diagram is original-small. The untyped universe of
all such diagrams is one level wider. Current-fibre graph observations
are deliberately separate from future-indexed matching evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphDiagrams

open CategoryTheory
universe u
variable (D : Type u) [Category.{u} D]

structure Diagram where
  nodes : D ⥤ Type u
  edge : (point : D) → nodes.obj point → nodes.obj point → Prop
  edge_transport : ∀ {first second : D} (arrival : first ⟶ second)
    {parent child : nodes.obj first}, edge first parent child →
      edge second (nodes.map arrival parent) (nodes.map arrival child)

abbrev Value (point : D) : Type (u+1) := Σ diagram : Diagram D, diagram.nodes.obj point

def move {first second : D} (arrival : first ⟶ second) (value : Value D first) :
    Value D second := ⟨value.1, value.1.nodes.map arrival value.2⟩

theorem move_identity (point : D) (value : Value D point) :
    move D (𝟙 point) value = value :=
  congrArg (Sigma.mk value.1) (value.1.nodes.map_id_apply point value.2)

theorem move_composition {first middle last : D} (earlier : first ⟶ middle)
    (later : middle ⟶ last) (value : Value D first) :
    move D (earlier ≫ later) value = move D later (move D earlier value) :=
  congrArg (Sigma.mk value.1) (value.1.nodes.map_comp_apply earlier later value.2)

def values : D ⥤ Type (u+1) where
  obj := Value D
  map arrival := TypeCat.ofHom (move D arrival)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact move_identity D point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact move_composition D earlier later

abbrev Child {point : D} (value : Value D point) : Type u :=
  {node : value.1.nodes.obj point // value.1.edge point value.2 node}

def childValue {point : D} (value : Value D point) (child : Child D value) : Value D point :=
  ⟨value.1, child.val⟩

def moveChild {first second : D} (arrival : first ⟶ second) (value : Value D first)
    (child : Child D value) : Child D (move D arrival value) :=
  ⟨value.1.nodes.map arrival child.val, value.1.edge_transport arrival child.property⟩

theorem move_childValue {first second : D} (arrival : first ⟶ second)
    (value : Value D first) (child : Child D value) :
    move D arrival (childValue D value child) =
      childValue D (move D arrival value) (moveChild D arrival value child) := rfl

def picture {point : D} (value : Value D point) : GraphSetRealization.Graph.{u} :=
  AccessiblePointedGraph.generated (value.1.edge point) value.2

/-- A constant diagram is an explicit comparison object, not the varying
universe itself. -/
def constant (graph : GraphSetRealization.Graph.{u}) : Diagram D where
  nodes := {
    obj _ := graph.Node
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ := graph.edge
  edge_transport := fun {_ _} _ {_ _} available => available

def constantValue (graph : GraphSetRealization.Graph.{u}) (point : D) : Value D point :=
  ⟨constant D graph, graph.point⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphDiagrams
