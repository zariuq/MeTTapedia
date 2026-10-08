import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies

/-!
# All literal nodes of contextual graph values

The node family retains every node of each authored graph, including the
actual root. Reindexing transports a node through its graph and the stated
value equation. Rerooting is natural, and graph edges are preserved under
the same action. These data support families with attached material bodies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyNodes

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualGraphDiagrams ContextualSmallFamilyUniverse
universe u
variable (D : Type u) [Category.{u} D]

abbrev Nodes {point : D} (value : Value D point) : Type u := value.1.nodes.obj point

def moveNode {first second : D} (arrival : first ⟶ second) (value : Value D first)
    (node : Nodes D value) : Nodes D (move D arrival value) := value.1.nodes.map arrival node

theorem moveNode_heq {source target : D} (arrival : source ⟶ target)
    {first second : Value D source} (same : first = second)
    (left : Nodes D first) (right : Nodes D second) (nodes : HEq left right) :
    HEq (moveNode D arrival first left) (moveNode D arrival second right) := by
  cases same
  cases eq_of_heq nodes
  rfl

def family : (values D).Elements ⥤ Type u where
  obj point := Nodes D point.2
  map {first second} step := TypeCat.ofHom fun node =>
    cast (congrArg (Nodes D) step.2) (moveNode D step.1 first.2 node)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro node
    apply eq_of_heq
    change HEq (cast (congrArg (Nodes D) ((values D).map_id_apply point.1 point.2))
      (point.2.1.nodes.map (𝟙 point.1) node)) node
    exact (ContextualSmallFamilyUniverse.cast_heq _ _).trans
      (heq_of_eq (point.2.1.nodes.map_id_apply point.1 node))
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro node
    apply eq_of_heq
    have mapSame := moveNode_heq D later.1 earlier.2.symm
      (cast (congrArg (Nodes D) earlier.2) (moveNode D earlier.1 first.2 node))
      (moveNode D earlier.1 first.2 node) (ContextualSmallFamilyUniverse.cast_heq _ _)
    exact (ContextualSmallFamilyUniverse.cast_heq _ _).trans
      ((heq_of_eq (first.2.1.nodes.map_comp_apply earlier.1 later.1 node)).trans
        (mapSame.symm.trans (ContextualSmallFamilyUniverse.cast_heq _ _).symm))

theorem map_heq {first second : (values D).Elements} (step : first ⟶ second)
    (node : Nodes D first.2) : HEq ((family D).map step node) (moveNode D step.1 first.2 node) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

def roots : (family D).sections :=
  ⟨fun point => point.2.2, by
    intro first second step
    apply eq_of_heq
    exact (map_heq D step first.2.2).trans (Sigma.mk.inj_iff.mp step.2).2⟩

def reroot {point : D} (value : Value D point) (node : Nodes D value) : Value D point :=
  ⟨value.1, node⟩

theorem reroot_cast {point : D} {first second : Value D point} (same : first = second)
    (node : Nodes D first) : reroot D second (cast (congrArg (Nodes D) same) node) = reroot D first node := by
  cases same
  rfl

theorem reroot_map {first second : (values D).Elements} (step : first ⟶ second)
    (node : Nodes D first.2) :
    reroot D second.2 ((family D).map step node) = move D step.1 (reroot D first.2 node) :=
  reroot_cast D step.2 (moveNode D step.1 first.2 node)

def reading : NaturalHom (total (family D)) (values D) where
  app _ receipt := reroot D receipt.1 receipt.2
  naturality {first second} arrival receipt :=
    (reroot_map D (CategoryOfElements.homMk (F := values D) ⟨first, receipt.1⟩
      ⟨second, move D arrival receipt.1⟩ arrival rfl) receipt.2).symm

theorem edge_cast {point : D} {first second : Value D point} (same : first = second)
    {left right : Nodes D first} (available : first.1.edge point left right) :
    second.1.edge point (cast (congrArg (Nodes D) same) left) (cast (congrArg (Nodes D) same) right) := by
  cases same
  exact available

theorem edge_transport {first second : (values D).Elements} (step : first ⟶ second)
    {left right : Nodes D first.2} (available : first.2.1.edge first.1 left right) :
    second.2.1.edge second.1 ((family D).map step left) ((family D).map step right) :=
  edge_cast D step.2 (first.2.1.edge_transport step.1 available)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyNodes
