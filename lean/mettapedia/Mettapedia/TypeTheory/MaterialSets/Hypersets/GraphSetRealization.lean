import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBisimulationRealizers

/-!
# Graph equality and membership with matching data

Material values are accessible pointed graph presentations. Equality is
a small coherent matching realizer. A member retains an actual child
receipt and a matching realizer at that child. Equality transports these
receipts in both arguments, and two-sided membership transport constructs
an equality realizer.

The forgetful interpretation is ordinary graph bisimilarity and material
membership. It does not select data from propositional bisimilarity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization

open GraphBisimulationRealizers

universe u

abbrev Graph := AccessiblePointedGraph.{u}

/-- Equality retains coherent two-sided matching data. -/
abbrev Equal (first second : Graph.{u}) : Type u :=
  Realizer first.edge second.edge first.point second.point

namespace Equal

def refl (graph : Graph.{u}) : Equal graph graph := Realizer.refl graph.point

def symm {first second : Graph.{u}} (proof : Equal first second) : Equal second first :=
  Realizer.symm proof

def trans {first middle last : Graph.{u}} (firstProof : Equal first middle)
    (secondProof : Equal middle last) : Equal first last := Realizer.trans firstProof secondProof

theorem forget {first second : Graph.{u}} (proof : Equal first second) : first ≈ second :=
  Realizer.forget proof

end Equal

/-- Generated-subgraph inclusion supplies a matching realizer at every node. -/
def repointInclusion (graph : Graph.{u}) (node : graph.Node) :
    Realizer (graph.repoint node).edge graph.edge (graph.repoint node).point node :=
  GraphBisimulationRealizers.generated node (graph.repoint node).point

def pointed {first second : Graph.{u}} {left : first.Node} {right : second.Node}
    (proof : Realizer first.edge second.edge left right) :
    Equal (first.repoint left) (second.repoint right) :=
  (repointInclusion first left).trans (proof.trans (repointInclusion second right).symm)

def unpointed {first second : Graph.{u}} {left : first.Node} {right : second.Node}
    (proof : Equal (first.repoint left) (second.repoint right)) :
    Realizer first.edge second.edge left right :=
  Realizer.trans (Realizer.symm (repointInclusion first left))
    (Realizer.trans proof (repointInclusion second right))

def repointPoint (graph : Graph.{u}) : Equal (graph.repoint graph.point) graph :=
  repointInclusion graph graph.point

/-- A member consists of a literal child and equality to the child picture. -/
abbrev Member (child parent : Graph.{u}) : Type u :=
  Σ receipt : Child parent.edge parent.point, Equal child (parent.repoint receipt.val)

namespace Member

def atChild (parent : Graph.{u}) (receipt : Child parent.edge parent.point) :
    Member (parent.repoint receipt.val) parent := ⟨receipt, Equal.refl _⟩

def transportChild {child other parent : Graph.{u}} (same : Equal child other)
    (proof : Member child parent) : Member other parent :=
  ⟨proof.1, same.symm.trans proof.2⟩

def transportParent {child parent other : Graph.{u}} (same : Equal parent other)
    (proof : Member child parent) : Member child other :=
  let matched := same.out.1 proof.1
  ⟨matched.1, proof.2.trans (pointed matched.2)⟩

def transport {child otherChild parent otherParent : Graph.{u}}
    (sameChild : Equal child otherChild) (sameParent : Equal parent otherParent)
    (proof : Member child parent) : Member otherChild otherParent :=
  transportParent sameParent (transportChild sameChild proof)

end Member

/-- Actual two-sided membership maps give a matching realizer. The child
picture is used as the witness to each unbounded membership quantifier. -/
def extensionality {first second : Graph.{u}}
    (forth : ∀ child : Graph.{u}, Member child first → Member child second)
    (back : ∀ child : Graph.{u}, Member child second → Member child first) : Equal first second :=
  Realizer.roll
    ⟨fun child =>
      let matched := forth (first.repoint child.val) (Member.atChild first child)
      ⟨matched.1, unpointed matched.2⟩,
      fun child =>
      let matched := back (second.repoint child.val) (Member.atChild second child)
      ⟨matched.1, (unpointed matched.2).symm⟩⟩

namespace Sup

variable {Index : Type u} (graphs : Index → Graph.{u})

/-- A root child of a disjoint union contains its actual family index. -/
def index (child : Child (AccessiblePointedGraph.sup graphs).edge
    (AccessiblePointedGraph.sup graphs).point) : Index :=
  match child with
  | ⟨none, impossible⟩ => False.elim (by cases impossible)
  | ⟨some ⟨selected, _⟩, _⟩ => selected

theorem node (child : Child (AccessiblePointedGraph.sup graphs).edge
    (AccessiblePointedGraph.sup graphs).point) :
    child.val = some ⟨index graphs child, (graphs (index graphs child)).point⟩ := by
  rcases child with ⟨_, edge⟩
  cases edge
  rfl

def child (selected : Index) : Child (AccessiblePointedGraph.sup graphs).edge
    (AccessiblePointedGraph.sup graphs).point :=
  ⟨some ⟨selected, (graphs selected).point⟩, .point selected⟩

/-- Child lifting reads the retained component index and uses only proved
equalities of those indices. -/
def liftChild (selected : Index) (source : (graphs selected).Node)
    (target : Child (AccessiblePointedGraph.sup graphs).edge (some ⟨selected, source⟩)) :
    {child : Child (graphs selected).edge source //
      (some ⟨selected, child.val⟩ : (AccessiblePointedGraph.sup graphs).Node) = target.val} := by
  rcases target with ⟨target, edge⟩
  cases target with
  | none => exact False.elim (by cases edge)
  | some target =>
    rcases target with ⟨other, target⟩
    have same : other = selected := by cases edge; rfl
    cases same
    have actualEdge : (graphs selected).edge source target := by
      cases edge with
      | edge _ actual => exact actual
    exact ⟨⟨target, actualEdge⟩, rfl⟩

def component (selected : Index) (source : (graphs selected).Node) :
    Realizer (graphs selected).edge (AccessiblePointedGraph.sup graphs).edge
      source (some ⟨selected, source⟩) :=
  Realizer.ofMap (left := (graphs selected).edge) (right := (AccessiblePointedGraph.sup graphs).edge)
    (fun source => (some ⟨selected, source⟩ : (AccessiblePointedGraph.sup graphs).Node))
    (fun _ _ edge => AccessiblePointedGraph.SupEdge.edge selected edge)
    (liftChild graphs selected) source

def picture (selected : Index) :
    Equal (graphs selected)
      ((AccessiblePointedGraph.sup graphs).repoint (child graphs selected).val) :=
  (component graphs selected (graphs selected).point).trans
    (repointInclusion (AccessiblePointedGraph.sup graphs) (child graphs selected).val).symm

def intro {value : Graph.{u}} (selected : Index) (same : Equal value (graphs selected)) :
    Member value (AccessiblePointedGraph.sup graphs) :=
  ⟨child graphs selected, same.trans (picture graphs selected)⟩

def eliminate {value : Graph.{u}} (proof : Member value (AccessiblePointedGraph.sup graphs)) :
    Σ selected : Index, Equal value (graphs selected) := by
  refine ⟨index graphs proof.1, ?_⟩
  have nodeSame := node graphs proof.1
  exact proof.2.trans (nodeSame ▸ (picture graphs (index graphs proof.1)).symm)

end Sup

def emptyEliminate {value : Graph.{u}} (proof : Member value AccessiblePointedGraph.empty) :
    PEmpty.{u+1} :=
  False.elim (AccessiblePointedGraph.not_edge_empty _ proof.1.property)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization
