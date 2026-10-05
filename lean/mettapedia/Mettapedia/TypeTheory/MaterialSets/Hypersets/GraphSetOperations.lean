import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization

/-!
# Original-bound graph set operations

Pairing and union are disjoint unions of actual original-small graph
families. Their introduction and elimination maps retain child receipts
and computed equality data. Unfolding a graph as the union of its child
pictures gives an equality realizer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetOperations

open GraphBisimulationRealizers GraphSetRealization

universe u

def pair (first second : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun choice : ULift.{u} Bool => if choice.down then first else second)

def pairFirst (first second : Graph.{u}) : Member first (pair first second) :=
  Sup.intro _ ⟨true⟩ (Equal.refl first)

def pairSecond (first second : Graph.{u}) : Member second (pair first second) :=
  Sup.intro _ ⟨false⟩ (Equal.refl second)

def pairEliminate {value first second : Graph.{u}} (proof : Member value (pair first second)) :
    Equal value first ⊕ Equal value second :=
  let decoded := Sup.eliminate _ proof
  match decoded.1.down with
  | true => .inl decoded.2
  | false => .inr decoded.2

abbrev UnionIndex (parent : Graph.{u}) : Type u :=
  Σ child : Child parent.edge parent.point,
    Child (parent.repoint child.val).edge (parent.repoint child.val).point

def union (parent : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun receipt : UnionIndex parent =>
    (parent.repoint receipt.1.val).repoint receipt.2.val)

def unionIntro {value child parent : Graph.{u}} (outer : Member child parent)
    (inner : Member value child) : Member value (union parent) :=
  let normalized := Member.transportParent outer.2 inner
  Sup.intro _ ⟨outer.1, normalized.1⟩ normalized.2

def unionEliminate {value parent : Graph.{u}} (proof : Member value (union parent)) :
    Σ child : Graph.{u}, Member child parent × Member value child :=
  let decoded := Sup.eliminate _ proof
  ⟨parent.repoint decoded.1.1.val, Member.atChild parent decoded.1.1,
    ⟨decoded.1.2, decoded.2⟩⟩

def unfolding (parent : Graph.{u}) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun child : Child parent.edge parent.point => parent.repoint child.val)

def unfoldingEqual (parent : Graph.{u}) : Equal parent (unfolding parent) :=
  extensionality
    (fun _ proof => Sup.intro _ proof.1 proof.2)
    (fun _ proof => let decoded := Sup.eliminate _ proof; ⟨decoded.1, decoded.2⟩)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetOperations
