import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization

/-!
# Graph anti-foundation with realized equality

Every original-small directed graph is decorated by its generated
pointed graphs. The decoration equation retains actual matching receipts
for both directions. Any other decoration satisfying those realized
equations has a constructed equality realizer to the generated one.

The uniqueness proof coiterates through the supplied equations at every
child; it does not replace their actual matching data with erased
propositional existence. Equality here is realized graph equality, not
literal identity of graph presentations or native higher identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedAntiFoundation

open GraphBisimulationRealizers GraphSetRealization

universe u

variable {Node : Type u} (edge : Node → Node → Prop)

def canonical (node : Node) : Graph.{u} := AccessiblePointedGraph.generated edge node

def members (decoration : Node → Graph.{u}) (node : Node) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun child : Child edge node => decoration child.val)

def canonicalChild (node : Node) (child : Child (canonical edge node).edge (canonical edge node).point) :
    Realizer (canonical edge node).edge (canonical edge child.val.val).edge
      child.val (canonical edge child.val.val).point :=
  (GraphBisimulationRealizers.generated node child.val).trans
    (GraphBisimulationRealizers.generated child.val.val (canonical edge child.val.val).point).symm

def canonicalEquation (node : Node) :
    Equal (canonical edge node) (members edge (canonical edge) node) :=
  Realizer.roll
    ⟨fun child =>
      let receipt : Child edge node := ⟨child.val.val, child.property⟩
      ⟨Sup.child (fun receipt : Child edge node => canonical edge receipt.val) receipt,
        (canonicalChild edge node child).trans
          (Sup.component (fun receipt : Child edge node => canonical edge receipt.val) receipt
            (canonical edge receipt.val).point)⟩,
      fun child =>
      let receipt := Sup.index (fun receipt : Child edge node => canonical edge receipt.val) child
      let source : Child (canonical edge node).edge (canonical edge node).point :=
        ⟨⟨receipt.val, Relation.ReflTransGen.refl.tail receipt.property⟩, receipt.property⟩
      let continuation := (canonicalChild edge node source).trans
        (Sup.component (fun receipt : Child edge node => canonical edge receipt.val) receipt
          (canonical edge receipt.val).point)
      ⟨source, (Sup.node (fun receipt : Child edge node => canonical edge receipt.val) child).symm ▸
        continuation⟩⟩

variable (decoration : Node → Graph.{u})
variable (equations : ∀ node, Equal (decoration node) (members edge decoration node))

/-- A state of the coiteration relates an arbitrary node of the fixed
root picture to the point of the decoration at its current graph node. -/
def uniquenessStep (root : Node) (first : (decoration root).Node) (second : Node)
    (proof : Realizer (decoration root).edge (decoration second).edge first (decoration second).point) :
    Layer (decoration root).edge edge
      (fun first second => Realizer (decoration root).edge (decoration second).edge
        first (decoration second).point) first second :=
  let unfolded := Realizer.trans proof (equations second)
  ⟨fun child =>
    let matched := unfolded.out.1 child
    let receipt := Sup.index (fun receipt : Child edge second => decoration receipt.val) matched.1
    let continuation : Realizer (decoration root).edge (members edge decoration second).edge
        child.val (some ⟨receipt, (decoration receipt.val).point⟩) :=
      Sup.node (fun receipt : Child edge second => decoration receipt.val) matched.1 ▸ matched.2
    ⟨receipt, continuation.trans
      (Sup.component (fun receipt : Child edge second => decoration receipt.val) receipt
        (decoration receipt.val).point).symm⟩,
    fun child =>
    let matched := unfolded.out.2
      (Sup.child (fun receipt : Child edge second => decoration receipt.val) child)
    ⟨matched.1, matched.2.trans
      (Sup.component (fun receipt : Child edge second => decoration receipt.val) child
        (decoration child.val).point).symm⟩⟩

/-- Coiteration constructs the comparison for the whole graph. -/
def uniqueness (root : Node) : Equal (decoration root) (canonical edge root) :=
  (corec (decoration root).edge edge (uniquenessStep edge decoration equations root)
    (Realizer.refl (decoration root).point)).trans
    (GraphBisimulationRealizers.generated root (canonical edge root).point).symm

/-- Actual existence and realized uniqueness of graph decoration. -/
def graphAntiFoundation :
    Σ result : Node → Graph.{u},
      (∀ node, Equal (result node) (members edge result node)) ×
      ((other : Node → Graph.{u}) →
        (∀ node, Equal (other node) (members edge other node)) →
        ∀ node, Equal (result node) (other node)) :=
  ⟨canonical edge, canonicalEquation edge,
    fun other otherEquations node => (uniqueness edge other otherEquations node).symm⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedAntiFoundation
