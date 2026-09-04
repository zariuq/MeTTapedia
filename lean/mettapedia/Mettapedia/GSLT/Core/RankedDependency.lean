import Mathlib.Order.WellFounded

/-!
# Dependencies ranked by an independent well-founded order

A physical carrier may safely retain earlier values only when its dependency
graph is well founded.  This module isolates the representation-independent
contract.  Nodes map into an arbitrary well-founded rank relation, and every
direct dependency must map to a strictly earlier rank.

The induced dependency relation is well founded, every nonempty dependency
path maps to a nonempty path between ranks, and cyclic carriers are
impossible.  The final induction theorem is the recursion principle needed by
forcing, tracing, compaction, and ownership proofs: a node may be processed
after all values it depends on.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.RankedDependency

universe uNode uRank

/-- A dependency graph equipped with a map into a well-founded rank
relation.  `dependsOn node dependency` points from a newer consumer to an
earlier value it retains. -/
structure Order (Node : Type uNode) (Rank : Type uRank) where
  rank : Node → Rank
  earlier : Rank → Rank → Prop
  earlierWellFounded : WellFounded earlier
  dependsOn : Node → Node → Prop
  decreases :
    ∀ {node dependency},
      dependsOn node dependency → earlier (rank dependency) (rank node)

namespace Order

variable {Node : Type uNode} {Rank : Type uRank}

/-- Orient the dependency relation in the direction used by well-founded
recursion: an earlier dependency precedes its consumer. -/
def Precedes (order : Order Node Rank) (dependency node : Node) : Prop :=
  order.dependsOn node dependency

theorem precedes_rank (order : Order Node Rank)
    {dependency node : Node} (edge : order.Precedes dependency node) :
    order.earlier (order.rank dependency) (order.rank node) :=
  order.decreases edge

/-- Pulling the well-founded rank relation back along `rank` and restricting
it to actual dependency edges proves the physical dependency graph well
founded. -/
theorem precedes_wellFounded (order : Order Node Rank) :
    WellFounded order.Precedes := by
  exact (InvImage.wf order.rank order.earlierWellFounded).mono
    (fun dependency node edge => order.precedes_rank edge)

/-- Every finite nonempty dependency path maps to a finite nonempty path in
the independent rank relation. -/
theorem path_rankPath (order : Order Node Rank)
    {older newer : Node}
    (path : Relation.TransGen order.Precedes older newer) :
    Relation.TransGen order.earlier
      (order.rank older) (order.rank newer) := by
  induction path with
  | single edge =>
      exact .single (order.precedes_rank edge)
  | tail path edge inductionHypothesis =>
      exact .tail inductionHypothesis (order.precedes_rank edge)

/-- A capture cannot directly retain itself. -/
theorem no_self_dependency (order : Order Node Rank) (node : Node) :
    ¬ order.dependsOn node node := by
  exact order.precedes_wellFounded.irrefl.irrefl node

/-- No nonempty chain of retained values can return to its starting node. -/
theorem no_dependency_cycle (order : Order Node Rank) (node : Node) :
    ¬ Relation.TransGen order.Precedes node node := by
  exact order.precedes_wellFounded.transGen.irrefl.irrefl node

/-- Well-founded processing of a carrier: if a property can be established
for a node after all of its retained dependencies, it holds for every node. -/
theorem dependency_induction (order : Order Node Rank)
    (motive : Node → Prop)
    (step :
      ∀ node,
        (∀ dependency, order.dependsOn node dependency → motive dependency) →
          motive node) :
    ∀ node, motive node := by
  intro node
  apply order.precedes_wellFounded.induction node
  intro current inductionHypothesis
  apply step current
  intro dependency edge
  exact inductionHypothesis dependency edge

end Order

/-! ## Positive and negative controls -/

namespace Canaries

inductive Capture
  | root
  | middle
  | leaf
deriving DecidableEq

def rank : Capture → Nat
  | .root => 0
  | .middle => 1
  | .leaf => 2

def dependsOn : Capture → Capture → Prop
  | .middle, .root => True
  | .leaf, .middle => True
  | _, _ => False

theorem decreases {node dependency : Capture}
    (edge : dependsOn node dependency) :
    rank dependency < rank node := by
  cases node <;> cases dependency <;>
    simp [dependsOn, rank] at edge ⊢

def order : Order Capture Nat where
  rank := rank
  earlier := (· < ·)
  earlierWellFounded := wellFounded_lt
  dependsOn := dependsOn
  decreases := decreases

/-- The root is a transitive dependency of the leaf through the middle
capture, and its rank path is correspondingly nonempty. -/
example : Relation.TransGen order.Precedes .root .leaf := by
  apply Relation.TransGen.tail (b := Capture.middle)
  · exact Relation.TransGen.single (by
      simp [Order.Precedes, order, dependsOn])
  · simp [Order.Precedes, order, dependsOn]

/-- The admitted chronology rejects a dependency cycle. -/
example : ¬ Relation.TransGen order.Precedes .leaf .leaf :=
  order.no_dependency_cycle .leaf

/-- A proposed edge from the oldest capture to the newest one cannot inhabit
the same natural-number chronology. -/
def cyclic : Capture → Capture → Prop
  | .root, .leaf => True
  | node, dependency => dependsOn node dependency

example :
    ¬ ∃ candidate : Order Capture Nat,
        candidate.rank = rank ∧
          candidate.earlier = (· < ·) ∧
          candidate.dependsOn = cyclic := by
  rintro ⟨candidate, rankEquation, earlierEquation,
    dependencyEquation⟩
  have edge : candidate.dependsOn Capture.root Capture.leaf := by
    simp [dependencyEquation, cyclic]
  have decrease := candidate.decreases edge
  rw [earlierEquation, rankEquation] at decrease
  simp [rank] at decrease

#print axioms Order.precedes_wellFounded
#print axioms Order.path_rankPath
#print axioms Order.no_self_dependency
#print axioms Order.no_dependency_cycle
#print axioms Order.dependency_induction

end Canaries

end Mettapedia.GSLT.Core.RankedDependency
