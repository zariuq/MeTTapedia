import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.SharedLatentDAG

/-!
# Dependency order for forward initialization

A forward initialization computes a node only after every dependency used by
that node is available.  This module isolates the graph-theoretic certificate:
every dependency edge strictly increases a natural-number rank and every root
is supplied by the known boundary.  The rank makes every nonempty directed
path strictly increasing, hence rules out directed cycles.

The result formalizes and generalizes the structural boundary in Proposition
3.2 of Pinchetti, Frieder, Lukasiewicz, and Salvatori (2026).  It applies to
arbitrary edge-indexed dependency graphs, including repeated edges, and maps
the existing shared-latent predictive-coding DAG into the same interface.
Warm-start quality and convergence speed are separate analytic obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

universe uNode uEdge

/-- Directed dependency graph.  Parallel edges are retained through the edge
index even though acyclicity depends only on their endpoints. -/
structure PredictionDependencyGraph
    (Node : Type uNode) (Edge : Type uEdge) where
  source : Edge → Node
  target : Edge → Node

namespace PredictionDependencyGraph

variable {Node : Type uNode} {Edge : Type uEdge}

/-- One directed dependency step. -/
def Step (graph : PredictionDependencyGraph Node Edge) : Node → Node → Prop :=
  fun source target =>
    ∃ edge, graph.source edge = source ∧ graph.target edge = target

/-- Directed acyclicity expressed through the nonempty transitive closure. -/
def DirectedAcyclic (graph : PredictionDependencyGraph Node Edge) : Prop :=
  ∀ node, ¬ Relation.TransGen graph.Step node node

/-- A root has no incoming dependency edge. -/
def IsRoot (graph : PredictionDependencyGraph Node Edge) (node : Node) : Prop :=
  ¬ ∃ edge, graph.target edge = node

end PredictionDependencyGraph

/-- Certificate that a forward initialization has a dependency-respecting
order and receives every root from a known boundary value. -/
structure ForwardInitializationCertificate
    {Node : Type uNode} {Edge : Type uEdge}
    (graph : PredictionDependencyGraph Node Edge)
    (known : Set Node) where
  rank : Node → ℕ
  forward : ∀ edge, rank (graph.source edge) < rank (graph.target edge)
  rootsKnown : ∀ node, graph.IsRoot node → node ∈ known

namespace ForwardInitializationCertificate

variable {Node : Type uNode} {Edge : Type uEdge}
variable {graph : PredictionDependencyGraph Node Edge} {known : Set Node}

/-- Every nonempty dependency path strictly increases initialization rank. -/
theorem rank_lt_of_path
    (certificate : ForwardInitializationCertificate graph known)
    {first last : Node}
    (path : Relation.TransGen graph.Step first last) :
    certificate.rank first < certificate.rank last := by
  have lifted :
      Relation.TransGen (fun first last : ℕ => first < last)
        (certificate.rank first) (certificate.rank last) :=
    path.lift certificate.rank (by
      intro source target step
      obtain ⟨edge, rfl, rfl⟩ := step
      exact certificate.forward edge)
  simpa only [Relation.transGen_eq_self] using lifted

/-- A dependency-respecting forward initialization cannot contain a directed
cycle. -/
theorem directedAcyclic
    (certificate : ForwardInitializationCertificate graph known) :
    graph.DirectedAcyclic := by
  intro node cycle
  exact (Nat.lt_irrefl (certificate.rank node))
    (certificate.rank_lt_of_path cycle)

/-- The boundary part of the certificate exposes every root value. -/
theorem root_mem_known
    (certificate : ForwardInitializationCertificate graph known)
    {node : Node} (hroot : graph.IsRoot node) :
    node ∈ known :=
  certificate.rootsKnown node hroot

end ForwardInitializationCertificate

/-! ## Bridge to shared-latent predictive-coding DAGs -/

namespace SharedLatentDAG

variable {Node Edge : Type*} [Fintype Node] [Fintype Edge]

/-- Forget the analytic data of a shared-latent PC DAG while retaining its
dependency occurrences. -/
def dependencyGraph (graph : SharedLatentDAG Node Edge) :
    PredictionDependencyGraph Node Edge where
  source := graph.source
  target := graph.target

/-- The rank already carried by `SharedLatentDAG` is a forward-initialization
order.  Taking every node as known isolates the acyclicity component without
asserting a particular clamping policy. -/
def forwardInitializationOrder (graph : SharedLatentDAG Node Edge) :
    ForwardInitializationCertificate graph.dependencyGraph Set.univ where
  rank := graph.rank
  forward := graph.forward
  rootsKnown := by simp

/-- Every existing shared-latent PC DAG is directed-acyclic under its actual
edge occurrences. -/
theorem dependencyGraph_directedAcyclic
    (graph : SharedLatentDAG Node Edge) :
    graph.dependencyGraph.DirectedAcyclic :=
  graph.forwardInitializationOrder.directedAcyclic

end SharedLatentDAG

/-! ## Positive and negative finite fixtures -/

namespace ForwardInitializationFixture

/-- A single dependency from `false` to `true`. -/
def oneWayGraph : PredictionDependencyGraph Bool Unit where
  source := fun _ => false
  target := fun _ => true

def oneWayKnown : Set Bool := {false}

def oneWayCertificate :
    ForwardInitializationCertificate oneWayGraph oneWayKnown where
  rank
    | false => 0
    | true => 1
  forward := by
    intro edge
    cases edge
    decide
  rootsKnown := by
    intro node hroot
    cases node
    · simp [oneWayKnown]
    · exfalso
      apply hroot
      exact ⟨(), rfl⟩

theorem oneWayGraph_is_directedAcyclic :
    oneWayGraph.DirectedAcyclic :=
  oneWayCertificate.directedAcyclic

/-- Two opposite dependencies form a directed cycle. -/
def twoCycleGraph : PredictionDependencyGraph Bool Bool where
  source
    | false => false
    | true => true
  target
    | false => true
    | true => false

/-- No known-boundary choice can repair a cyclic dependency order. -/
theorem twoCycleGraph_has_no_forwardInitializationCertificate
    (known : Set Bool) :
    ¬ Nonempty (ForwardInitializationCertificate twoCycleGraph known) := by
  intro certificate
  obtain ⟨certificate⟩ := certificate
  have forwardFirst := certificate.forward false
  have forwardSecond := certificate.forward true
  simp [twoCycleGraph] at forwardFirst forwardSecond
  omega

end ForwardInitializationFixture

#print axioms ForwardInitializationCertificate.rank_lt_of_path
#print axioms ForwardInitializationCertificate.directedAcyclic
#print axioms SharedLatentDAG.dependencyGraph_directedAcyclic
#print axioms ForwardInitializationFixture.oneWayGraph_is_directedAcyclic
#print axioms ForwardInitializationFixture.twoCycleGraph_has_no_forwardInitializationCertificate

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
