import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Incidence graphs and their simple support

`Mathlib.Combinatorics.Graph` is the declarative carrier for undirected
multigraphs with explicit edge occurrences.  `SimpleGraph` is the right
quotient when loops and multiplicity are irrelevant.  This module makes that
loss of information explicit instead of silently identifying the two notions.
-/

namespace Graph

/-- Forget loops, edge identity, and edge multiplicity from an incidence
graph.  Ambient vertices outside `G.vertexSet` remain isolated; this keeps the
vertex type fixed and makes the construction compositional. -/
def simpleSupport {V E : Type*} (G : Graph V E) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.Adj u v
  symm.symm _ _ adjacency := ⟨Ne.symm adjacency.1, adjacency.2.symm⟩
  loopless.irrefl _ adjacency := adjacency.1 rfl

@[simp]
theorem simpleSupport_adj {V E : Type*} (G : Graph V E) (u v : V) :
    G.simpleSupport.Adj u v ↔ u ≠ v ∧ ∃ edge, G.IsLink edge u v :=
  Iff.rfl

/-- Every non-loop incidence occurrence appears in the simple support. -/
theorem IsLink.simpleSupport_adj {V E : Type*} {G : Graph V E}
    {edge : E} {u v : V} (link : G.IsLink edge u v) (hne : u ≠ v) :
    G.simpleSupport.Adj u v :=
  ⟨hne, edge, link⟩

/-- Simple support depends only on adjacency, not on which edge occurrence
witnesses it. -/
theorem simpleSupport_eq_of_adj_iff {V E₁ E₂ : Type*}
    {G : Graph V E₁} {H : Graph V E₂}
    (same : ∀ u v, G.Adj u v ↔ H.Adj u v) :
    G.simpleSupport = H.simpleSupport := by
  ext u v
  simp only [Graph.simpleSupport_adj]
  exact and_congr_right fun _ => same u v

end Graph

namespace Mettapedia.GraphTheory

namespace IncidenceCanary

private def oneParallelEdge : Graph Bool (Fin 2) :=
  Graph.banana false true {0}

private def twoParallelEdges : Graph Bool (Fin 2) :=
  Graph.banana false true {0, 1}

/-- Positive control: an explicit edge occurrence survives as adjacency in the
simple support. -/
theorem oneParallelEdge_adj :
    oneParallelEdge.simpleSupport.Adj false true := by
  simp [oneParallelEdge, Graph.simpleSupport]

/-- Negative control: simple support cannot distinguish one parallel edge from
two.  Algorithms sensitive to edge identity or multiplicity must remain over
`Graph V E` (or another occurrence-preserving carrier). -/
theorem simpleSupport_forgets_parallel_multiplicity :
    oneParallelEdge.simpleSupport = twoParallelEdges.simpleSupport := by
  apply Graph.simpleSupport_eq_of_adj_iff
  intro u v
  simp [oneParallelEdge, twoParallelEdges]

/-- The source incidence graphs in the negative control really are distinct. -/
theorem parallel_edge_sources_ne : oneParallelEdge ≠ twoParallelEdges := by
  intro equal
  have edgeSetsEqual : oneParallelEdge.edgeSet = twoParallelEdges.edgeSet :=
    congrArg Graph.edgeSet equal
  have : (1 : Fin 2) ∈ oneParallelEdge.edgeSet := by
    rw [edgeSetsEqual]
    simp [twoParallelEdges]
  simp [oneParallelEdge] at this

end IncidenceCanary

#print axioms Graph.IsLink.simpleSupport_adj
#print axioms Graph.simpleSupport_eq_of_adj_iff
#print axioms IncidenceCanary.simpleSupport_forgets_parallel_multiplicity
#print axioms IncidenceCanary.parallel_edge_sources_ne

end Mettapedia.GraphTheory
