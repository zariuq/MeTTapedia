import Mettapedia.GraphTheory.Representation.RepresentationGSLT
import Mettapedia.GraphTheory.HamiltonianDegree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Transporting graph theorems across representation GSLT paths

A representation rewrite changes data layout, not the represented graph.
Consequently every extensional graph property transports through the total
conversion path.  Operational cost is deliberately excluded: changing the
layout is useful precisely because it may change the work needed by an
observer.
-/

namespace Mettapedia.GraphTheory.Representation.SemanticTransport

open Mettapedia.GraphTheory.Representation
open Mettapedia.GraphTheory.Representation.RepresentationGSLT

/-- Any predicate on the independent simple-graph meaning is invariant under
total representation conversion. -/
theorem convert_property_iff {n : Nat}
    (property : SimpleGraph (Fin n) → Prop)
    (source : State n) (target : Layout) :
    property source.denote ↔
      property (materialize target (canonicalMatrix source)).denote := by
  rw [convertPath_commutes source target]

theorem convert_hamiltonian_iff {n : Nat}
    (source : State n) (target : Layout) :
    source.denote.IsHamiltonian ↔
      (materialize target (canonicalMatrix source)).denote.IsHamiltonian :=
  convert_property_iff SimpleGraph.IsHamiltonian source target

/-- Ore's semantic premise may be checked on any source representation; the
resulting Hamiltonicity theorem then transports through every total layout
conversion. -/
theorem converted_hamiltonian_of_ore {n : Nat}
    (source : State n) (target : Layout)
    [DecidableRel source.denote.Adj]
    (atLeastThree : 3 ≤ n)
    (degreeSum : ∀ u v : Fin n, u ≠ v → ¬source.denote.Adj u v →
      n ≤ source.denote.degree u + source.denote.degree v) :
    (materialize target (canonicalMatrix source)).denote.IsHamiltonian := by
  apply (convert_hamiltonian_iff source target).mp
  apply HamiltonianDegree.ore_theorem source.denote (by simpa using atLeastThree)
  intro u v different nonadjacent
  simpa using degreeSum u v different nonadjacent

/-- Dirac's pointwise degree premise likewise produces a theorem about every
meaning-preserving target layout, without re-proving it for concrete data. -/
theorem converted_hamiltonian_of_dirac {n : Nat}
    (source : State n) (target : Layout)
    [DecidableRel source.denote.Adj]
    (atLeastThree : 3 ≤ n)
    (minimumDegree : ∀ vertex : Fin n,
      n ≤ 2 * source.denote.degree vertex) :
    (materialize target (canonicalMatrix source)).denote.IsHamiltonian := by
  apply (convert_hamiltonian_iff source target).mp
  apply HamiltonianDegree.ore_theorem source.denote (by simpa using atLeastThree)
  intro u v _different _nonadjacent
  have degreeU := minimumDegree u
  have degreeV := minimumDegree v
  simp only [Fintype.card_fin]
  omega

theorem convert_connected_iff {n : Nat}
    (source : State n) (target : Layout) :
    source.denote.Connected ↔
      (materialize target (canonicalMatrix source)).denote.Connected :=
  convert_property_iff SimpleGraph.Connected source target

theorem convert_bipartite_iff {n : Nat}
    (source : State n) (target : Layout) :
    source.denote.IsBipartite ↔
      (materialize target (canonicalMatrix source)).denote.IsBipartite :=
  convert_property_iff SimpleGraph.IsBipartite source target

theorem convert_acyclic_iff {n : Nat}
    (source : State n) (target : Layout) :
    source.denote.IsAcyclic ↔
      (materialize target (canonicalMatrix source)).denote.IsAcyclic :=
  convert_property_iff SimpleGraph.IsAcyclic source target

/-- The cardinality of a neighbour set is another extensional observation
transported by the same commuting path.  For finite vertices this is the
ordinary degree, stated without choosing a representation-specific
`Fintype` instance for the neighbour subtype. -/
theorem convert_neighbor_card_eq {n : Nat}
    (source : State n) (target : Layout) (vertex : Fin n) :
    Nat.card (source.denote.neighborSet vertex) =
      Nat.card
        ((materialize target (canonicalMatrix source)).denote.neighborSet
          vertex) := by
  rw [convertPath_commutes source target]

namespace Canary

/-- Negative control: semantic preservation does not imply cost preservation.
The absent edge `0--2` costs two occurrence probes in the path edge list and
one cell probe after matrix materialisation. -/
theorem path3_matrix_changes_lookup_work :
    (EdgeList.edge EdgeList.Canary.path3
        EdgeList.Canary.v0 EdgeList.Canary.v2).work ≠
      (AdjacencyMatrix.edge
        (canonicalMatrix (State.edgeList EdgeList.Canary.path3))
        EdgeList.Canary.v0 EdgeList.Canary.v2).work := by
  rw [EdgeList.Canary.path3_absent_edge_cost]
  decide

end Canary

#print axioms convert_property_iff
#print axioms convert_hamiltonian_iff
#print axioms converted_hamiltonian_of_ore
#print axioms converted_hamiltonian_of_dirac
#print axioms convert_neighbor_card_eq
#print axioms Canary.path3_matrix_changes_lookup_work

end Mettapedia.GraphTheory.Representation.SemanticTransport
