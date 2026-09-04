/-
# Graph Theory - Basic Definitions

This file contains fundamental definitions from graph theory, following:
- Bondy & Murty, "Graph Theory" (GTM 244)
- Diestel, "Graph Theory"

## Current Coverage
- [x] Chapter 1: Basic definitions (SimpleGraph from Mathlib)
- [x] Chapter 4: Trees (using Mathlib's IsTree, IsAcyclic)
- [ ] Chapter 3: Connectivity
- [ ] Chapter 18: Hamilton Cycles (Dirac, Ore, Chvátal-Erdős)
- [ ] Chapter 5: Matchings
- [ ] Chapter 6: Tree-Search Algorithms (DFS/BFS)
- [ ] Chapter 7: Flows in Networks
- [ ] Chapter 10: Vertex Colourings
- [ ] Chapter 12: Edge Colourings
- [ ] Chapter 14: Random Graphs
- [ ] Chapter 16: Ramsey Theory
- [ ] Chapter 17: Planar Graphs

-/

-- Mathlib's SimpleGraph and related infrastructure
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
set_option checkBinderAnnotations false

open Classical

namespace Mettapedia.GraphTheory

/-!
## Using Mathlib's SimpleGraph

We use `SimpleGraph V` from Mathlib directly. Key types and predicates:
- `G.Adj u v` : adjacency predicate
- `G.Walk u v` : inductive walk type from u to v
- `G.Walk.IsPath` : walk with no repeated vertices
- `G.Walk.IsCycle` : closed walk with only start/end repeated
- `G.Connected` : every pair of vertices is connected
- `G.IsAcyclic` : no cycles
- `G.IsTree` : connected and acyclic
-/

variable {V : Type*} [DecidableEq V]

/-!
## Section 1: Basic Graph Properties (Chapter 1)
-/

omit [DecidableEq V] in
/-- Symmetry of adjacency (from Mathlib) -/
theorem adj_comm (G : SimpleGraph V) (u v : V) : G.Adj u v ↔ G.Adj v u :=
  SimpleGraph.adj_comm G u v

omit [DecidableEq V] in
/-- No vertex is adjacent to itself -/
theorem not_adj_self (G : SimpleGraph V) (v : V) : ¬G.Adj v v :=
  G.loopless.irrefl v

omit [DecidableEq V] in
/-- Neighbor set -/
def neighbors (G : SimpleGraph V) (v : V) : Set V := G.neighborSet v

omit [DecidableEq V] in
/-- A vertex is not its own neighbor -/
theorem not_mem_neighbors_self (G : SimpleGraph V) (v : V) : v ∉ neighbors G v := by
  simp only [neighbors, SimpleGraph.neighborSet, Set.mem_setOf_eq]
  exact G.loopless.irrefl v

/-- Complete graph: every pair of distinct vertices is adjacent -/
def Complete (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

/-- Empty graph: no edges -/
def Empty (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬G.Adj u v

omit [DecidableEq V] in
/-- Subgraph relation -/
def IsSubgraph (G H : SimpleGraph V) : Prop :=
  ∀ u v, G.Adj u v → H.Adj u v

omit [DecidableEq V] in
theorem isSubgraph_refl (G : SimpleGraph V) : IsSubgraph G G := fun _ _ h => h

omit [DecidableEq V] in
theorem isSubgraph_trans {G H K : SimpleGraph V}
    (hGH : IsSubgraph G H) (hHK : IsSubgraph H K) : IsSubgraph G K :=
  fun u v hG => hHK u v (hGH u v hG)

/-!
## Section 2: Degree (Chapter 1)
-/

/-- Degree of a vertex using Mathlib's definition -/
noncomputable def degree [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  G.degree v

/-!
## Section 3: Trees (Chapter 4)

Using Mathlib's `IsTree` and `IsAcyclic` definitions.
-/

/-- A tree is a connected acyclic graph (Bondy & Murty Chapter 4) -/
def Tree (G : SimpleGraph V) : Prop := G.IsTree

/-- A forest is an acyclic graph -/
def Forest (G : SimpleGraph V) : Prop := G.IsAcyclic

omit [DecidableEq V] in
/-- Key theorem: In a tree, there is a unique simple path between any two vertices.
    This is Mathlib's `SimpleGraph.IsTree.existsUnique_path`. -/
theorem tree_unique_path (G : SimpleGraph V) [G.Connected] :
    G.IsTree → ∀ u v, ∃! p : G.Walk u v, p.IsPath := by
  intro hTree u v
  exact hTree.existsUnique_path u v

omit [DecidableEq V] in
/-- A connected graph with n vertices and n - 1 edges is a tree.
    Uses Mathlib's characterization via edge count. -/
theorem connected_n_minus_one_edges_tree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hConn : G.Connected)
    (hEdges : G.edgeFinset.card = Fintype.card V - 1) :
    G.IsTree := by
  -- Use Mathlib's characterization: isTree_iff_connected_and_card
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact hConn
  · -- Convert from Finset.card to Nat.card
    -- Nat.card G.edgeSet + 1 = Nat.card V
    have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
    have hE : Nat.card G.edgeSet = Fintype.card G.edgeSet := Nat.card_eq_fintype_card
    rw [hV, hE, ← SimpleGraph.edgeFinset_card]
    -- Now: G.edgeFinset.card + 1 = Fintype.card V
    -- Given: G.edgeFinset.card = Fintype.card V - 1
    have hpos : Fintype.card V ≥ 1 := by
      have := hConn.nonempty
      exact Fintype.card_pos
    omega

/-- A finite vertex set separates two surviving vertices when every walk
between them meets the set. -/
def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ u v : V, u ∉ S ∧ v ∉ S ∧ u ≠ v ∧
    ∀ walk : G.Walk u v, ∃ x ∈ walk.support, x ∈ S

/-- Connectivity number: the minimum finite vertex-separator size, with the
standard complete-graph value `|V| - 1` when no separator exists. -/
noncomputable def connectivity [Fintype V] (G : SimpleGraph V) : ℕ :=
  let separators := Finset.univ.filter (IsVertexSeparator G)
  if present : separators.Nonempty then
    separators.inf' present Finset.card
  else
    Fintype.card V - 1

/-- Independence number: the largest cardinality of a finite vertex set with
no adjacent distinct pair. -/
noncomputable def independence_number [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.sup Finset.univ fun S : Finset V =>
    if (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) then S.card else 0

/-!
## Section 4: Coloring and matchings
-/

omit [DecidableEq V] in
/-- Vertex chromatic number, using Mathlib's independently defined coloring
semantics.  The value is extended-natural because an infinite graph need not
admit a coloring by any finite palette. -/
noncomputable abbrev ChromaticNumber (G : SimpleGraph V) : ℕ∞ := G.chromaticNumber

omit [DecidableEq V] in
/-- Edge chromatic number, defined canonically as the vertex chromatic number
of the line graph. -/
noncomputable abbrev EdgeChromaticNumber (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

omit [DecidableEq V] in
/-- Every finite graph colors itself by using its vertices as colors. -/
theorem chromaticNumber_le_vertexCard [Fintype V] (G : SimpleGraph V) :
    ChromaticNumber G ≤ Fintype.card V := by
  exact G.chromaticNumber_le_card

omit [DecidableEq V] in
/-- The analogous unconditional edge bound follows by coloring the vertices
of the line graph, one color per edge occurrence. -/
theorem edgeChromaticNumber_le_edgeCard [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    EdgeChromaticNumber G ≤ Fintype.card G.edgeSet := by
  exact G.lineGraph.chromaticNumber_le_card

omit [DecidableEq V] in
/-- The graph admits a matching subgraph.  The matching itself retains its
edge occurrences as a `SimpleGraph.Subgraph`. -/
def Matching (G : SimpleGraph V) : Prop :=
  ∃ matching : G.Subgraph, matching.IsMatching

omit [DecidableEq V] in
/-- The graph admits a matching subgraph spanning every vertex. -/
def PerfectMatching (G : SimpleGraph V) : Prop :=
  ∃ matching : G.Subgraph, matching.IsPerfectMatching

omit [DecidableEq V] in
/-- Handshaking lemma -/
theorem handshaking_lemma [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges G

omit [DecidableEq V] in
/-- Trees on n vertices have exactly n - 1 edges -/
theorem tree_edge_count [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hTree : G.IsTree) :
    G.edgeFinset.card = Fintype.card V - 1 := by
  -- Mathlib's card_edgeFinset gives: card + 1 = n
  have h := hTree.card_edgeFinset
  omega

omit [DecidableEq V] in
/-- Removing any edge from a tree disconnects it -/
theorem tree_edge_is_bridge [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTree : G.IsTree) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    G.IsBridge e := by
  have hacyclic := hTree.isAcyclic
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge] at hacyclic
  exact hacyclic he

omit [DecidableEq V] in
/-- Every tree with at least two vertices has at least two leaves.
    Proof sketch: Sum of degrees = 2(n-1). Each leaf has degree 1, each non-leaf has degree ≥ 2.
    If |leaves| ≤ 1, then sum ≥ 1 + 2(n-1) = 2n - 1 > 2(n-1), contradiction.
    Therefore |leaves| ≥ 2. -/
theorem tree_two_leaves [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTree : G.IsTree) (hn : Fintype.card V ≥ 2) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := hTree.exists_vert_degree_one_of_nontrivial
  by_contra noPair
  have uniqueLeaf {v : V} (hv : G.degree v = 1) : v = u := by
    by_contra hvu
    exact noPair ⟨u, v, Ne.symm hvu, hu, hv⟩
  have two_le_degree {v : V} (hvu : v ≠ u) : 2 ≤ G.degree v := by
    have positive : 0 < G.degree v :=
      hTree.preconnected.degree_pos_of_nontrivial v
    have notOne : G.degree v ≠ 1 := fun hv => hvu (uniqueLeaf hv)
    omega
  have eraseBound :
      2 * (Finset.univ.erase u).card ≤
        ∑ v ∈ (Finset.univ.erase u), G.degree v := by
    calc
      2 * (Finset.univ.erase u).card =
          ∑ _v ∈ (Finset.univ.erase u), 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ (Finset.univ.erase u), G.degree v :=
        Finset.sum_le_sum fun v hv =>
          two_le_degree (Finset.ne_of_mem_erase hv)
  have eraseCard : (Finset.univ.erase u).card = Fintype.card V - 1 := by
    simp
  have sumSplit :
      (∑ v ∈ (Finset.univ.erase u), G.degree v) + G.degree u =
        ∑ v : V, G.degree v := by
    simpa using
      (Finset.sum_erase_add Finset.univ (fun v : V => G.degree v)
        (Finset.mem_univ u))
  have lower : 2 * (Fintype.card V - 1) + 1 ≤ ∑ v : V, G.degree v := by
    rw [← sumSplit, hu, ← eraseCard]
    exact Nat.add_le_add_right eraseBound 1
  have exactSum : ∑ v : V, G.degree v = 2 * (Fintype.card V - 1) := by
    rw [handshaking_lemma G, tree_edge_count G hTree]
  omega

omit [DecidableEq V] in
/-- A graph is bipartite exactly when every closed walk has even length.  This
form is stronger and more compositional than quantifying only over cycles,
and is Mathlib's executable coloring characterization. -/
theorem bipartite_iff_all_closed_walks_even (G : SimpleGraph V) :
    G.IsBipartite ↔ ∀ (v : V) (walk : G.Walk v v), Even walk.length :=
  SimpleGraph.two_colorable_iff_forall_loop_even

/-!
## Additional placeholders for future development
-/

/- TODO: actual Turan extremal theorem. -/

/- TODO: actual Ramsey existence statement. -/

/- TODO: actual statement (Kőnig line coloring theorem). -/

/- TODO: Hall's marriage theorem. -/

/- TODO: Tutte's 1-factor theorem. -/

/- TODO: max-flow min-cut theorem. -/

/- TODO: termination of Ford–Fulkerson for integral capacities. -/

/- TODO: Menger's theorem (vertex connectivity form). -/

/- TODO: Whitney connectivity results. -/

/- TODO: Euler's formula for planar graphs. -/

/- TODO: Kuratowski's theorem. -/

/- TODO: five color theorem. -/

/- TODO: six color theorem. -/

/- TODO: strong perfect graph theorem. -/

/- TODO: Lovász local lemma based coloring bounds. -/

end Mettapedia.GraphTheory
