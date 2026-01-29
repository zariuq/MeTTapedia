/-
# Directed Graphs for Bayesian Networks

This file provides the foundational graph theory for Bayesian networks:
directed graphs, acyclicity, parents, ancestors, and topological ordering.

## Overview

A directed graph is defined as a relation V → V → Prop representing edges.
We define:
- `parents`, `children`: immediate neighbors
- `ancestors`, `descendants`: transitive closure
- `IsAcyclic`: no self-reachable vertices

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Koller & Friedman, "Probabilistic Graphical Models" (2009)
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

/-! ## Directed Graph Structure -/

/-- A directed graph on vertices V, represented as an edge relation. -/
@[ext]
structure DirectedGraph (V : Type*) where
  /-- The edge relation: `edges u v` means there is an edge from u to v. -/
  edges : V → V → Prop

namespace DirectedGraph

variable {V : Type*} (G : DirectedGraph V)

/-! ## Parents and Children -/

/-- The parents of a vertex: all vertices with an edge TO this vertex. -/
def parents (v : V) : Set V := { u | G.edges u v }

/-- The children of a vertex: all vertices with an edge FROM this vertex. -/
def children (v : V) : Set V := { w | G.edges v w }

/-- A vertex is a parent of another if there's an edge between them. -/
theorem mem_parents_iff (u v : V) : u ∈ G.parents v ↔ G.edges u v := Iff.rfl

/-- A vertex is a child of another if there's an edge between them. -/
theorem mem_children_iff (u w : V) : w ∈ G.children u ↔ G.edges u w := Iff.rfl

/-! ## Paths and Reachability -/

/-- A path in the graph: sequence of vertices where consecutive pairs have edges. -/
inductive Path : V → V → Prop where
  | refl (v : V) : Path v v
  | step {u v w : V} : G.edges u v → Path v w → Path u w

/-- The transitive closure of the edge relation: reachability. -/
def Reachable (u v : V) : Prop := G.Path u v

/-- Reachability is reflexive. -/
theorem reachable_refl (v : V) : G.Reachable v v := Path.refl v

/-- Reachability is transitive. -/
theorem reachable_trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w := by
  induction huv with
  | refl => exact hvw
  | step hedge _ ih => exact Path.step hedge (ih hvw)

/-- An edge implies reachability. -/
theorem edge_reachable {u v : V} (h : G.edges u v) : G.Reachable u v :=
  Path.step h (Path.refl v)

/-! ## Ancestors and Descendants -/

/-- The ancestors of a vertex: all vertices that can reach it via directed paths
    (excluding the vertex itself). -/
def ancestors (v : V) : Set V := { u | G.Reachable u v ∧ u ≠ v }

/-- The descendants of a vertex: all vertices reachable from it via directed paths
    (excluding the vertex itself). -/
def descendants (v : V) : Set V := { w | G.Reachable v w ∧ w ≠ v }

/-- Parents are a subset of ancestors (for irreflexive edge relations). -/
theorem parents_subset_ancestors_of_irrefl (v : V)
    (hirrefl : ∀ w, ¬G.edges w w) : G.parents v ⊆ G.ancestors v := by
  intro u hu
  simp only [Set.mem_setOf_eq, ancestors, parents] at *
  constructor
  · exact edge_reachable G hu
  · intro heq
    subst heq
    exact hirrefl u hu

/-- Children are a subset of descendants (for irreflexive edge relations). -/
theorem children_subset_descendants_of_irrefl (v : V)
    (hirrefl : ∀ w, ¬G.edges w w) : G.children v ⊆ G.descendants v := by
  intro w hw
  simp only [Set.mem_setOf_eq, descendants, children] at *
  constructor
  · exact edge_reachable G hw
  · intro heq
    subst heq
    exact hirrefl w hw

/-! ## Acyclicity -/

/-- A directed graph is acyclic if no vertex can reach itself via a non-trivial path.
    Equivalently: there are no cycles. -/
def IsAcyclic : Prop := ∀ v : V, ¬∃ u : V, G.edges v u ∧ G.Reachable u v

/-- Alternative characterization: acyclic iff no vertex has itself as ancestor. -/
theorem isAcyclic_iff_no_self_reach :
    G.IsAcyclic ↔ ∀ v u : V, G.edges v u → ¬G.Reachable u v := by
  constructor
  · intro hacyclic v u hedge hreach
    exact hacyclic v ⟨u, hedge, hreach⟩
  · intro h v ⟨u, hedge, hreach⟩
    exact h v u hedge hreach

/-- In an acyclic graph, the edge relation is irreflexive. -/
theorem isAcyclic_irrefl (h : G.IsAcyclic) (v : V) : ¬G.edges v v := by
  intro hedge
  apply h v
  exact ⟨v, hedge, Path.refl v⟩

/-- In an acyclic graph, there are no 2-cycles. -/
theorem isAcyclic_no_two_cycle (h : G.IsAcyclic) (u v : V) :
    G.edges u v → G.edges v u → False := by
  intro huv hvu
  apply h u
  exact ⟨v, huv, edge_reachable G hvu⟩

/-- Parents are ancestors in acyclic graphs. -/
theorem parents_subset_ancestors (h : G.IsAcyclic) (v : V) :
    G.parents v ⊆ G.ancestors v :=
  G.parents_subset_ancestors_of_irrefl v (G.isAcyclic_irrefl h)

/-- Children are descendants in acyclic graphs. -/
theorem children_subset_descendants (h : G.IsAcyclic) (v : V) :
    G.children v ⊆ G.descendants v :=
  G.children_subset_descendants_of_irrefl v (G.isAcyclic_irrefl h)

/-! ## Graph Operations -/

/-- The reverse graph (flip all edges). -/
def reverse : DirectedGraph V where
  edges := fun u v => G.edges v u

/-- Parents in reverse graph are children in original. -/
theorem reverse_parents_eq_children (v : V) :
    G.reverse.parents v = G.children v := by
  ext u
  simp [parents, children, reverse]

/-- Children in reverse graph are parents in original. -/
theorem reverse_children_eq_parents (v : V) :
    G.reverse.children v = G.parents v := by
  ext u
  simp [parents, children, reverse]

/-- Reverse of reverse is original. -/
theorem reverse_reverse : G.reverse.reverse = G := by
  ext u v
  simp [reverse]

/-- Reverse edges are decidable if original edges are. -/
instance reverse_decidableRel [DecidableRel G.edges] : DecidableRel G.reverse.edges :=
  fun u v => inferInstanceAs (Decidable (G.edges v u))

/-- Reachability in reverse is reverse reachability. -/
theorem reverse_reachable {u v : V} :
    G.reverse.Reachable u v ↔ G.Reachable v u := by
  constructor
  · intro hreach
    induction hreach with
    | refl => exact reachable_refl G _
    | step hedge _ ih =>
      apply reachable_trans G ih
      exact edge_reachable G hedge
  · intro hreach
    induction hreach with
    | refl => exact reachable_refl G.reverse _
    | step hedge _ ih =>
      apply reachable_trans G.reverse ih
      exact edge_reachable G.reverse hedge

/-- Reverse preserves acyclicity. -/
theorem reverse_isAcyclic (h : G.IsAcyclic) : G.reverse.IsAcyclic := by
  intro v ⟨u, hedge, hreach⟩
  apply h u
  exact ⟨v, hedge, (reverse_reachable (G := G)).1 hreach⟩

/-! ## Finite Graphs and Decidability -/

variable [DecidableEq V]

/-- For a decidable edge relation, parents form a decidable set. -/
instance [DecidableRel G.edges] (v : V) : DecidablePred (· ∈ G.parents v) :=
  fun u => inferInstanceAs (Decidable (G.edges u v))

/-- For a decidable edge relation, children form a decidable set. -/
instance [DecidableRel G.edges] (v : V) : DecidablePred (· ∈ G.children v) :=
  fun u => inferInstanceAs (Decidable (G.edges v u))

/-! ## Sources and Sinks -/

/-- A vertex is a source if it has no parents (no incoming edges). -/
def IsSource (v : V) : Prop := G.parents v = ∅

/-- A vertex is a sink if it has no children (no outgoing edges). -/
def IsSink (v : V) : Prop := G.children v = ∅

/-- The set of all sources. -/
def sources : Set V := { v | G.IsSource v }

/-- The set of all sinks. -/
def sinks : Set V := { v | G.IsSink v }

omit [DecidableEq V] in
theorem isSource_iff (v : V) : G.IsSource v ↔ ∀ u, ¬G.edges u v := by
  simp [IsSource, parents, Set.eq_empty_iff_forall_notMem]

omit [DecidableEq V] in
theorem isSink_iff (v : V) : G.IsSink v ↔ ∀ w, ¬G.edges v w := by
  simp [IsSink, children, Set.eq_empty_iff_forall_notMem]

/-! ## Finite Acyclic Graphs Have Sources -/

section Finite

variable [Fintype V] [DecidableRel G.edges]

omit [DecidableEq V] [DecidableRel G.edges] in
/-- In a finite acyclic graph, sources exist (assuming non-empty). -/
theorem exists_source_of_acyclic_nonempty [Nonempty V] (h : G.IsAcyclic) :
    ∃ v : V, G.IsSource v := by
  by_contra hno
  push_neg at hno
  -- Every vertex has a parent
  have hhas_parent : ∀ v, ∃ u, G.edges u v := by
    intro v
    specialize hno v
    rw [isSource_iff] at hno
    push_neg at hno
    exact hno
  -- Choose a parent function
  classical
  choose parent hparent using hhas_parent
  -- Build a sequence by iterating parent
  let chain : ℕ → V := fun n => parent^[n] (Classical.arbitrary V)
  -- By pigeonhole, any function from ℕ to a finite type must have repeated values
  -- in any interval of length > card V
  have hpigeonhole : ∃ i j, i < j ∧ j ≤ Fintype.card V ∧ chain i = chain j := by
    -- Consider chain 0, chain 1, ..., chain (card V)
    -- There are card V + 1 values, but only card V possible outputs
    -- So by pigeonhole, two must be equal
    have : ¬Function.Injective (fun n : Fin (Fintype.card V + 1) => chain n) := by
      intro hinj
      have hle := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fin] at hle
      omega
    -- Get two distinct indices with same value
    simp only [Function.Injective] at this
    push_neg at this
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, heq, hne⟩ := this
    -- Ensure i < j (swap if needed)
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact ⟨i, j, hij, Nat.lt_succ_iff.mp hj, heq⟩
    · exact absurd hij (Fin.val_ne_of_ne hne)
    · exact ⟨j, i, hij, Nat.lt_succ_iff.mp hi, heq.symm⟩
  obtain ⟨i, j, hij, _, heq⟩ := hpigeonhole
  -- chain j = chain i with i < j creates a cycle
  -- Edges go: G.edges (parent v) v, so G.edges (chain (n+1)) (chain n)
  -- From chain j, we can reach chain (j-1), ..., chain i = chain j
  -- Apply acyclicity to chain j: need ∃ u, G.edges (chain j) u ∧ G.Reachable u (chain j)
  have hj_pos : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le i) hij
  -- Edge: chain j → chain (j-1)
  have hedge_j : G.edges (chain j) (chain (j - 1)) := by
    have hkey : chain j = parent (chain (j - 1)) := by
      simp only [chain]
      have hj_eq : j = (j - 1) + 1 := by omega
      conv_lhs => rw [hj_eq]
      rw [Function.iterate_succ_apply']
    rw [hkey]
    exact hparent _
  -- Path: chain (j-1) reaches chain j (= chain i) via descending edges
  have hpath_back : G.Reachable (chain (j - 1)) (chain j) := by
    rw [← heq]  -- chain i = chain j, so rewrite to chain i
    -- Path: chain (j-1) → chain (j-2) → ... → chain i
    -- Build path by induction on the "distance" j - 1 - i
    have hle : i ≤ j - 1 := Nat.le_sub_one_of_lt hij
    -- Helper: from any k ≥ i, chain k reaches chain i
    have hreach_down : ∀ k, i ≤ k → G.Reachable (chain k) (chain i) := by
      intro k
      induction k with
      | zero =>
        intro hik
        have : i = 0 := Nat.eq_zero_of_le_zero hik
        subst this
        exact reachable_refl G _
      | succ n ih =>
        intro hik
        rcases Nat.lt_or_eq_of_le hik with hlt | heq'
        · -- i < n + 1, so i ≤ n
          have hle' : i ≤ n := Nat.lt_succ_iff.mp hlt
          have hedge_step : G.edges (chain (n + 1)) (chain n) := by
            simp only [chain, Function.iterate_succ_apply']
            exact hparent _
          exact reachable_trans G (edge_reachable G hedge_step) (ih hle')
        · -- i = n + 1
          subst heq'
          exact reachable_refl G _
    exact hreach_down (j - 1) hle
  -- Contradiction: acyclicity says no such edge+path can exist
  apply h (chain j)
  exact ⟨chain (j - 1), hedge_j, hpath_back⟩

 omit [DecidableEq V] [DecidableRel G.edges] in
 /-- Sinks exist in finite acyclic non-empty graphs. -/
 theorem exists_sink_of_acyclic_nonempty [Nonempty V] (h : G.IsAcyclic) :
    ∃ v : V, G.IsSink v := by
  have hrev := reverse_isAcyclic G h
  obtain ⟨v, hv⟩ := exists_source_of_acyclic_nonempty G.reverse hrev
  use v
  rw [IsSink, ← reverse_parents_eq_children]
  exact hv

end Finite

/-! ## Empty Graph -/

/-- The empty graph (no edges). -/
def empty : DirectedGraph V where
  edges := fun _ _ => False

omit [DecidableEq V] in
/-- The empty graph is acyclic. -/
theorem empty_isAcyclic : (empty : DirectedGraph V).IsAcyclic := by
  intro v ⟨u, hedge, _⟩
  exact hedge

omit [DecidableEq V] in
/-- Every vertex is a source in the empty graph. -/
theorem empty_all_sources (v : V) : (empty : DirectedGraph V).IsSource v := by
  simp [IsSource, parents, empty]

omit [DecidableEq V] in
/-- Every vertex is a sink in the empty graph. -/
theorem empty_all_sinks (v : V) : (empty : DirectedGraph V).IsSink v := by
  simp [IsSink, children, empty]

/-! ## Complete Graph -/

/-- The complete directed graph (all edges except self-loops). -/
 def complete : DirectedGraph V where
  edges := fun u v => u ≠ v

omit [DecidableEq V] in
/-- The complete graph on 3+ vertices has cycles. -/
theorem complete_has_cycle {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    ¬(complete : DirectedGraph V).IsAcyclic := by
  intro h
  apply h u
  use v
  constructor
  · exact huv
  · -- v reaches u via: v → w → u (using v ≠ w and w ≠ u)
    -- complete.edges x y = (x ≠ y)
    have hvw' : (complete (V := V)).edges v w := hvw
    have hwu' : (complete (V := V)).edges w u := hwu
    exact reachable_trans (complete (V := V)) (edge_reachable complete hvw') (edge_reachable complete hwu')

end DirectedGraph

end Mettapedia.ProbabilityTheory.BayesianNetworks
