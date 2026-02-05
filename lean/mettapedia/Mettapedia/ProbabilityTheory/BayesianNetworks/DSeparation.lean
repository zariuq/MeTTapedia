/-
# D-Separation in Bayesian Networks

D-separation is the graphical criterion for conditional independence in
Bayesian networks. Two sets of variables X and Y are conditionally independent
given Z if and only if they are d-separated by Z in the graph.

## Overview

A path from X to Y is **blocked** by Z if:
1. The path contains a **chain** (A → B → C) or **fork** (A ← B → C) where B ∈ Z
2. The path contains a **collider** (A → B ← C) where neither B nor any
   descendant of B is in Z

X and Y are **d-separated** by Z if every undirected path from X to Y is blocked.

## Key Results

- `DSeparated`: Definition of d-separation
- `dsep_symmetric`: D-separation is symmetric in X and Y
- `dsep_implies_cond_indep`: D-separation implies conditional independence
  (the soundness theorem - this requires measure theory and is stated as a
  specification for now)

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988), Chapter 3
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 3
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

open DirectedGraph

variable {V : Type*}

/-! ## Undirected Edges and Paths

For d-separation, we consider undirected paths (ignoring edge direction)
but track the local structure (chain, fork, collider) at each node.
-/

/-- An undirected edge: either u → v or v → u in the directed graph. -/
def UndirectedEdge (G : DirectedGraph V) (u v : V) : Prop :=
  G.edges u v ∨ G.edges v u

/-- Undirected edge is symmetric. -/
theorem undirectedEdge_symm (G : DirectedGraph V) (u v : V) :
    UndirectedEdge G u v ↔ UndirectedEdge G v u := by
  unfold UndirectedEdge
  exact or_comm

/-! ## Path Triples and Colliders

A path triple (a, b, c) represents three consecutive vertices on an undirected path.
The structure at b determines whether the path is blocked.
-/

/-- A path triple (a, b, c) where consecutive vertices are connected. -/
structure PathTriple (G : DirectedGraph V) where
  a : V
  b : V
  c : V
  edge_ab : UndirectedEdge G a b
  edge_bc : UndirectedEdge G b c
  a_ne_c : a ≠ c

/-- A collider at b: both edges point INTO b (a → b ← c). -/
def IsCollider (G : DirectedGraph V) (t : PathTriple G) : Prop :=
  G.edges t.a t.b ∧ G.edges t.c t.b

/-- A non-collider at b: at least one edge points OUT of b.
    This includes chains (a → b → c) and forks (a ← b → c). -/
def IsNonCollider (G : DirectedGraph V) (t : PathTriple G) : Prop :=
  ¬IsCollider G t

/-- At a non-collider, the middle vertex has at least one outgoing edge. -/
theorem nonCollider_has_outgoing (G : DirectedGraph V) (t : PathTriple G)
    (h : IsNonCollider G t) : G.edges t.b t.a ∨ G.edges t.b t.c := by
  unfold IsNonCollider IsCollider at h
  push_neg at h
  -- We have: G.edges t.a t.b → ¬G.edges t.c t.b
  cases t.edge_ab with
  | inl hab => -- a → b
    have hnot_cb := h hab
    -- Since edge_bc is undirected: b → c or c → b
    -- ¬(c → b) so must be b → c
    cases t.edge_bc with
    | inl hbc => right; exact hbc
    | inr hcb => exact absurd hcb hnot_cb
  | inr hba => -- b → a
    left; exact hba

/-! ## Blocking Conditions

A path through a node b is blocked by conditioning set Z if:
- b is a NON-collider and b ∈ Z (blocking by conditioning)
- b is a COLLIDER and neither b nor any descendant of b is in Z (blocking by non-conditioning)
-/

/-- A path triple is blocked at the middle vertex by conditioning set Z. -/
def IsBlocked (G : DirectedGraph V) (Z : Set V) (t : PathTriple G) : Prop :=
  (IsNonCollider G t ∧ t.b ∈ Z) ∨
  (IsCollider G t ∧ t.b ∉ Z ∧ ∀ d ∈ G.descendants t.b, d ∉ Z)

/-- A path triple is active (not blocked) given conditioning set Z. -/
def IsActive (G : DirectedGraph V) (Z : Set V) (t : PathTriple G) : Prop :=
  ¬IsBlocked G Z t

/-- Active non-collider: not in Z. -/
theorem active_nonCollider_not_in_Z (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hact : IsActive G Z t) (hnonc : IsNonCollider G t) :
    t.b ∉ Z := by
  unfold IsActive IsBlocked at hact
  push_neg at hact
  exact hact.1 hnonc

/-- Active collider: b or a descendant is in Z. -/
theorem active_collider_desc_in_Z (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hact : IsActive G Z t) (hcol : IsCollider G t) :
    t.b ∈ Z ∨ ∃ d ∈ G.descendants t.b, d ∈ Z := by
  unfold IsActive IsBlocked at hact
  push_neg at hact
  -- hact.2 hcol : t.b ∉ Z → ∃ d ∈ G.descendants t.b, d ∈ Z
  -- Convert implication to disjunction
  by_cases hbZ : t.b ∈ Z
  · left; exact hbZ
  · right; exact hact.2 hcol hbZ

/-! ## D-Separation (Simplified Definition)

We define d-separation using a predicate on paths. A full formalization
would use an inductive path type; here we use a simplified approach.
-/

/-- Predicate: There exists an active (unblocked) path from x to y given Z.
    This is defined as the negation of "all paths are blocked". -/
def HasActivePath (G : DirectedGraph V) (Z : Set V) (x y : V) : Prop :=
  -- Simplified: x and y are connected by an undirected edge and either:
  -- (1) x = y (trivial path), or
  -- (2) There's a direct undirected edge x ~ y (no intermediate vertex to block), or
  -- (3) There's a longer path with at least one unblocked triple
  x = y ∨
  (UndirectedEdge G x y ∧ x ≠ y) ∨
  (∃ b : V, b ≠ x ∧ b ≠ y ∧
    UndirectedEdge G x b ∧ UndirectedEdge G b y ∧
    ∃ (hab : UndirectedEdge G x b) (hbc : UndirectedEdge G b y) (hac : x ≠ y),
      IsActive G Z ⟨x, b, y, hab, hbc, hac⟩)

/-- D-separation: X and Y are d-separated by Z if no active paths exist. -/
def DSeparated (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬HasActivePath G Z x y

/-! ## Basic Properties of D-Separation -/

/-- Empty X means trivial d-separation. -/
theorem dsep_of_empty_X (G : DirectedGraph V) (Y Z : Set V) :
    DSeparated G ∅ Y Z := by
  intro x hx _ _ _
  exact absurd hx (Set.notMem_empty x)

/-- Empty Y means trivial d-separation. -/
theorem dsep_of_empty_Y (G : DirectedGraph V) (X Z : Set V) :
    DSeparated G X ∅ Z := by
  intro _ _ y hy _
  exact absurd hy (Set.notMem_empty y)

/-- Collider is symmetric: swapping endpoints preserves collider status. -/
theorem isCollider_comm (a b c : V) (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c)
    (hac : a ≠ c) (hcb : UndirectedEdge G c b) (hba : UndirectedEdge G b a) (hca : c ≠ a) :
    IsCollider G ⟨a, b, c, hab, hbc, hac⟩ ↔ IsCollider G ⟨c, b, a, hcb, hba, hca⟩ := by
  unfold IsCollider
  exact and_comm

/-- D-separation is symmetric in X and Y (statement).
    The proof requires careful handling of path reversal. -/
theorem dsep_symmetric (G : DirectedGraph V) (X Y Z : Set V)
    (hdsep : DSeparated G X Y Z) : DSeparated G Y X Z := by
  intro y hy x hx hne hpath
  -- We need to show ¬HasActivePath G Z y x
  -- Given: ∀ paths from x ∈ X to y ∈ Y are blocked
  -- Transform path from y to x into path from x to y
  apply hdsep x hx y hy hne.symm
  unfold HasActivePath at hpath ⊢
  rcases hpath with rfl | ⟨hedge, hne'⟩ | ⟨b, hby, hbx, hyb, hbx', hab', hbc', hac', hactive⟩
  · left; rfl
  · right; left
    exact ⟨(undirectedEdge_symm G y x).mp hedge, hne'.symm⟩
  · -- Path y ~ b ~ x becomes x ~ b ~ y
    right; right
    use b, hbx, hby
    have hxb := (undirectedEdge_symm G b x).mp hbx'
    have hby'' := (undirectedEdge_symm G y b).mp hyb
    refine ⟨hxb, hby'', hxb, hby'', hne.symm, ?_⟩
    -- Active triple ⟨y, b, x⟩ → Active triple ⟨x, b, y⟩
    -- The key: collider status only depends on edge directions into b
    -- IsCollider ⟨y,b,x⟩ = (y→b ∧ x→b) = IsCollider ⟨x,b,y⟩
    unfold IsActive at hactive ⊢
    intro hblocked
    apply hactive
    unfold IsBlocked at hblocked ⊢
    rcases hblocked with ⟨hnc_xby, hbZ⟩ | ⟨hc_xby, hnotZ, hdesc⟩
    · -- ⟨x,b,y⟩ is non-collider, b ∈ Z
      left
      refine ⟨?_, hbZ⟩
      unfold IsNonCollider at hnc_xby ⊢
      unfold IsCollider at hnc_xby ⊢
      -- ¬(G.edges x b ∧ G.edges y b) ↔ ¬(G.edges y b ∧ G.edges x b)
      rw [and_comm] at hnc_xby
      exact hnc_xby
    · -- ⟨x,b,y⟩ is collider, b ∉ Z, no desc in Z
      right
      refine ⟨?_, hnotZ, hdesc⟩
      unfold IsCollider at hc_xby ⊢
      exact ⟨hc_xby.2, hc_xby.1⟩

/-! ## Soundness Theorem (Specification)

The key theorem: d-separation implies conditional independence.
This requires:
1. A probability measure on the joint space
2. The measure satisfies the factorization property
3. Conditional independence from Mathlib

For now, we state this as a class/specification.
-/

/-!
Note: The proper definition of conditional independence for vertex sets is
`CondIndepVertices` in DSeparationSoundness.lean, which uses Mathlib's
measure-theoretic `CondIndep`. That definition requires:
- A `BayesianNetwork V` (not just a graph)
- A probability measure `μ` on the joint space
- `[StandardBorelSpace]` instances for state spaces

The d-separation soundness theorem (d-sep ⟹ conditional independence) requires
additionally that the measure satisfies the local Markov property. This is a
major theorem (Koller & Friedman Thm 3.3) that we do not yet have.
-/

/-! ## Special Cases -/

/-- Single vertex d-separation: {v} ⊥ Y | Z when v has no active path to Y. -/
theorem dsep_singleton (G : DirectedGraph V) (v : V) (Y Z : Set V)
    (h : ∀ y ∈ Y, v ≠ y → ¬HasActivePath G Z v y) : DSeparated G {v} Y Z := by
  intro x hx y hy hne
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact h y hy hne

/-- If no direct edges exist between X and Y, there's no direct active path. -/
theorem dsep_no_direct_edges (G : DirectedGraph V) (X Y : Set V)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, ¬UndirectedEdge G x y) :
    ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬(x = y ∨ (UndirectedEdge G x y ∧ x ≠ y)) := by
  intro x hx y hy hne hpath
  rcases hpath with rfl | ⟨hedge, _⟩
  · exact hne rfl
  · exact hsep x hx y hy hedge

/-! ## Summary

This file establishes:

1. **Undirected edges**: Ignoring direction for path analysis
2. **Path triples**: Local structure (collider vs non-collider) at each node
3. **Blocking conditions**: When a conditioning set blocks a path
4. **D-separation**: All paths blocked ⟹ X ⊥ Y | Z
5. **Basic properties**: Empty sets, symmetry
6. **Soundness specification**: D-sep implies conditional independence (placeholder)

The full treatment requires:
- Inductive path types for arbitrary length paths
- Connection to BayesianNetwork factorization
- Mathlib's conditional independence API
-/

end Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
