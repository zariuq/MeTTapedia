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

theorem undirectedEdge_ne_of_irrefl (G : DirectedGraph V)
    (hirr : ∀ v : V, ¬G.edges v v) {u v : V}
    (h : UndirectedEdge G u v) : u ≠ v := by
  intro huv
  subst huv
  rcases h with huv | hvu
  · exact hirr u huv
  · exact hirr u hvu

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

/-- Ancestor closure of a vertex set. -/
def ancestorClosure (G : DirectedGraph V) (S : Set V) : Set V :=
  {v | v ∈ S ∨ ∃ s ∈ S, G.Reachable v s}

/-- Collider activation criterion in ancestor form: collider node is in `Anc(Z)`. -/
def ColliderActivated (G : DirectedGraph V) (Z : Set V) (b : V) : Prop :=
  b ∈ ancestorClosure G Z

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

theorem colliderActivated_iff_self_or_desc (G : DirectedGraph V) (Z : Set V) (b : V) :
    ColliderActivated G Z b ↔ b ∈ Z ∨ ∃ d ∈ G.descendants b, d ∈ Z := by
  constructor
  · intro h
    rcases h with hbZ | ⟨z, hzZ, hreach⟩
    · exact Or.inl hbZ
    · by_cases hzb : z = b
      · subst hzb
        exact Or.inl hzZ
      · exact Or.inr ⟨z, ⟨hreach, hzb⟩, hzZ⟩
  · intro h
    rcases h with hbZ | ⟨d, hdDesc, hdZ⟩
    · exact Or.inl hbZ
    · exact Or.inr ⟨d, hdZ, hdDesc.1⟩

theorem active_collider_activated (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hact : IsActive G Z t) (hcol : IsCollider G t) :
    ColliderActivated G Z t.b := by
  exact (colliderActivated_iff_self_or_desc G Z t.b).2
    (active_collider_desc_in_Z G Z t hact hcol)

theorem isActive_of_collider_and_activated (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hcol : IsCollider G t)
    (hActivated : ColliderActivated G Z t.b) :
    IsActive G Z t := by
  unfold IsActive IsBlocked
  intro hblocked
  rcases hblocked with ⟨hnonc, _⟩ | ⟨hcol', hbNotInZ, hdescNotInZ⟩
  · exact hnonc hcol
  · have hdescOrSelf : t.b ∈ Z ∨ ∃ d ∈ G.descendants t.b, d ∈ Z :=
      (colliderActivated_iff_self_or_desc G Z t.b).1 hActivated
    rcases hdescOrSelf with hbInZ | ⟨d, hdDesc, hdInZ⟩
    · exact hbNotInZ hbInZ
    · exact (hdescNotInZ d hdDesc) hdInZ

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

/-! ## D-Separation (Full Trail-Based Definition)

The placeholder `HasActivePath` above only inspects very short paths.
The definitions in this section are the proper arbitrary-length notion:

- `IsTrail` tracks undirected adjacency along a vertex list.
- `HasActiveTrail` packages endpoints + trail + activation.
- `DSeparatedFull` quantifies over all endpoints in X,Y.
-/

/-- A vertex list is an undirected trail if each consecutive pair is adjacent. -/
inductive IsTrail (G : DirectedGraph V) : List V → Prop
  | single (v : V) : IsTrail G [v]
  | cons {u v : V} {rest : List V}
      (hEdge : UndirectedEdge G u v)
      (hTail : IsTrail G (v :: rest)) :
      IsTrail G (u :: v :: rest)

/--
`ActiveTrail G Z p` is the proof-relevant trail predicate:
each extension step carries an undirected edge witness, and each internal node
carries a proof that the corresponding triple is active.
-/
inductive ActiveTrail (G : DirectedGraph V) (Z : Set V) : List V → Prop
  | single (v : V) : ActiveTrail G Z [v]
  | two {u v : V} (hEdge : UndirectedEdge G u v) : ActiveTrail G Z [u, v]
  | cons {a b c : V} {rest : List V}
      (hab : UndirectedEdge G a b)
      (hbc : UndirectedEdge G b c)
      (hac : a ≠ c)
      (hAct : IsActive G Z ⟨a, b, c, hab, hbc, hac⟩)
      (hTail : ActiveTrail G Z (b :: c :: rest)) :
      ActiveTrail G Z (a :: b :: c :: rest)

/-- Endpoints of a non-empty path list. -/
def PathEndpoints : List V → Option (V × V)
  | [] => none
  | [v] => some (v, v)
  | v :: rest =>
      match rest with
      | [] => some (v, v)
      | h :: t => some (v, (h :: t).getLast (by simp))

/-- Existence of an arbitrary-length active trail from `x` to `y` given `Z`. -/
def HasActiveTrail (G : DirectedGraph V) (Z : Set V) (x y : V) : Prop :=
  ∃ p : List V, p ≠ [] ∧
    PathEndpoints p = some (x, y) ∧
    ActiveTrail G Z p

/-- Full d-separation: no active trails between X and Y given Z. -/
def DSeparatedFull (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬HasActiveTrail G Z x y

theorem activeTrail_isTrail (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V}, ActiveTrail G Z p → IsTrail G p
  | _, ActiveTrail.single v => IsTrail.single (G := G) v
  | _, ActiveTrail.two hEdge => IsTrail.cons (G := G) hEdge (IsTrail.single (G := G) _)
  | _, ActiveTrail.cons hab hbc _ _ hTail =>
      IsTrail.cons (G := G) hab (activeTrail_isTrail G Z hTail)

theorem hasActiveTrail_hasTrail (G : DirectedGraph V) (Z : Set V) (x y : V)
    (h : HasActiveTrail G Z x y) :
    ∃ p : List V, p ≠ [] ∧ PathEndpoints p = some (x, y) ∧ IsTrail G p := by
  rcases h with ⟨p, hp, hEnds, hAct⟩
  exact ⟨p, hp, hEnds, activeTrail_isTrail G Z hAct⟩

/-- Any legacy short active path is a full active trail. -/
theorem hasActiveTrail_of_hasActivePath
    (G : DirectedGraph V) (Z : Set V) (x y : V) :
    HasActivePath G Z x y → HasActiveTrail G Z x y := by
  intro h
  unfold HasActivePath at h
  rcases h with rfl | ⟨hedge, _hne⟩ | ⟨b, hbx, hby, hxb, hby', hab, hbc, hxy, hAct⟩
  · refine ⟨[x], by simp, ?_, ActiveTrail.single x⟩
    simp [PathEndpoints]
  · refine ⟨[x, y], by simp, ?_, ActiveTrail.two hedge⟩
    simp [PathEndpoints]
  · refine ⟨[x, b, y], by simp, ?_, ?_⟩
    · simp [PathEndpoints]
    · exact ActiveTrail.cons hab hbc hxy hAct (ActiveTrail.two hby')

/-- Full d-separation implies legacy d-separation. -/
theorem dsep_of_dsepFull (G : DirectedGraph V) (X Y Z : Set V) :
    DSeparatedFull G X Y Z → DSeparated G X Y Z := by
  intro hfull x hx y hy hxy hshort
  exact hfull x hx y hy hxy (hasActiveTrail_of_hasActivePath G Z x y hshort)

/-- Empty `X` is trivially full-d-separated from any `Y` given `Z`. -/
theorem dsepFull_of_empty_X (G : DirectedGraph V) (Y Z : Set V) :
    DSeparatedFull G ∅ Y Z := by
  intro x hx _ _ _
  exact absurd hx (Set.notMem_empty x)

/-- Empty `Y` is trivially full-d-separated from any `X` given `Z`. -/
theorem dsepFull_of_empty_Y (G : DirectedGraph V) (X Z : Set V) :
    DSeparatedFull G X ∅ Z := by
  intro _ _ y hy _
  exact absurd hy (Set.notMem_empty y)

/-! ## Moralized-Ancestral Graph (bridge scaffolding)

This section provides the graph objects used by the standard d-separation
equivalence proof:

1. Restrict to ancestors of `X ∪ Y ∪ Z`.
2. Moralize (drop direction + connect co-parents).
3. Reduce d-separation to ordinary graph separation in the moralized graph.
-/

/-- Directed induced subgraph on a vertex set `W`. -/
def inducedSubgraph (G : DirectedGraph V) (W : Set V) : DirectedGraph V where
  edges u v := W u ∧ W v ∧ G.edges u v

/-- Moralized undirected edge relation for a DAG (on a fixed vertex universe). -/
def moralUndirectedEdge (G : DirectedGraph V) (u v : V) : Prop :=
  And (u = v -> False)
    (Or (UndirectedEdge G u v) (Exists fun c : V => And (G.edges u c) (G.edges v c)))

/-- Moralized graph represented as a symmetric directed graph. -/
def moralGraph (G : DirectedGraph V) : DirectedGraph V where
  edges u v := moralUndirectedEdge G u v

/-- A path avoids `Z` internally if all interior vertices are outside `Z`. -/
def PathAvoidsInternals (Z : Set V) : List V -> Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | _ :: b :: rest => And (b ∈ Z -> False) (PathAvoidsInternals Z (b :: rest))

theorem pathAvoidsInternals_tail {Z : Set V} :
    ∀ {a b : V} {rest : List V},
      PathAvoidsInternals Z (a :: b :: rest) →
      PathAvoidsInternals Z (b :: rest)
  | _, _, [], h => by simpa [PathAvoidsInternals] using h
  | _, _, _ :: _, h => And.right h

theorem pathEndpoints_singleton (v : V) :
    PathEndpoints ([v] : List V) = some (v, v) := by
  simp [PathEndpoints]

theorem pathEndpoints_pair (u v : V) :
    PathEndpoints ([u, v] : List V) = some (u, v) := by
  simp [PathEndpoints]

theorem pathEndpoints_cons_cons (a b : V) (rest : List V) :
    PathEndpoints (a :: b :: rest) = some (a, (b :: rest).getLast (by simp)) := by
  simp [PathEndpoints]

/-- All vertices appearing in a path lie in `W`. -/
def PathVerticesIn (W : Set V) : List V → Prop
  | [] => True
  | v :: rest => W v ∧ PathVerticesIn W rest

theorem pathVerticesIn_append {W : Set V} :
    ∀ {p q : List V}, PathVerticesIn W p → PathVerticesIn W q → PathVerticesIn W (p ++ q)
  | [], q, _, hq => hq
  | v :: rest, q, ⟨hv, hrest⟩, hq =>
      ⟨hv, pathVerticesIn_append hrest hq⟩

/-- Separation in the moralized graph (scaffold definition). -/
def SeparatedInMoral (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  forall x, x ∈ X -> forall y, y ∈ Y -> x ≠ y ->
    Not (Exists fun p : List V =>
      And (p ≠ []) (And (PathEndpoints p = some (x, y))
        (And (IsTrail (moralGraph G) p) (PathAvoidsInternals Z p))))

/-- Relevant vertices for d-separation: ancestors of X ∪ Y ∪ Z. -/
def relevantVertices (G : DirectedGraph V) (X Y Z : Set V) : Set V :=
  ancestorClosure G (X ∪ Y ∪ Z)

/-- Moralized ancestral graph used by the global-Markov separation criterion. -/
def moralAncestralGraph (G : DirectedGraph V) (X Y Z : Set V) : DirectedGraph V :=
  moralGraph (inducedSubgraph G (relevantVertices G X Y Z))

/--
Separation in the moralized ancestral graph:
there is no trail in the moralized ancestral graph from X to Y whose
internal vertices avoid Z.
-/
def SeparatedInMoralAncestral (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  forall x, x ∈ X -> forall y, y ∈ Y -> x ≠ y ->
    Not (Exists fun p : List V =>
      And (p ≠ []) (And (PathEndpoints p = some (x, y))
        (And (IsTrail (moralAncestralGraph G X Y Z) p) (PathAvoidsInternals Z p))))

theorem moralUndirectedEdge_symm (G : DirectedGraph V) (u v : V) :
    moralUndirectedEdge G u v <-> moralUndirectedEdge G v u := by
  constructor <;> intro h
  · rcases h with ⟨hne, huv | ⟨c, huc, hvc⟩⟩
    · exact ⟨fun hEq => hne hEq.symm, Or.inl ((undirectedEdge_symm G u v).1 huv)⟩
    · exact ⟨fun hEq => hne hEq.symm, Or.inr ⟨c, hvc, huc⟩⟩
  · rcases h with ⟨hne, huv | ⟨c, hvc, huc⟩⟩
    · exact ⟨fun hEq => hne hEq.symm, Or.inl ((undirectedEdge_symm G v u).1 huv)⟩
    · exact ⟨fun hEq => hne hEq.symm, Or.inr ⟨c, huc, hvc⟩⟩

theorem ancestorClosure_mono (G : DirectedGraph V) {S T : Set V}
    (hST : S ⊆ T) : ancestorClosure G S ⊆ ancestorClosure G T := by
  intro v hv
  rcases hv with hs | ⟨s, hs, hreach⟩
  · exact Or.inl (hST hs)
  · exact Or.inr ⟨s, hST hs, hreach⟩

theorem inducedSubgraph_edge_of_edge (G : DirectedGraph V) (W : Set V) {u v : V}
    (hu : W u) (hv : W v) (h : G.edges u v) :
    (inducedSubgraph G W).edges u v := by
  exact ⟨hu, hv, h⟩

theorem inducedSubgraph_univ (G : DirectedGraph V) :
    inducedSubgraph G (Set.univ : Set V) = G := by
  ext u v
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨trivial, trivial, h⟩

theorem pathVerticesIn_mono {W W' : Set V} (hWW' : W ⊆ W') :
    ∀ {p : List V}, PathVerticesIn W p → PathVerticesIn W' p
  | [], _ => trivial
  | v :: rest, ⟨hv, hrest⟩ =>
      ⟨hWW' hv, pathVerticesIn_mono hWW' hrest⟩

theorem pathVerticesIn_of_isTrail_induced_of_head
    (G : DirectedGraph V) (W : Set V) :
    ∀ {x : V} {rest : List V},
      W x →
      IsTrail (inducedSubgraph G W) (x :: rest) →
      PathVerticesIn W (x :: rest)
  | x, [], hx, IsTrail.single _ => ⟨hx, trivial⟩
  | x, v :: rs, hx, IsTrail.cons hEdge hTail => by
      have hv : W v := by
        rcases hEdge with huv | hvu
        · exact huv.2.1
        · exact hvu.1
      exact ⟨hx,
        pathVerticesIn_of_isTrail_induced_of_head G W hv hTail⟩

theorem relevantVertices_contains (G : DirectedGraph V) (X Y Z : Set V) :
    X ⊆ relevantVertices G X Y Z ∧
    Y ⊆ relevantVertices G X Y Z ∧
    Z ⊆ relevantVertices G X Y Z := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl (by simp [hx])
  · intro y hy
    exact Or.inl (by simp [hy])
  · intro z hz
    exact Or.inl (by simp [hz])

theorem isTrail_of_isTrail_inducedSubgraph (G : DirectedGraph V) (W : Set V) :
    ∀ {p : List V}, IsTrail (inducedSubgraph G W) p → IsTrail G p
  | _, IsTrail.single v => IsTrail.single (G := G) v
  | _, IsTrail.cons hEdge hTail =>
      IsTrail.cons (G := G)
        (by
          rcases hEdge with huv | hvu
          · exact Or.inl huv.2.2
          · exact Or.inr hvu.2.2)
        (isTrail_of_isTrail_inducedSubgraph G W hTail)

theorem isTrail_inducedSubgraph_of_isTrail_and_vertices (G : DirectedGraph V) (W : Set V) :
    ∀ {p : List V}, IsTrail G p → PathVerticesIn W p → IsTrail (inducedSubgraph G W) p
  | [v], IsTrail.single _, ⟨hv, _⟩ =>
      IsTrail.single (G := inducedSubgraph G W) v
  | u :: v :: rest, IsTrail.cons hEdge hTail, ⟨hu, ⟨hv, hrest⟩⟩ =>
      IsTrail.cons (G := inducedSubgraph G W)
        (by
          rcases hEdge with huv | hvu
          · exact Or.inl ⟨hu, hv, huv⟩
          · exact Or.inr ⟨hv, hu, hvu⟩)
        (isTrail_inducedSubgraph_of_isTrail_and_vertices G W hTail ⟨hv, hrest⟩)

theorem moralAncestral_eq_moral_of_relevant_univ
    (G : DirectedGraph V) (X Y Z : Set V)
    (hrel : relevantVertices G X Y Z = (Set.univ : Set V)) :
    moralAncestralGraph G X Y Z = moralGraph G := by
  simp [moralAncestralGraph, moralGraph, hrel, inducedSubgraph_univ]

theorem separatedInMoralAncestral_iff_separatedInMoral_of_relevant_univ
    (G : DirectedGraph V) (X Y Z : Set V)
    (hrel : relevantVertices G X Y Z = (Set.univ : Set V)) :
    SeparatedInMoralAncestral G X Y Z ↔ SeparatedInMoral G X Y Z := by
  simp [SeparatedInMoralAncestral, SeparatedInMoral,
    moralAncestral_eq_moral_of_relevant_univ (G := G) (X := X) (Y := Y) (Z := Z) hrel]

theorem undirectedEdge_in_moral_of_irrefl (G : DirectedGraph V)
    (hirr : ∀ v : V, ¬G.edges v v) {u v : V}
    (h : UndirectedEdge G u v) :
    UndirectedEdge (moralGraph G) u v := by
  left
  exact ⟨undirectedEdge_ne_of_irrefl G hirr h, Or.inl h⟩

theorem activeTrail_isTrail_moral_of_irrefl (G : DirectedGraph V) (Z : Set V)
    (hirr : ∀ v : V, ¬G.edges v v) :
    ∀ {p : List V}, ActiveTrail G Z p → IsTrail (moralGraph G) p
  | _, ActiveTrail.single v => IsTrail.single (G := moralGraph G) v
  | _, ActiveTrail.two hEdge =>
      IsTrail.cons (G := moralGraph G)
        (undirectedEdge_in_moral_of_irrefl G hirr hEdge)
        (IsTrail.single (G := moralGraph G) _)
  | _, ActiveTrail.cons hab hbc _ _ hTail =>
      IsTrail.cons (G := moralGraph G)
        (undirectedEdge_in_moral_of_irrefl G hirr hab)
        (activeTrail_isTrail_moral_of_irrefl G Z hirr hTail)

theorem moralUndirectedEdge_of_induced (G : DirectedGraph V) (W : Set V) {u v : V} :
    moralUndirectedEdge (inducedSubgraph G W) u v → moralUndirectedEdge G u v := by
  intro h
  rcases h with ⟨hne, huv | ⟨c, huc, hvc⟩⟩
  · refine ⟨hne, ?_⟩
    exact Or.inl (by
      rcases huv with huv | hvu
      · exact Or.inl huv.2.2
      · exact Or.inr hvu.2.2)
  · refine ⟨hne, Or.inr ?_⟩
    exact ⟨c, huc.2.2, hvc.2.2⟩

theorem vertices_of_moralUndirectedEdge_induced (G : DirectedGraph V) (W : Set V) {u v : V} :
    moralUndirectedEdge (inducedSubgraph G W) u v → (W u ∧ W v) := by
  intro h
  rcases h with ⟨_, huv | ⟨c, huc, hvc⟩⟩
  · rcases huv with huv | hvu
    · exact ⟨huv.1, huv.2.1⟩
    · exact ⟨hvu.2.1, hvu.1⟩
  · exact ⟨huc.1, hvc.1⟩

theorem isTrail_moral_of_isTrail_moralAncestral (G : DirectedGraph V) (X Y Z : Set V) :
    ∀ {p : List V}, IsTrail (moralAncestralGraph G X Y Z) p → IsTrail (moralGraph G) p
  | _, IsTrail.single v => IsTrail.single (G := moralGraph G) v
  | _, IsTrail.cons hEdge hTail =>
      IsTrail.cons (G := moralGraph G)
        (by
          rcases hEdge with huv | hvu
          · exact Or.inl (moralUndirectedEdge_of_induced G (relevantVertices G X Y Z) huv)
          · exact Or.inr (moralUndirectedEdge_of_induced G (relevantVertices G X Y Z) hvu))
        (isTrail_moral_of_isTrail_moralAncestral G X Y Z hTail)

theorem pathVerticesIn_of_isTrail_moralAncestral_of_head
    (G : DirectedGraph V) (X Y Z : Set V) :
    ∀ {x : V} {rest : List V},
      relevantVertices G X Y Z x →
      IsTrail (moralAncestralGraph G X Y Z) (x :: rest) →
      PathVerticesIn (relevantVertices G X Y Z) (x :: rest)
  | x, [], hx, IsTrail.single _ => ⟨hx, trivial⟩
  | x, v :: rs, hx, IsTrail.cons hEdge hTail => by
      have hv : relevantVertices G X Y Z v := by
        rcases hEdge with huv | hvu
        · exact (vertices_of_moralUndirectedEdge_induced
            (G := G) (W := relevantVertices G X Y Z) huv).2
        · exact (vertices_of_moralUndirectedEdge_induced
            (G := G) (W := relevantVertices G X Y Z) hvu).1
      exact ⟨hx, pathVerticesIn_of_isTrail_moralAncestral_of_head G X Y Z hv hTail⟩

/-- Any moralized edge can be expanded to a short undirected trail in the original graph. -/
theorem exists_shortTrail_of_moralUndirectedEdge (G : DirectedGraph V) {u v : V}
    (h : moralUndirectedEdge G u v) :
    ∃ p : List V, PathEndpoints p = some (u, v) ∧ IsTrail G p ∧ p.length ≤ 3 := by
  rcases h with ⟨_, huv | ⟨c, huc, hvc⟩⟩
  · refine ⟨[u, v], by simp [PathEndpoints], ?_, by simp⟩
    exact IsTrail.cons (G := G) huv (IsTrail.single (G := G) _)
  · refine ⟨[u, c, v], by simp [PathEndpoints], ?_, by simp⟩
    refine IsTrail.cons (G := G) ?_ (IsTrail.cons (G := G) ?_ (IsTrail.single (G := G) _))
    · exact Or.inl huc
    · exact Or.inr hvc

/--
Single-step realization: a moralized edge induces an active trail in the original graph,
assuming spouse-edge colliders are activated.
-/
theorem hasActiveTrail_of_moralUndirectedEdge_of_spouseActivated
    (G : DirectedGraph V) (Z : Set V) {u v : V}
    (h : moralUndirectedEdge G u v)
    (hSpouseActivated :
      ∀ {a b c : V}, a ≠ b → G.edges a c → G.edges b c → ColliderActivated G Z c) :
    HasActiveTrail G Z u v := by
  rcases h with ⟨hne, huv | ⟨c, huc, hvc⟩⟩
  · refine ⟨[u, v], by simp, by simp [PathEndpoints], ActiveTrail.two ?_⟩
    exact huv
  · have huv : UndirectedEdge G u c := Or.inl huc
    have hcv : UndirectedEdge G c v := Or.inr hvc
    have hcol : IsCollider G ⟨u, c, v, huv, hcv, hne⟩ := ⟨huc, hvc⟩
    have hAct : IsActive G Z ⟨u, c, v, huv, hcv, hne⟩ :=
      isActive_of_collider_and_activated G Z ⟨u, c, v, huv, hcv, hne⟩
        hcol (hSpouseActivated hne huc hvc)
    refine ⟨[u, c, v], by simp, by simp [PathEndpoints], ?_⟩
    exact ActiveTrail.cons huv hcv hne hAct (ActiveTrail.two hcv)

theorem undirectedEdge_in_moralAncestral_of_vertices
    (G : DirectedGraph V) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬G.edges v v)
    {u v : V}
    (hu : relevantVertices G X Y Z u)
    (hv : relevantVertices G X Y Z v)
    (h : UndirectedEdge G u v) :
    UndirectedEdge (moralAncestralGraph G X Y Z) u v := by
  let W := relevantVertices G X Y Z
  have hne : u ≠ v := undirectedEdge_ne_of_irrefl G hirr h
  have hInd : UndirectedEdge (inducedSubgraph G W) u v := by
    rcases h with huv | hvu
    · exact Or.inl ⟨hu, hv, huv⟩
    · exact Or.inr ⟨hv, hu, hvu⟩
  refine Or.inl ?_
  exact ⟨hne, Or.inl hInd⟩

theorem isTrail_moralAncestral_of_isTrail_and_vertices
    (G : DirectedGraph V) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬G.edges v v) :
    ∀ {p : List V},
      IsTrail G p →
      PathVerticesIn (relevantVertices G X Y Z) p →
      IsTrail (moralAncestralGraph G X Y Z) p
  | [v], IsTrail.single _, ⟨_, _⟩ =>
      IsTrail.single (G := moralAncestralGraph G X Y Z) v
  | u :: v :: rest, IsTrail.cons hEdge hTail, ⟨hu, ⟨hv, hrest⟩⟩ =>
      IsTrail.cons (G := moralAncestralGraph G X Y Z)
        (undirectedEdge_in_moralAncestral_of_vertices G X Y Z hirr hu hv hEdge)
        (isTrail_moralAncestral_of_isTrail_and_vertices G X Y Z hirr hTail ⟨hv, hrest⟩)

/--
Modular bridge step for the global theorem:
if every active trail from `X` to `Y` is known to (1) stay in relevant vertices
and (2) avoid `Z` internally, then separation in the moral-ancestral graph
implies full d-separation.
-/
theorem dsepFull_of_separatedInMoralAncestral_of_activeTrail_obligations
    (G : DirectedGraph V) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬G.edges v v)
    (hSep : SeparatedInMoralAncestral G X Y Z)
    (hVertices :
      ∀ {x y : V} {p : List V},
        PathEndpoints p = some (x, y) →
        ActiveTrail G Z p →
        PathVerticesIn (relevantVertices G X Y Z) p)
    (hAvoid :
      ∀ {x y : V} {p : List V},
        PathEndpoints p = some (x, y) →
        ActiveTrail G Z p →
        PathAvoidsInternals Z p) :
    DSeparatedFull G X Y Z := by
  intro x hx y hy hxy hAct
  rcases hAct with ⟨p, hpne, hEnds, hAT⟩
  have hTrail : IsTrail G p := activeTrail_isTrail G Z hAT
  have hV : PathVerticesIn (relevantVertices G X Y Z) p := hVertices hEnds hAT
  have hMA : IsTrail (moralAncestralGraph G X Y Z) p :=
    isTrail_moralAncestral_of_isTrail_and_vertices G X Y Z hirr hTrail hV
  have hA : PathAvoidsInternals Z p := hAvoid hEnds hAT
  exact hSep x hx y hy hxy ⟨p, hpne, hEnds, hMA, hA⟩

/--
Correct bridge shape for the forward global-Markov direction:
each active trail may be rewritten to a different moral-ancestral trail
with the same endpoints and internal-avoidance condition.
-/
theorem dsepFull_of_separatedInMoralAncestral_of_activeTrail_transform
    (G : DirectedGraph V) (X Y Z : Set V)
    (hSep : SeparatedInMoralAncestral G X Y Z)
    (hTransform :
      ∀ {x y : V} {p : List V},
        x ∈ X → y ∈ Y →
        p ≠ [] →
        PathEndpoints p = some (x, y) →
        ActiveTrail G Z p →
        ∃ p' : List V,
          p' ≠ [] ∧
          PathEndpoints p' = some (x, y) ∧
          IsTrail (moralAncestralGraph G X Y Z) p' ∧
          PathAvoidsInternals Z p') :
    DSeparatedFull G X Y Z := by
  intro x hx y hy hxy hAct
  rcases hAct with ⟨p, hpne, hEnds, hAT⟩
  rcases hTransform hx hy hpne hEnds hAT with ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩
  exact hSep x hx y hy hxy ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩

/--
Correct bridge shape for the reverse global-Markov direction:
each moral-ancestral trail avoiding `Z` may be rewritten to an active trail
with the same endpoints.
-/
theorem separatedInMoralAncestral_of_dsepFull_of_moralTrail_transform
    (G : DirectedGraph V) (X Y Z : Set V)
    (hdsep : DSeparatedFull G X Y Z)
    (hTransform :
      ∀ {x y : V} {p : List V},
        p ≠ [] →
        PathEndpoints p = some (x, y) →
        IsTrail (moralAncestralGraph G X Y Z) p →
        PathAvoidsInternals Z p →
        ∃ p' : List V,
          p' ≠ [] ∧
          PathEndpoints p' = some (x, y) ∧
          ActiveTrail G Z p') :
    SeparatedInMoralAncestral G X Y Z := by
  intro x hx y hy hxy hSepTrail
  rcases hSepTrail with ⟨p, hpne, hEnds, hTrail, hAvoid⟩
  rcases hTransform hpne hEnds hTrail hAvoid with ⟨p', hp'ne, hEnds', hAct'⟩
  exact hdsep x hx y hy hxy ⟨p', hp'ne, hEnds', hAct'⟩

/--
Global equivalence from explicit path-transform obligations.
This packages the remaining proof work for `DSeparatedFull ↔ SeparatedInMoralAncestral`
into two endpoint-preserving transformation lemmas.
-/
theorem dsepFull_iff_separatedInMoralAncestral_of_transforms
    (G : DirectedGraph V) (X Y Z : Set V)
    (hATtoMoral :
      ∀ {x y : V} {p : List V},
        x ∈ X → y ∈ Y →
        p ≠ [] →
        PathEndpoints p = some (x, y) →
        ActiveTrail G Z p →
        ∃ p' : List V,
          p' ≠ [] ∧
          PathEndpoints p' = some (x, y) ∧
          IsTrail (moralAncestralGraph G X Y Z) p' ∧
          PathAvoidsInternals Z p')
    (hMoralToAT :
      ∀ {x y : V} {p : List V},
        p ≠ [] →
        PathEndpoints p = some (x, y) →
        IsTrail (moralAncestralGraph G X Y Z) p →
        PathAvoidsInternals Z p →
        ∃ p' : List V,
          p' ≠ [] ∧
          PathEndpoints p' = some (x, y) ∧
          ActiveTrail G Z p') :
    DSeparatedFull G X Y Z ↔ SeparatedInMoralAncestral G X Y Z := by
  constructor
  · intro hdsep
    exact separatedInMoralAncestral_of_dsepFull_of_moralTrail_transform
      G X Y Z hdsep hMoralToAT
  · intro hSep
    exact dsepFull_of_separatedInMoralAncestral_of_activeTrail_transform
      G X Y Z hSep hATtoMoral

/--
Dual modular bridge step for the global theorem:
if every moral-ancestral trail that avoids `Z` can be converted to an active trail,
then full d-separation implies separation in the moral-ancestral graph.
-/
theorem separatedInMoralAncestral_of_dsepFull_of_moralTrail_to_activeTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    (hdsep : DSeparatedFull G X Y Z)
    (hLift :
      ∀ {x y : V} {p : List V},
        p ≠ [] →
        PathEndpoints p = some (x, y) →
        IsTrail (moralAncestralGraph G X Y Z) p →
        PathAvoidsInternals Z p →
        HasActiveTrail G Z x y) :
    SeparatedInMoralAncestral G X Y Z := by
  intro x hx y hy hxy hSepTrail
  rcases hSepTrail with ⟨p, hpne, hEnds, hTrail, hAvoid⟩
  exact hdsep x hx y hy hxy (hLift hpne hEnds hTrail hAvoid)

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

/-! ## Phase 1: Active Trail → Moral-Ancestral Trail (hATtoMoral)

Given an active trail in G from x to y, produce a trail in the moralized
ancestral graph with the same endpoints that avoids Z internally.

**Strategy — Collider Compression**: An active trail can pass through Z at
collider nodes (a→b←c where b∈Z). The moral trail must avoid Z internally.
When b∈Z is a collider with edges a→b and c→b, a and c share child b,
creating a moral spouse edge a—c. Replace `...a,b,c...` with `...a,c...`.
-/

/-- At an active triple, b is either a collider or not in Z. -/
theorem activeTrail_internal_collider_or_notInZ
    (G : DirectedGraph V) (Z : Set V) {a b c : V}
    (hab : UndirectedEdge G a b)
    (hbc : UndirectedEdge G b c)
    (hac : a ≠ c)
    (hAct : IsActive G Z ⟨a, b, c, hab, hbc, hac⟩) :
    IsCollider G ⟨a, b, c, hab, hbc, hac⟩ ∨ b ∉ Z := by
  by_cases hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩
  · left; exact hcol
  · right; exact active_nonCollider_not_in_Z G Z ⟨a, b, c, hab, hbc, hac⟩ hAct hcol

/-- At a collider a→b←c, there is a moral spouse edge between a and c. -/
theorem moralUndirectedEdge_of_collider (G : DirectedGraph V)
    {a b c : V} (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c) (hac : a ≠ c)
    (hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩) :
    moralUndirectedEdge G a c := by
  exact ⟨hac, Or.inr ⟨b, hcol.1, hcol.2⟩⟩

/-- Spouse edge in the induced subgraph when vertices are relevant. -/
theorem moralUndirectedEdge_induced_of_collider
    (G : DirectedGraph V) (W : Set V)
    {a b c : V}
    (ha : W a) (hb : W b) (hc : W c)
    (hcol_ab : G.edges a b) (hcol_cb : G.edges c b)
    (hac : a ≠ c) :
    moralUndirectedEdge (inducedSubgraph G W) a c := by
  exact ⟨hac, Or.inr ⟨b, ⟨ha, hb, hcol_ab⟩, ⟨hc, hb, hcol_cb⟩⟩⟩

/-- In an acyclic graph, consecutive internal vertices on an active trail
    cannot both be colliders (would create a 2-cycle). -/
theorem no_consecutive_colliders_in_dag
    (G : DirectedGraph V) (Z : Set V)
    (hacyclic : G.IsAcyclic)
    {a b c d : V}
    (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c)
    (hcd : UndirectedEdge G c d)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hcol_b : IsCollider G ⟨a, b, c, hab, hbc, hac⟩)
    (hcol_c : IsCollider G ⟨b, c, d, hbc, hcd, hbd⟩) : False :=
  G.isAcyclic_no_two_cycle hacyclic b c hcol_c.1 hcol_b.2

/-- After a collider-in-Z on an active trail in a DAG, the next vertex
    cannot be in Z (it would need to be a collider, creating a 2-cycle). -/
theorem next_after_collider_notInZ
    (G : DirectedGraph V) (Z : Set V)
    (hacyclic : G.IsAcyclic)
    {a b c d : V} {rest : List V}
    (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c) (hac : a ≠ c)
    (hcol_b : IsCollider G ⟨a, b, c, hab, hbc, hac⟩)
    (hTail : ActiveTrail G Z (b :: c :: d :: rest)) :
    c ∉ Z := by
  cases hTail with
  | cons hbc' hcd' hbd' hAct_c hTail' =>
    rcases activeTrail_internal_collider_or_notInZ G Z hbc' hcd' hbd' hAct_c with hcol_c | hnotZ
    · exact absurd (no_consecutive_colliders_in_dag G Z hacyclic hab hbc hcd'
        hac hbd' hcol_b hcol_c) (by tauto)
    · exact hnotZ

/-- Spouse edge in moralAncestralGraph from a collider when all vertices relevant. -/
theorem spouseEdge_in_moralAncestral
    (G : DirectedGraph V) (X Y Z : Set V)
    {a b c : V}
    (ha : relevantVertices G X Y Z a)
    (hb : relevantVertices G X Y Z b)
    (hc : relevantVertices G X Y Z c)
    (hcol_ab : G.edges a b) (hcol_cb : G.edges c b)
    (hac : a ≠ c) :
    UndirectedEdge (moralAncestralGraph G X Y Z) a c := by
  left
  exact moralUndirectedEdge_induced_of_collider G (relevantVertices G X Y Z)
    ha hb hc hcol_ab hcol_cb hac

theorem endpoint_in_relevant_X (G : DirectedGraph V) (X Y Z : Set V)
    {x : V} (hx : x ∈ X) : x ∈ relevantVertices G X Y Z :=
  (relevantVertices_contains G X Y Z).1 hx

theorem endpoint_in_relevant_Y (G : DirectedGraph V) (X Y Z : Set V)
    {y : V} (hy : y ∈ Y) : y ∈ relevantVertices G X Y Z :=
  (relevantVertices_contains G X Y Z).2.1 hy

theorem z_in_relevant (G : DirectedGraph V) (X Y Z : Set V)
    {z : V} (hz : z ∈ Z) : z ∈ relevantVertices G X Y Z :=
  (relevantVertices_contains G X Y Z).2.2 hz

/-- If u → v (directed edge) and v ∈ Anc(S), then u ∈ Anc(S). -/
theorem edge_source_relevant (G : DirectedGraph V) (X Y Z : Set V)
    {u v : V} (hv : v ∈ relevantVertices G X Y Z) (h : G.edges u v) :
    u ∈ relevantVertices G X Y Z := by
  unfold relevantVertices ancestorClosure at hv ⊢
  rcases hv with hvS | ⟨s, hsS, hreach⟩
  · exact Or.inr ⟨v, hvS, DirectedGraph.edge_reachable G h⟩
  · exact Or.inr ⟨s, hsS, G.reachable_trans (DirectedGraph.edge_reachable G h) hreach⟩

/-- ColliderActivated implies membership in relevantVertices
    (since Anc(Z) ⊆ Anc(X∪Y∪Z)). -/
theorem colliderActivated_in_relevant (G : DirectedGraph V) (X Y Z : Set V)
    {b : V} (h : ColliderActivated G Z b) :
    b ∈ relevantVertices G X Y Z := by
  unfold ColliderActivated ancestorClosure at h
  unfold relevantVertices ancestorClosure
  rcases h with hbZ | ⟨z, hzZ, hreach⟩
  · exact Or.inl (by simp [hbZ])
  · exact Or.inr ⟨z, by simp [hzZ], hreach⟩

/-- In a DAG, if b starts a rightward directed chain (G.edges b c) on an active
    trail and the last vertex is relevant, then b is relevant.
    By DAG acyclicity, the chain proceeds rightward without 2-cycles, reaching
    a collider (in Anc(Z)) or the last vertex within finite steps. -/
private theorem rightChainRelevant
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    (n : ℕ) :
    ∀ {b c : V} {rest : List V},
      rest.length ≤ n →
      ActiveTrail G Z (b :: c :: rest) →
      G.edges b c →
      (∀ v, (b :: c :: rest).getLast? = some v → v ∈ relevantVertices G X Y Z) →
      b ∈ relevantVertices G X Y Z := by
  induction n with
  | zero =>
    intro b c rest hlen hAT hbc_dir hLastRel
    have hrest : rest = [] := by cases rest <;> simp_all
    subst hrest
    exact edge_source_relevant G X Y Z (hLastRel c (by simp)) hbc_dir
  | succ n ih =>
    intro b c rest hlen hAT hbc_dir hLastRel
    match rest, hlen, hAT, hLastRel with
    | [], _, ActiveTrail.two _, hLastRel =>
      exact edge_source_relevant G X Y Z (hLastRel c (by simp)) hbc_dir
    | d :: rest', hlen, ActiveTrail.cons hab hcd hbd hAct hTail, hLastRel =>
      -- b→c (hbc_dir), triple (b,c,d) with edges hab, hcd, c≠d (hbd)
      by_cases hcol : IsCollider G ⟨b, c, d, hab, hcd, hbd⟩
      · exact edge_source_relevant G X Y Z
          (colliderActivated_in_relevant G X Y Z
            (active_collider_activated G Z ⟨b, c, d, hab, hcd, hbd⟩ hAct hcol))
          hbc_dir
      · have hout := nonCollider_has_outgoing G ⟨b, c, d, hab, hcd, hbd⟩ hcol
        rcases hout with hcb | hcd_dir
        · -- c→b: 2-cycle with b→c. Contradiction.
          exact absurd hcb (fun h => G.isAcyclic_no_two_cycle hacyclic b c hbc_dir h)
        · -- c→d: chain continues. rest'.length ≤ n.
          have hlen' : rest'.length ≤ n := by
            simp only [List.length_cons] at hlen; omega
          exact edge_source_relevant G X Y Z
            (ih hlen' hTail hcd_dir
              (fun v hv => hLastRel v (by
                simp only [List.getLast?] at hv ⊢; exact hv)))
            hbc_dir

/-- Every vertex on an active trail is in relevantVertices, given that
    the head and last vertices are relevant.

    In a DAG, non-colliders have outgoing edges. If outgoing goes left
    (toward head), head is relevant → vertex relevant. If outgoing goes
    right, the rightward chain terminates at a collider or last vertex
    (both relevant) by DAG acyclicity. -/
theorem activeTrail_pathVerticesIn_relevant_gen
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) :
    ∀ {p : List V},
      ActiveTrail G Z p →
      (∀ v, p.head? = some v → v ∈ relevantVertices G X Y Z) →
      (∀ v, p.getLast? = some v → v ∈ relevantVertices G X Y Z) →
      PathVerticesIn (relevantVertices G X Y Z) p := by
  intro p hAT hHead hLast
  induction hAT with
  | single v =>
    exact ⟨hHead v (by simp [List.head?]), trivial⟩
  | two _ =>
    exact ⟨hHead _ (by simp [List.head?]),
           hLast _ (by simp [List.getLast?]), trivial⟩
  | @cons a b c rest hab hbc hac hAct hTail ih =>
    have haRel : a ∈ relevantVertices G X Y Z := hHead a (by simp [List.head?])
    -- Prove b is relevant
    have hbRel : b ∈ relevantVertices G X Y Z := by
      by_cases hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩
      · exact colliderActivated_in_relevant G X Y Z
          (active_collider_activated G Z ⟨a, b, c, hab, hbc, hac⟩ hAct hcol)
      · have hout := nonCollider_has_outgoing G ⟨a, b, c, hab, hbc, hac⟩ hcol
        rcases hout with hba | hbc_dir
        · exact edge_source_relevant G X Y Z haRel hba
        · exact rightChainRelevant G X Y Z hacyclic rest.length
            (Nat.le_refl _) hTail hbc_dir
            (fun v hv => hLast v (by simp only [List.getLast?] at hv ⊢; exact hv))
    exact ⟨haRel, ih (fun v hv => by simp [List.head?] at hv; subst hv; exact hbRel)
                      (fun v hv => hLast v (by simp only [List.getLast?] at hv ⊢; exact hv))⟩

/-- Every vertex on an active trail from x ∈ X to y ∈ Y in a DAG is in
    relevantVertices. Specialization of the general version. -/
theorem activeTrail_pathVerticesIn_relevant
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y)
    {p : List V} (hEnds : PathEndpoints p = some (x, y))
    (hAT : ActiveTrail G Z p) :
    PathVerticesIn (relevantVertices G X Y Z) p := by
  apply activeTrail_pathVerticesIn_relevant_gen G X Y Z hacyclic hAT
  · -- head = x ∈ X → relevant
    intro v hv
    suffices v = x from this ▸ endpoint_in_relevant_X G X Y Z hx
    cases hAT <;> simp_all [PathEndpoints, List.head?]
  · -- last = y ∈ Y → relevant
    intro v hv
    suffices v = y from this ▸ endpoint_in_relevant_Y G X Y Z hy
    cases hAT <;> simp_all [PathEndpoints, List.getLast?]

/-- Helper: if a :: p' is a trail and p' avoids Z internally, and the head of p'
    is not in Z, then a :: p' avoids Z internally. -/
theorem pathAvoidsInternals_cons_of_head_notInZ {Z : Set V} {a : V} :
    ∀ {p' : List V},
      p' ≠ [] →
      PathAvoidsInternals Z p' →
      (∀ v, p'.head? = some v → v ∉ Z) →
      PathAvoidsInternals Z (a :: p') := by
  intro p' hp' hAvoid hHead
  match p' with
  | [] => exact absurd rfl hp'
  | [v] => exact trivial
  | v :: w :: rest =>
    exact ⟨hHead v (by simp), hAvoid⟩

/-- Core compression: transform an active trail in G to a trail in the
    moralized ancestral graph that avoids Z internally.

    Uses fuel parameter n ≥ p.length for well-founded recursion.
    Colliders in Z are compressed using spouse edges. -/
private theorem activeTrail_to_moralTrail_aux
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v)
    (n : ℕ) :
    ∀ {p : List V},
      p.length ≤ n →
      ActiveTrail G Z p →
      PathVerticesIn (relevantVertices G X Y Z) p →
      ∃ p' : List V,
        p' ≠ [] ∧
        p'.head? = p.head? ∧
        p'.getLast? = p.getLast? ∧
        IsTrail (moralAncestralGraph G X Y Z) p' ∧
        PathAvoidsInternals Z p' := by
  induction n with
  | zero =>
    intro p hlen hAT _
    cases hAT with
    | single v => exact ⟨[v], by simp, rfl, rfl, IsTrail.single v, trivial⟩
    | two _ => simp at hlen
    | cons _ _ _ _ _ => simp at hlen
  | succ n ih =>
    intro p hlen hAT hVert
    cases hAT with
    | single v =>
      exact ⟨[v], by simp, rfl, rfl, IsTrail.single v, trivial⟩
    | @two u v hEdge =>
      have ⟨huR, hvR, _⟩ := hVert
      exact ⟨[u, v], by simp, rfl, rfl,
        IsTrail.cons (undirectedEdge_in_moralAncestral_of_vertices G X Y Z hirr huR hvR hEdge)
          (IsTrail.single v),
        trivial⟩
    | @cons a b c rest hab hbc hac hAct hTail =>
      -- Trail: a :: b :: c :: rest. All vertices relevant.
      have ⟨haR, hbR, hcR, hRestV⟩ := hVert
      by_cases hbZ : b ∈ Z
      · -- Compression case: b ∈ Z, must be collider
        have hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩ := by
          rcases activeTrail_internal_collider_or_notInZ G Z hab hbc hac hAct with h | h
          · exact h
          · exact absurd hbZ h
        -- Spouse edge a—c in moral-ancestral graph
        have hSpouse : UndirectedEdge (moralAncestralGraph G X Y Z) a c :=
          spouseEdge_in_moralAncestral G X Y Z haR hbR hcR hcol.1 hcol.2 hac
        -- Case split on rest
        match rest, hTail, hRestV with
        | [], ActiveTrail.two _, _ =>
          -- Trail [a, b, c]. Compress to [a, c].
          exact ⟨[a, c], by simp, by simp, by simp,
            IsTrail.cons hSpouse (IsTrail.single c), trivial⟩
        | d :: rest', ActiveTrail.cons hbc' hcd hbd hAct' hTail', hRestV' =>
          -- Trail: a :: b :: c :: d :: rest'. Sub-trail: c :: d :: rest'.
          -- c ∉ Z (consecutive colliders impossible in DAG)
          have hcNotZ : c ∉ Z := by
            rcases activeTrail_internal_collider_or_notInZ G Z hbc' hcd hbd hAct' with hcol' | h
            · exact absurd (no_consecutive_colliders_in_dag G Z hacyclic hab hbc hcd hac hbd hcol hcol')
                (by tauto)
            · exact h
          -- Apply IH to sub-trail c :: d :: rest'
          have hSubLen : (c :: d :: rest').length ≤ n := by
            simp only [List.length_cons] at hlen ⊢; omega
          have hSubVert : PathVerticesIn (relevantVertices G X Y Z) (c :: d :: rest') :=
            ⟨hcR, hRestV'⟩
          rcases ih hSubLen hTail' hSubVert with ⟨p', hp'ne, hp'head, hp'last, hp'trail, hp'avoid⟩
          -- p' starts with c (from hp'head). Destructure p'.
          match p', hp'ne, hp'head, hp'last, hp'trail, hp'avoid with
          | v :: prest, _, hp'head, hp'last, hp'trail, hp'avoid =>
            have hvc : v = c := by simp [List.head?] at hp'head; exact hp'head
            refine ⟨a :: v :: prest, by simp, by simp, ?_, ?_, ?_⟩
            · -- getLast? preservation: definitional reduction of getLast? on cons-cons
              show (v :: prest).getLast? = (c :: d :: rest').getLast?
              exact hp'last
            · -- IsTrail: spouse edge a—v (= a—c) then tail
              exact IsTrail.cons (hvc ▸ hSpouse) hp'trail
            · -- PathAvoidsInternals: v ∉ Z (v = c ∉ Z)
              exact pathAvoidsInternals_cons_of_head_notInZ
                (List.cons_ne_nil v prest) hp'avoid
                (fun w hw => by simp at hw; exact hw ▸ hvc ▸ hcNotZ)
      · -- Non-compression case: b ∉ Z. Keep b, prepend a.
        have hTailLen : (b :: c :: rest).length ≤ n := by
          simp only [List.length_cons] at hlen ⊢; omega
        have hTailVert : PathVerticesIn (relevantVertices G X Y Z) (b :: c :: rest) :=
          ⟨hbR, hcR, hRestV⟩
        rcases ih hTailLen hTail hTailVert with ⟨p', hp'ne, hp'head, hp'last, hp'trail, hp'avoid⟩
        -- p' starts with b (from hp'head). Destructure p'.
        have hMoralAB : UndirectedEdge (moralAncestralGraph G X Y Z) a b :=
          undirectedEdge_in_moralAncestral_of_vertices G X Y Z hirr haR hbR hab
        match p', hp'ne, hp'head, hp'last, hp'trail, hp'avoid with
        | v :: prest, _, hp'head, hp'last, hp'trail, hp'avoid =>
          have hvb : v = b := by simp [List.head?] at hp'head; exact hp'head
          refine ⟨a :: v :: prest, by simp, by simp, ?_, ?_, ?_⟩
          · -- getLast? preservation: definitional reduction
            show (v :: prest).getLast? = (b :: c :: rest).getLast?
            exact hp'last
          · exact IsTrail.cons (hvb ▸ hMoralAB) hp'trail
          · exact pathAvoidsInternals_cons_of_head_notInZ
              (List.cons_ne_nil v prest) hp'avoid
              (fun w hw => by simp at hw; exact hw ▸ hvb ▸ hbZ)

/-- PathEndpoints is determined by head? and getLast?. -/
theorem pathEndpoints_of_head_last {p : List V} (hp : p ≠ [])
    {x y : V} (hHead : p.head? = some x) (hLast : p.getLast? = some y) :
    PathEndpoints p = some (x, y) := by
  match p, hp with
  | [v], _ =>
    simp [List.head?] at hHead
    simp [List.getLast?] at hLast
    subst hHead; subst hLast; rfl
  | v :: w :: rest, _ =>
    simp [List.head?] at hHead
    simp [List.getLast?] at hLast
    subst hHead; subst hLast; rfl

/-- head? is the first component of PathEndpoints. -/
theorem head_of_pathEndpoints {p : List V} {x y : V}
    (hEnds : PathEndpoints p = some (x, y)) : p.head? = some x := by
  match p with
  | [] => simp [PathEndpoints] at hEnds
  | [v] => simp [PathEndpoints] at hEnds; simp [hEnds.1]
  | v :: w :: rest => simp [PathEndpoints] at hEnds; simp [hEnds.1]

/-- getLast? is the second component of PathEndpoints. -/
theorem getLast_of_pathEndpoints {p : List V} {x y : V}
    (hEnds : PathEndpoints p = some (x, y)) : p.getLast? = some y := by
  match p with
  | [] => simp [PathEndpoints] at hEnds
  | [v] => simp [PathEndpoints] at hEnds; simp [List.getLast?, hEnds.2]
  | v :: w :: rest =>
    rw [pathEndpoints_cons_cons] at hEnds
    simp at hEnds
    simp [List.getLast?, hEnds.2]

/-- The hATtoMoral transform: every active trail in G from x ∈ X to y ∈ Y
    can be compressed to a trail in the moralized ancestral graph with the
    same endpoints that avoids Z internally. -/
theorem activeTrail_to_moralAncestralTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v) :
    ∀ {x y : V} {p : List V},
      x ∈ X → y ∈ Y →
      p ≠ [] →
      PathEndpoints p = some (x, y) →
      ActiveTrail G Z p →
      ∃ p' : List V,
        p' ≠ [] ∧
        PathEndpoints p' = some (x, y) ∧
        IsTrail (moralAncestralGraph G X Y Z) p' ∧
        PathAvoidsInternals Z p' := by
  intro x y p hx hy hne hEnds hAT
  have hVert := activeTrail_pathVerticesIn_relevant G X Y Z hacyclic hx hy hEnds hAT
  rcases activeTrail_to_moralTrail_aux G X Y Z hacyclic hirr p.length
    (Nat.le_refl _) hAT hVert with ⟨p', hp'ne, hp'head, hp'last, hp'trail, hp'avoid⟩
  exact ⟨p', hp'ne,
    pathEndpoints_of_head_last hp'ne
      (hp'head ▸ head_of_pathEndpoints hEnds)
      (hp'last ▸ getLast_of_pathEndpoints hEnds),
    hp'trail, hp'avoid⟩

/--
Forward global bridge with no extra transform obligations:
in DAGs, separation in the moralized ancestral graph implies full d-separation.
-/
theorem dsepFull_of_separatedInMoralAncestral
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v)
    (hSep : SeparatedInMoralAncestral G X Y Z) :
    DSeparatedFull G X Y Z := by
  exact dsepFull_of_separatedInMoralAncestral_of_activeTrail_transform
    G X Y Z hSep (activeTrail_to_moralAncestralTrail G X Y Z hacyclic hirr)

end Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
