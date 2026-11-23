/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Vertex connectivity

`k`-vertex-connectivity of a finite graph (Diestel, *Graph Theory*, §1.4), next to Mathlib's
`IsEdgeConnected`, and Diestel's Proposition 1.4.2: `κ(G) ≤ λ(G) ≤ δ(G)`.

## Main results

* `SimpleGraph.IsVertexConnected.le_minDegree`: `κ(G) ≤ δ(G)`.
* `SimpleGraph.IsVertexConnected.isEdgeConnected`: `κ(G) ≤ λ(G)`.
* `SimpleGraph.not_isEdgeConnected_minDegree_add_one`: `λ(G) ≤ δ(G)`.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Vertex connectivity -/

/-- A graph G is **k-vertex-connected** if |V| > k and G remains
    (pre)connected after removing any set of fewer than k vertices.

    Diestel §1.4: "A graph G = (V, E) is called k-connected (for k ∈ ℕ)
    if |G| > k and G − X is connected for every set X ⊆ V with |X| < k."

    We use `Preconnected` (no `Nonempty` requirement) since the cardinality
    bound `k < |V|` already guarantees the complement of any small set is
    nonempty. -/
def IsVertexConnected (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ (S : Finset V), S.card < k →
    (G.induce ((↑S : Set V)ᶜ)).Preconnected

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Every graph with ≥ 1 vertex is 0-vertex-connected (vacuously: no set
    has cardinality < 0). -/
theorem isVertexConnected_zero (h : 0 < Fintype.card V) :
    IsVertexConnected G 0 :=
  ⟨h, fun _ hS => absurd hS (by omega)⟩

/-- k-vertex-connected implies minimum degree ≥ k.

    Proof: if deg(v) < k, then |N(v)| < k. By k-vertex-connectivity,
    G − N(v) is preconnected. But v ∈ (N(v))ᶜ (no self-loops) and v is
    isolated in G − N(v). Since |(N(v))ᶜ| ≥ |V| − k + 1 ≥ 2, there
    exists u ≠ v in (N(v))ᶜ. Preconnectedness gives a walk v→u, but v
    is isolated, so the walk is nil, forcing v = u. Contradiction. -/
theorem IsVertexConnected.le_minDegree {k : ℕ}
    (h : IsVertexConnected G k) : k ≤ G.minDegree := by
  classical
  obtain ⟨hcard, hconn⟩ := h
  have hne : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  by_contra hlt; push Not at hlt
  obtain ⟨v₀, hv₀⟩ := G.exists_minimal_degree_vertex
  have hdeg : G.degree v₀ < k := by omega
  -- S = N(v₀), |S| = deg(v₀) < k
  set S := G.neighborFinset v₀ with hS_def
  have hS_lt : S.card < k := by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  -- G − S is preconnected
  have hpre := hconn S hS_lt
  -- v₀ ∈ Sᶜ (v₀ ∉ N(v₀) by irreflexivity)
  have hv₀_in : (v₀ : V) ∈ ((↑S : Set V)ᶜ) := by
    simp only [Set.mem_compl_iff, Finset.mem_coe, hS_def, mem_neighborFinset]
    exact fun h => absurd h G.irrefl
  -- Sᶜ has ≥ 2 vertices: |V| − |S| > |V| − k ≥ 1
  -- (Sᶜ as Finset has card > 1 by Finset.card_compl)
  have hSc_card : 1 < Fintype.card ↥((↑S : Set V)ᶜ) := by
    have h1 := Fintype.card_compl_set (↑S : Set V)
    have h2 : Fintype.card ↥(↑S : Set V) = S.card := Fintype.card_coe S
    rw [h1, h2, hS_def, SimpleGraph.card_neighborFinset_eq_degree]; omega
  -- Pick u ≠ v₀ in Sᶜ
  obtain ⟨⟨u, hu⟩, hu_ne⟩ := Fintype.exists_ne_of_one_lt_card hSc_card ⟨v₀, hv₀_in⟩
  -- v₀ and u connected in G[Sᶜ]
  obtain ⟨p⟩ := hpre ⟨v₀, hv₀_in⟩ ⟨u, hu⟩
  -- But v₀ is isolated in G[Sᶜ]: every neighbor of v₀ in G is in S = N(v₀),
  -- so no neighbor lies in Sᶜ. Hence walk must be nil, forcing v₀ = u.
  -- v₀ has degree 0 in the induced subgraph (isolated)
  -- v₀ has no neighbors in G[Sᶜ]: any neighbor of v₀ in G lies in S = N(v₀)
  have hiso : ∀ w : ↥((↑S : Set V)ᶜ), ¬(G.induce ((↑S : Set V)ᶜ)).Adj ⟨v₀, hv₀_in⟩ w := by
    intro ⟨w, hw⟩ hadj
    -- hadj : G.Adj v₀ w (by definition of induce/comap)
    -- hw : w ∈ (↑S)ᶜ, i.e., w ∉ S = neighborFinset v₀
    -- But G.Adj v₀ w → w ∈ neighborFinset v₀ = S. Contradiction.
    simp only [Set.mem_compl_iff, Finset.mem_coe, hS_def, SimpleGraph.mem_neighborFinset] at hw
    exact hw hadj
  -- Any walk from v₀ in G[Sᶜ] must be nil (v₀ is isolated)
  have hnil : p.Nil := by
    by_contra hnn
    have hlen : 0 < p.length := Walk.not_nil_iff_lt_length.mp hnn
    have hadj := p.adj_getVert_succ hlen
    rw [Walk.getVert_zero] at hadj
    exact hiso _ hadj
  -- hnil.eq : ⟨v₀, hv₀_in⟩ = ⟨u, hu⟩. Need hu_ne : ⟨u, hu⟩ ≠ ⟨v₀, hv₀_in⟩ → False
  exact hu_ne hnil.eq.symm

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A 1-vertex-connected graph with ≥ 2 vertices is connected. -/
theorem IsVertexConnected.connected_of_one (h : IsVertexConnected G 1)
    [Nonempty V] : G.Connected where
  preconnected u v := by
    have hpre := h.2 ∅ (by simp)
    have hu : u ∈ ((↑(∅ : Finset V) : Set V)ᶜ) := by simp
    have hv : v ∈ ((↑(∅ : Finset V) : Set V)ᶜ) := by simp
    obtain ⟨w⟩ := hpre ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨w.map ⟨Subtype.val, fun h => h⟩⟩

/-! ### Proposition 1.4.2 (Diestel §1.4, p. 12)

> "Every non-trivial graph G satisfies κ(G) ≤ λ(G) ≤ δ(G)."
-/

omit [DecidableEq V] in
/-- Diestel, Proposition 1.4.2, second inequality (`λ(G) ≤ δ(G)`): a nontrivial finite graph
is not `(δ(G) + 1)`-edge-connected. It follows from Mathlib's `IsEdgeConnected.le_degree`
at a vertex of minimum degree. -/
theorem not_isEdgeConnected_minDegree_add_one [Nontrivial V] :
    ¬G.IsEdgeConnected (G.minDegree + 1) := by
  intro h
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  have := h.le_degree (u := v)
  omega

/-- Diestel, Proposition 1.4.2, first inequality (`κ(G) ≤ λ(G)`):
    If G is k-vertex-connected then G is k-edge-connected.

    PROOF SKETCH:
    Given edge set F with |F| < k and vertices u, v:
    1. Pick one endpoint from each edge in F (avoiding u and v when possible)
       to form vertex set S with |S| ≤ |F| < k.
    2. By k-vertex-connectivity, G - S is preconnected.
    3. Case {u,v} ∉ F: both u,v ∈ G-S. Path in G-S avoids all edges of F
       (each edge has an endpoint in S). Transfer to G.deleteEdges F.
    4. Case {u,v} ∈ F: must place one of u,v in S. Key counting:
       each edge blocks at most one neighbor of v (either via S membership
       or via deleted edge), so |blocked| ≤ |F| < k ≤ deg(v).
       Thus ∃ w ∈ N(v) with w ∉ S and {v,w} ∉ F.
       Path: u →(in G-S)→ w →(edge in G.deleteEdges F)→ v. -/
theorem IsVertexConnected.isEdgeConnected {k : ℕ}
    (hconn : IsVertexConnected G k) : G.IsEdgeConnected k := by
  classical
  intro u v s hs_lt
  -- k = 0: vacuously true since no set has encard < 0
  rcases k with _ | k
  · simp only [Nat.cast_zero] at hs_lt
    exact absurd hs_lt not_lt_zero
  -- Work with s' = s ∩ G.edgeSet (actual graph edges only; self-loops can't exist)
  -- G.deleteEdges s = G.deleteEdges s' since non-edges have no effect
  let s' := s ∩ G.edgeSet
  have hs'_subset : s' ⊆ s := Set.inter_subset_left
  have hs'_lt : s'.encard < ↑(k + 1) := lt_of_le_of_lt (Set.encard_mono hs'_subset) hs_lt
  have hs'_fin : s'.Finite := Set.finite_of_encard_le_coe (le_of_lt hs'_lt)
  have hdelete_eq : G.deleteEdges s = G.deleteEdges s' := by
    ext a b; simp only [deleteEdges_adj]
    constructor
    · intro ⟨hadj, hne⟩; exact ⟨hadj, fun ⟨h1, _⟩ => hne h1⟩
    · intro ⟨hadj, hne⟩; exact ⟨hadj, fun h1 => hne ⟨h1, hadj⟩⟩
  -- For edges in s', they are actual graph edges, so e.out.1 ≠ e.out.2
  have hirrefl : ∀ e ∈ s', e.out.1 ≠ e.out.2 := fun e he => by
    have he_edge : e ∈ G.edgeSet := he.2
    intro heq
    -- If e.out.1 = e.out.2, then e is diagonal (self-loop)
    have hdiag : e.IsDiag := by
      have hmk : s(e.out.1, e.out.2) = e := Quot.out_eq e
      rw [← hmk]
      exact Sym2.mk_isDiag_iff.mpr heq
    -- But graph edges are not diagonal (SimpleGraph is irreflexive)
    exact G.not_isDiag_of_mem_edgeSet he_edge hdiag
  set sf := hs'_fin.toFinset with hsf_def
  have hs_mem : ∀ e, e ∈ sf ↔ e ∈ s' := fun e => hs'_fin.mem_toFinset
  have hsf_card : sf.card < k + 1 := by
    have h1 : s'.encard = ↑sf.card := hs'_fin.encard_eq_coe_toFinset_card
    rw [h1] at hs'_lt; exact_mod_cast hs'_lt
  -- pickVertex: pick one endpoint per edge, avoiding u and v when possible
  let pickVertex (e : Sym2 V) : V :=
    if u ∈ e then (if e.out.1 = u then e.out.2 else e.out.1)
    else if v ∈ e then (if e.out.1 = v then e.out.2 else e.out.1)
    else e.out.1
  have hpick_mem : ∀ e, pickVertex e ∈ e := fun e => by
    simp only [pickVertex]
    split_ifs <;> first | exact Sym2.out_fst_mem e | exact Sym2.out_snd_mem e
  -- For proper edges (e.out.1 ≠ e.out.2), picking avoids u when u ∈ e
  have hpick_ne_u : ∀ e ∈ sf, u ∈ e → pickVertex e ≠ u := fun e he hu => by
    have hne := hirrefl e ((hs_mem e).mp he)
    simp only [pickVertex, hu, ↓reduceIte]
    split_ifs with h
    · -- e.out.1 = u, so pickVertex = e.out.2. Need e.out.2 ≠ u.
      intro heq
      rw [heq, h] at hne
      exact hne rfl
    · exact h
  -- For proper edges, picking avoids v when v ∈ e and u ∉ e
  have hpick_ne_v : ∀ e ∈ sf, v ∈ e → u ∉ e → pickVertex e ≠ v := fun e he hv hnu => by
    have hne := hirrefl e ((hs_mem e).mp he)
    -- Simplify using hypotheses: u ∉ e kills first branch, v ∈ e enters second
    simp only [pickVertex, hnu, ↓reduceIte, hv]
    -- Now we're in: if e.out.1 = v then e.out.2 else e.out.1
    split_ifs with hv'
    · -- e.out.1 = v, so pickVertex = e.out.2. Need e.out.2 ≠ v.
      intro heq
      rw [heq, hv'] at hne
      exact hne rfl
    · exact hv'
  set S := sf.image pickVertex with hS_def
  have hS_card : S.card < k + 1 := Nat.lt_of_le_of_lt Finset.card_image_le hsf_card
  have hpre : (G.induce ((↑S : Set V)ᶜ)).Preconnected := hconn.2 S hS_card
  have hu_notin : u ∉ S := by
    simp only [hS_def, Finset.mem_image, not_exists, not_and]
    intro e he
    by_cases h : u ∈ e
    · exact hpick_ne_u e he h
    · exact fun heq => h (heq ▸ hpick_mem e)
  have hu_in_compl : u ∈ ((↑S : Set V)ᶜ) := by simp [hu_notin]
  -- Key: every edge in s' has an endpoint in S
  have hedge_hits_S : ∀ e ∈ s', ∃ x ∈ S, x ∈ e := fun e he =>
    ⟨pickVertex e, Finset.mem_image.mpr ⟨e, (hs_mem e).mpr he, rfl⟩, hpick_mem e⟩
  -- Edges with both endpoints in Sᶜ are not in s' (hence not in s either, or harmless)
  have hedge_not_in_s' : ∀ e, (∀ x ∈ e, x ∈ ((↑S : Set V)ᶜ)) → e ∉ s' := fun e hall he => by
    obtain ⟨x, hxS, hxe⟩ := hedge_hits_S e he; exact (hall x hxe) hxS
  -- Case: {u,v} ∈ s' or not
  by_cases huv_in : s(u, v) ∈ s'
  · -- Case {u,v} ∈ s': v ∈ S (since pickVertex({u,v}) = v when avoiding u)
    have huv_irrefl : (s(u, v) : Sym2 V).out.1 ≠ (s(u, v)).out.2 :=
      hirrefl s(u, v) huv_in
    have hv_in_S : v ∈ S := by
      rw [hS_def, Finset.mem_image]
      use s(u, v), (hs_mem _).mpr huv_in
      simp only [pickVertex, Sym2.mem_iff, true_or, ↓reduceIte]
      -- u ∈ s(u,v), so we pick the non-u element which is v
      have hout := Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v) : Sym2 V))
      split_ifs with h
      · -- e.out.1 = u, so pick e.out.2
        have hsnd := Sym2.mem_iff.mp (Sym2.out_snd_mem (s(u, v) : Sym2 V))
        rcases hsnd with heq | heq
        · -- e.out.2 = u, contradicts irreflexivity with h
          rw [heq, h] at huv_irrefl; exact absurd rfl huv_irrefl
        · exact heq
      · -- e.out.1 ≠ u, so e.out.1 = v by hout
        rcases hout with heq | heq
        · exact absurd heq h
        · exact heq
    -- The {u,v} ∈ s case: find unblocked neighbor w of v
    -- Step 1: v has ≥ k+1 neighbors (from minDegree ≥ k+1)
    have hdeg : k + 1 ≤ G.degree v := le_trans (IsVertexConnected.le_minDegree G hconn) (G.minDegree_le_degree v)
    -- Step 2: Define blocked neighbors (w ∈ S or edge {v,w} deleted)
    let blocked := (G.neighborFinset v).filter (fun w => w ∈ S ∨ s(v, w) ∈ s)
    -- Step 3: Counting argument - each edge in sf blocks at most one neighbor of v
    -- Proof sketch: Define injection blocked → sf mapping w to its "blocking edge"
    -- - If {v,w} ∈ sf: map to {v,w} (blocks w via S or edge deletion)
    -- - Else (w ∈ S): map to some e with pickVertex(e) = w
    -- Key: for w ∈ N(v) with w ≠ u, if {v,w} ∈ s then {v,w} ∈ sf (since {v,w} ∈ G.edgeSet),
    -- and pickVertex({v,w}) = w, so w ∈ S. Hence {v,w} ∈ s → w ∈ S for w ≠ u.
    have hblocked_card : blocked.card ≤ sf.card := by
      -- Key lemma: For w ≠ u in N(v), if {v,w} ∈ s then {v,w} ∈ sf and pickVertex({v,w}) = w
      have hvw_in_sf : ∀ w ∈ G.neighborFinset v, w ≠ u → s(v, w) ∈ s → s(v, w) ∈ sf := by
        intro w hw hne hs_in
        have hadj : G.Adj v w := mem_neighborFinset G v w |>.mp hw
        exact (hs_mem _).mpr ⟨hs_in, hadj⟩
      have hpick_vw : ∀ w ∈ G.neighborFinset v, w ≠ u → s(v, w) ∈ sf → pickVertex s(v, w) = w := by
        intro w _ hne hvw_sf
        have hv_mem : v ∈ (s(v, w) : Sym2 V) := Sym2.mem_iff.mpr (Or.inl rfl)
        have hirr := hirrefl s(v, w) ((hs_mem _).mp hvw_sf)
        have hfst := Sym2.mem_iff.mp (Sym2.out_fst_mem s(v, w))
        have hsnd := Sym2.mem_iff.mp (Sym2.out_snd_mem s(v, w))
        -- Case: u ∈ {v,w} or u ∉ {v,w}
        by_cases hu_in : u ∈ (s(v, w) : Sym2 V)
        · -- u ∈ {v,w}: pickVertex picks non-u element
          -- Since w ≠ u and s(v,w) = {v,w}, we have u = v, so picking non-u gives w
          unfold pickVertex; simp only [hu_in, ↓reduceIte]
          split_ifs with h
          · -- out.1 = u, so out.2 ≠ u (by hirr), hence out.2 = w
            cases hsnd with
            | inl hsnd_v =>
              -- out.2 = v and out.1 = u. If u = v then hirr gives contradiction.
              -- u ∈ {v,w} and w ≠ u means u = v.
              simp only [Sym2.mem_iff] at hu_in
              cases hu_in with
              | inl huv => subst huv; rw [h] at hirr; exact absurd hsnd_v.symm hirr
              | inr huw => exact absurd huw.symm hne
            | inr hsnd_w => exact hsnd_w
          · -- out.1 ≠ u, so out.1 must be w (the other element in {v,w})
            cases hfst with
            | inl hfst_v =>
              -- out.1 = v. If u = v then h says out.1 ≠ u = v, contradiction.
              simp only [Sym2.mem_iff] at hu_in
              cases hu_in with
              | inl huv => subst huv; exact absurd hfst_v h
              | inr huw => exact absurd huw.symm hne
            | inr hfst_w => exact hfst_w
        · -- u ∉ {v,w}: pickVertex picks based on v ∈ {v,w}
          unfold pickVertex; simp only [hu_in, ↓reduceIte, hv_mem]
          split_ifs with h
          · -- out.1 = v, so out.2 ≠ v (by hirr), hence out.2 = w
            cases hsnd with
            | inl hsnd_v => rw [h] at hirr; exact absurd hsnd_v.symm hirr
            | inr hsnd_w => exact hsnd_w
          · -- out.1 ≠ v, so out.1 = w
            cases hfst with
            | inl hfst_v => exact absurd hfst_v h
            | inr hfst_w => exact hfst_w
      -- For w ≠ u: {v,w} ∈ s implies w ∈ S
      have hvw_imp_S : ∀ w ∈ G.neighborFinset v, w ≠ u → s(v, w) ∈ s → w ∈ S := by
        intro w hw hne hs_in
        have hvw_sf := hvw_in_sf w hw hne hs_in
        rw [hS_def, Finset.mem_image]
        exact ⟨s(v, w), hvw_sf, hpick_vw w hw hne hvw_sf⟩
      -- blocked ⊆ S ∪ {u}
      have hblocked_subset : ∀ w ∈ blocked, w ∈ S ∨ w = u := by
        intro w hw
        simp only [Finset.mem_filter, blocked] at hw
        obtain ⟨hw_nbr, hS_or_edge⟩ := hw
        by_cases hwu : w = u
        · right; exact hwu
        · left; rcases hS_or_edge with hS | hedge
          · exact hS
          · exact hvw_imp_S w hw_nbr hwu hedge
      -- Bound blocked.card
      have hS_le : S.card ≤ sf.card := Finset.card_image_le
      by_cases hu_blocked : u ∈ blocked
      · -- u is blocked: need injection argument
        -- blocked ⊆ S ∪ {u}, and u ∉ S (from hu_notin)
        -- Each w ∈ blocked \ {u} is in S, so w = pickVertex(e) for some e ∈ sf
        -- And u is blocked means {u,v} ∈ s (since u ∉ S), so {u,v} ∈ sf
        -- Key: each edge contributes at most one blocked neighbor
        -- Use Finset.card_le_card_of_injOn with witness function
        have huv_sf : s(u, v) ∈ sf := by
          simp only [Finset.mem_filter, blocked] at hu_blocked
          obtain ⟨hu_nbr, hS_or_edge⟩ := hu_blocked
          rcases hS_or_edge with hS | hedge
          · exact absurd hS hu_notin
          · rw [Sym2.eq_swap] at hedge
            exact (hs_mem _).mpr ⟨hedge, ((mem_neighborFinset G v u).mp hu_nbr).symm⟩
        -- Define witness: blocked → sf
        -- For w ∈ blocked: if w = u then {u,v}, else some e with pickVertex(e) = w
        -- Since w ≠ u implies w ∈ S = sf.image pickVertex, such e exists
        have hwitness : ∀ w ∈ blocked, ∃ e ∈ sf,
            (w = u ∧ e = s(u, v)) ∨ (w ≠ u ∧ pickVertex e = w) := by
          intro w hw
          by_cases hwu : w = u
          · exact ⟨s(u, v), huv_sf, Or.inl ⟨hwu, rfl⟩⟩
          · have hw_S := (hblocked_subset w hw).resolve_right hwu
            rw [hS_def, Finset.mem_image] at hw_S
            obtain ⟨e, he, heq⟩ := hw_S
            exact ⟨e, he, Or.inr ⟨hwu, heq⟩⟩
        -- For injectivity: if two blocked elements map to same edge, they're equal
        have hinj : ∀ w₁ ∈ blocked, ∀ w₂ ∈ blocked, ∀ e ∈ sf,
            ((w₁ = u ∧ e = s(u, v)) ∨ (w₁ ≠ u ∧ pickVertex e = w₁)) →
            ((w₂ = u ∧ e = s(u, v)) ∨ (w₂ ≠ u ∧ pickVertex e = w₂)) → w₁ = w₂ := by
          intro w₁ hw1 w₂ hw2 e he h1 h2
          -- Avoid rfl patterns to prevent substitution issues
          rcases h1 with ⟨hw1_eq, he_uv1⟩ | ⟨hne1, hp1⟩
          · -- w₁ = u
            rcases h2 with ⟨hw2_eq, _⟩ | ⟨hne2, hp2⟩
            · exact hw1_eq.trans hw2_eq.symm
            · -- w₂ ≠ u, pickVertex(e) = w₂, e = {u,v}
              -- pickVertex({u,v}) avoids u, so = v. But w₂ ∈ N(v), so w₂ ≠ v.
              exfalso
              have hpick_uv_ne_u := hpick_ne_u s(u, v) ((hs_mem _).mpr huv_in) (Sym2.mem_iff.mpr (Or.inl rfl))
              -- pickVertex(s(u,v)) ∈ {u, v}, and ≠ u, so = v
              have hpick_uv_v : pickVertex s(u, v) = v := by
                have hmem := hpick_mem s(u, v)
                simp only [Sym2.mem_iff] at hmem
                cases hmem with
                | inl h => exact absurd h hpick_uv_ne_u
                | inr h => exact h
              -- w₂ ∈ blocked ⊆ N(v), so G.Adj v w₂, so w₂ ≠ v
              have hw2_nbr : w₂ ∈ G.neighborFinset v := Finset.mem_filter.mp hw2 |>.1
              have hadj_v_w2 : G.Adj v w₂ := (mem_neighborFinset G v w₂).mp hw2_nbr
              have hw2_ne_v : w₂ ≠ v := hadj_v_w2.ne.symm
              -- But hp2 : pickVertex e = w₂ and he_uv1 : e = s(u,v)
              rw [he_uv1, hpick_uv_v] at hp2
              exact hw2_ne_v hp2.symm
          · -- w₁ ≠ u, pickVertex(e) = w₁
            rcases h2 with ⟨hw2_eq, he_uv2⟩ | ⟨_, hp2⟩
            · -- w₂ = u, e = {u,v}, pickVertex({u,v}) = w₁
              -- Similar contradiction: pickVertex(s(u,v)) = v, but w₁ ∈ N(v) so w₁ ≠ v
              exfalso
              have hpick_uv_ne_u := hpick_ne_u s(u, v) ((hs_mem _).mpr huv_in) (Sym2.mem_iff.mpr (Or.inl rfl))
              have hpick_uv_v : pickVertex s(u, v) = v := by
                have hmem := hpick_mem s(u, v)
                simp only [Sym2.mem_iff] at hmem
                cases hmem with
                | inl h => exact absurd h hpick_uv_ne_u
                | inr h => exact h
              have hw1_nbr : w₁ ∈ G.neighborFinset v := Finset.mem_filter.mp hw1 |>.1
              have hadj_v_w1 : G.Adj v w₁ := (mem_neighborFinset G v w₁).mp hw1_nbr
              have hw1_ne_v : w₁ ≠ v := hadj_v_w1.ne.symm
              rw [he_uv2, hpick_uv_v] at hp1
              exact hw1_ne_v hp1.symm
            · exact hp1.symm.trans hp2
        -- Now use this to bound cardinality
        -- blocked injects into sf via witness
        -- Define witness function using decidable membership
        let f : V → Sym2 V := fun w => if hw : w ∈ blocked then (hwitness w hw).choose else s(u, v)
        have hf_spec : ∀ w (hw : w ∈ blocked), f w = (hwitness w hw).choose := by
          intro w hw; simp only [f, dif_pos hw]
        have hf_maps : Set.MapsTo f blocked sf := by
          intro w hw
          rw [hf_spec w hw]; exact (hwitness w hw).choose_spec.1
        have hf_inj : (blocked : Set V).InjOn f := by
          intro w₁ hw₁ w₂ hw₂ heq
          -- Convert Set membership to Finset membership
          have hw₁' : w₁ ∈ blocked := hw₁
          have hw₂' : w₂ ∈ blocked := hw₂
          have h1 := (hwitness w₁ hw₁').choose_spec.2
          have h2 := (hwitness w₂ hw₂').choose_spec.2
          rw [hf_spec w₁ hw₁', hf_spec w₂ hw₂'] at heq
          -- heq now relates (hwitness w₁ hw₁').choose and (hwitness w₂ hw₂').choose
          -- But we need to show the same edge for hinj
          -- Use heq to transfer h1 to talk about f w₂
          have he1 : (hwitness w₁ hw₁').choose = (hwitness w₂ hw₂').choose := heq
          have h1' : (w₁ = u ∧ (hwitness w₂ hw₂').choose = s(u, v)) ∨
                     (w₁ ≠ u ∧ pickVertex (hwitness w₂ hw₂').choose = w₁) := by
            rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
            · left; exact ⟨h1a, he1 ▸ h1b⟩
            · right; exact ⟨h1a, he1 ▸ h1b⟩
          exact hinj w₁ hw₁' w₂ hw₂' (hwitness w₂ hw₂').choose (hwitness w₂ hw₂').choose_spec.1 h1' h2
        exact Finset.card_le_card_of_injOn f hf_maps hf_inj
      · -- u not blocked: blocked ⊆ S
        have hsub : blocked ⊆ S := by
          intro w hw
          rcases hblocked_subset w hw with hS | rfl
          · exact hS
          · exact absurd hw hu_blocked
        exact Nat.le_trans (Finset.card_le_card hsub) hS_le
    have hblocked_lt : blocked.card < k + 1 := Nat.lt_of_le_of_lt hblocked_card hsf_card
    -- Step 4: There exists unblocked neighbor (since |N(v)| ≥ k+1 > |blocked|)
    have hunblocked : ∃ w ∈ G.neighborFinset v, w ∉ blocked := by
      by_contra hall; push Not at hall
      have hsub : G.neighborFinset v ⊆ blocked := by
        intro w hw
        have := hall w hw
        simp only [Finset.mem_filter, blocked] at this ⊢
        exact ⟨hw, this.2⟩
      have hle : (G.neighborFinset v).card ≤ blocked.card := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hle
      omega
    obtain ⟨w, hw_nbr, hw_not_blocked⟩ := hunblocked
    have hw_props : w ∉ S ∧ s(v, w) ∉ s := by
      simp only [Finset.mem_filter, not_and, not_or, blocked] at hw_not_blocked
      exact hw_not_blocked hw_nbr
    have hw_in_compl : w ∈ ((↑S : Set V)ᶜ) := hw_props.1
    -- Step 5: Path u → w in G[Sᶜ]
    obtain ⟨p⟩ := hpre ⟨u, hu_in_compl⟩ ⟨w, hw_in_compl⟩
    -- Step 6: Construct path in G.deleteEdges s: u →* w → v
    let p_G := p.map (Embedding.induce ((↑S : Set V)ᶜ)).toHom
    have hp_avoids : ∀ e ∈ p_G.edges, e ∉ s := by
      intro e he hes
      rw [Walk.edges_map] at he
      obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp he
      have he'_edge : e' ∈ (G.induce ((↑S : Set V)ᶜ)).edgeSet := p.edges_subset_edgeSet he'_mem
      induction e' using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he'_edge
        have he_eq : e = s(a.val, b.val) := by rw [← he'_eq]; rfl
        have hall : ∀ x ∈ e, x ∈ ((↑S : Set V)ᶜ) := by
          rw [he_eq]; intro x hx; simp only [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl <;> [exact a.property; exact b.property]
        have he_edge : e ∈ G.edgeSet := by
          rw [he_eq, SimpleGraph.mem_edgeSet]; exact he'_edge
        exact hedge_not_in_s' e hall ⟨hes, he_edge⟩
    let p_del := p_G.toDeleteEdges s hp_avoids
    -- Final edge w → v is in G.deleteEdges s
    have hadj_wv : G.Adj w v := (mem_neighborFinset G v w).mp hw_nbr |>.symm
    have hwv_not_in_s : s(w, v) ∉ s := by rw [Sym2.eq_swap]; exact hw_props.2
    have hadj_del : (G.deleteEdges s).Adj w v := deleteEdges_adj.mpr ⟨hadj_wv, hwv_not_in_s⟩
    exact ⟨p_del.append (Walk.cons hadj_del Walk.nil)⟩
  · -- Case {u,v} ∉ s': v ∉ S
    -- Also need: s(u,v) ∉ s (for the final path) - either it's not in s, or it's not an edge
    have huv_not_in_s : s(u, v) ∉ s ∨ s(u, v) ∉ G.edgeSet := by
      by_contra hall; push Not at hall
      exact huv_in ⟨hall.1, hall.2⟩
    have hv_notin : v ∉ S := by
      by_cases huv_eq : u = v
      · -- u = v: follows from hu_notin
        rw [← huv_eq]; exact hu_notin
      · -- u ≠ v: use edge membership argument
        simp only [hS_def, Finset.mem_image, not_exists, not_and]
        intro e he
        by_cases hue : u ∈ e
        · -- If both u and v in e, then e = {u,v}
          by_cases hve : v ∈ e
          · -- Both u and v in e with u ≠ v means e = s(u,v)
            have heq : e = s(u, v) := by
              induction e using Sym2.ind with
              | _ a b =>
                simp only [Sym2.mem_iff] at hue hve
                rcases hue with rfl | rfl <;> rcases hve with rfl | rfl
                · exact absurd rfl huv_eq  -- u = a, v = a implies u = v
                · rfl  -- u = a, v = b
                · simp [Sym2.eq_swap]  -- u = b, v = a
                · exact absurd rfl huv_eq  -- u = b, v = b implies u = v
            rw [heq, hs_mem] at he; exact absurd he huv_in
          · exact fun heq => hve (heq ▸ hpick_mem e)
        · -- u ∉ e, so pickVertex avoids v
          by_cases hve : v ∈ e
          · exact hpick_ne_v e he hve hue
          · exact fun heq => hve (heq ▸ hpick_mem e)
    have hv_in_compl : v ∈ ((↑S : Set V)ᶜ) := by simp [hv_notin]
    -- Path in G[Sᶜ]
    obtain ⟨p⟩ := hpre ⟨u, hu_in_compl⟩ ⟨v, hv_in_compl⟩
    -- Map to G
    let p_G := p.map (Embedding.induce ((↑S : Set V)ᶜ)).toHom
    -- Show edges avoid s: vertices of p are in Sᶜ, so edges have both endpoints in Sᶜ
    -- Edges with both endpoints in Sᶜ are not in s' (they miss the picked vertex)
    have hp_avoids : ∀ e ∈ p_G.edges, e ∉ s := by
      intro e he hes
      -- e comes from mapping an induced subgraph edge
      rw [Walk.edges_map] at he
      obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp he
      -- e' ∈ p.edges means e' is in the induced subgraph's edge set
      have he'_edge : e' ∈ (G.induce ((↑S : Set V)ᶜ)).edgeSet := p.edges_subset_edgeSet he'_mem
      -- Extract adjacency using Sym2.ind
      induction e' using Sym2.ind with
      | _ a b =>
        -- e' = s(a, b) where a, b : ↥Sᶜ
        simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he'_edge
        -- he'_edge : G.Adj a.val b.val
        -- The mapped edge e = s(a.val, b.val)
        have he_eq : e = s(a.val, b.val) := by
          rw [← he'_eq]; rfl
        -- Both endpoints are in Sᶜ (from subtype membership)
        have ha_compl : a.val ∈ ((↑S : Set V)ᶜ) := a.property
        have hb_compl : b.val ∈ ((↑S : Set V)ᶜ) := b.property
        have hall : ∀ x ∈ e, x ∈ ((↑S : Set V)ᶜ) := by
          rw [he_eq]
          intro x hx
          simp only [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl <;> assumption
        -- e is a graph edge (from adjacency)
        have he_edge : e ∈ G.edgeSet := by
          rw [he_eq, SimpleGraph.mem_edgeSet]
          exact he'_edge
        -- e ∈ s and e ∈ G.edgeSet means e ∈ s'
        -- But edges with both endpoints in Sᶜ are not in s'
        exact hedge_not_in_s' e hall ⟨hes, he_edge⟩
    exact ⟨hdelete_eq ▸ p_G.toDeleteEdges s hp_avoids⟩

end SimpleGraph
