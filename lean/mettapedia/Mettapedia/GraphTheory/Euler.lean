/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Eulerian graphs

A connected finite graph with at least one edge has an Euler tour, a closed walk through every
edge exactly once, if and only if every vertex has even degree (Diestel, *Graph Theory*,
Theorem 1.8.1; Euler 1736). Mathlib proves the necessity (`Walk.IsEulerian.even_degree_iff`).
Sufficiency: a longest trail is closed by the parity argument and uses every edge by
connectivity.

## Main results

* `SimpleGraph.Connected.isEulerian_of_even_degree`: sufficiency.
* `SimpleGraph.Connected.isEulerian_iff_even_degree`: the characterisation.
-/

namespace SimpleGraph

open Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph is **Eulerian** if it admits a closed walk that traverses
    every edge exactly once (an Euler tour in Diestel's terminology). -/
def IsEulerian : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsEulerian ∧ p.IsCircuit

/-! ### Theorem 1.8.1 (Diestel §1.8, p. 22)

> "A connected graph is Eulerian if and only if every vertex has even degree."
-/

/-- Diestel, Theorem 1.8.1, necessity:
    An Eulerian graph has all even degrees.

    Follows from Mathlib's `Walk.IsEulerian.even_degree_iff`:
    for a closed Eulerian walk (u = v), every vertex has even degree. -/
theorem IsEulerian.even_degree (h : IsEulerian G) :
    ∀ v : V, Even (G.degree v) := by
  obtain ⟨u, p, hE, hC⟩ := h
  intro x
  rw [hE.even_degree_iff]
  intro hne; exact absurd rfl hne

/-! ### Sufficiency: connected + all even degrees + nonempty edges → Eulerian

The maximal-trail approach: the longest closed trail in a connected
graph with all even degrees must use every edge.

Note: for a graph with no edges (single vertex), the theorem requires
non-empty edge set, because our `IsEulerian` demands a non-nil circuit. -/

/-- A maximal trail (among all trails in G) in a graph with all even
    degrees is closed.  Proof: if a trail ends at u ≠ v, then the
    parity argument shows u has at least one unused incident edge,
    so we can extend the trail by one step — contradicting maximality. -/
private theorem maximal_trail_closed_of_even_degrees
    (heven : ∀ v : V, Even (G.degree v))
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsTrail → p'.length ≤ p.length) :
    u = v := by
  by_contra hne
  -- Step 1: trail has ODD many edges at u (parity lemma)
  have hodd : ¬Even (p.edges.countP fun e => u ∈ e) := by
    rw [hp.even_countP_edges_iff u]
    exact fun h => (h hne).1 rfl
  -- Step 2: G.degree u is even
  have heven_u := heven u
  -- Step 3: trail's count at u ≤ G.degree u
  -- Trail edges incident to u ⊆ G's incidence set at u
  have hle : p.edges.countP (u ∈ ·) ≤ G.degree u := by
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
    -- countP on edges ≤ |edgeFinset.filter (u ∈ ·)|
    -- because p.edges is nodup (trail) and all edges ∈ G.edgeSet
    have hnd : (p.edges.filter (u ∈ ·)).Nodup :=
      hp.edges_nodup.filter _
    calc p.edges.countP (u ∈ ·)
        = (p.edges.filter (u ∈ ·)).length := by rw [List.countP_eq_length_filter]
      _ = (p.edges.filter (u ∈ ·)).toFinset.card := by
          rw [List.toFinset_card_of_nodup hnd]
      _ ≤ (G.edgeFinset.filter (u ∈ ·)).card := by
          apply Finset.card_le_card
          intro e he
          rw [List.mem_toFinset, List.mem_filter] at he
          rw [Finset.mem_filter]
          exact ⟨G.mem_edgeFinset.mpr (p.edges_subset_edgeSet he.1),
                 by simpa using he.2⟩
  -- Step 4: odd < even (since they can't be equal due to parity)
  have hne_count : p.edges.countP (u ∈ ·) ≠ G.degree u := by
    intro heq; exact hodd (heq ▸ heven_u)
  have hlt := Nat.lt_of_le_of_ne hle hne_count
  -- Step 5: extract an unused edge at u
  -- Since countP < degree, some neighbor w has s(u,w) ∉ p.edges.
  have ⟨w, hadj, hnotmem⟩ : ∃ w, G.Adj u w ∧ s(u, w) ∉ p.edges := by
    by_contra hall
    push Not at hall  -- hall : ∀ w, G.Adj u w → s(u, w) ∈ p.edges
    -- Every neighbor's edge is in the trail ⟹ degree ≤ countP
    -- giving degree ≤ countP < degree, contradiction
    suffices G.degree u ≤ p.edges.countP (u ∈ ·) by omega
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter,
        List.countP_eq_length_filter,
        ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨?_, by simpa using he.2⟩
    -- e ∈ G.edgeFinset with u ∈ e. Extract the other vertex using Sym2.Mem.other'.
    have he_mem : u ∈ e := by simpa using he.2
    have he_adj := G.mem_edgeFinset.mp he.1
    -- Rewrite e = s(u, other) and use hall
    rw [← Sym2.other_spec' he_mem] at he_adj ⊢
    exact hall _ he_adj
  -- Step 6: extend the trail, contradicting maximality
  have hext := hmax w v (Walk.cons hadj.symm p) (by
    rw [Walk.isTrail_cons]
    exact ⟨hp, by rwa [Sym2.eq_swap]⟩)
  simp [Walk.length_cons] at hext

/-- Diestel, Theorem 1.8.1, sufficiency:
    A connected graph with nonempty edge set in which every vertex
    has even degree is Eulerian.

    Proof: the maximal trail is closed (by parity) and covers all edges
    (by connectivity: if some edge is missed, splicing a sub-trail at
    a shared vertex produces a longer trail, contradicting maximality). -/
theorem Connected.isEulerian_of_even_degree
    (hconn : G.Connected) (heven : ∀ v : V, Even (G.degree v))
    (hedge : G.edgeSet.Nonempty) :
    IsEulerian G := by
  -- The graph has at least one vertex (from nonempty edges)
  have hne : Nonempty V := by
    obtain ⟨e, he⟩ := hedge
    have := G.not_isDiag_of_mem_edgeSet he
    exact Sym2.ind (fun a _ _ => ⟨a⟩) e this
  -- Step 1: Take a maximal trail in G
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isTrail_forall_isTrail_length_le_length G
  -- Step 2: The maximal trail is closed (by parity lemma)
  have huv := maximal_trail_closed_of_even_degrees G heven hp hmax
  subst huv
  -- Step 3: The trail covers all edges
  -- Key argument: if some edge is missing, by connectivity and the
  -- support-intersection argument, some trail vertex has an unused
  -- incident edge. Rotating the trail to start there and prepending
  -- gives a longer trail, contradicting maximality.
  have hEulerian : p.IsEulerian := by
    -- Show every G-edge is in p.edges, by contradiction.
    rw [Walk.isEulerian_iff]; exact ⟨hp, fun e he => by
    by_contra hne
    -- Step A: All edges at support vertices are in the trail.
    -- If not, rotate the trail to that vertex + prepend unused edge → longer trail.
    have hall : ∀ w ∈ p.support, ∀ z, G.Adj w z → s(w, z) ∈ p.edges := by
      by_contra h; push Not at h
      obtain ⟨w, hw, z, hadj, hnotmem⟩ := h
      -- Rotate: split p at w, form q₂.append q₁
      obtain ⟨q₁, q₂, hpq⟩ := Walk.mem_support_iff_exists_append.mp hw
      -- Rotated trail has same edges (nodup preserved)
      have hp' : (q₂.append q₁).IsTrail := by
        rw [isTrail_def, Walk.edges_append, List.nodup_append_comm]
        rw [← Walk.edges_append, ← hpq]; exact hp.edges_nodup
      -- s(w,z) not in rotated edges (same edge multiset)
      have hnotmem' : s(w, z) ∉ (q₂.append q₁).edges := by
        rw [Walk.edges_append]; rw [hpq, Walk.edges_append] at hnotmem
        simp only [List.mem_append] at hnotmem ⊢; tauto
      -- Extend: prepend edge {z,w}
      have := hmax z w (Walk.cons hadj.symm (q₂.append q₁)) (by
        rw [Walk.isTrail_cons]; exact ⟨hp', by rwa [Sym2.eq_swap]⟩)
      -- Length contradiction
      have hlen : (q₂.append q₁).length = p.length := by
        rw [Walk.length_append]; rw [hpq, Walk.length_append]; omega
      rw [Walk.length_cons] at this; omega
    -- Step B: Support closed under adjacency
    have hclosed : ∀ w, w ∈ p.support → ∀ z, G.Adj w z → z ∈ p.support :=
      fun w hw z hadj => p.snd_mem_support_of_mem_edges (hall w hw z hadj)
    -- Step C: All vertices in support (connectivity + closure)
    have hsupp : ∀ v : V, v ∈ p.support := by
      intro v; obtain ⟨q⟩ := hconn.preconnected u v
      suffices ∀ a b, (q' : G.Walk a b) → a ∈ p.support → b ∈ p.support from
        this u v q p.start_mem_support
      intro a b q' ha
      induction q' with
      | nil => exact ha
      | @cons x y z hadj' q'' ih => exact ih (hclosed x ha y hadj')
    -- Step D: All edges used → contradiction
    exact absurd (Sym2.ind (fun a b (h : G.Adj a b) =>
      hall a (hsupp a) b h) e he) hne⟩
  -- Step 4: The trail is non-nil (graph has edges)
  have hCircuit : p.IsCircuit := by
    refine ⟨hp, ?_⟩
    intro hnil
    -- If p = nil, then p has no edges, but p is Eulerian and G has edges
    rw [hnil] at hEulerian
    obtain ⟨e, he⟩ := hedge
    exact absurd (hEulerian e he) (by simp [Walk.edges])
  exact ⟨u, p, hEulerian, hCircuit⟩

/-- Diestel, Theorem 1.8.1:
    A connected graph with nonempty edges is Eulerian iff every vertex
    has even degree. -/
theorem Connected.isEulerian_iff_even_degree
    (hconn : G.Connected) (hedge : G.edgeSet.Nonempty) :
    IsEulerian G ↔ ∀ v : V, Even (G.degree v) :=
  ⟨IsEulerian.even_degree G, fun h => Connected.isEulerian_of_even_degree G hconn h hedge⟩

end SimpleGraph
