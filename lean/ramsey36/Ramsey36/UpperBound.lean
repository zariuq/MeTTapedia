/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Upper Bound: R(3,6) ≤ 18

This file contains the upper bound proof following Cariolaro's paper.

The proof proceeds by contradiction: assume G is a triangle-free graph on 18 vertices
with no 6-independent set, then derive structural claims that lead to contradiction.

## Structure

- **Infrastructure**: Basic lemmas about triangle-free graphs
- **Claim 1**: G is 5-regular
- **Claim 2**: Neighborhood structure (4+8 partition)
- **Claim 3**: The 4 p-vertices form a 4-cycle
- **Final**: Exhaustive case analysis → contradiction
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Ramsey36.Basic

open SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Infrastructure Lemmas -/

/-- **Key Lemma**: In a triangle-free graph, the neighborhood of any vertex forms an independent set.

    Proof: If x, y are both neighbors of v and also adjacent to each other,
    then {v, x, y} forms a triangle, contradicting triangle-free.
-/
lemma neighborSet_indep_of_triangleFree {G : SimpleGraph α} (h_tri : TriangleFree G) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  -- Goal: ∀ x y ∈ N(v), x ≠ y → ¬G.Adj x y
  intro x hx y hy hne h_adj
  -- We have: x ∈ N(v), y ∈ N(v), x ≠ y, G.Adj x y
  -- So: G.Adj v x, G.Adj v y, G.Adj x y
  -- Therefore {v, x, y} is a 3-clique

  -- Construct the clique as a finset
  let s : Finset α := {v, x, y}

  -- Show it's a 3-clique
  have h_clique : G.IsNClique 3 s := by
    constructor
    · -- IsClique: pairwise adjacent
      intro a ha b hb hab
      simp [s] at ha hb
      -- Case analysis on which vertices a and b are
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · -- a = v, b = v: impossible (hab)
        contradiction
      · -- a = v, b = x: G.Adj v x
        exact (mem_neighborSet _ _).mp hx
      · -- a = v, b = y: G.Adj v y
        exact (mem_neighborSet _ _).mp hy
      · -- a = x, b = v: G.Adj x v
        exact G.symm ((mem_neighborSet _ _).mp hx)
      · -- a = x, b = x: impossible
        contradiction
      · -- a = x, b = y: G.Adj x y (our assumption)
        exact h_adj
      · -- a = y, b = v: G.Adj y v
        exact G.symm ((mem_neighborSet _ _).mp hy)
      · -- a = y, b = x: G.Adj y x
        exact G.symm h_adj
      · -- a = y, b = y: impossible
        contradiction
    · -- Card = 3
      simp [s]
      -- Need to show x ≠ v, y ≠ v, x ≠ y
      constructor
      · -- x ≠ v: from loopless + adjacency
        intro h_eq
        subst h_eq
        exact G.loopless v ((mem_neighborSet _ _).mp hx)
      constructor
      · -- y ≠ v: from loopless + adjacency
        intro h_eq
        subst h_eq
        exact G.loopless v ((mem_neighborSet _ _).mp hy)
      · -- x ≠ y: our assumption
        exact hne

  -- This contradicts triangle-free
  unfold TriangleFree CliqueFree at h_tri
  exact h_tri s h_clique.isClique h_clique.card_eq

/-- In a triangle-free graph with no k-independent set, every vertex has degree ≤ k-1.

    Proof: N(v) is independent (by previous lemma), and there's no k-independent set,
    so |N(v)| < k, i.e., deg(v) ≤ k-1.
-/
lemma degree_le_of_triangleFree_no_indep {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no_k_indep : NoKIndepSet k G) (v : Fin n) :
    G.degree v ≤ k - 1 := by
  -- Get independence of neighborhood
  have h_indep_set := neighborSet_indep_of_triangleFree h_tri v

  -- Prove by contradiction
  by_contra h_big
  push_neg at h_big
  -- h_big: k ≤ G.degree v

  -- So |N(v)| ≥ k
  have h_card : (G.neighborFinset v).card ≥ k := by
    calc (G.neighborFinset v).card
        = G.degree v := by rw [card_neighborFinset_eq_degree]
      _ ≥ k := h_big

  -- Pick a k-element subset of N(v)
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq h_card

  -- This subset is also independent (subset of independent set)
  have h_t_indep : G.IsIndepSet (t : Set (Fin n)) := by
    intro x hx y hy hne
    -- x, y ∈ t ⊆ neighborFinset v
    have hx_n : x ∈ G.neighborSet v := by
      simp [neighborSet]
      have : x ∈ G.neighborFinset v := ht_sub hx
      exact (mem_neighborFinset _ _).mp this
    have hy_n : y ∈ G.neighborSet v := by
      simp [neighborSet]
      have : y ∈ G.neighborFinset v := ht_sub hy
      exact (mem_neighborFinset _ _).mp this
    exact h_indep_set hx_n hy_n hne

  -- So t is a k-independent set
  have h_is_k_indep : G.IsNIndepSet k t := by
    constructor
    · exact h_t_indep
    · exact ht_card

  -- This contradicts h_no_k_indep
  unfold NoKIndepSet IndepSetFree at h_no_k_indep
  exact h_no_k_indep t ht_card h_t_indep

/-! ## Claim 1: 5-Regularity -/

/-- **Claim 1**: Any triangle-free graph on 18 vertices with no 6-IS is 5-regular.

    Proof outline:
    1. Triangle-free + no 6-IS ⟹ deg(v) ≤ 5 for all v (by degree_le lemma)
    2. If deg(v) ≤ 4 for some v, consider H = G - N[v]
    3. |H| ≥ 13, and H is triangle-free with no 5-IS
    4. By R(3,5) = 14, this is impossible
    5. Therefore deg(v) = 5 for all v
-/
lemma claim1_five_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    IsKRegular G 5 := by
  -- Step 1: Upper bound deg(v) ≤ 5
  have h_deg_le_5 : ∀ v, G.degree v ≤ 5 :=
    fun v => degree_le_of_triangleFree_no_indep (k := 6) h_tri h_no6 v

  -- Step 2: Prove lower bound deg(v) ≥ 5 by contradiction using R(3,5) = 14
  have h_deg_ge_5 : ∀ v, 5 ≤ G.degree v := by
    intro v
    by_contra h_small
    push_neg at h_small
    -- deg(v) < 5, so deg(v) ≤ 4

    -- Let H be the induced subgraph on vertices outside N[v]
    -- (where N[v] = {v} ∪ neighbors of v)
    let closed_neighborhood := insert v (G.neighborFinset v)
    let H_vertices := Finset.univ \ closed_neighborhood

    -- Count vertices in H
    have h_H_card : H_vertices.card ≥ 13 := by
      calc H_vertices.card
          = Finset.card Finset.univ - closed_neighborhood.card := by
            rw [card_sdiff (subset_univ _)]
        _ = 18 - (1 + G.degree v) := by
            simp [closed_neighborhood, card_insert_of_not_mem (not_mem_neighborFinset_self _ _),
                  card_neighborFinset_eq_degree]
        _ ≥ 18 - (1 + 4) := by omega
        _ = 13 := by norm_num

    -- TODO: The rest requires formalizing:
    -- 1. H is triangle-free (inherited from G)
    -- 2. H has no 5-independent set (would give 6-IS with v)
    -- 3. By R(3,5) = 14, any graph on ≥14 vertices has triangle or 5-IS
    -- 4. But |H| = 13, and R(3,5)-critical graphs on 13 vertices don't exist
    -- This is the contradiction
    sorry

  -- Combine bounds: deg(v) = 5 for all v
  intro v
  exact Nat.le_antisymm (h_deg_le_5 v) (h_deg_ge_5 v)

/-! ## Claim 2: Neighborhood Structure -/

/-- **Claim 2**: In a 5-regular triangle-free graph on 18 vertices with no 6-IS,
    each vertex v has a precise neighborhood structure among its 12 non-neighbors.

    For any vertex v:
    - Exactly 4 non-neighbors share 1 common neighbor with v (the "P-vertices")
    - Exactly 8 non-neighbors share 2 common neighbors with v (the "Q-vertices")

    Proof: Edge counting (handshake lemma) between N(v) and non-neighbors of v.
-/
lemma claim2_neighbor_structure {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) (v : Fin 18) :
    ∃ (P Q : Finset (Fin 18)),
      P.card = 4 ∧ Q.card = 8 ∧
      (∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) ∧
      (∀ q ∈ Q, ¬G.Adj v q ∧ commonNeighborsCard G v q = 2) := by
  sorry  -- This is the most complex combinatorial argument

/-! ## Upper Bound Theorem -/

/-- **Main Theorem**: R(3,6) ≤ 18

    Proof by contradiction: Assume there exists a triangle-free graph G on 18 vertices
    with no 6-independent set. Use Claims 1-3 to derive a contradiction.
-/
theorem ramsey_three_six_upper : ramseyNumber 3 6 ≤ 18 := by
  sorry  -- Requires completing all claims and final contradiction
