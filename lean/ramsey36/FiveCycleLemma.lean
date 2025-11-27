-- The 5-Cycle Structural Lemma
-- Generic graph theory result, independent of Ramsey theory

import Ramsey36.RamseyDef
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open SimpleGraph Finset

/-!
# The 5-Cycle Structural Lemma

**Statement**: If a graph H on 5 vertices is triangle-free and has independence number ≤ 2,
then H is a 5-cycle (i.e., 2-regular).

**Proof Strategy**:
1. Minimum degree ≥ 2 (else get 3-IS)
2. Maximum degree ≤ 2 (else neighborhood is 3-IS)
3. Therefore all degrees = 2 → 2-regular → cycle

This lemma is KEY for Claim 3's proof.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Main structural lemma
omit [Fintype V] in
theorem five_cycle_structure
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (vertices : Finset V)
    (h_card : vertices.card = 5)
    (h_tri : TriangleFree G)
    (h_no3IS : ∀ S : Finset V, S ⊆ vertices → S.card = 3 → G.IsIndepSet S → False) :
    ∀ v ∈ vertices, (vertices.filter (G.Adj v)).card = 2 := by
  intro v hv

  let deg := (vertices.filter (G.Adj v)).card

  -- Step 1: Prove minimum degree ≥ 2
  have h_min_deg : 2 ≤ deg := by
    by_contra h_not
    push_neg at h_not
    -- v has degree ≤ 1 in vertices, so at least 3 non-neighbors (among the other 4)
    -- Pick 3 non-neighbors; they can't all be pairwise adjacent (triangle-free)
    -- So get a non-adjacent pair among them → 3-IS with v

    have h_non_nbrs : 3 ≤ (vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w)).card := by
      -- |vertices| = 5, v ∈ vertices, so |vertices \ {v}| = 4
      -- deg = |neighbors of v in vertices| ≤ 1
      -- So |non-neighbors of v in vertices \ {v}| ≥ 4 - 1 = 3
      have h_others_card : (vertices.erase v).card = 4 := by
        calc (vertices.erase v).card
          _ = vertices.card - 1 := card_erase_of_mem hv
          _ = 5 - 1 := by rw [h_card]
          _ = 4 := by norm_num

      -- Neighbors card ≤ deg
      have h_nbrs_le : (vertices.filter (fun w => w ≠ v ∧ G.Adj v w)).card ≤ deg := by
        apply card_le_card
        intro w
        simp only [mem_filter]
        tauto

      -- Partition: erase v = neighbors ∪ non-neighbors (disjoint)
      have h_partition_eq : vertices.erase v = (vertices.filter (fun w => w ≠ v ∧ G.Adj v w)) ∪
                                                (vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w)) := by
        ext w
        simp only [mem_union, mem_erase, mem_filter]
        constructor
        · intro ⟨hne, hw⟩  -- mem_erase is w ≠ v ∧ w ∈ vertices
          by_cases h : G.Adj v w
          · left; exact ⟨hw, hne, h⟩
          · right; exact ⟨hw, hne, h⟩
        · intro h; cases h with
          | inl h =>
            obtain ⟨hw, hne, _⟩ := h
            exact ⟨hne, hw⟩
          | inr h =>
            obtain ⟨hw, hne, _⟩ := h
            exact ⟨hne, hw⟩

      rw [h_partition_eq, card_union_of_disjoint] at h_others_card
      · omega
      · rw [disjoint_left]
        intro w hw h_nonadj
        simp only [mem_filter] at hw h_nonadj
        exact h_nonadj.2.2 hw.2.2

    -- Extract 3 non-neighbors
    obtain ⟨S, hS_sub, hS_card⟩ := exists_subset_card_eq h_non_nbrs

    -- S has 3 vertices, all non-adjacent to v
    -- Since triangle-free, S is not a clique
    -- So ∃ a, b ∈ S with a ≠ b and ¬G.Adj a b
    have h_exists_non_edge : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬G.Adj a b := by
      by_contra h_all_adj
      push_neg at h_all_adj
      -- All pairs in S are adjacent → S is a 3-clique
      have h_S_clique : G.IsNClique 3 S := by
        rw [isNClique_iff]
        exact ⟨h_all_adj, hS_card⟩
      exact h_tri S h_S_clique

    obtain ⟨a, ha, b, hb, hab_ne, hab_non_adj⟩ := h_exists_non_edge

    -- Form 3-IS: {v, a, b}
    let I : Finset V := {v, a, b}
    have h_I_card : I.card = 3 := by
      have h_v_ne_a : v ≠ a := by
        have ha_in_filter : a ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub ha
        simp only [mem_filter] at ha_in_filter
        exact ha_in_filter.2.1.symm
      have h_v_ne_b : v ≠ b := by
        have hb_in_filter : b ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub hb
        simp only [mem_filter] at hb_in_filter
        exact hb_in_filter.2.1.symm
      simp only [I]
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]; exact hab_ne
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h_v_ne_a, h_v_ne_b⟩

    have h_I_indep : G.IsIndepSet ↑I := by
      -- Collect facts before case analysis
      have ha_nonadj_v : ¬G.Adj v a := by
        have ha_in_filter : a ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub ha
        simp only [mem_filter] at ha_in_filter
        exact ha_in_filter.2.2
      have hb_nonadj_v : ¬G.Adj v b := by
        have hb_in_filter : b ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub hb
        simp only [mem_filter] at hb_in_filter
        exact hb_in_filter.2.2

      intros x hx y hy hxy h_adj
      simp only [I, mem_coe, mem_insert, mem_singleton] at hx hy
      obtain (rfl | rfl | rfl) := hx <;> obtain (rfl | rfl | rfl) := hy
      · exact hxy rfl
      · exact ha_nonadj_v h_adj
      · exact hb_nonadj_v h_adj
      · exact ha_nonadj_v (G.symm h_adj)
      · exact hxy rfl
      · exact hab_non_adj h_adj
      · exact hb_nonadj_v (G.symm h_adj)
      · exact hab_non_adj (G.symm h_adj)
      · exact hxy rfl

    have h_I_in_vertices : I ⊆ vertices := by
      -- Collect facts before case analysis
      have ha_in_vertices : a ∈ vertices := by
        have ha_in_filter : a ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub ha
        simp only [mem_filter] at ha_in_filter
        exact ha_in_filter.1
      have hb_in_vertices : b ∈ vertices := by
        have hb_in_filter : b ∈ vertices.filter (fun w => w ≠ v ∧ ¬G.Adj v w) := hS_sub hb
        simp only [mem_filter] at hb_in_filter
        exact hb_in_filter.1

      intros w hw
      simp only [I, mem_insert, mem_singleton] at hw
      obtain (rfl | rfl | rfl) := hw
      · exact hv
      · exact ha_in_vertices
      · exact hb_in_vertices

    exact h_no3IS I h_I_in_vertices h_I_card h_I_indep

  -- Step 2: Prove maximum degree ≤ 2
  have h_max_deg : deg ≤ 2 := by
    by_contra h_not
    push_neg at h_not
    -- v has degree ≥ 3, neighborhood has ≥ 3 vertices
    -- In triangle-free graph, neighborhood is independent → 3-IS

    -- The neighborhood restricted to vertices has ≥ 3 elements
    have h_nbhd_size : 3 ≤ deg := h_not

    -- Pick any 3 vertices from the neighborhood
    have h_exists_3 : ∃ S : Finset V, S ⊆ vertices.filter (G.Adj v) ∧ S.card = 3 := by
      exact exists_subset_card_eq h_nbhd_size

    obtain ⟨S, hS_sub, hS_card⟩ := h_exists_3

    -- S is independent (all neighbors of v, triangle-free)
    have hS_indep : G.IsIndepSet S := by
      intros x hx y hy hne
      by_contra h_adj
      -- x, y both adjacent to v and to each other → triangle
      have hx_in_nbhd : x ∈ vertices.filter (G.Adj v) := hS_sub hx
      have hy_in_nbhd : y ∈ vertices.filter (G.Adj v) := hS_sub hy
      simp only [mem_filter] at hx_in_nbhd hy_in_nbhd

      -- Form triangle {v, x, y}
      let tri : Finset V := {v, x, y}
      have h_tri_clique : G.IsNClique 3 tri := by
        rw [isNClique_iff]
        constructor
        · -- G.IsClique tri: all pairs are adjacent
          intros a ha b hb hab_ne
          -- a, b ∈ {v, x, y}, check all 9 cases
          simp only [tri, mem_coe, mem_insert, mem_singleton] at ha hb
          obtain (rfl | rfl | rfl) := ha <;> obtain (rfl | rfl | rfl) := hb
          · exact absurd rfl hab_ne
          · exact hx_in_nbhd.2
          · exact hy_in_nbhd.2
          · exact G.symm hx_in_nbhd.2
          · exact absurd rfl hab_ne
          · exact h_adj
          · exact G.symm hy_in_nbhd.2
          · exact G.symm h_adj
          · exact absurd rfl hab_ne
        · -- tri.card = 3
          have h_v_ne_x : v ≠ x := G.ne_of_adj hx_in_nbhd.2
          have h_v_ne_y : v ≠ y := G.ne_of_adj hy_in_nbhd.2
          simp only [tri]
          rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
          · simp only [mem_singleton]; exact hne
          · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h_v_ne_x, h_v_ne_y⟩
      exact h_tri tri h_tri_clique

    have hS_in_vertices : S ⊆ vertices := by
      trans (vertices.filter (G.Adj v))
      exact hS_sub
      exact filter_subset _ _

    exact h_no3IS S hS_in_vertices hS_card hS_indep

  -- Combine: deg ≥ 2 and deg ≤ 2 → deg = 2
  omega

