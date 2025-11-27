import Ramsey36.RamseyDef
import Ramsey36.SmallRamsey
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Known Ramsey Numbers (PROVEN in SmallRamsey.lean) -/
-- These are proven theorems, not axioms!
theorem ramsey_three_four : ramseyNumber 3 4 = 9 := ramsey_three_four_proof
theorem ramsey_three_five : ramseyNumber 3 5 = 14 := ramsey_three_five_proof

/-! ## Generic Ramsey facts -/

lemma ramsey_two_right {m : ℕ} (hm : 2 ≤ m) : ramseyNumber m 2 = m := by
  classical
  let S :=
    {n : ℕ |
      n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty m 2 G}
  -- m belongs to S (witness for upper bound)
  have h_mem : m ∈ S := by
    constructor
    · exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hm
    · intro G
      -- Either G is complete or has a non-edge
      by_cases hK : ∀ v w, v ≠ w → G.Adj v w
      · left
        refine ⟨Finset.univ, ?_⟩
        constructor
        · intro x hx y hy hxy; simpa using hK x y hxy
        · simp
      · right
        rcases not_forall.1 hK with ⟨v, hv⟩
        rcases not_forall.1 hv with ⟨w, hw⟩
        -- Extract that v ≠ w and ¬G.Adj v w from hw
        -- hw : ¬(v ≠ w → G.Adj v w) means the implication is false
        -- An implication is false iff premise is true and conclusion is false
        push_neg at hw
        obtain ⟨hneq, hnotadj⟩ := hw
        refine ⟨{v, w}, ?_⟩
        constructor
        · intro x hx y hy hxy
          simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> try contradiction
          · exact hnotadj
          · exact mt G.adj_symm hnotadj
        · simp [Finset.card_insert_of_notMem, Finset.card_singleton, hneq]
  -- m is a lower bound for S: any n in S has n ≥ m
  have h_lb : ∀ ⦃n⦄, n ∈ S → m ≤ n := by
    intro n hn
    rcases hn with ⟨hpos, hprop⟩
    by_contra hlt
    have hlt' : n < m := Nat.lt_of_not_ge hlt
    -- Consider complete graph on n vertices; it fails HasRamseyProperty m 2 when n < m.
    let G := completeGraph (Fin n)
    have h_no : ¬ HasRamseyProperty m 2 G := by
      unfold HasRamseyProperty
      push_neg
      constructor
      · intro s hs
        -- no m-clique: card s = m > n
        have hcard := hs.2
        have hle : s.card ≤ n := by
          calc s.card ≤ Fintype.card (Fin n) := Finset.card_le_univ (α := Fin n) (s := s)
            _ = n := Fintype.card_fin n
        linarith
      · intro s hs
        -- no 2-indep set: complete graph has all edges between distinct vertices
        rcases hs with ⟨hindep, hcard⟩
        have htwo : s.card = 2 := hcard
        -- any two distinct vertices are adjacent
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
        have : (completeGraph (Fin n)).Adj x y := by
          dsimp [completeGraph]; exact hxy
        -- contradict independence
        have hind := hindep (Finset.mem_insert_self x {y})
                            (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
                            hxy
        exact (hind this).elim
    exact h_no (hprop G)
  -- Conclude sInf S = m
  have h_upper : ramseyNumber m 2 ≤ m := by
    apply csInf_le
    · use m
      exact fun _ hn => h_lb hn
    · exact h_mem
  have h_lower : m ≤ ramseyNumber m 2 := by
    -- since m is a lower bound of S
    apply le_csInf
    · exact ⟨m, h_mem⟩
    · intro n hn
      exact h_lb hn
  exact le_antisymm h_upper h_lower

/-! ## Helper Lemmas -/

lemma triangleFree_iff_cliqueFree_three {G : SimpleGraph V} :
    TriangleFree G ↔ G.CliqueFree 3 := by rfl




/-- If a graph G has >= n vertices, and all graphs on n vertices have the Ramsey property (k, l),
    then G also has the Ramsey property (k, l). -/
theorem hasRamseyProperty_of_card_ge {k l n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_ramsey : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], HasRamseyProperty k l H)
    (h_card : Fintype.card V ≥ n) :
    HasRamseyProperty k l G := by
  rw [← Fintype.card_fin n] at h_card
  have : Nonempty (Fin n ↪ V) := Function.Embedding.nonempty_of_card_le h_card
  let f := this.some
  let H := G.comap f
  have prop := h_ramsey H
  rcases prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    use s.map f
    rw [isNClique_iff] at hs ⊢
    rw [Finset.card_map]
    constructor
    · rw [isClique_iff] at hs ⊢
      intro x hx y hy hne
      simp only [Finset.mem_map, Finset.mem_coe] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne' : x' ≠ y' := by intro contra; apply hne; rw [contra]
      have hadj := hs.1 hx' hy' hne'
      exact hadj
    · exact hs.2
  · right
    use s.map f
    rw [isNIndepSet_iff] at hs ⊢
    rw [Finset.card_map]
    constructor
    · rw [isIndepSet_iff] at hs ⊢
      intro x hx y hy hne
      simp only [Finset.mem_map, Finset.mem_coe] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne' : x' ≠ y' := by intro contra; apply hne; rw [contra]
      have h_indep := hs.1 hx' hy' hne'
      exact h_indep
    · exact hs.2

theorem ramsey_three_five_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 14) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 5 s := by
  have h_prop : HasRamseyProperty 3 5 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_five
    exact (ramsey_of_ramseyNumber_eq h_eq).2
  rcases h_prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    exact h_tri s hs
  · exact ⟨s, hs⟩

theorem ramsey_three_four_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 9) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 4 s := by
  have h_prop : HasRamseyProperty 3 4 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_four
    exact (ramsey_of_ramseyNumber_eq h_eq).2
  rcases h_prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    exact h_tri s hs
  · exact ⟨s, hs⟩


-- H13 fact in polymorphic form (provable from graph theory!)
lemma r35_critical_is_4_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h_card : Fintype.card V = 13) (h_tri : TriangleFree G) (h_no5 : NoKIndepSet 5 G)
    [DecidableRel G.Adj] :
    IsKRegular G 4 := by
  sorry

/-! ## Claim 1 -/

/-- In an 18-vertex triangle-free graph with no 6-independent set,
    every vertex has degree at least 4.

    Proof: If deg(v) ≤ 3, then the non-neighbors H have size ≥ 14.
    By R(3,5)=14, any 14-vertex graph contains a triangle or 5-independent set.
    - Triangle in H extends to triangle in G (contradiction)
    - 5-independent in H extends to 6-independent in G (adding v) -/
lemma degree_ge_four_of_triangleFree_no_6indep
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) :
    G.degree v ≥ 4 := by
  -- Proof by contradiction: assume deg(v) ≤ 3
  by_contra h_not
  push_neg at h_not
  have h_deg_le_3 : G.degree v ≤ 3 := Nat.lt_succ_iff.mp h_not

  -- Non-neighbors of v (excluding v itself)
  let H := (Finset.univ : Finset (Fin 18)) \ (insert v (G.neighborFinset v))

  have h_H_card : H.card ≥ 14 := by
    -- |H| = 18 - |{v} ∪ neighbors(v)| = 18 - (1 + deg(v)) ≥ 18 - 4 = 14
    have h_union_card : (insert v (G.neighborFinset v)).card ≤ 4 := by
      calc (insert v (G.neighborFinset v)).card
          = (G.neighborFinset v).card + 1 := by
            rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
        _ = G.degree v + 1 := by rw [G.card_neighborFinset_eq_degree]
        _ ≤ 3 + 1 := by omega
        _ = 4 := by norm_num
    have h_disjoint : Disjoint H (insert v (G.neighborFinset v)) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext w
      simp only [H, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, mem_neighborFinset, true_and,
                 Finset.notMem_empty, iff_false]
      tauto
    have h_union : H ∪ (insert v (G.neighborFinset v)) = Finset.univ := by
      ext w
      simp only [H, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, mem_neighborFinset, true_and, iff_true]
      tauto
    have h_card_union : H.card + (insert v (G.neighborFinset v)).card = 18 := by
      have h_eq : (H ∪ (insert v (G.neighborFinset v))).card =
                   H.card + (insert v (G.neighborFinset v)).card :=
        Finset.card_union_of_disjoint h_disjoint
      rw [h_union] at h_eq
      have : (Finset.univ : Finset (Fin 18)).card = 18 := by simp [Fintype.card_fin]
      rw [this] at h_eq
      exact h_eq.symm
    calc H.card
        = 18 - (insert v (G.neighborFinset v)).card := by omega
      _ ≥ 18 - 4 := by omega
      _ = 14 := by norm_num

  -- Extract 14-element subset from H
  obtain ⟨H14, hH14_sub, hH14_card⟩ := Finset.exists_subset_card_eq h_H_card

  -- v is not adjacent to any vertex in H14
  have h_v_nonadj_H14 : ∀ w ∈ H14, ¬ G.Adj v w := by
    intro w hw h_adj
    have hw_in_H : w ∈ H := hH14_sub hw
    simp only [H, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw_in_H
    apply hw_in_H
    apply Finset.mem_insert_of_mem
    rw [mem_neighborFinset]
    exact h_adj

  -- Create induced subgraph on H14 via comap
  have h_H14_card_type : Fintype.card (↑H14 : Set (Fin 18)) = 14 := by
    simp [Fintype.card_coe, hH14_card]

  have h_card_eq : Fintype.card (Fin 14) = Fintype.card (↑H14 : Set (Fin 18)) := by
    simp only [Fintype.card_fin]
    exact h_H14_card_type.symm
  let e : Fin 14 ≃ (↑H14 : Set (Fin 18)) := Fintype.equivOfCardEq h_card_eq
  let f : Fin 14 ↪ Fin 18 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let G_H14 := G.comap f

  -- Apply R(3,5)=14 to G_H14
  have h_ramsey_prop : HasRamseyProperty 3 5 G_H14 := by
    exact (ramsey_of_ramseyNumber_eq ramsey_three_five).2 G_H14
  rcases h_ramsey_prop with ⟨S, hS⟩ | ⟨T, hT⟩

  · -- Case 1: G_H14 contains a 3-clique S → triangle in G
    have h_clique_G : G.IsNClique 3 (S.map f) := by
      constructor
      · intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
        have hne : x' ≠ y' := by
          intro h_eq
          apply hxy
          simp [h_eq]
        exact hS.1 hx' hy' hne
      · simp [Finset.card_map, hS.2]
    exact h_tri (S.map f) h_clique_G

  · -- Case 2: G_H14 contains a 5-independent set T → T ∪ {v} is 6-independent in G
    let T_plus_v := insert v (T.map f)
    have h_indep_6 : G.IsNIndepSet 6 T_plus_v := by
      constructor
      · -- Show T_plus_v is independent
        intro x hx y hy hxy h_adj
        show False
        have hx' : x = v ∨ x ∈ T.map f := Finset.mem_insert.mp hx
        have hy' : y = v ∨ y ∈ T.map f := Finset.mem_insert.mp hy
        rcases hx' with rfl | hx_in_T <;> rcases hy' with rfl | hy_in_T
        · exact hxy rfl
        · have : y ∈ (↑H14 : Set (Fin 18)) := by
            rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
            show (f y') ∈ ↑H14
            change (e y').val ∈ ↑H14
            exact (e y').property
          have h_y_nonadj_v : ¬ G.Adj x y := h_v_nonadj_H14 y this
          exact h_y_nonadj_v h_adj
        · have : x ∈ (↑H14 : Set (Fin 18)) := by
            rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
            show (f x') ∈ ↑H14
            change (e x').val ∈ ↑H14
            exact (e x').property
          have h_x_nonadj_v : ¬ G.Adj y x := h_v_nonadj_H14 x this
          exact h_x_nonadj_v (G.symm h_adj)
        · rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
          rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
          have hne : x' ≠ y' := by
            intro h_eq
            apply hxy
            simp [h_eq]
          exact hT.1 hx'_in_T hy'_in_T hne h_adj
      · have h_v_not_in_map : v ∉ T.map f := by
          intro h_v_in_T
          rcases Finset.mem_map.mp h_v_in_T with ⟨t, ht, h_eq⟩
          have h_ft_in_H14 : (f t : Fin 18) ∈ H14 := by
            have : (f t : Fin 18) ∈ (↑H14 : Set (Fin 18)) := by
              change (e t).val ∈ ↑H14
              exact (e t).property
            simpa using this
          have h_v_in_H14 : v ∈ H14 := by rwa [h_eq] at h_ft_in_H14
          -- But v ∈ H14 means v ∉ insert v (neighborFinset v), which contradicts v ∈ insert v ...
          have h_v_in_H : v ∈ H := hH14_sub h_v_in_H14
          simp only [H, Finset.mem_sdiff, Finset.mem_univ, true_and] at h_v_in_H
          exact h_v_in_H (Finset.mem_insert_self v _)
        calc T_plus_v.card
            = (insert v (T.map f)).card := rfl
          _ = (T.map f).card + 1 := Finset.card_insert_of_notMem h_v_not_in_map
          _ = T.card + 1 := by rw [Finset.card_map]
          _ = 5 + 1 := by rw [hT.2]
          _ = 6 := by norm_num
    exact h_no6 T_plus_v h_indep_6

/-! ### H13: The unique Ramsey(3,5;13) graph

H13 is the Paley graph of order 13 (cyclic graph C_13(1,5)).
It is 4-regular, triangle-free, and has no 5-independent set.
This is a provable result from graph theory (Greenwood & Gleason 1955).

TODO: Prove this from graph theory principles, not axiomatize!
-/
lemma ramsey_3_5_13_is_four_regular
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no5 : NoKIndepSet 5 G) :
    IsKRegular G 4 := by
  sorry

/-! ### Claim 1 Part 3: No vertex has degree 4

Following Krüger's argument (explained by Gemini):
If deg(v) = 4, then G_v (13 non-neighbors) must be isomorphic to H13 (4-regular).
Edge counting between N(v) (4 vertices) and G_v (13 vertices) leads to contradiction:
- Upper bound: Each vertex in G_v has degree 4 in G_v, total degree ≤ 5 in G,
  so max 1 edge to N(v) → at most 13 total edges
- Lower bound: Each vertex in N(v) has degree ≥ 4, uses 1 for v,
  needs ≥ 3 to G_v → at least 12 total edges

Case analysis:
1. If exactly 12 edges: One vertex w ∈ S has 0 edges to N(v), so deg(w) = 4.
   Then G_w (non-neighbors of w) must also be H13 (4-regular).
   But N(v) ⊆ G_w, and vertices in N(v) lose edges when restricted to G_w,
   breaking the regularity. Contradiction.

2. If exactly 13 edges: Degrees in N(v) sum to 4 + 13 = 17.
   Only partition of 17 into 4 parts (≥ 4 each): {4,4,4,5}.
   Pick u ∈ N(v) with deg(u) = 4. Then G_u must be H13 (4-regular).
   Pick another z ∈ N(v) with deg(z) = 4. Then z ∈ G_u (since N(v) independent).
   But z is connected to v in G, and v ∈ N(u), so in G_u, z loses edge to v.
   Thus deg_{G_u}(z) = 3, contradicting G_u being 4-regular.

TODO: Complete the technical Lean proof.
-/
lemma degree_not_four_of_triangleFree_no_6indep
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no6 : NoKIndepSet 6 G)
    (h_max_deg : ∀ v, G.degree v ≤ 5)
    (h_min_deg : ∀ v, G.degree v ≥ 4)
    (v : Fin 18) :
    G.degree v ≠ 4 := by
  sorry

lemma claim1_five_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    IsKRegular G 5 := by
  -- Part 1: degree <= 5
  have h_le : ∀ v, G.degree v ≤ 5 := by
    intro v
    apply degree_le_of_triangleFree_no_indep h_tri h_no6

  -- Part 2: degree >= 4 (proven via R(3,5)=14)
  have h_ge_4 : ∀ v, G.degree v ≥ 4 := by
    intro v
    exact degree_ge_four_of_triangleFree_no_6indep h_tri h_no6 v

  -- Part 3: degree = 4 leads to contradiction
  -- Uses the fact that H13 (unique Ramsey(3,5;13) graph) is 4-regular
  have h_no_deg_4 : ∀ v, G.degree v ≠ 4 := by
    intro v
    exact degree_not_four_of_triangleFree_no_6indep h_tri h_no6 h_le h_ge_4 v

  -- Therefore degree = 5
  have h_ge : ∀ v, G.degree v ≥ 5 := by
    intro v
    have h_le_v := h_le v
    have h_ge_4_v := h_ge_4 v
    have h_no_4_v := h_no_deg_4 v
    omega

  intro v
  exact le_antisymm (h_le v) (h_ge v)

/-! ## Claims 2 & 3 & Final -/

/-! ### Claim 2: Neighbor structure partition

In a 5-regular triangle-free graph on 18 vertices with no 6-independent set,
the non-neighbors of any vertex v partition into sets P (4 vertices sharing 1 common
neighbor with v) and Q (8 vertices sharing 2 common neighbors with v).

This follows from double-counting: each of v's 5 neighbors has degree 5, uses 1 edge
to v, and has 4 remaining edges. Triangle-freeness means N(v) is independent, so these
20 total edges must go to the 12 non-neighbors of v. Solving P + Q = 12 and P + 2Q = 20
gives P = 4, Q = 8.

TODO: Complete the edge-counting argument.
-/

/-! ### Claim 2 Helper Lemmas -/

/-- Common neighbors lower bound: Every non-neighbor of v has at least 1 common neighbor.
If w had 0 common neighbors with v, then N(v) ∪ {w} would be a 6-independent set. -/
lemma commonNeighborsCard_pos
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no6 : NoKIndepSet 6 G)
    (h_reg : IsKRegular G 5)
    (v w : Fin 18)
    (hw_neq : w ≠ v)
    (hw_nonadj : ¬G.Adj v w) :
    0 < commonNeighborsCard G v w := by
  by_contra h_zero
  push_neg at h_zero
  have h_zero' : commonNeighborsCard G v w = 0 := Nat.le_zero.mp h_zero

  -- N(v) is independent (triangle-free)
  let N := G.neighborFinset v
  have hN_card : N.card = 5 := h_reg v
  have hN_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v

  -- commonNeighbors = ∅ means w has no neighbors in N(v)
  have h_empty : _root_.commonNeighbors G v w = ∅ := by
    unfold commonNeighborsCard _root_.commonNeighbors at h_zero'
    exact Finset.card_eq_zero.mp h_zero'

  have hw_no_neighbors_in_N : ∀ n ∈ N, ¬G.Adj w n := by
    intro n hn
    unfold _root_.commonNeighbors at h_empty
    rw [Finset.eq_empty_iff_forall_not_mem] at h_empty
    intro h_adj
    have hmem : n ∈ G.neighborFinset v ∩ G.neighborFinset w := by
      rw [Finset.mem_inter]
      constructor
      · exact hn
      · rw [mem_neighborFinset]
        exact h_adj
    exact h_empty n hmem

  -- Build 6-independent set: N ∪ {w}
  let I := insert w N
  have hI_card : I.card = 6 := by
    rw [Finset.card_insert_of_not_mem, hN_card]
    intro h_in_N
    rw [mem_neighborFinset] at h_in_N
    exact hw_nonadj h_in_N

  have hI_indep : G.IsNIndepSet 6 I := by
    rw [isNIndepSet_iff]
    constructor
    · -- IsIndepSet: show no two distinct elements of I = insert w N are adjacent
      intro x hx y hy hxy
      -- hx : x ∈ I, but I = insert w N, so convert to x = w ∨ x ∈ N
      have hx' : x = w ∨ x ∈ N := Finset.mem_insert.mp hx
      have hy' : y = w ∨ y ∈ N := Finset.mem_insert.mp hy
      -- Case split using obtain
      obtain hxw | hxN := hx'
      · -- Case x = w
        obtain hyw | hyN := hy'
        · -- y = w too, but x ≠ y, contradiction
          subst hxw hyw
          exact (hxy rfl).elim
        · -- y ∈ N, show ¬G.Adj w y
          subst hxw
          exact hw_no_neighbors_in_N y hyN
      · -- Case x ∈ N
        obtain hyw | hyN := hy'
        · -- y = w, show ¬G.Adj x w
          subst hyw
          intro h_adj
          exact hw_no_neighbors_in_N x hxN (G.adj_symm h_adj)
        · -- Both x, y ∈ N: use that N(v) is independent
          intro h_adj
          have hxN' : x ∈ G.neighborSet v := by rw [mem_neighborSet, ← mem_neighborFinset]; exact hxN
          have hyN' : y ∈ G.neighborSet v := by rw [mem_neighborSet, ← mem_neighborFinset]; exact hyN
          exact hN_indep hxN' hyN' hxy h_adj
    · exact hI_card

  exact h_no6 I hI_indep

/-- Common neighbors upper bound: Every non-neighbor of v has at most 2 common neighbors.
If w had ≥3 common neighbors, it would have ≤2 neighbors in M, leaving ≥9 non-neighbors.
R(3,4)=9 would give a 4-independent set in those 9 vertices, extending to 6-independent with v,w. -/
lemma commonNeighborsCard_le_two
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no6 : NoKIndepSet 6 G)
    (h_reg : IsKRegular G 5)
    (v w : Fin 18)
    (hw_neq : w ≠ v)
    (hw_nonadj : ¬G.Adj v w) :
    commonNeighborsCard G v w ≤ 2 := by
  by_contra h_gt
  push_neg at h_gt

  -- Setup: N = neighbors of v, M = non-neighbors of v (excluding v)
  let N := G.neighborFinset v
  let M := Finset.univ \ insert v N
  have hN_card : N.card = 5 := h_reg v

  -- |M| = 18 - 6 = 12
  have hM_card : M.card = 12 := by
    have h_univ : (Finset.univ : Finset (Fin 18)).card = 18 := Finset.card_fin 18
    have h_not_self : v ∉ N := G.notMem_neighborFinset_self v
    have h_insert : (insert v N).card = 6 := by
      rw [Finset.card_insert_of_notMem h_not_self, hN_card]
    have h_inter : insert v N ∩ Finset.univ = insert v N := Finset.inter_univ _
    rw [Finset.card_sdiff, h_inter, h_univ, h_insert]

  -- w ∈ M (since w is not v and not adjacent to v)
  have hw_in_M : w ∈ M := by
    simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    constructor
    · exact hw_neq
    · intro h_in_N
      rw [mem_neighborFinset] at h_in_N
      exact hw_nonadj h_in_N

  -- M' = M \ {w} has 11 vertices
  let M' := M.erase w
  have hM'_card : M'.card = 11 := by
    rw [Finset.card_erase_of_mem hw_in_M, hM_card]

  -- Degree partitioning: w has ≤2 neighbors in M'
  have h_w_nbrs_in_M_le : (M' ∩ G.neighborFinset w).card ≤ 2 := by
    -- Partition w's neighbors: Nw = (Nw ∩ N) ∪ (Nw \ N)
    let Nw := G.neighborFinset w
    have h_common_ge : (Nw ∩ N).card ≥ 3 := by
      -- commonNeighborsCard G v w = (N ∩ Nw).card = (Nw ∩ N).card
      have : (N ∩ Nw).card = commonNeighborsCard G v w := rfl
      rw [Finset.inter_comm] at this
      omega
    -- Show Nw = (Nw ∩ N) ∪ (Nw \ N)
    have h_partition : Nw = (Nw ∩ N) ∪ (Nw \ N) := by
      ext x
      simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    -- Show disjoint
    have h_disj : Disjoint (Nw ∩ N) (Nw \ N) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    -- Show card sum
    have h_card_sum : (Nw ∩ N).card + (Nw \ N).card = Nw.card := by
      rw [← Finset.card_union_of_disjoint h_disj, ← h_partition]
    have h_deg_w : Nw.card = 5 := h_reg w
    have h_sdiff_le : (Nw \ N).card ≤ 2 := by omega
    -- M' ∩ Nw ⊆ Nw \ N
    have h_sub : M' ∩ Nw ⊆ Nw \ N := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢
      simp only [M', M, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_univ, true_and] at hx
      tauto
    exact Finset.card_le_card h_sub |>.trans h_sdiff_le

  -- X = non-neighbors of w in M', |X| ≥ 9
  let X := M'.filter (fun x => ¬G.Adj w x)
  have hX_card_ge : X.card ≥ 9 := by
    have h_complement : M' = (M' ∩ G.neighborFinset w) ∪ X := by
      ext x
      simp only [Finset.mem_union, X, Finset.mem_filter, Finset.mem_inter, mem_neighborFinset]
      constructor
      · intro hx
        by_cases h_adj : G.Adj w x
        · left; exact ⟨hx, h_adj⟩
        · right; exact ⟨hx, h_adj⟩
      · intro h; cases h <;> tauto
    have h_disjoint : Disjoint (M' ∩ G.neighborFinset w) X := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x; simp [X, Finset.mem_inter, Finset.mem_filter, mem_neighborFinset]
      tauto
    have h_card_sum : (M' ∩ G.neighborFinset w).card + X.card = M'.card := by
      rw [← Finset.card_union_of_disjoint h_disjoint, ← h_complement]
    omega

  -- Apply R(3,4)=9 to a 9-element subset of X
  obtain ⟨X9, hX9_sub, hX9_card⟩ := Finset.exists_subset_card_eq hX_card_ge

  have h_X9_card_type : Fintype.card (↑X9 : Set (Fin 18)) = 9 := by
    simp [Fintype.card_coe, hX9_card]
  have h_card_eq : Fintype.card (Fin 9) = Fintype.card (↑X9 : Set (Fin 18)) := by
    simp only [Fintype.card_fin]; exact h_X9_card_type.symm
  let e : Fin 9 ≃ (↑X9 : Set (Fin 18)) := Fintype.equivOfCardEq h_card_eq
  let f : Fin 9 ↪ Fin 18 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let G_X9 := G.comap f

  have h_ramsey : HasRamseyProperty 3 4 G_X9 := hasRamseyProperty_3_4_9.2 G_X9
  rcases h_ramsey with ⟨S, hS⟩ | ⟨T, hT⟩

  · -- 3-clique → triangle
    have h_clique_G : G.IsNClique 3 (S.map f) := by
      constructor
      · intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
        have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
        exact hS.1 hx' hy' hne
      · simp [Finset.card_map, hS.2]
    exact h_tri (S.map f) h_clique_G

  · -- 4-independent set → extend to 6-independent with v,w
    have h_X9_nonadj_v : ∀ x ∈ X9, ¬G.Adj v x := by
      intro x hx
      have hxX : x ∈ X := hX9_sub hx
      simp only [X, Finset.mem_filter, M'] at hxX
      have hxM : x ∈ M := Finset.mem_of_mem_erase hxX.1
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or] at hxM
      intro h_adj
      rw [mem_neighborFinset] at hxM
      exact hxM.2 h_adj

    have h_X9_nonadj_w : ∀ x ∈ X9, ¬G.Adj w x := by
      intro x hx
      have hxX : x ∈ X := hX9_sub hx
      simp only [X, Finset.mem_filter] at hxX
      exact hxX.2

    let I := insert v (insert w (T.map f))
    have hI_indep : G.IsNIndepSet 6 I := by
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hxy h_adj
        have hx' : x = v ∨ x ∈ insert w (T.map f) := Finset.mem_insert.mp hx
        have hy' : y = v ∨ y ∈ insert w (T.map f) := Finset.mem_insert.mp hy
        obtain rfl | hx_wT := hx' <;> obtain rfl | hy_wT := hy'
        · exact hxy rfl
        · obtain rfl | hy_T := Finset.mem_insert.mp hy_wT
          · exact hw_nonadj h_adj
          · rcases Finset.mem_map.mp hy_T with ⟨y', hy', rfl⟩
            have : (f y') ∈ X9 := by change (e y').val ∈ X9; exact (e y').property
            exact h_X9_nonadj_v (f y') this h_adj
        · obtain rfl | hx_T := Finset.mem_insert.mp hx_wT
          · exact hw_nonadj (G.adj_symm h_adj)
          · rcases Finset.mem_map.mp hx_T with ⟨x', hx', rfl⟩
            have : (f x') ∈ X9 := by change (e x').val ∈ X9; exact (e x').property
            exact h_X9_nonadj_v (f x') this (G.adj_symm h_adj)
        · obtain rfl | hx_T := Finset.mem_insert.mp hx_wT <;> obtain rfl | hy_T := Finset.mem_insert.mp hy_wT
          · exact hxy rfl
          · rcases Finset.mem_map.mp hy_T with ⟨y', hy', rfl⟩
            have : (f y') ∈ X9 := by change (e y').val ∈ X9; exact (e y').property
            exact h_X9_nonadj_w (f y') this h_adj
          · rcases Finset.mem_map.mp hx_T with ⟨x', hx', rfl⟩
            have : (f x') ∈ X9 := by change (e x').val ∈ X9; exact (e x').property
            exact h_X9_nonadj_w (f x') this (G.adj_symm h_adj)
          · rcases Finset.mem_map.mp hx_T with ⟨x', hx', rfl⟩
            rcases Finset.mem_map.mp hy_T with ⟨y', hy', rfl⟩
            have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
            exact hT.1 hx' hy' hne h_adj
      · have h_v_ne_w : v ≠ w := hw_neq.symm
        have h_v_notin_T : v ∉ T.map f := by
          intro hv_in
          rcases Finset.mem_map.mp hv_in with ⟨t, _, hv_eq_ft⟩
          have hft_in_X9 : (f t) ∈ X9 := by
            change (e t).val ∈ X9
            exact (e t).property
          -- Now have v = f t ∈ X9 ⊆ X ⊆ M' ⊆ M
          have hvX : v ∈ X := by
            rw [← hv_eq_ft]
            exact hX9_sub hft_in_X9
          have hvM' : v ∈ M' := by
            simp only [X, Finset.mem_filter] at hvX
            exact hvX.1
          have hvM : v ∈ M := Finset.mem_of_mem_erase hvM'
          -- But M = univ \ insert v N, so v ∉ insert v N, which contradicts v ∈ insert v
          have : v ∉ insert v N := by
            simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hvM
            exact hvM
          have hv_in : v ∈ insert v N := Finset.mem_insert_self v N
          exact this hv_in
        have h_w_notin_T : w ∉ T.map f := by
          intro hw_in
          rcases Finset.mem_map.mp hw_in with ⟨t, _, hw_eq_ft⟩
          have hft_in_X9 : (f t) ∈ X9 := by
            change (e t).val ∈ X9
            exact (e t).property
          -- Now have w = f t ∈ X9 ⊆ X, but X is filter of M', and M' = M.erase w
          have hwX : w ∈ X := by
            rw [← hw_eq_ft]
            exact hX9_sub hft_in_X9
          have hwM' : w ∈ M' := by
            simp only [X, Finset.mem_filter] at hwX
            exact hwX.1
          -- But M' = M.erase w, so w ∉ M' (contradiction!)
          have hw_ne_w : w ≠ w := by
            simp only [M', Finset.mem_erase] at hwM'
            exact hwM'.1
          exact hw_ne_w rfl
        have h_v_notin_wT : v ∉ insert w (T.map f) := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨h_v_ne_w, h_v_notin_T⟩
        rw [Finset.card_insert_of_notMem h_v_notin_wT,
            Finset.card_insert_of_notMem h_w_notin_T,
            Finset.card_map, hT.2]

    exact h_no6 I hI_indep

lemma claim2_neighbor_structure {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) (v : Fin 18) :
    ∃ (P Q : Finset (Fin 18)),
      P.card = 4 ∧ Q.card = 8 ∧
      (∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) ∧
      (∀ q ∈ Q, ¬G.Adj v q ∧ commonNeighborsCard G v q = 2) := by
  classical
  -- Setup: N = neighbors of v, M = non-neighbors of v
  let N := G.neighborFinset v
  let M := Finset.univ \ insert v N
  have hN_card : N.card = 5 := h_reg v
  have hv_notin_N : v ∉ N := G.notMem_neighborFinset_self v

  -- |M| = 12 (same proof as in commonNeighborsCard_le_two)
  have hM_card : M.card = 12 := by
    have h_univ : (Finset.univ : Finset (Fin 18)).card = 18 := Finset.card_fin 18
    rw [Finset.card_sdiff (Finset.subset_univ _)]
    rw [h_univ, Finset.card_insert_of_notMem hv_notin_N, hN_card]

  -- Define P and Q by filtering M
  let P := M.filter (fun w => commonNeighborsCard G v w = 1)
  let Q := M.filter (fun w => commonNeighborsCard G v w = 2)

  -- Key fact: every w in M has exactly 1 or 2 common neighbors
  have h_M_bounds : ∀ w ∈ M, commonNeighborsCard G v w = 1 ∨ commonNeighborsCard G v w = 2 := by
    intro w hwM
    -- w is in M = univ \ insert v N, so w ≠ v and w ∉ N
    have hw_props : w ∈ Finset.univ ∧ w ∉ insert v N := Finset.mem_sdiff.mp hwM
    have hw_ne_v : w ≠ v := by
      intro h
      have : w ∉ insert v N := hw_props.2
      simp [h] at this
    have hw_nonadj : ¬G.Adj v w := by
      intro h_adj
      have : w ∉ insert v N := hw_props.2
      rw [mem_neighborFinset] at h_adj
      simp [h_adj] at this
    -- Apply our proven bounds
    have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v w hw_ne_v hw_nonadj
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v w hw_ne_v hw_nonadj
    omega

  -- P and Q partition M
  have hPQ_union : P ∪ Q = M := by
    ext w
    simp only [P, Q, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      cases h with
      | inl hp => exact hp.1
      | inr hq => exact hq.1
    · intro hwM
      have := h_M_bounds w hwM
      cases this with
      | inl h1 => left; exact ⟨hwM, h1⟩
      | inr h2 => right; exact ⟨hwM, h2⟩

  have hPQ_disj : Disjoint P Q := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext w
    simp only [P, Q, Finset.mem_inter, Finset.mem_filter, Finset.not_mem_empty, iff_false]
    intro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    rw [h1] at h2
    norm_num at h2

  have hPQ_card_sum : P.card + Q.card = 12 := by
    rw [← Finset.card_union_of_disjoint hPQ_disj, hPQ_union, hM_card]

  -- Edge counting argument via double-counting
  -- Sum of commonNeighborsCard over M equals 20
  -- (each neighbor of v has degree 5, uses 1 edge on v, 0 on other neighbors, 4 on M)
  have h_sum_eq_20 : M.sum (fun w => commonNeighborsCard G v w) = 20 := by
    -- Count edges between N and M from both sides
    -- From M side: ∑_{w ∈ M} |N ∩ neighbors(w)| = ∑_{w ∈ M} commonNeighborsCard(v,w)
    -- From N side: ∑_{n ∈ N} |neighbors(n) ∩ M|

    -- Key: common neighbors of v and w are exactly N ∩ neighbors(w)
    have h_common_eq : ∀ w ∈ M, commonNeighborsCard G v w =
        (N.filter (fun n => G.Adj n w)).card := by
      intro w hwM
      unfold commonNeighborsCard _root_.commonNeighbors
      congr 1
      ext n
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborFinset, Finset.mem_filter]
      constructor
      · intro h
        obtain ⟨hn1, hn2⟩ := h
        exact ⟨hn1, G.adj_comm.mp hn2⟩
      · intro h
        obtain ⟨hn, hadj⟩ := h
        exact ⟨hn, G.adj_comm.mp hadj⟩

    -- Rewrite LHS using this
    have h_rewrite : M.sum (fun w => commonNeighborsCard G v w) =
        M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) := by
      congr 1
      ext w
      by_cases hw : w ∈ M
      · exact h_common_eq w hw
      · simp [hw]
    rw [h_rewrite]

    -- Now apply double-counting: this equals ∑_{n ∈ N} |neighbors(n) ∩ M|
    rw [show M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) =
            N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) by
      -- Double-counting edges between N and M
      -- Define edge set E = {(n,w) : n ∈ N, w ∈ M, Adj n w}
      classical
      let E := (N ×ˢ M).filter (fun p => G.Adj p.1 p.2)

      -- Count E by first coordinate: ∑_{w ∈ M} |{n ∈ N : Adj n w}|
      have h_from_M : M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) = E.card := by
        rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := M)]
        · congr 1
          ext w
          simp only [E, mem_filter, mem_product]
        · intros p hp
          obtain ⟨n, w⟩ := p
          simp only [E, mem_filter, mem_product] at hp
          exact hp.1.2

      -- Count E by second coordinate: ∑_{n ∈ N} |{w ∈ M : Adj n w}|
      have h_from_N : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) = E.card := by
        rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := N)]
        · congr 1
          ext n
          simp only [E, mem_filter, mem_product]
        · intros p hp
          obtain ⟨n, w⟩ := p
          simp only [E, mem_filter, mem_product] at hp
          exact hp.1.1

      omega
    ]

    -- Each n ∈ N has degree 5, adjacent to v, not adjacent to other neighbors (triangle-free)
    -- So n has exactly 4 neighbors in M
    have h_deg_in_M : ∀ n ∈ N, (M.filter (fun w => G.Adj n w)).card = 4 := by
      intro n hnN
      -- n has degree 5
      have h_deg_n : (G.neighborFinset n).card = 5 := h_reg n
      -- Partition neighbors of n: {v} ∪ (N \ {n}) ∪ (M ∩ neighbors(n))
      -- v ∈ neighbors(n) since n ∈ N
      have hn_adj_v : G.Adj n v := by
        rw [mem_neighborFinset] at hnN
        exact G.adj_comm.mp hnN
      -- N \ {n} and M are disjoint from v
      -- neighbors(n) ∩ (N \ {n}) = ∅ by triangle-free
      have h_no_nbr_in_N : ∀ m ∈ N, m ≠ n → ¬G.Adj n m := by
        intros m hmN hne
        intro h_adj
        -- Would form triangle: v-n-m-v
        have h_adj_mv : G.Adj m v := by
          rw [mem_neighborFinset] at hmN
          exact G.adj_comm.mp hmN
        exact h_tri v n m hn_adj_v h_adj (G.adj_comm.mp h_adj_mv)
      -- Count: neighbors(n) = {v} ∪ (M ∩ neighbors(n))
      have h_partition : G.neighborFinset n = insert v ((M.filter (fun w => G.Adj n w)).image id) := by
        ext w
        simp only [mem_neighborFinset, mem_insert, mem_image, mem_filter, id_eq, exists_prop, exists_eq_right]
        constructor
        · intro hw_adj
          by_cases hw_eq_v : w = v
          · left; exact hw_eq_v
          · right
            constructor
            · -- w ∈ M
              simp only [M, mem_sdiff, mem_univ, mem_insert, true_and]
              constructor
              · exact hw_eq_v
              · intro hw_in_N
                -- If w ∈ N, then n-w edge contradicts triangle-free (since both n,w ∈ N)
                have : w ≠ n := by
                  intro heq
                  subst heq
                  exact G.loopless n hw_adj
                exact h_no_nbr_in_N w hw_in_N this hw_adj
            · exact hw_adj
        · intro h
          cases h with
          | inl hw_v => subst hw_v; exact hn_adj_v
          | inr h_right =>
            obtain ⟨_, hw_adj⟩ := h_right
            exact hw_adj
      rw [h_partition, card_insert_of_notMem, card_image_of_injective] at h_deg_n
      · omega
      · intros x y; simp only [id_eq, imp_self]
      · simp only [mem_image, mem_filter, id_eq, exists_prop, exists_eq_right, not_and]
        intro h_contr
        have : v ∈ M := h_contr hn_adj_v
        simp only [M, mem_sdiff, mem_insert, mem_univ, true_and] at this
        simp at this

    -- Sum equals 5 * 4 = 20
    have h_all_4 : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) = N.sum (fun _ => 4) := by
      apply sum_congr rfl h_deg_in_M
    rw [h_all_4]
    -- ∑ n ∈ N, 4 = 5 * 4 = 20
    rw [show N.sum (fun _ : Fin 18 => (4 : ℕ)) = N.card * 4 by
      induction' N using Finset.induction with x s hx ih
      · simp
      · rw [sum_insert hx, card_insert_of_notMem hx, ih]
        ring
    ]
    rw [hN_card]; norm_num

  -- Split sum over P and Q
  have h_sum_split : M.sum (fun w => commonNeighborsCard G v w) =
                      P.sum (fun w => commonNeighborsCard G v w) +
                      Q.sum (fun w => commonNeighborsCard G v w) := by
    rw [← hPQ_union]
    exact Finset.sum_union hPQ_disj

  -- On P, commonNeighborsCard = 1
  have h_sum_P : P.sum (fun w => commonNeighborsCard G v w) = P.card := by
    have : ∀ w ∈ P, commonNeighborsCard G v w = 1 := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    simp only [this, Finset.sum_const, nsmul_eq_mul, mul_one]

  -- On Q, commonNeighborsCard = 2
  have h_sum_Q : Q.sum (fun w => commonNeighborsCard G v w) = 2 * Q.card := by
    have : ∀ w ∈ Q, commonNeighborsCard G v w = 2 := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    simp only [this, Finset.sum_const, nsmul_eq_mul]

  -- Linear system: P.card + 2*Q.card = 20
  have h_linear : P.card + 2 * Q.card = 20 := by
    calc P.card + 2 * Q.card
        = P.sum (fun w => commonNeighborsCard G v w) +
          Q.sum (fun w => commonNeighborsCard G v w) := by rw [h_sum_P, h_sum_Q]
      _ = M.sum (fun w => commonNeighborsCard G v w) := by rw [← h_sum_split]
      _ = 20 := h_sum_eq_20

  -- Solve the system
  have hP_card : P.card = 4 := by omega
  have hQ_card : Q.card = 8 := by omega

  -- Build the result
  use P, Q
  refine ⟨hP_card, hQ_card, ?_, ?_⟩
  -- Prove properties of P
  · intro p hp
    have hpM : p ∈ M := (Finset.mem_filter.mp hp).1
    have hp_eq1 : commonNeighborsCard G v p = 1 := (Finset.mem_filter.mp hp).2
    have hp_props : p ∈ Finset.univ ∧ p ∉ insert v N := Finset.mem_sdiff.mp hpM
    have hp_nonadj : ¬G.Adj v p := by
      intro h_adj
      have : p ∉ insert v N := hp_props.2
      have h_in_N : p ∈ N := by
        rw [mem_neighborFinset]
        exact h_adj
      simp [h_in_N] at this
    exact ⟨hp_nonadj, hp_eq1⟩
  -- Prove properties of Q
  · intro q hq
    have hqM : q ∈ M := (Finset.mem_filter.mp hq).1
    have hq_eq2 : commonNeighborsCard G v q = 2 := (Finset.mem_filter.mp hq).2
    have hq_props : q ∈ Finset.univ ∧ q ∉ insert v N := Finset.mem_sdiff.mp hqM
    have hq_nonadj : ¬G.Adj v q := by
      intro h_adj
      have : q ∉ insert v N := hq_props.2
      have h_in_N : q ∈ N := by
        rw [mem_neighborFinset]
        exact h_adj
      simp [h_in_N] at this
    exact ⟨hq_nonadj, hq_eq2⟩

lemma claim3_four_cycle {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP : P.card = 4 ∧ ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∃ (p1 p2 p3 p4 : Fin 18), P = {p1, p2, p3, p4} ∧ G.Adj p1 p2 := by
  sorry

lemma final_contradiction {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    False := by
  sorry

/-! ## Upper Bound Theorem -/

theorem ramsey_three_six_upper_bound_property :
    HasRamseyProperty 3 6 (completeGraph (Fin 18)) := by
  sorry

/-- Upper bound primitive: 18 has the Ramsey property.
    (This is the goal of the combinatorial proof in this file) -/
theorem hasRamseyProperty_3_6_18 :
    0 < 18 ∧ ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj], HasRamseyProperty 3 6 G := by
  constructor
  · simp
  · intro G inst
    -- Main upper bound proof
    -- By contradiction, assume NOT Ramsey
    by_contra h_not_ramsey
    unfold HasRamseyProperty at h_not_ramsey
    push_neg at h_not_ramsey
    rcases h_not_ramsey with ⟨h_no_clique, h_no_indep⟩
    
    have h_tri : TriangleFree G := by
      intro t ht
      exact h_no_clique t ht
      
    have h_no6 : NoKIndepSet 6 G := by
      intro t ht
      exact h_no_indep t ht

    have h_reg : IsKRegular G 5 := claim1_five_regular h_tri h_no6
    exact final_contradiction h_reg h_tri h_no6

/-- The set of Ramsey numbers for (3,6) is nonempty. -/
theorem ramseySet_3_6_nonempty :
    Set.Nonempty {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 6 G} :=
  ⟨18, hasRamseyProperty_3_6_18⟩

theorem ramsey_three_six_upper : ramseyNumber 3 6 ≤ 18 := by
  apply csInf_le
  · -- Set is bounded below by 0 (trivial for Nat)
    use 0
    intro n hn
    exact Nat.zero_le n
  · -- 18 is in the set
    exact hasRamseyProperty_3_6_18
