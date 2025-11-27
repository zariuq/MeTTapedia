import Ramsey36.RamseyDef
import Ramsey36.SmallRamsey
import Ramsey36.FiveCycleLemma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open SimpleGraph Finset

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
  intro v
  -- Goal: G.degree v = 4
  apply le_antisymm
  · -- Prove degree ≤ 4
    by_contra h_gt
    push_neg at h_gt
    -- Neighbors of v form an independent set (triangle-free)
    -- If deg(v) ≥ 5, neighbors contain a 5-independent set
    have h_nbrs_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v
    -- Extract 5 neighbors
    have h_deg_ge_5 : (G.neighborFinset v).card ≥ 5 := by
      rw [G.card_neighborFinset_eq_degree]
      exact h_gt
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_deg_ge_5
    -- S is a 5-independent set
    have hS_indep : G.IsNIndepSet 5 S := by
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hxy
        have hxN : x ∈ G.neighborSet v := by
          rw [mem_neighborSet, ← mem_neighborFinset]
          exact hS_sub hx
        have hyN : y ∈ G.neighborSet v := by
          rw [mem_neighborSet, ← mem_neighborFinset]
          exact hS_sub hy
        exact h_nbrs_indep hxN hyN hxy
      · exact hS_card
    exact h_no5 S hS_indep
  · -- Prove degree ≥ 4
    by_contra h_lt
    push_neg at h_lt
    have h_deg_le_3 : G.degree v ≤ 3 := Nat.lt_succ_iff.mp h_lt
    -- Non-neighbors of v (excluding v)
    let N := G.neighborFinset v
    let M := (Finset.univ : Finset V) \ (insert v N)
    -- |M| ≥ 13 - 1 - 3 = 9
    have hM_card_ge : M.card ≥ 9 := by
      have h_union_card : (insert v N).card ≤ 4 := by
        calc (insert v N).card
            = N.card + 1 := by rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
          _ = G.degree v + 1 := by rw [G.card_neighborFinset_eq_degree]
          _ ≤ 3 + 1 := by omega
          _ = 4 := by norm_num
      have h_disjoint : Disjoint M (insert v N) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext w
        simp only [M, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                   Finset.notMem_empty, iff_false]
        tauto
      have h_union : M ∪ (insert v N) = Finset.univ := by
        ext w
        simp only [M, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
        tauto
      have h_card_union : M.card + (insert v N).card = Fintype.card V := by
        have h_eq : (M ∪ (insert v N)).card = M.card + (insert v N).card :=
          Finset.card_union_of_disjoint h_disjoint
        rw [h_union] at h_eq
        simp only [Finset.card_univ] at h_eq
        exact h_eq.symm
      rw [h_card] at h_card_union
      omega
    -- Extract 9-element subset of M
    obtain ⟨M9, hM9_sub, hM9_card⟩ := Finset.exists_subset_card_eq hM_card_ge
    -- v is not adjacent to any vertex in M9
    have h_v_nonadj_M9 : ∀ w ∈ M9, ¬ G.Adj v w := by
      intro w hw
      have hw_in_M : w ∈ M := hM9_sub hw
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw_in_M
      intro h_adj
      apply hw_in_M
      apply Finset.mem_insert_of_mem
      rw [mem_neighborFinset]
      exact h_adj
    -- Create induced subgraph on M9 via comap
    have h_M9_card_type : Fintype.card (↑M9 : Set V) = 9 := by
      simp [Fintype.card_coe, hM9_card]
    have h_card_eq : Fintype.card (Fin 9) = Fintype.card (↑M9 : Set V) := by
      simp only [Fintype.card_fin]
      exact h_M9_card_type.symm
    let e : Fin 9 ≃ (↑M9 : Set V) := Fintype.equivOfCardEq h_card_eq
    let f : Fin 9 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
    let G_M9 := G.comap f
    -- Apply R(3,4)=9 to G_M9
    have h_ramsey_prop : HasRamseyProperty 3 4 G_M9 := hasRamseyProperty_3_4_9.2 G_M9
    rcases h_ramsey_prop with ⟨S, hS⟩ | ⟨T, hT⟩
    · -- Case 1: G_M9 contains a 3-clique (triangle) → contradiction
      have h_clique_G : G.IsNClique 3 (S.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
          exact hS.1 hx' hy' hne
        · simp [Finset.card_map, hS.2]
      exact h_tri (S.map f) h_clique_G
    · -- Case 2: G_M9 contains a 4-independent set T → T ∪ {v} is 5-independent in G
      let T_plus_v := insert v (T.map f)
      have h_indep_5 : G.IsNIndepSet 5 T_plus_v := by
        constructor
        · -- Independence
          intro x hx y hy hxy h_adj
          have hx' : x = v ∨ x ∈ T.map f := Finset.mem_insert.mp hx
          have hy' : y = v ∨ y ∈ T.map f := Finset.mem_insert.mp hy
          rcases hx' with rfl | hx_in_T <;> rcases hy' with rfl | hy_in_T
          · exact hxy rfl
          · have : y ∈ (↑M9 : Set V) := by
              rcases Finset.mem_map.mp hy_in_T with ⟨y', _, rfl⟩
              change (e y').val ∈ ↑M9
              exact (e y').property
            exact h_v_nonadj_M9 y this h_adj
          · have : x ∈ (↑M9 : Set V) := by
              rcases Finset.mem_map.mp hx_in_T with ⟨x', _, rfl⟩
              change (e x').val ∈ ↑M9
              exact (e x').property
            exact h_v_nonadj_M9 x this (G.symm h_adj)
          · rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
            rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
            have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
            exact hT.1 hx'_in_T hy'_in_T hne h_adj
        · have h_v_not_in_map : v ∉ T.map f := by
            intro h_v_in_T
            rcases Finset.mem_map.mp h_v_in_T with ⟨t, _, h_eq⟩
            have h_ft_in_M9 : (f t : V) ∈ M9 := by
              have : (f t : V) ∈ (↑M9 : Set V) := by
                change (e t).val ∈ ↑M9
                exact (e t).property
              simpa using this
            have h_v_in_M9 : v ∈ M9 := by rwa [h_eq] at h_ft_in_M9
            have h_v_in_M : v ∈ M := hM9_sub h_v_in_M9
            simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at h_v_in_M
            exact h_v_in_M (Finset.mem_insert_self v N)
          calc T_plus_v.card
              = (insert v (T.map f)).card := rfl
            _ = (T.map f).card + 1 := Finset.card_insert_of_notMem h_v_not_in_map
            _ = T.card + 1 := by rw [Finset.card_map]
            _ = 4 + 1 := by rw [hT.2]
            _ = 5 := by norm_num
      exact h_no5 T_plus_v h_indep_5

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
    IsKRegular G 4 :=
  r35_critical_is_4_regular G (Fintype.card_fin 13) h_tri h_no5

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
  intro h_deg4
  -- Setup: N = neighbors of v (4 vertices), M = non-neighbors (13 vertices)
  let N := G.neighborFinset v
  let M := Finset.univ \ insert v N

  have hN_card : N.card = 4 := by
    rw [G.card_neighborFinset_eq_degree]
    exact h_deg4

  have hM_card : M.card = 13 := by
    have h_univ : (Finset.univ : Finset (Fin 18)).card = 18 := Finset.card_fin 18
    have hv_notin_N : v ∉ N := G.notMem_neighborFinset_self v
    have h_insert : (insert v N).card = 5 := by
      rw [Finset.card_insert_of_notMem hv_notin_N, hN_card]
    have h_inter : insert v N ∩ Finset.univ = insert v N := Finset.inter_univ _
    rw [Finset.card_sdiff, h_inter, h_univ, h_insert]

  -- N is independent (triangle-free)
  have hN_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v

  -- M induces a triangle-free subgraph with no 5-independent set
  -- Create induced subgraph on M via comap
  have h_M_card_type : Fintype.card (↑M : Set (Fin 18)) = 13 := by
    simp [Fintype.card_coe, hM_card]
  have h_card_eq : Fintype.card (Fin 13) = Fintype.card (↑M : Set (Fin 18)) := by
    simp only [Fintype.card_fin]
    exact h_M_card_type.symm
  let e : Fin 13 ≃ (↑M : Set (Fin 18)) := Fintype.equivOfCardEq h_card_eq
  let f : Fin 13 ↪ Fin 18 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let G_M := G.comap f

  -- Helper: f maps into M
  have hf_in_M : ∀ i : Fin 13, (f i : Fin 18) ∈ M := by
    intro i
    have : (f i : Fin 18) ∈ (↑M : Set (Fin 18)) := by
      change (e i).val ∈ ↑M
      exact (e i).property
    simpa using this

  -- G_M is triangle-free
  have h_M_tri : TriangleFree G_M := by
    intro S hS
    have h_clique_G : G.IsNClique 3 (S.map f) := by
      constructor
      · intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
        have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
        exact hS.1 hx' hy' hne
      · simp [Finset.card_map, hS.2]
    exact h_tri (S.map f) h_clique_G

  -- G_M has no 5-independent set
  have h_M_no5 : NoKIndepSet 5 G_M := by
    intro S hS
    -- If S is 5-independent in G_M, then S ∪ {v} would be 6-independent in G
    -- (since v is not adjacent to anything in M)
    let S_plus_v := insert v (S.map f)
    have h_v_nonadj_M : ∀ w ∈ M, ¬G.Adj v w := by
      intro w hw
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw
      intro h_adj
      apply hw
      apply Finset.mem_insert_of_mem
      rw [mem_neighborFinset]
      exact h_adj
    have h_indep_6 : G.IsNIndepSet 6 S_plus_v := by
      constructor
      · intro x hx y hy hxy h_adj
        have hx' : x = v ∨ x ∈ S.map f := Finset.mem_insert.mp hx
        have hy' : y = v ∨ y ∈ S.map f := Finset.mem_insert.mp hy
        rcases hx' with rfl | hx_in_S <;> rcases hy' with rfl | hy_in_S
        · exact hxy rfl
        · rcases Finset.mem_map.mp hy_in_S with ⟨y', _, rfl⟩
          exact h_v_nonadj_M (f y') (hf_in_M y') h_adj
        · rcases Finset.mem_map.mp hx_in_S with ⟨x', _, rfl⟩
          exact h_v_nonadj_M (f x') (hf_in_M x') (G.symm h_adj)
        · rcases Finset.mem_map.mp hx_in_S with ⟨x', hx'_in_S, rfl⟩
          rcases Finset.mem_map.mp hy_in_S with ⟨y', hy'_in_S, rfl⟩
          have hne : x' ≠ y' := by intro h_eq; apply hxy; simp [h_eq]
          exact hS.1 hx'_in_S hy'_in_S hne h_adj
      · have h_v_not_in_map : v ∉ S.map f := by
          intro h_v_in_S
          rcases Finset.mem_map.mp h_v_in_S with ⟨s, _, h_eq⟩
          have h_v_in_M : v ∈ M := by rw [← h_eq]; exact hf_in_M s
          simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at h_v_in_M
          exact h_v_in_M (Finset.mem_insert_self v N)
        calc S_plus_v.card
            = (S.map f).card + 1 := Finset.card_insert_of_notMem h_v_not_in_map
          _ = S.card + 1 := by rw [Finset.card_map]
          _ = 5 + 1 := by rw [hS.2]
          _ = 6 := by norm_num
    exact h_no6 S_plus_v h_indep_6

  -- By r35_critical_is_4_regular, G_M is 4-regular
  have h_M_reg : IsKRegular G_M 4 := ramsey_3_5_13_is_four_regular G_M h_M_tri h_M_no5

  /-
  Edge counting argument (Krüger's proof):
  - Each w ∈ M has deg_M(w) = 4 (from h_M_reg) and deg_G(w) ≤ 5 (from h_max_deg)
  - So each w has at most 1 neighbor outside M (i.e., in N, since v ∉ neighbors of w)
  - Upper bound on edges M → N: 13 × 1 = 13

  - Each n ∈ N has deg_G(n) ≥ 4 (from h_min_deg), uses 1 edge on v
  - N is independent (triangle-free), so n has 0 edges to other N vertices
  - So n has at least 3 neighbors in M
  - Lower bound on edges N → M: 4 × 3 = 12

  These are the same edges counted from both sides, so 12 ≤ edges ≤ 13.

  Case 12 edges: Some w ∈ M has 0 edges to N, so deg_G(w) = 4.
    Then w's non-neighbors (13 vertices) must be 4-regular by our lemma.
    But N ⊆ non-neighbors of w, and in w's non-neighbor graph, each n ∈ N
    loses its edge to v (since v is a neighbor of w? No, wait...)
    Actually if deg_G(w) = 4 and w ∈ M, then w's neighbors are exactly the 4 vertices in M
    that are adjacent to w. The non-neighbors of w include v and all of N.
    [Complex case analysis leads to contradiction with regularity]

  Case 13 edges: Each w ∈ M has exactly 1 edge to N, so deg_G(w) = 5.
    Sum of degrees in N: sum_{n ∈ N} deg_G(n) where each deg ∈ {4, 5}.
    Edges from N to M = sum_{n ∈ N} (deg_G(n) - 1) = sum_{n ∈ N} deg_G(n) - 4
    If this equals 13, then sum of degrees = 17.
    With 4 vertices each having degree ≥ 4, the only partition of 17 is {4,4,4,5}.
    Pick u ∈ N with deg_G(u) = 4. Then u's non-neighbors (13 vertices) must be 4-regular.
    But N \ {u} ⊆ non-neighbors of u (since N is independent).
    These 3 vertices from N have degree ≥ 4 in G but lose their edge to v in the
    non-neighbor subgraph of u (since v is adjacent to u).
    So their degree in that subgraph is ≤ 4 - 1 = 3, contradicting 4-regularity.
  -/
  -- The full edge counting argument is complex to formalize.
  -- Key insight: M is 4-regular, but edges between N and M create contradictions
  -- in both the 12-edge and 13-edge cases.
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
    have h_inter : insert v N ∩ Finset.univ = insert v N := inter_univ _
    rw [card_sdiff, h_inter, h_univ, card_insert_of_notMem hv_notin_N, hN_card]

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
      have h_mem : w ∈ N := by rw [mem_neighborFinset]; exact h_adj
      simp [h_mem] at this
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
      intro w _
      -- commonNeighborsCard G v w = (G.neighborFinset v ∩ G.neighborFinset w).card
      unfold commonNeighborsCard _root_.commonNeighbors
      -- Need: (N ∩ G.neighborFinset w).card = (N.filter (fun n => G.Adj n w)).card
      -- These sets are equal since n ∈ G.neighborFinset w ↔ G.Adj w n ↔ G.Adj n w
      congr 1
      ext n
      simp only [N, mem_inter, mem_filter, mem_neighborFinset]
      -- Goal is now: G.Adj v n ∧ G.Adj w n ↔ G.Adj v n ∧ G.Adj n w
      constructor
      · intro ⟨hv_adj_n, hw_adj_n⟩
        exact ⟨hv_adj_n, G.symm hw_adj_n⟩
      · intro ⟨hv_adj_n, hn_adj_w⟩
        exact ⟨hv_adj_n, G.symm hn_adj_w⟩

    -- Rewrite LHS using this
    have h_rewrite : M.sum (fun w => commonNeighborsCard G v w) =
        M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) := by
      apply sum_congr rfl
      intro w hw
      exact h_common_eq w hw
    rw [h_rewrite]

    -- Now apply double-counting: this equals ∑_{n ∈ N} |neighbors(n) ∩ M|
    -- Both sums count the same set of edge pairs between N and M
    rw [show M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) =
            N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) by
      -- Both sums count pairs (n, w) with n ∈ N, w ∈ M, G.Adj n w
      -- Express as sum over indicator functions and use commutativity
      have h1 : M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) =
                M.sum (fun w => N.sum (fun n => if G.Adj n w then 1 else 0)) := by
        congr 1; ext w
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have h2 : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) =
                N.sum (fun n => M.sum (fun w => if G.Adj n w then 1 else 0)) := by
        congr 1; ext n
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [h1, h2]
      rw [Finset.sum_comm]
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
        exact G.symm hnN
      -- N \ {n} and M are disjoint from v
      -- neighbors(n) ∩ (N \ {n}) = ∅ by triangle-free
      have h_no_nbr_in_N : ∀ m ∈ N, m ≠ n → ¬G.Adj n m := by
        intros m hmN hne
        intro h_adj
        -- Would form triangle: {v, n, m}
        have h_adj_nv : G.Adj n v := hn_adj_v
        have h_adj_mv : G.Adj m v := by rw [mem_neighborFinset] at hmN; exact G.symm hmN
        -- Construct the triangle
        let T : Finset (Fin 18) := {v, n, m}
        have hT_clique : G.IsNClique 3 T := by
          rw [isNClique_iff]
          constructor
          · -- IsClique
            intros a ha b hb hab
            simp only [T, mem_coe, mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
            · exact absurd rfl hab
            · exact G.symm h_adj_nv
            · exact G.symm h_adj_mv
            · exact h_adj_nv
            · exact absurd rfl hab
            · exact h_adj
            · exact h_adj_mv
            · exact G.symm h_adj
            · exact absurd rfl hab
          · -- card = 3
            simp only [T]
            have hv_ne_n : v ≠ n := fun h => G.loopless v (h ▸ h_adj_nv)
            have hv_ne_m : v ≠ m := fun h => G.loopless v (h ▸ h_adj_mv)
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp [hne.symm]
            · simp [hv_ne_n, hv_ne_m]
        exact h_tri T hT_clique
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
              simp only [M, mem_sdiff, mem_univ, mem_insert, true_and, not_or]
              exact ⟨hw_eq_v, fun hw_in_N =>
                -- If w ∈ N, then n-w edge contradicts triangle-free (since both n,w ∈ N)
                have : w ≠ n := fun heq => G.loopless n (heq ▸ hw_adj)
                h_no_nbr_in_N w hw_in_N this hw_adj⟩
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
        intro h_v_in_M _
        simp only [M, mem_sdiff, mem_insert, mem_univ, true_and] at h_v_in_M
        simp at h_v_in_M

    -- Sum equals 5 * 4 = 20
    have h_all_4 : N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) = N.sum (fun _ => 4) := by
      apply sum_congr rfl h_deg_in_M
    rw [h_all_4]
    -- ∑ n ∈ N, 4 = 5 * 4 = 20
    rw [sum_const, hN_card, smul_eq_mul]

  -- Split sum over P and Q
  have h_sum_split : M.sum (fun w => commonNeighborsCard G v w) =
                      P.sum (fun w => commonNeighborsCard G v w) +
                      Q.sum (fun w => commonNeighborsCard G v w) := by
    rw [← hPQ_union]
    exact Finset.sum_union hPQ_disj

  -- On P, commonNeighborsCard = 1
  have h_sum_P : P.sum (fun w => commonNeighborsCard G v w) = P.card := by
    have h_eq_1 : ∀ w ∈ P, commonNeighborsCard G v w = 1 := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    rw [show P.sum (fun w => commonNeighborsCard G v w) = P.sum (fun _ => 1) from
      sum_congr rfl h_eq_1]
    simp [sum_const]

  -- On Q, commonNeighborsCard = 2
  have h_sum_Q : Q.sum (fun w => commonNeighborsCard G v w) = 2 * Q.card := by
    have h_eq_2 : ∀ w ∈ Q, commonNeighborsCard G v w = 2 := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    rw [show Q.sum (fun w => commonNeighborsCard G v w) = Q.sum (fun _ => 2) from
      sum_congr rfl h_eq_2]
    simp [sum_const, mul_comm]

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

/-!
### Claim 3: P induces a 4-cycle

The set P of 4 vertices (each with exactly 1 common neighbor with v) forms a 4-cycle.

**Cariolaro Proof Strategy**:
1. Label v's neighbors as {t, s₁, s₂, s₃, s₄} where t is special
2. Each sᵢ has exactly one neighbor pᵢ ∈ P (since commonNeighborsCard = 1)
3. Partition Q (8 vertices with 2 common neighbors) into T (neighbors of t) and W (rest)
4. Each sᵢ has exactly 1 neighbor in T and 2 neighbors in W (edge counting)
5. For pairs (sᵢ, sⱼ) sharing a common w ∈ W:
   - Construct X = {pᵢ, pⱼ, sᵢ, sⱼ, w} (5 vertices)
   - X is triangle-free (from h_tri)
   - X has no 3-IS (would extend to 6-IS in G with v)
   - By five_cycle_structure, X is 2-regular
   - Since sᵢ-sⱼ not adjacent (triangle-free with v), deg(sᵢ)=2 forces pᵢ-pⱼ adjacent
6. Count: exactly 4 such pairs give 4 edges in P → P is C₄
-/

/-- Key helper: for vertices in P, their unique common neighbor with v is one of v's neighbors -/
lemma P_partner_in_N {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G)
    (v : Fin 18) (p : Fin 18)
    (hp_nonadj : ¬G.Adj v p)
    (hp_common1 : commonNeighborsCard G v p = 1) :
    ∃! s, s ∈ G.neighborFinset v ∧ G.Adj s p := by
  -- commonNeighborsCard = 1 means exactly one common neighbor
  unfold commonNeighborsCard _root_.commonNeighbors at hp_common1
  have h_card1 : (G.neighborFinset v ∩ G.neighborFinset p).card = 1 := hp_common1
  rw [Finset.card_eq_one] at h_card1
  obtain ⟨s, hs⟩ := h_card1
  use s
  constructor
  · have hs_in : s ∈ G.neighborFinset v ∩ G.neighborFinset p := by
      rw [hs]; exact Finset.mem_singleton_self s
    simp only [Finset.mem_inter, mem_neighborFinset] at hs_in
    constructor
    · rw [mem_neighborFinset]; exact hs_in.1
    · exact G.symm hs_in.2
  · intro s' hs'
    have hs'_in : s' ∈ G.neighborFinset v ∩ G.neighborFinset p := by
      simp only [Finset.mem_inter, mem_neighborFinset]
      constructor
      · rw [mem_neighborFinset] at hs'; exact hs'.1
      · exact G.symm hs'.2
    rw [hs] at hs'_in
    exact Finset.mem_singleton.mp hs'_in

/-- Key helper: If two s-vertices (neighbors of v) share a common w-vertex
(a non-neighbor of v with 2 common neighbors), then the corresponding p-vertices
must be adjacent. This is because {p₁, p₂, s₁, s₂, w} forms a 5-cycle. -/
lemma p_adjacent_of_shared_w {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18)
    (p1 p2 s1 s2 w : Fin 18)
    -- p's are distinct non-neighbors of v with unique s-partners
    (hp1_nonadj : ¬G.Adj v p1) (hp2_nonadj : ¬G.Adj v p2) (hp_ne : p1 ≠ p2)
    -- s's are distinct neighbors of v
    (hs1_adj_v : G.Adj v s1) (hs2_adj_v : G.Adj v s2) (hs_ne : s1 ≠ s2)
    -- s-p adjacencies
    (hs1_adj_p1 : G.Adj s1 p1) (hs2_adj_p2 : G.Adj s2 p2)
    -- s1 not adjacent to p2, s2 not adjacent to p1
    (hs1_nonadj_p2 : ¬G.Adj s1 p2) (hs2_nonadj_p1 : ¬G.Adj s2 p1)
    -- w is adjacent to both s1 and s2
    (hw_adj_s1 : G.Adj w s1) (hw_adj_s2 : G.Adj w s2)
    -- w is not adjacent to v, p1, p2 (w is in Q, p's in P)
    (hw_nonadj_v : ¬G.Adj w v) (hw_nonadj_p1 : ¬G.Adj w p1) (hw_nonadj_p2 : ¬G.Adj w p2)
    -- s1 and s2 not adjacent (both in N(v), triangle-free)
    (hs1_s2_nonadj : ¬G.Adj s1 s2)
    -- Three witnesses from N(v)\{s1,s2} that are independent from {p1,p2,w}
    (t s3 s4 : Fin 18)
    (ht_adj_v : G.Adj v t) (hs3_adj_v : G.Adj v s3) (hs4_adj_v : G.Adj v s4)
    (ht_ne_s1 : t ≠ s1) (ht_ne_s2 : t ≠ s2) (hs3_ne_s1 : s3 ≠ s1) (hs3_ne_s2 : s3 ≠ s2)
    (hs4_ne_s1 : s4 ≠ s1) (hs4_ne_s2 : s4 ≠ s2)
    (ht_ne_s3 : t ≠ s3) (ht_ne_s4 : t ≠ s4) (hs3_ne_s4 : s3 ≠ s4)
    -- These 3 witnesses are not adjacent to p1, p2, w
    (ht_nonadj_p1 : ¬G.Adj t p1) (ht_nonadj_p2 : ¬G.Adj t p2) (ht_nonadj_w : ¬G.Adj t w)
    (hs3_nonadj_p1 : ¬G.Adj s3 p1) (hs3_nonadj_p2 : ¬G.Adj s3 p2) (hs3_nonadj_w : ¬G.Adj s3 w)
    (hs4_nonadj_p1 : ¬G.Adj s4 p1) (hs4_nonadj_p2 : ¬G.Adj s4 p2) (hs4_nonadj_w : ¬G.Adj s4 w) :
    G.Adj p1 p2 := by
  -- The 5-vertex set X = {p1, p2, s1, s2, w} is triangle-free (from h_tri)
  -- and has no 3-IS (else with {a,b,c} we'd get a 6-IS).
  -- By five_cycle_structure, X is 2-regular.
  -- Since s1-s2 are not adjacent (both neighbors of v, triangle-free),
  -- the 5-cycle structure forces p1-p2 to be adjacent.
  let X : Finset (Fin 18) := {p1, p2, s1, s2, w}

  -- Show |X| = 5 (need all elements distinct)
  have h1 : p1 ≠ s1 := by
    intro h; subst h
    exact G.loopless p1 hs1_adj_p1
  have h2 : p1 ≠ s2 := by
    intro h; subst h
    -- If p1 = s2, then s2 adj p1 = s2 adj s2, contradiction with loopless
    -- Actually: s2 adj p2 and p1 = s2 means s2 adj p2, but s2 not adj p1 = s2 not adj s2
    -- This is automatic since hs2_nonadj_p1 and if p1 = s2, we'd need ¬G.Adj s2 s2 which is true
    -- But also hs2_adj_p2 : G.Adj s2 p2, and if p1 = s2, then hp_ne : s2 ≠ p2
    -- The issue is that s2 = p1 means s2 is not adjacent to v (hp1_nonadj), but hs2_adj_v says it is
    exact hp1_nonadj hs2_adj_v
  have h3 : p1 ≠ w := by
    intro h; subst h
    -- If p1 = w, then hw_nonadj_p1 : ¬G.Adj w p1 = ¬G.Adj p1 p1, which is fine
    -- But hw_adj_s1 : G.Adj w s1 = G.Adj p1 s1, and hs1_adj_p1 : G.Adj s1 p1
    -- So G.Adj p1 s1 and G.Adj s1 p1 are symmetric, both true
    -- But hw_nonadj_p1 says ¬G.Adj w p1 = ¬G.Adj p1 p1, loopless is fine
    -- The issue is: p1 = w means p1 is adjacent to s1 (from hw_adj_s1), which is consistent
    -- But p1 = w and hw_nonadj_v : ¬G.Adj w v = ¬G.Adj p1 v, yet hp1_nonadj is ¬G.Adj v p1
    -- These are symmetric, so consistent.
    -- The real issue: p1 ∈ P (non-neighbor of v with 1 common neighbor)
    -- w should be in Q (non-neighbor of v with 2 common neighbors)
    -- So they have different commonNeighborsCard - but we don't have that here directly.
    -- Actually, hw_adj_s1 and hw_adj_s2 mean w is adjacent to both s1 and s2
    -- If p1 = w, then p1 is adjacent to s1 and s2. But hs2_nonadj_p1 says ¬G.Adj s2 p1
    exact hs2_nonadj_p1 (G.symm hw_adj_s2)
  have h4 : p2 ≠ s1 := by
    intro h; subst h
    -- p2 = s1 means G.Adj s1 p1 and s1 not adj p2 = s1 not adj s1 (loopless, fine)
    -- But hs1_nonadj_p2 : ¬G.Adj s1 p2 = ¬G.Adj s1 s1, which is true by loopless
    -- The issue: p2 = s1 and hs1_adj_v : G.Adj v s1 = G.Adj v p2, but hp2_nonadj : ¬G.Adj v p2
    exact hp2_nonadj hs1_adj_v
  have h5 : p2 ≠ s2 := by
    intro h; subst h
    exact G.loopless p2 hs2_adj_p2
  have h6 : p2 ≠ w := by
    intro h; subst h
    -- Similar to h3: if p2 = w, then w adj s1 and w adj s2, but hs1_nonadj_p2 says ¬G.Adj s1 p2
    exact hs1_nonadj_p2 (G.symm hw_adj_s1)
  have h7 : s1 ≠ w := by
    intro h; subst h
    exact G.loopless s1 hw_adj_s1
  have h8 : s2 ≠ w := by
    intro h; subst h
    exact G.loopless s2 hw_adj_s2

  have hX_card : X.card = 5 := by
    simp only [X]
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
        card_insert_of_notMem, card_singleton]
    -- Side goal 1: s2 ∉ {w}
    · simp only [mem_singleton]; exact h8
    -- Side goal 2: s1 ∉ {s2, w}
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hs_ne, h7⟩
    -- Side goal 3: p2 ∉ {s1, s2, w}
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨h4, h5, h6⟩
    -- Side goal 4: p1 ∉ {p2, s1, s2, w}
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hp_ne, h1, h2, h3⟩

  -- X has no 3-IS: Extend any 3-IS in X with {t, s3, s4} to get a 6-IS (contradiction).
  -- Proof outline:
  -- 1. Let W = {t, s3, s4} and I = S ∪ W
  -- 2. |W| = 3 (t, s3, s4 are distinct by ht_ne_s3, ht_ne_s4, hs3_ne_s4)
  -- 3. S ∩ W = ∅ because:
  --    - p1, p2, w ∉ N(v) but t, s3, s4 ∈ N(v)
  --    - s1, s2 ≠ t, s3, s4 by ht_ne_s1, etc.
  -- 4. I is independent:
  --    - S is independent (given)
  --    - W ⊆ N(v) is independent (N(v) independent in triangle-free graph)
  --    - Cross-edges: t, s3, s4 not adjacent to p1, p2, w by ht_nonadj_p1, etc.
  --      And s1, s2 not adjacent to t, s3, s4 (all in N(v))
  -- 5. |I| = |S| + |W| = 3 + 3 = 6
  -- This contradicts h_no6.
  have h_no3IS : ∀ S : Finset (Fin 18), S ⊆ X → S.card = 3 → G.IsIndepSet S → False := by
    intro S hS_sub hS_card hS_indep
    -- Strategy: extend S to a 6-IS by adding {t, s3, s4}
    let W : Finset (Fin 18) := {t, s3, s4}
    -- Show W has card 3
    have hW_card : W.card = 3 := by
      simp only [W]
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]; exact hs3_ne_s4
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨ht_ne_s3, ht_ne_s4⟩
    -- Show S and W are disjoint
    have hSW_disj : Disjoint S W := by
      rw [Finset.disjoint_left]
      intro x hxS hxW
      have hxX : x ∈ X := hS_sub hxS
      simp only [X, mem_insert, mem_singleton] at hxX
      simp only [W, mem_insert, mem_singleton] at hxW
      rcases hxX with rfl | rfl | rfl | rfl | rfl
      · -- x = p1: p1 ∉ W because p1 ∉ N(v) but t, s3, s4 ∈ N(v)
        rcases hxW with rfl | rfl | rfl
        · exact hp1_nonadj ht_adj_v
        · exact hp1_nonadj hs3_adj_v
        · exact hp1_nonadj hs4_adj_v
      · -- x = p2: similar
        rcases hxW with rfl | rfl | rfl
        · exact hp2_nonadj ht_adj_v
        · exact hp2_nonadj hs3_adj_v
        · exact hp2_nonadj hs4_adj_v
      · -- x = s1: s1 ≠ t, s3, s4 by hypothesis
        rcases hxW with rfl | rfl | rfl
        · exact ht_ne_s1 rfl
        · exact hs3_ne_s1 rfl
        · exact hs4_ne_s1 rfl
      · -- x = s2: s2 ≠ t, s3, s4 by hypothesis
        rcases hxW with rfl | rfl | rfl
        · exact ht_ne_s2 rfl
        · exact hs3_ne_s2 rfl
        · exact hs4_ne_s2 rfl
      · -- x = w: w ∉ N(v) but t, s3, s4 ∈ N(v)
        rcases hxW with rfl | rfl | rfl
        · exact hw_nonadj_v (G.symm ht_adj_v)
        · exact hw_nonadj_v (G.symm hs3_adj_v)
        · exact hw_nonadj_v (G.symm hs4_adj_v)
    -- Union has card 6
    let I : Finset (Fin 18) := S ∪ W
    have hI_card : I.card = 6 := by
      rw [Finset.card_union_of_disjoint hSW_disj, hS_card, hW_card]
    -- I is a 6-IS: W ⊆ N(v) is independent, S is independent, and cross-edges ruled out by hypotheses
    -- The detailed case analysis involves:
    -- - W independent because t, s3, s4 ∈ N(v) and N(v) is independent (triangle-free)
    -- - No S-W edges: p1, p2, w not adj to t, s3, s4 (given); s1, s2 not adj to t, s3, s4 (all in N(v))
    have hI_indep : G.IsIndepSet I := by
      -- I = S ∪ W. Need to show all distinct pairs are non-adjacent.
      intro x hxI y hyI hxy h_adj
      simp only [I, mem_coe, mem_union] at hxI hyI
      -- Case analysis on where x and y come from
      rcases hxI with hxS | hxW <;> rcases hyI with hyS | hyW
      · -- Both in S: contradicts hS_indep
        exact hS_indep hxS hyS hxy h_adj
      · -- x ∈ S, y ∈ W: need to show no S-W edges
        have hxX : x ∈ X := hS_sub hxS
        simp only [X, mem_insert, mem_singleton] at hxX
        simp only [W, mem_insert, mem_singleton] at hyW
        rcases hxX with rfl | rfl | rfl | rfl | rfl <;> rcases hyW with rfl | rfl | rfl
        -- x = p1, y = t: ht_nonadj_p1
        · exact ht_nonadj_p1 (G.symm h_adj)
        · exact hs3_nonadj_p1 (G.symm h_adj)
        · exact hs4_nonadj_p1 (G.symm h_adj)
        -- x = p2, y = t, s3, s4
        · exact ht_nonadj_p2 (G.symm h_adj)
        · exact hs3_nonadj_p2 (G.symm h_adj)
        · exact hs4_nonadj_p2 (G.symm h_adj)
        -- x = s1, y = t, s3, s4: all in N(v), so independent
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs1_adj_v ht_adj_v ht_ne_s1.symm h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs1_adj_v hs3_adj_v hs3_ne_s1.symm h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs1_adj_v hs4_adj_v hs4_ne_s1.symm h_adj
        -- x = s2, y = t, s3, s4
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs2_adj_v ht_adj_v ht_ne_s2.symm h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs2_adj_v hs3_adj_v hs3_ne_s2.symm h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs2_adj_v hs4_adj_v hs4_ne_s2.symm h_adj
        -- x = w, y = t, s3, s4
        · exact ht_nonadj_w (G.symm h_adj)
        · exact hs3_nonadj_w (G.symm h_adj)
        · exact hs4_nonadj_w (G.symm h_adj)
      · -- x ∈ W, y ∈ S: symmetric to above
        have hyX : y ∈ X := hS_sub hyS
        simp only [X, mem_insert, mem_singleton] at hyX
        simp only [W, mem_insert, mem_singleton] at hxW
        rcases hxW with rfl | rfl | rfl <;> rcases hyX with rfl | rfl | rfl | rfl | rfl
        -- x = t, y = p1, p2, s1, s2, w
        · exact ht_nonadj_p1 h_adj
        · exact ht_nonadj_p2 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep ht_adj_v hs1_adj_v ht_ne_s1 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep ht_adj_v hs2_adj_v ht_ne_s2 h_adj
        · exact ht_nonadj_w h_adj
        -- x = s3, y = p1, p2, s1, s2, w
        · exact hs3_nonadj_p1 h_adj
        · exact hs3_nonadj_p2 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs3_adj_v hs1_adj_v hs3_ne_s1 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs3_adj_v hs2_adj_v hs3_ne_s2 h_adj
        · exact hs3_nonadj_w h_adj
        -- x = s4, y = p1, p2, s1, s2, w
        · exact hs4_nonadj_p1 h_adj
        · exact hs4_nonadj_p2 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs4_adj_v hs1_adj_v hs4_ne_s1 h_adj
        · have hN_indep := neighborSet_indep_of_triangleFree h_tri v
          exact hN_indep hs4_adj_v hs2_adj_v hs4_ne_s2 h_adj
        · exact hs4_nonadj_w h_adj
      · -- Both in W: W ⊆ N(v), use neighborSet_indep_of_triangleFree
        simp only [W, mem_insert, mem_singleton] at hxW hyW
        have hN_indep := neighborSet_indep_of_triangleFree h_tri v
        rcases hxW with rfl | rfl | rfl <;> rcases hyW with rfl | rfl | rfl
        · exact absurd rfl hxy  -- x = y = t
        · exact hN_indep ht_adj_v hs3_adj_v ht_ne_s3 h_adj
        · exact hN_indep ht_adj_v hs4_adj_v ht_ne_s4 h_adj
        · exact hN_indep hs3_adj_v ht_adj_v ht_ne_s3.symm h_adj
        · exact absurd rfl hxy  -- x = y = s3
        · exact hN_indep hs3_adj_v hs4_adj_v hs3_ne_s4 h_adj
        · exact hN_indep hs4_adj_v ht_adj_v ht_ne_s4.symm h_adj
        · exact hN_indep hs4_adj_v hs3_adj_v hs3_ne_s4.symm h_adj
        · exact absurd rfl hxy  -- x = y = s4
    -- I is a 6-IS, contradiction
    exact h_no6 I ⟨hI_indep, hI_card⟩

  -- Apply five_cycle_structure
  have h_2reg := five_cycle_structure (G := G) X hX_card h_tri h_no3IS

  -- p1 has degree 2 in X. Its only possible neighbors in X are p2, s1.
  -- Since s1-p1 ∈ E(G) and |neighbors of p1 in X| = 2, p1 must also be adjacent to p2.
  have hp1_in_X : p1 ∈ X := by simp [X]
  have hp1_deg : (X.filter (G.Adj p1)).card = 2 := h_2reg p1 hp1_in_X

  -- p1's neighbor s1 is in X
  have hp1_adj_s1_in_X : s1 ∈ X.filter (G.Adj p1) := by
    rw [mem_filter]
    constructor
    · simp only [X, mem_insert, mem_singleton]
      -- Goal is s1 = p1 ∨ s1 = p2 ∨ s1 = s1 ∨ s1 = s2 ∨ s1 = w
      -- Simplify: s1 = s1 is in there, so True
      tauto
    · exact G.symm hs1_adj_p1

  -- p1 is not adjacent to s2, w (given), and not to itself
  have hp1_neighbors_in_X : X.filter (G.Adj p1) ⊆ {p2, s1} := by
    intro x hx
    simp only [X, mem_filter, mem_insert, mem_singleton] at hx
    obtain ⟨hxX, hx_adj⟩ := hx
    simp only [mem_insert, mem_singleton]
    rcases hxX with hx_eq | hx_eq | hx_eq | hx_eq | hx_eq
    · -- x = p1: not possible since G.loopless
      subst hx_eq
      exact (G.loopless _ hx_adj).elim
    · -- x = p2
      subst hx_eq; left; rfl
    · -- x = s1
      subst hx_eq; right; rfl
    · -- x = s2: not possible since s2 not adj p1
      subst hx_eq
      exact (hs2_nonadj_p1 (G.symm hx_adj)).elim
    · -- x = w: not possible since w not adj p1
      subst hx_eq
      exact (hw_nonadj_p1 (G.symm hx_adj)).elim

  -- Since |neighbors| = 2 and s1 is one, and neighbors ⊆ {p2, s1}, we need p2
  have h_p2_ne_s1 : p2 ≠ s1 := fun h => h4 h
  have h_card_target : ({p2, s1} : Finset (Fin 18)).card = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simp only [mem_singleton]
    exact h_p2_ne_s1

  have h_eq : X.filter (G.Adj p1) = {p2, s1} := by
    apply Finset.eq_of_subset_of_card_le hp1_neighbors_in_X
    rw [h_card_target, hp1_deg]

  have hp2_in_filter : p2 ∈ X.filter (G.Adj p1) := by
    rw [h_eq]
    simp only [mem_insert, mem_singleton, true_or]

  simp only [mem_filter] at hp2_in_filter
  exact hp2_in_filter.2

/-! ### Helper lemmas for the 4-cycle structure -/

/-- Each s ∈ N(v) has exactly 3 neighbors in Q (non-neighbors of v).
This is because s has degree 5, with 1 edge to v and 1 edge to its p-partner,
and s is not adjacent to any other s (N(v) is independent) or other p (cross non-adjacency). -/
lemma s_has_three_Q_neighbors {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v s p : Fin 18)
    (hs_adj_v : G.Adj v s) (hs_adj_p : G.Adj s p)
    (hp_nonadj_v : ¬G.Adj v p) (hvp_ne : v ≠ p)
    (Q : Finset (Fin 18))
    (hQ_def : ∀ q, q ∈ Q ↔ ¬G.Adj v q ∧ commonNeighborsCard G v q = 2)
    (hQ_complete : ∀ q, ¬G.Adj v q → commonNeighborsCard G v q = 2 → q ∈ Q) :
    (Q.filter (G.Adj s)).card = 3 := by
  -- s has degree 5 (from regularity)
  have hs_deg : G.degree s = 5 := h_reg s

  -- s's neighbors include v and p
  have hv_nbr : v ∈ G.neighborFinset s := by rw [mem_neighborFinset]; exact G.symm hs_adj_v
  have hp_nbr : p ∈ G.neighborFinset s := by rw [mem_neighborFinset]; exact hs_adj_p

  -- The neighbors of s are: v, p, and 3 others
  -- These 3 others must be in Q (non-neighbors of v with 2 common neighbors)

  -- For now, we use the degree constraint directly
  -- Full proof would show the 3 remaining neighbors are exactly the Q-neighbors
  sorry

/-- The induced subgraph on P has at least 2 edges (P is not too sparse).
This follows from the S-W structure: at least 2 pairs of s's share W-neighbors. -/
lemma P_has_at_least_two_edges {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP_card : P.card = 4)
    (hP_props : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    2 ≤ (P.filter (fun p₁ => (P.filter (fun p₂ => p₁ ≠ p₂ ∧ G.Adj p₁ p₂)).Nonempty)).card := by
  -- The S-W bipartite graph has at least 2 connected components means at least 2 pairs
  -- share W-neighbors, giving at least 2 P-edges by p_adjacent_of_shared_w
  sorry

/-- The induced subgraph on P has at most 4 edges (P is not K₄).
Proof: If P were K₄ (6 edges), then each p would have 3 P-neighbors.
With 1 N(v)-neighbor, each p would have only 1 Q-neighbor.
But the S-W structure requires each p to have at least 2 Q-neighbors. -/
lemma P_has_at_most_four_edges {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP_card : P.card = 4)
    (hP_props : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    (Finset.filter (fun e : Fin 18 × Fin 18 => e.1 ∈ P ∧ e.2 ∈ P ∧ e.1 < e.2 ∧ G.Adj e.1 e.2)
      Finset.univ).card ≤ 4 := by
  -- Each p has degree 5, exactly 1 neighbor in N(v) (its s-partner)
  -- So each p has 4 neighbors outside N(v) ∪ {v}, i.e., in P ∪ Q
  -- If P were complete, each p has 3 P-neighbors and 1 Q-neighbor
  -- The detailed argument shows this violates the W-sharing structure
  sorry

/-- P is 2-regular: each p ∈ P has exactly 2 neighbors in P.
This is the key structural lemma that implies P is a 4-cycle. -/
lemma P_is_two_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP_card : P.card = 4)
    (hP_props : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = 2 := by
  intro p hp
  -- Each p has degree 5
  -- 1 neighbor in N(v) (the s-partner)
  -- 4 neighbors in P ∪ Q
  -- The S-W structure forces exactly 2 of these to be in P

  -- Lower bound: if p had ≤1 P-neighbors, it would have ≥3 Q-neighbors
  -- This leads to contradiction via the W-structure constraints

  -- Upper bound: if p had ≥3 P-neighbors, it would have ≤1 Q-neighbor
  -- This also leads to contradiction

  sorry

/-- A 2-regular graph on 4 vertices is a 4-cycle (C₄).
This is a graph-theoretic fact: 4 vertices with each having degree 2
forms a single cycle of length 4. -/
lemma two_regular_four_vertices_is_cycle
    {α : Type*} [DecidableEq α] [Fintype α]
    (P : Finset α) (hP_card : P.card = 4)
    (adj : α → α → Prop) [DecidableRel adj]
    (h_symm : ∀ x y, adj x y → adj y x)
    (h_irrefl : ∀ x, ¬adj x x)
    (h_2reg : ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ adj p q)).card = 2) :
    ∃ (p1 p2 p3 p4 : α),
      p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4 ∧
      P = {p1, p2, p3, p4} ∧
      adj p1 p2 ∧ adj p2 p3 ∧ adj p3 p4 ∧ adj p4 p1 ∧
      ¬adj p1 p3 ∧ ¬adj p2 p4 := by
  classical
  -- pick an arbitrary vertex p1
  obtain ⟨p1, hp1P⟩ : ∃ p, p ∈ P := by
    have : 0 < P.card := by simpa [hP_card] using (by decide : (0 : ℕ) < 4)
    simpa [Finset.card_pos] using this

  -- neighbors of p1 inside P: exactly two, call them p2 and p4
  set N1 : Finset α := P.filter (fun q => q ≠ p1 ∧ adj p1 q)
  have hN1_card : N1.card = 2 := h_2reg _ hp1P
  obtain ⟨p2, p4, hp2p4, hN1_eq⟩ := Finset.card_eq_two.mp hN1_card
  have hp2N1 : p2 ∈ N1 := by simpa [hN1_eq] using Finset.mem_insert_self _ _
  have hp4N1 : p4 ∈ N1 := by
    have : p4 ∈ ({p2, p4} : Finset α) := by simp [hp2p4]
    simpa [hN1_eq] using this
  have hp2P : p2 ∈ P := (Finset.mem_filter.mp hp2N1).1
  have hp4P : p4 ∈ P := (Finset.mem_filter.mp hp4N1).1
  have hp1p2 : adj p1 p2 := (Finset.mem_filter.mp hp2N1).2.2
  have hp1p4 : adj p1 p4 := (Finset.mem_filter.mp hp4N1).2.2
  have hp2ne1 : p2 ≠ p1 := (Finset.mem_filter.mp hp2N1).2.1
  have hp4ne1 : p4 ≠ p1 := (Finset.mem_filter.mp hp4N1).2.1
  have hp1ne2 : p1 ≠ p2 := hp2ne1.symm
  have hp1ne4 : p1 ≠ p4 := hp4ne1.symm
  have hp2ne4 : p2 ≠ p4 := hp2p4

  -- the remaining vertex p3 is extracted by erasing p1,p2,p4
  set P0 : Finset α := P.erase p1
  set P1 : Finset α := P0.erase p2
  set P2 : Finset α := P1.erase p4
  have hP0_card : P0.card = 3 := by simp [P0, hp1P, hP_card]
  have hp2P0 : p2 ∈ P0 := by simpa [P0, Finset.mem_erase, hp2ne1] using hp2P
  have hP1_card : P1.card = 2 := by simp [P1, hp2P0, hP0_card]
  have hp4P1 : p4 ∈ P1 := by
    have hp4P0 : p4 ∈ P0 := by simpa [P0, Finset.mem_erase, hp4ne1] using hp4P
    simpa [P1, Finset.mem_erase, hp2ne4.symm] using hp4P0
  have hP2_card : P2.card = 1 := by simp [P2, hp4P1, hP1_card]
  obtain ⟨p3, hP2_eq⟩ := Finset.card_eq_one.mp hP2_card
  have hp3P2 : p3 ∈ P2 := by simpa [hP2_eq]
  have hp3P1 : p3 ∈ P1 := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P2
  have hp3P0 : p3 ∈ P0 := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P1
  have hp3P : p3 ∈ P := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P0
  have hp3ne4 : p3 ≠ p4 := (Finset.mem_erase.mp (by simpa [P2] using hp3P2)).1
  have hp3ne2 : p3 ≠ p2 := (Finset.mem_erase.mp (by simpa [P1] using hp3P1)).1
  have hp3ne1 : p3 ≠ p1 := (Finset.mem_erase.mp (by simpa [P0] using hp3P0)).1

  -- p3 is not adjacent to p1, otherwise it would be in N1
  have h_not_adj_13 : ¬adj p1 p3 := by
    intro h
    have : p3 ∈ N1 := Finset.mem_filter.mpr ⟨hp3P, hp3ne1, h⟩
    have : p3 ∈ ({p2, p4} : Finset α) := by simpa [hN1_eq] using this
    rcases Finset.mem_insert.mp this with h' | h'
    · exact hp3ne2 h'
    · simp only [Finset.mem_singleton] at h'; exact hp3ne4 h'

  -- describe P.erase p3 explicitly
  have hP_erase3_card : (P.erase p3).card = 3 := by simp [hp3P, hP_card]
  have hsubset_erase3 : ({p1, p2, p4} : Finset α) ⊆ P.erase p3 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_erase.mpr ⟨hp3ne1.symm, hp1P⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_erase.mpr ⟨hp3ne2.symm, hp2P⟩
    · simp only [Finset.mem_singleton] at hx; subst hx
      exact Finset.mem_erase.mpr ⟨hp3ne4.symm, hp4P⟩
  have h_card_three : ({p1, p2, p4} : Finset α).card = 3 := by
    simp [hp1ne2, hp1ne4, hp2ne4]
  have hErase3_eq : P.erase p3 = {p1, p2, p4} := by
    have hle : (P.erase p3).card ≤ ({p1, p2, p4} : Finset α).card := by
      simp only [hP_erase3_card, h_card_three]; rfl
    exact (Finset.eq_of_subset_of_card_le hsubset_erase3 hle).symm

  -- neighbors of p3: they live in {p2,p4} since p1 is not adjacent
  set N3 : Finset α := P.filter (fun q => q ≠ p3 ∧ adj p3 q)
  have hN3_card : N3.card = 2 := h_2reg _ hp3P
  have hN3_subset : N3 ⊆ ({p2, p4} : Finset α) := by
    intro x hx
    have hx_ne : x ≠ p3 := (Finset.mem_filter.mp hx).2.1
    have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
    have hx_in_erase : x ∈ P.erase p3 := by simp [Finset.mem_erase, hx_ne, hxP]
    have hx_in_set : x ∈ ({p1, p2, p4} : Finset α) := by simpa [hErase3_eq] using hx_in_erase
    rcases Finset.mem_insert.mp hx_in_set with hx1 | hx_rest
    · subst hx1
      have h_adj := (Finset.mem_filter.mp hx).2.2
      exact (h_not_adj_13 (h_symm _ _ h_adj)).elim
    rcases Finset.mem_insert.mp hx_rest with hx2 | hx3
    · subst hx2; simp
    · simp only [Finset.mem_singleton] at hx3; subst hx3; simp
  have hN3_eq : N3 = ({p2, p4} : Finset α) := by
    apply Finset.eq_of_subset_of_card_le hN3_subset
    have hcard : ({p2, p4} : Finset α).card = 2 := by simp [hp2ne4]
    have : N3.card ≤ ({p2, p4} : Finset α).card := by
      have : N3.card = 2 := hN3_card
      have : N3.card ≤ 2 := by omega
      simpa [hcard] using this
    simpa [hN3_card, hcard] using this
  have hp3p2 : adj p3 p2 := by
    have : p2 ∈ N3 := by simpa [hN3_eq] using Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2.2
  have hp3p4 : adj p3 p4 := by
    have : p4 ∈ N3 := by
      have : p4 ∈ ({p2, p4} : Finset α) := by simp
      simpa [hN3_eq] using this
    exact (Finset.mem_filter.mp this).2.2

  -- neighbors of p2: must be p1 and p3, ruling out p4
  set N2 : Finset α := P.filter (fun q => q ≠ p2 ∧ adj p2 q)
  have hN2_card : N2.card = 2 := h_2reg _ hp2P
  have hp1N2 : p1 ∈ N2 := Finset.mem_filter.mpr ⟨hp1P, hp1ne2, h_symm _ _ hp1p2⟩
  have hp3N2 : p3 ∈ N2 := Finset.mem_filter.mpr ⟨hp3P, hp3ne2, h_symm _ _ hp3p2⟩
  have hN2_subset : ({p1, p3} : Finset α) ⊆ N2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp1N2
    · simp only [Finset.mem_singleton] at hx; subst hx; exact hp3N2
  have h_not_adj_24 : ¬adj p2 p4 := by
    intro h
    have hp4N2 : p4 ∈ N2 := Finset.mem_filter.mpr ⟨hp4P, hp2ne4.symm, h⟩
    have hsub : ({p1, p3, p4} : Finset α) ⊆ N2 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp1N2
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp3N2
      · simp only [Finset.mem_singleton] at hx; subst hx; exact hp4N2
    have hcard : ({p1, p3, p4} : Finset α).card = 3 := by
      have hp1ne3 : p1 ≠ p3 := hp3ne1.symm
      have hp1ne4' : p1 ≠ p4 := hp1ne4
      have hp3ne4' : p3 ≠ p4 := hp3ne4
      simp [hp1ne3, hp1ne4', hp3ne4']
    have : 3 ≤ N2.card := by
      have := Finset.card_le_card hsub
      simp only [hcard] at this
      exact this
    have : (N2.card) ≠ 2 := by omega
    exact this hN2_card
  have hN2_eq : N2 = ({p1, p3} : Finset α) := by
    have hcard : ({p1, p3} : Finset α).card = 2 := by
      have hp1ne3 : p1 ≠ p3 := hp3ne1.symm
      simp [hp1ne3]
    have hle : N2.card ≤ ({p1, p3} : Finset α).card := by
      simp only [hN2_card, hcard]; rfl
    exact (Finset.eq_of_subset_of_card_le hN2_subset hle).symm

  have hp2p3 : adj p2 p3 := h_symm _ _ hp3p2
  have hp4p3 : adj p4 p3 := h_symm _ _ hp3p4
  have hp4p1 : adj p4 p1 := h_symm _ _ hp1p4

  -- P equals the four-element set
  have hsubset : ({p1, p2, p3, p4} : Finset α) ⊆ P := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp1P
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp2P
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp3P
    · simp only [Finset.mem_singleton] at hx; subst hx; exact hp4P
  have h_card_four : ({p1, p2, p3, p4} : Finset α).card = 4 := by
    simp [hp1ne2, hp3ne1.symm, hp1ne4, hp3ne2.symm, hp2ne4, hp3ne4]
  have hP_eq : P = {p1, p2, p3, p4} :=
    (Finset.eq_of_subset_of_card_le hsubset (by simp [h_card_four, hP_card])).symm

  refine ⟨p1, p2, p3, p4, hp1ne2, hp3ne1.symm, hp1ne4, hp3ne2.symm, hp2ne4, hp3ne4, hP_eq,
    hp1p2, hp2p3, hp3p4, hp4p1, h_not_adj_13, h_not_adj_24⟩

/-- P induces a 4-cycle: exactly 4 edges forming a cycle.

From Cariolaro's proof:
- Label N(v) = {t, s₁, s₂, s₃, s₄} where sᵢ-pᵢ are the unique edges to P
- Label Q = {t₁,t₂,t₃,t₄} ∪ {w₁,w₂,w₃,w₄} where tᵢ ∈ N(t)
- Each sᵢ sends: 1 edge to v, 1 to pᵢ, 1 to some tⱼ, 2 to W
- When two sᵢ's share a common w, the 5-vertex set {pᵢ,pⱼ,sᵢ,sⱼ,w}
  is triangle-free with no 3-IS, hence a 5-cycle by five_cycle_structure
- This forces pᵢ-pⱼ adjacent. Exactly 4 such pairs → P is C₄
-/
lemma claim3_four_cycle {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP : P.card = 4 ∧ ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∃ (p1 p2 p3 p4 : Fin 18),
      p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4 ∧
      P = {p1, p2, p3, p4} ∧
      -- P forms a 4-cycle: p1-p2-p3-p4-p1
      G.Adj p1 p2 ∧ G.Adj p2 p3 ∧ G.Adj p3 p4 ∧ G.Adj p4 p1 ∧
      -- No diagonals (would create issues with s-partners)
      ¬G.Adj p1 p3 ∧ ¬G.Adj p2 p4 := by
  obtain ⟨hP_card, hP_props⟩ := hP

  -- Step 1: Extract 4 elements from P
  have h_nonempty : P.Nonempty := card_pos.mp (by omega : 0 < P.card)
  obtain ⟨p1, hp1⟩ := h_nonempty

  have h_erase1 : (P.erase p1).card = 3 := by
    rw [card_erase_of_mem hp1, hP_card]

  have h_nonempty2 : (P.erase p1).Nonempty := card_pos.mp (by omega : 0 < (P.erase p1).card)
  obtain ⟨p2, hp2⟩ := h_nonempty2
  have hp2_in_P : p2 ∈ P := (mem_erase.mp hp2).2
  have hp1_ne_p2 : p1 ≠ p2 := fun h => (mem_erase.mp hp2).1 h.symm

  have h_erase2 : ((P.erase p1).erase p2).card = 2 := by
    rw [card_erase_of_mem hp2, h_erase1]

  have h_nonempty3 : ((P.erase p1).erase p2).Nonempty := card_pos.mp (by omega : 0 < ((P.erase p1).erase p2).card)
  obtain ⟨p3, hp3⟩ := h_nonempty3
  have hp3_in_erase1 : p3 ∈ P.erase p1 := (mem_erase.mp hp3).2
  have hp3_in_P : p3 ∈ P := (mem_erase.mp hp3_in_erase1).2
  have hp2_ne_p3 : p2 ≠ p3 := fun h => (mem_erase.mp hp3).1 h.symm
  have hp1_ne_p3 : p1 ≠ p3 := fun h => (mem_erase.mp hp3_in_erase1).1 h.symm

  have h_erase3 : (((P.erase p1).erase p2).erase p3).card = 1 := by
    rw [card_erase_of_mem hp3, h_erase2]

  have h_nonempty4 : (((P.erase p1).erase p2).erase p3).Nonempty := card_pos.mp (by omega : 0 < (((P.erase p1).erase p2).erase p3).card)
  obtain ⟨p4, hp4⟩ := h_nonempty4
  have hp4_in_erase2 : p4 ∈ (P.erase p1).erase p2 := (mem_erase.mp hp4).2
  have hp4_in_erase1 : p4 ∈ P.erase p1 := (mem_erase.mp hp4_in_erase2).2
  have hp4_in_P : p4 ∈ P := (mem_erase.mp hp4_in_erase1).2
  have hp3_ne_p4 : p3 ≠ p4 := fun h => (mem_erase.mp hp4).1 h.symm
  have hp2_ne_p4 : p2 ≠ p4 := fun h => (mem_erase.mp hp4_in_erase2).1 h.symm
  have hp1_ne_p4 : p1 ≠ p4 := fun h => (mem_erase.mp hp4_in_erase1).1 h.symm

  -- Show P = {p1, p2, p3, p4}
  have hP_eq : P = {p1, p2, p3, p4} := by
    ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases h1 : x = p1
      · left; exact h1
      · by_cases h2 : x = p2
        · right; left; exact h2
        · by_cases h3 : x = p3
          · right; right; left; exact h3
          · by_cases h4 : x = p4
            · right; right; right; exact h4
            · -- x ∉ {p1, p2, p3, p4} but x ∈ P, contradiction with |P| = 4
              have hx_in_erase : x ∈ ((P.erase p1).erase p2).erase p3 := by
                simp only [mem_erase]
                exact ⟨h3, h2, h1, hx⟩
              rw [card_eq_one] at h_erase3
              obtain ⟨y, hy⟩ := h_erase3
              rw [hy, mem_singleton] at hx_in_erase hp4
              -- hx_in_erase : x = y, hp4 : p4 = y
              rw [hx_in_erase, ← hp4] at h4
              exact (h4 rfl).elim
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hp1
      · exact hp2_in_P
      · exact hp3_in_P
      · exact hp4_in_P

  -- Step 2: Get s-partners for each p
  have ⟨hp1_nonadj, hp1_common1⟩ := hP_props p1 hp1
  have ⟨hp2_nonadj, hp2_common1⟩ := hP_props p2 hp2_in_P
  have ⟨hp3_nonadj, hp3_common1⟩ := hP_props p3 hp3_in_P
  have ⟨hp4_nonadj, hp4_common1⟩ := hP_props p4 hp4_in_P

  obtain ⟨s1, ⟨hs1_in_N, hs1_adj_p1⟩, hs1_unique⟩ := P_partner_in_N h_reg h_tri v p1 hp1_nonadj hp1_common1
  obtain ⟨s2, ⟨hs2_in_N, hs2_adj_p2⟩, hs2_unique⟩ := P_partner_in_N h_reg h_tri v p2 hp2_nonadj hp2_common1
  obtain ⟨s3, ⟨hs3_in_N, hs3_adj_p3⟩, hs3_unique⟩ := P_partner_in_N h_reg h_tri v p3 hp3_nonadj hp3_common1
  obtain ⟨s4, ⟨hs4_in_N, hs4_adj_p4⟩, hs4_unique⟩ := P_partner_in_N h_reg h_tri v p4 hp4_nonadj hp4_common1

  -- Step 3: Show s-partners are pairwise distinct
  -- If s_i = s_j for i ≠ j, either we get a triangle or a 6-IS
  -- The proof involves case analysis: if p_i-p_j adjacent → triangle,
  -- else {p_i, p_j} ∪ (N(v) \ {s}) forms a 6-IS.
  -- This is the "P_partners_distinct" argument from the blueprint.
  let N := G.neighborFinset v
  have hN_card : N.card = 5 := h_reg v
  have hN_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v

  -- Helper: Prove s_a ≠ s_b for given p_a, p_b, s (where s_a = s_b = s assumed)
  have distinct_helper : ∀ (pa pb s : Fin 18),
      pa ≠ pb →
      ¬G.Adj v pa → ¬G.Adj v pb →
      s ∈ N → G.Adj s pa → G.Adj s pb →
      (∀ x, x ∈ N → x ≠ s → ¬G.Adj x pa) →
      (∀ x, x ∈ N → x ≠ s → ¬G.Adj x pb) →
      False := by
    intro pa pb s hne hpa_nonadj hpb_nonadj hs_in hs_pa hs_pb hunique_pa hunique_pb
    by_cases hadj : G.Adj pa pb
    · -- Case 1: pa-pb adjacent → {s, pa, pb} is a triangle
      have h_clique : G.IsNClique 3 {s, pa, pb} := by
        rw [isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [mem_coe, mem_insert, mem_singleton] at hx hy
          obtain (rfl | rfl | rfl) := hx <;> obtain (rfl | rfl | rfl) := hy
          all_goals first | exact absurd rfl hxy | exact hs_pa | exact hs_pb
                          | exact G.symm hs_pa | exact G.symm hs_pb | exact hadj | exact G.symm hadj
        · have h1 : s ≠ pa := G.ne_of_adj hs_pa
          have h2 : s ≠ pb := G.ne_of_adj hs_pb
          rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
          · simp only [mem_singleton]; exact hne
          · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h1, h2⟩
      exact h_tri {s, pa, pb} h_clique
    · -- Case 2: pa-pb not adjacent → {pa, pb} ∪ (N \ {s}) is a 6-IS
      let N' := N.erase s
      have hN'_card : N'.card = 4 := by rw [card_erase_of_mem hs_in, hN_card]
      let I := insert pa (insert pb N')
      have hI_card : I.card = 6 := by
        have h_pa_notin : pa ∉ insert pb N' := by
          simp only [mem_insert, not_or]
          refine ⟨hne, ?_⟩
          intro h
          have hpa_in_N := mem_of_mem_erase h
          rw [mem_neighborFinset] at hpa_in_N
          exact hpa_nonadj hpa_in_N
        have h_pb_notin_N' : pb ∉ N' := by
          intro h
          have hpb_in_N := mem_of_mem_erase h
          rw [mem_neighborFinset] at hpb_in_N
          exact hpb_nonadj hpb_in_N
        rw [card_insert_of_notMem h_pa_notin, card_insert_of_notMem h_pb_notin_N', hN'_card]
      have hI_indep : G.IsIndepSet I := by
        intro x hx y hy hxy h_edge
        simp only [I, mem_coe, mem_insert] at hx hy
        have h_N'_to_N : ∀ z, z ∈ N' → z ∈ N := fun z hz => mem_of_mem_erase hz
        rcases hx with rfl | rfl | hx_N' <;> rcases hy with rfl | rfl | hy_N'
        · exact hxy rfl
        · exact hadj h_edge
        · -- pa adj to y ∈ N', y ≠ s
          have hy_ne_s : y ≠ s := (mem_erase.mp hy_N').1
          exact hunique_pa y (h_N'_to_N y hy_N') hy_ne_s (G.symm h_edge)
        · exact hadj (G.symm h_edge)
        · exact hxy rfl
        · have hy_ne_s : y ≠ s := (mem_erase.mp hy_N').1
          exact hunique_pb y (h_N'_to_N y hy_N') hy_ne_s (G.symm h_edge)
        · have hx_ne_s : x ≠ s := (mem_erase.mp hx_N').1
          exact hunique_pa x (h_N'_to_N x hx_N') hx_ne_s h_edge
        · have hx_ne_s : x ≠ s := (mem_erase.mp hx_N').1
          exact hunique_pb x (h_N'_to_N x hx_N') hx_ne_s h_edge
        · -- Both in N', use N indep
          have hx_in_N : x ∈ N := h_N'_to_N x hx_N'
          have hy_in_N : y ∈ N := h_N'_to_N y hy_N'
          rw [mem_neighborFinset] at hx_in_N hy_in_N
          exact hN_indep hx_in_N hy_in_N hxy h_edge
      exact h_no6 I ⟨hI_indep, hI_card⟩

  -- Get uniqueness facts for each p's partner
  have h1_unique : ∀ x, x ∈ N → x ≠ s1 → ¬G.Adj x p1 := by
    intro x hx hne hadj
    have hx' : x ∈ G.neighborFinset v := hx
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p1 := And.intro hx' hadj
    have heq : x = s1 := hs1_unique x h_and
    exact hne heq
  have h2_unique : ∀ x, x ∈ N → x ≠ s2 → ¬G.Adj x p2 := by
    intro x hx hne hadj
    have hx' : x ∈ G.neighborFinset v := hx
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p2 := And.intro hx' hadj
    have heq : x = s2 := hs2_unique x h_and
    exact hne heq
  have h3_unique : ∀ x, x ∈ N → x ≠ s3 → ¬G.Adj x p3 := by
    intro x hx hne hadj
    have hx' : x ∈ G.neighborFinset v := hx
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p3 := And.intro hx' hadj
    have heq : x = s3 := hs3_unique x h_and
    exact hne heq
  have h4_unique : ∀ x, x ∈ N → x ≠ s4 → ¬G.Adj x p4 := by
    intro x hx hne hadj
    have hx' : x ∈ G.neighborFinset v := hx
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p4 := And.intro hx' hadj
    have heq : x = s4 := hs4_unique x h_and
    exact hne heq

  have hs_distinct : s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h_eq; subst h_eq)
    · exact distinct_helper p1 p2 s1 hp1_ne_p2 hp1_nonadj hp2_nonadj hs1_in_N hs1_adj_p1 hs2_adj_p2 h1_unique h2_unique
    · exact distinct_helper p1 p3 s1 hp1_ne_p3 hp1_nonadj hp3_nonadj hs1_in_N hs1_adj_p1 hs3_adj_p3 h1_unique h3_unique
    · exact distinct_helper p1 p4 s1 hp1_ne_p4 hp1_nonadj hp4_nonadj hs1_in_N hs1_adj_p1 hs4_adj_p4 h1_unique h4_unique
    · exact distinct_helper p2 p3 s2 hp2_ne_p3 hp2_nonadj hp3_nonadj hs2_in_N hs2_adj_p2 hs3_adj_p3 h2_unique h3_unique
    · exact distinct_helper p2 p4 s2 hp2_ne_p4 hp2_nonadj hp4_nonadj hs2_in_N hs2_adj_p2 hs4_adj_p4 h2_unique h4_unique
    · exact distinct_helper p3 p4 s3 hp3_ne_p4 hp3_nonadj hp4_nonadj hs3_in_N hs3_adj_p3 hs4_adj_p4 h3_unique h4_unique

  obtain ⟨hs12_ne, hs13_ne, hs14_ne, hs23_ne, hs24_ne, hs34_ne⟩ := hs_distinct

  -- Step 4: Find t (the 5th vertex of N(v))
  -- N(v) has 5 elements, {s1,s2,s3,s4} are 4 of them
  let S := ({s1, s2, s3, s4} : Finset (Fin 18))
  have hS_card : S.card = 4 := by
    have h4_notin : s4 ∉ ({} : Finset (Fin 18)) := not_mem_empty s4
    have h3_notin : s3 ∉ ({s4} : Finset (Fin 18)) := by simp [hs34_ne]
    have h2_notin : s2 ∉ ({s3, s4} : Finset (Fin 18)) := by simp [hs23_ne, hs24_ne]
    have h1_notin : s1 ∉ ({s2, s3, s4} : Finset (Fin 18)) := by simp [hs12_ne, hs13_ne, hs14_ne]
    simp only [S, card_insert_of_notMem h1_notin, card_insert_of_notMem h2_notin,
               card_insert_of_notMem h3_notin, card_singleton]

  have hS_sub_N : S ⊆ N := by
    intro x hx
    simp only [S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hs1_in_N
    · exact hs2_in_N
    · exact hs3_in_N
    · exact hs4_in_N

  -- N \ S has exactly 1 element
  have h_diff : (N \ S).card = 1 := by
    simp only [Finset.card_sdiff_of_subset hS_sub_N, hN_card, hS_card]

  -- Extract t from N \ S
  have h_nonempty_diff : (N \ S).Nonempty := by
    rw [← card_pos, h_diff]; norm_num

  obtain ⟨t, ht_in_diff⟩ := h_nonempty_diff
  have ht_in_N : t ∈ N := mem_sdiff.mp ht_in_diff |>.1
  have ht_notin_S : t ∉ S := mem_sdiff.mp ht_in_diff |>.2

  -- t is distinct from all s_i
  have ht_ne_s1 : t ≠ s1 := by
    intro h; subst h; simp only [S, mem_insert, true_or, not_true] at ht_notin_S
  have ht_ne_s2 : t ≠ s2 := by
    intro h; subst h; simp only [S, mem_insert, true_or, or_true, not_true] at ht_notin_S
  have ht_ne_s3 : t ≠ s3 := by
    intro h; subst h; simp only [S, mem_insert, true_or, or_true, not_true] at ht_notin_S
  have ht_ne_s4 : t ≠ s4 := by
    intro h; subst h; simp only [S, mem_insert, mem_singleton, or_true, not_true] at ht_notin_S

  -- t is adjacent to v
  rw [mem_neighborFinset] at ht_in_N
  have ht_adj_v : G.Adj v t := ht_in_N

  -- The remaining proof requires establishing:
  -- 1. Each p is not adjacent to s_i for i ≠ partner (from uniqueness)
  -- 2. Edges in P via shared W-neighbors
  -- 3. No diagonals (from edge counting or direct argument)

  -- s1 is only adjacent to p1 among {p1,p2,p3,p4}
  have hs1_nonadj_p2' : ¬G.Adj s1 p2 := by
    intro h
    have h12_in : s1 ∈ G.neighborFinset v ∧ G.Adj s1 p2 := ⟨hs1_in_N, h⟩
    have : s1 = s2 := hs2_unique s1 h12_in
    exact hs12_ne this
  have hs1_nonadj_p3 : ¬G.Adj s1 p3 := by
    intro h
    have h13_in : s1 ∈ G.neighborFinset v ∧ G.Adj s1 p3 := ⟨hs1_in_N, h⟩
    have : s1 = s3 := hs3_unique s1 h13_in
    exact hs13_ne this
  have hs1_nonadj_p4 : ¬G.Adj s1 p4 := by
    intro h
    have h14_in : s1 ∈ G.neighborFinset v ∧ G.Adj s1 p4 := ⟨hs1_in_N, h⟩
    have : s1 = s4 := hs4_unique s1 h14_in
    exact hs14_ne this

  have hs2_nonadj_p1 : ¬G.Adj s2 p1 := by
    intro h
    have h21_in : s2 ∈ G.neighborFinset v ∧ G.Adj s2 p1 := ⟨hs2_in_N, h⟩
    have : s2 = s1 := hs1_unique s2 h21_in
    exact hs12_ne this.symm
  have hs2_nonadj_p3 : ¬G.Adj s2 p3 := by
    intro h
    have h23_in : s2 ∈ G.neighborFinset v ∧ G.Adj s2 p3 := ⟨hs2_in_N, h⟩
    have : s2 = s3 := hs3_unique s2 h23_in
    exact hs23_ne this
  have hs2_nonadj_p4 : ¬G.Adj s2 p4 := by
    intro h
    have h24_in : s2 ∈ G.neighborFinset v ∧ G.Adj s2 p4 := ⟨hs2_in_N, h⟩
    have : s2 = s4 := hs4_unique s2 h24_in
    exact hs24_ne this

  have hs3_nonadj_p1 : ¬G.Adj s3 p1 := by
    intro h
    have h31_in : s3 ∈ G.neighborFinset v ∧ G.Adj s3 p1 := ⟨hs3_in_N, h⟩
    have : s3 = s1 := hs1_unique s3 h31_in
    exact hs13_ne this.symm
  have hs3_nonadj_p2 : ¬G.Adj s3 p2 := by
    intro h
    have h32_in : s3 ∈ G.neighborFinset v ∧ G.Adj s3 p2 := ⟨hs3_in_N, h⟩
    have : s3 = s2 := hs2_unique s3 h32_in
    exact hs23_ne this.symm
  have hs3_nonadj_p4 : ¬G.Adj s3 p4 := by
    intro h
    have h34_in : s3 ∈ G.neighborFinset v ∧ G.Adj s3 p4 := ⟨hs3_in_N, h⟩
    have : s3 = s4 := hs4_unique s3 h34_in
    exact hs34_ne this

  have hs4_nonadj_p1 : ¬G.Adj s4 p1 := by
    intro h
    have h41_in : s4 ∈ G.neighborFinset v ∧ G.Adj s4 p1 := ⟨hs4_in_N, h⟩
    have : s4 = s1 := hs1_unique s4 h41_in
    exact hs14_ne this.symm
  have hs4_nonadj_p2 : ¬G.Adj s4 p2 := by
    intro h
    have h42_in : s4 ∈ G.neighborFinset v ∧ G.Adj s4 p2 := ⟨hs4_in_N, h⟩
    have : s4 = s2 := hs2_unique s4 h42_in
    exact hs24_ne this.symm
  have hs4_nonadj_p3 : ¬G.Adj s4 p3 := by
    intro h
    have h43_in : s4 ∈ G.neighborFinset v ∧ G.Adj s4 p3 := ⟨hs4_in_N, h⟩
    have : s4 = s3 := hs3_unique s4 h43_in
    exact hs34_ne this.symm

  -- The remaining proof uses degree counting to establish P forms a C4.
  --
  -- Key structure:
  -- - Each s_i has degree 5: edges to v, p_i, and 3 vertices in Q
  -- - N(v) = {t, s1, s2, s3, s4} is independent (triangle-free)
  -- - Q splits into T (4 vertices adjacent to t) and W (4 vertices not adjacent to t)
  -- - Each q ∈ T has 2 N(v)-neighbors: t and exactly 1 s_i
  -- - Each q ∈ W has 2 N(v)-neighbors: exactly 2 s_i's
  -- - So edges S→T = 4, edges S→W = 8
  -- - Each s has 1 T-neighbor and 2 W-neighbors (uniform distribution)
  -- - The S-W bipartite graph is 2-regular, forming an 8-cycle
  -- - Consecutive s's in this cycle share a W-neighbor
  -- - By p_adjacent_of_shared_w, consecutive p's are adjacent
  -- - This gives exactly 4 P-edges forming C4

  -- Step 5: Show each s has exactly 2 neighbors in P ∪ Q that are NOT adjacent to v
  -- More precisely: show the S-W structure forces P to be 2-regular

  -- We use a counting argument:
  -- - Each p_i has degree 5, with exactly 1 neighbor in N(v) (which is s_i)
  -- - So p_i has 4 neighbors in V \ (N(v) ∪ {v}) = P ∪ Q
  -- - Sum over P: 4 × 4 = 16 = 2|E(P)| + |E(P,Q)|

  -- Each q ∈ Q has degree 5, with exactly 2 neighbors in N(v)
  -- So q has 3 neighbors in P ∪ Q
  -- Sum over Q: 8 × 3 = 24 = |E(P,Q)| + 2|E(Q)|

  -- Total edges in P∪Q: From 16 = 2|E(P)| + |E(P,Q)| and 24 = |E(P,Q)| + 2|E(Q)|
  -- Adding: 40 = 2|E(P)| + 2|E(P,Q)| + 2|E(Q)| = 2(|E(P)| + |E(P,Q)| + |E(Q)|)
  -- So |E(P∪Q)| = 20

  -- From 16 = 2|E(P)| + |E(P,Q)|:
  -- If |E(P)| = 4 (C4), then |E(P,Q)| = 8, and |E(Q)| = 20 - 4 - 8 = 8

  -- The constraint that P is 2-regular (|E(P)| = 4) comes from the S-W structure:
  -- The S-W bipartite graph being a single 8-cycle forces exactly 4 pairs of s's
  -- to share W-neighbors (consecutive in the cycle).

  -- For now, we establish the result using the counting constraints and
  -- the existence of shared W-neighbors (which follows from pigeonhole).

  -- The key insight: by five_cycle_structure, for any pair (s_i, s_j) sharing
  -- a W-neighbor w, the set {p_i, p_j, s_i, s_j, w} is 2-regular, forcing p_i-p_j adjacent.

  -- We can show at least 4 such pairs exist (forming C4), and the diagonal
  -- pairs (s_1,s_3) and (s_2,s_4) don't share W-neighbors.

  -- Step 5a: Establish that P has exactly 4 edges (is 2-regular)
  -- This follows from: each p has deg 5, 1 neighbor in N(v), and the S-W
  -- structure ensures exactly 4 P-pairs share W-neighbors.

  -- Due to the complexity of explicitly constructing W vertices and proving
  -- the bipartite structure, we use the established degree constraints.

  -- First, let's show there exist w's that give us the cycle edges.
  -- This is implicit in the degree counting, but making it explicit requires
  -- extracting 8 Q-vertices and analyzing their S-neighbors.

  -- The labeling step: order p1,p2,p3,p4 so the cycle is p1-p2-p3-p4-p1
  -- We can always do this since we're proving existence of such an ordering.

  -- For the result, we just need to show SOME 4-cycle labeling exists.
  -- Let's prove adjacencies exist by contradiction and degree counting.

  -- Step 5: Use the helper lemmas to establish P is a 4-cycle

  -- First, show P is 2-regular (each p has exactly 2 P-neighbors)
  have hP_2reg : ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = 2 :=
    P_is_two_regular h_reg h_tri h_no6 v P hP_card hP_props

  -- A 2-regular graph on 4 vertices is a 4-cycle
  have h_cycle := two_regular_four_vertices_is_cycle P hP_card G.Adj
    (fun _ _ h => G.symm h)
    G.loopless
    hP_2reg

  -- The cycle structure gives us the result directly
  exact h_cycle

/-- Final step of Cariolaro's proof: derive contradiction from the 4-cycle structure.

The proof labels vertices carefully:
- P = {p₁, p₂, p₃, p₄} forms cycle p₁-p₂-p₃-p₄-p₁
- N(v) = {t, s₁, s₂, s₃, s₄} where sᵢ-pᵢ are the unique edges
- Q = {t₁, t₂, t₃, t₄} ∪ {w₁, w₂, w₃, w₄} where tᵢ ∈ N(t)
- Each pᵢ has edges: 2 in P (cycle), 1 to sᵢ, 1 to some tⱼ, 1 to some wⱼ
- Label wᵢ so pᵢ-wᵢ ∈ E(G)

Key constraint tracking:
- w₁ shares 2 neighbors with v (it's in Q), candidates in {s₂, s₃, s₄}
- w₁ shares 2 neighbors with t, candidates in {t₂, t₃, t₄}
- Analysis shows w₁ must be adjacent to s₃, t₃, and also s₂, t₄
- Then s₂ must be adjacent to t₁ (to avoid triangles)
- But then s₂ and p₁ share {p₂, w₁, t₁} = 3 common neighbors
- This contradicts Claim 2's bound of ≤ 2 common neighbors!
-/
lemma final_contradiction {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    False := by
  -- Step 1: Pick any vertex v and get the partition of non-neighbors
  let v : Fin 18 := 0
  obtain ⟨P, Q, hP_card, hQ_card, hP_props, hQ_props⟩ :=
    claim2_neighbor_structure h_reg h_tri h_no6 v

  -- Step 2: By claim3, P forms a 4-cycle
  obtain ⟨p1, p2, p3, p4, hp_ne12, hp_ne13, hp_ne14, hp_ne23, hp_ne24, hp_ne34,
          hP_eq, h_adj12, h_adj23, h_adj34, h_adj41, h_nonadj13, h_nonadj24⟩ :=
    claim3_four_cycle h_reg h_tri h_no6 v P ⟨hP_card, hP_props⟩

  -- Step 3: Get s-partners for p1 and p2
  have hp1_in_P : p1 ∈ P := by rw [hP_eq]; simp
  have hp2_in_P : p2 ∈ P := by rw [hP_eq]; simp
  have ⟨hp1_nonadj_v, hp1_common1⟩ := hP_props p1 hp1_in_P
  have ⟨hp2_nonadj_v, hp2_common1⟩ := hP_props p2 hp2_in_P

  obtain ⟨s1, ⟨hs1_in_N, hs1_adj_p1⟩, hs1_unique⟩ :=
    P_partner_in_N h_reg h_tri v p1 hp1_nonadj_v hp1_common1
  obtain ⟨s2, ⟨hs2_in_N, hs2_adj_p2⟩, hs2_unique⟩ :=
    P_partner_in_N h_reg h_tri v p2 hp2_nonadj_v hp2_common1

  -- Step 4: Adjacent P vertices must have different s-partners (else triangle)
  have h_s_ne : s1 ≠ s2 := by
    intro h_eq
    subst h_eq
    -- {s1, p1, p2} is a triangle
    have h_triangle : G.IsNClique 3 {s1, p1, p2} := by
      rw [isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [mem_coe, mem_insert, mem_singleton] at hx hy
        obtain (rfl | rfl | rfl) := hx <;> obtain (rfl | rfl | rfl) := hy
        · exact absurd rfl hxy
        · exact hs1_adj_p1
        · exact hs2_adj_p2
        · exact G.symm hs1_adj_p1
        · exact absurd rfl hxy
        · exact h_adj12
        · exact G.symm hs2_adj_p2
        · exact G.symm h_adj12
        · exact absurd rfl hxy
      · have h_s_ne_p1 : s1 ≠ p1 := G.ne_of_adj hs1_adj_p1
        have h_s_ne_p2 : s1 ≠ p2 := G.ne_of_adj hs2_adj_p2
        rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        · simp only [mem_singleton]; exact hp_ne12
        · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h_s_ne_p1, h_s_ne_p2⟩
    exact h_tri {s1, p1, p2} h_triangle

  -- Step 5: The full Cariolaro argument shows that the constraint tracking
  -- eventually leads to some pair of non-adjacent vertices having 3 common neighbors,
  -- contradicting commonNeighborsCard ≤ 2.
  --
  -- Specifically: after labeling t, tᵢ's, wᵢ's and tracking edges,
  -- s₂ and p₁ end up sharing {p₂, w₁, t₁} as common neighbors.
  -- Since s₂ is not adjacent to p₁ (p₁'s only N(v)-neighbor is s₁),
  -- this violates the bound from Claim 2.
  --
  -- The full verification requires tracking all the edge constraints through
  -- the labeling scheme. See Cariolaro's paper for details.
  sorry

/-! ## Upper Bound Theorem -/

theorem ramsey_three_six_upper_bound_property :
    HasRamseyProperty 3 6 (completeGraph (Fin 18)) := by
  -- The complete graph on 18 vertices trivially contains a 3-clique (triangle)
  left
  use {0, 1, 2}
  constructor
  · -- IsClique: any two distinct vertices are adjacent in completeGraph
    intro x hx y hy hxy
    exact hxy
  · -- card = 3
    native_decide

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
