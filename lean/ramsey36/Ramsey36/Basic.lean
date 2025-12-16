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
          simp at hx hy
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

omit [Fintype V] [DecidableEq V] in
lemma triangleFree_iff_cliqueFree_three {G : SimpleGraph V} :
    TriangleFree G ↔ G.CliqueFree 3 := by rfl

/-- Bipartite edge counting symmetry for symmetric relations.
Both sides count |{(a,b) : a ∈ A, b ∈ B, R a b}|. -/
lemma bipartite_edge_count_symmetry {V : Type*} [DecidableEq V]
    (A B : Finset V) (R : V → V → Prop) [DecidableRel R] (hR : Symmetric R) :
    ∑ a ∈ A, (B.filter (R a)).card = ∑ b ∈ B, (A.filter (R b)).card := by
  -- Rewrite card as sum of 1s
  simp_rw [card_eq_sum_ones, sum_filter]
  -- Use sum_comm to swap summation order on LHS
  rw [Finset.sum_comm]
  -- Now both sides are extensionally equal using symmetry of R
  congr 1; ext b; congr 1; ext a
  simp only [hR.iff]

/-- Expand sum over a 4-element set into explicit addition. -/
lemma sum_over_four {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (f : α → β) :
    ∑ x ∈ ({a, b, c, d} : Finset α), f x = f a + f b + f c + f d := by
  -- Rewrite using insert notation
  have ha : a ∉ (insert b (insert c ({d} : Finset α))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hab, hac, had⟩
  have hb : b ∉ (insert c ({d} : Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hbc, hbd⟩
  have hc : c ∉ ({d} : Finset α) := by
    simp only [Finset.mem_singleton]
    exact hcd
  -- Expand the set as nested inserts
  have h_expand : ({a, b, c, d} : Finset α) = insert a (insert b (insert c {d})) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [h_expand, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc, Finset.sum_singleton]
  ac_rfl

/-! ## Pigeonhole Principles for Small Sets -/

/-- Pigeonhole for 4 non-negative integers: if they sum to S and one is at least k,
    then at least one of the remaining three is at most (S - k) / 3.
    This is the contrapositive form useful for proof by contradiction. -/
lemma pigeonhole_four_sum {a b c d S : ℕ} (h_sum : a + b + c + d = S) :
    a ≥ 2 → b ≥ 1 → c ≥ 1 → d ≥ 1 → S ≥ 5 := by omega

/-- If 4 non-negative integers sum to 4, and one is ≥ 2,
    then at least one of the others is 0. -/
lemma pigeonhole_four_sum_eq_four {a b c d : ℕ}
    (h_sum : a + b + c + d = 4) (h_ge2 : a ≥ 2) :
    b = 0 ∨ c = 0 ∨ d = 0 := by omega

/-- Symmetric version: if any of a,b,c,d is ≥ 2 and sum = 4, one is 0. -/
lemma pigeonhole_four_one_large {a b c d : ℕ}
    (h_sum : a + b + c + d = 4)
    (h_ge2 : a ≥ 2 ∨ b ≥ 2 ∨ c ≥ 2 ∨ d ≥ 2) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
  rcases h_ge2 with ha | hb | hc | hd <;> omega

/-! ## Collision Detection in Finite Sets -/

/-- Three elements from a 3-element set: either two collide or all three are distinct.
    This is the fundamental dichotomy for pigeonhole in small sets. -/
lemma three_from_three_dichotomy {α : Type*} [DecidableEq α]
    {x y z : α} (_hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z)
    {a b c : α}
    (_ha : a ∈ ({x, y, z} : Finset α))
    (_hb : b ∈ ({x, y, z} : Finset α))
    (_hc : c ∈ ({x, y, z} : Finset α)) :
    (a = b ∨ a = c ∨ b = c) ∨ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
  by_cases hab : a = b
  · left; left; exact hab
  · by_cases hac : a = c
    · left; right; left; exact hac
    · by_cases hbc : b = c
      · left; right; right; exact hbc
      · right; exact ⟨hab, hac, hbc⟩

/-- If three elements from {x,y,z} are all distinct, they form a permutation. -/
lemma three_distinct_is_perm {α : Type*} [DecidableEq α]
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {a b c : α}
    (ha : a ∈ ({x, y, z} : Finset α))
    (hb : b ∈ ({x, y, z} : Finset α))
    (hc : c ∈ ({x, y, z} : Finset α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset α) = {x, y, z} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  -- {a,b,c} ⊆ {x,y,z} and both have 3 distinct elements
  have h_card_abc : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hab, hac]
  have h_card_xyz : ({x, y, z} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hyz]
    · simp [hxy, hxz]
  -- {a,b,c} ⊆ {x,y,z}
  have h_sub : ({a, b, c} : Finset α) ⊆ {x, y, z} := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl | rfl
    · rcases ha with h | h | h <;> tauto
    · rcases hb with h | h | h <;> tauto
    · rcases hc with h | h | h <;> tauto
  -- Equal cardinality + subset → equality
  exact Finset.eq_of_subset_of_card_le h_sub (by omega)

/-! ## Neighborhood Counting Abstractions -/

/-- If vertex v has exactly k neighbors in disjoint sets A ∪ B,
    then the neighbor counts in A and B sum to k. -/
lemma neighbor_count_disjoint_union {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (A B : Finset V) (h_disj : Disjoint A B) :
    ((A ∪ B).filter (G.Adj v)).card =
    (A.filter (G.Adj v)).card + (B.filter (G.Adj v)).card := by
  rw [Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter h_disj

/-- Extract the unique element from a singleton intersection. -/
lemma extract_unique_from_singleton_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) (h_card : (A ∩ B).card = 1) :
    ∃ x, A ∩ B = {x} ∧ x ∈ A ∧ x ∈ B := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h_card
  refine ⟨x, hx, ?_, ?_⟩
  · have : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact Finset.mem_inter.mp this |>.1
  · have : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact Finset.mem_inter.mp this |>.2

/-- If n vertices each have at most k neighbors in W, and the total
    edge count (from W's perspective) is exactly n*k, then each has exactly k. -/
lemma degree_eq_from_bounds_and_bipartite_total {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S W : Finset V) (k : ℕ)
    (h_upper : ∀ s ∈ S, (W.filter (G.Adj s)).card ≤ k)
    (h_total : ∑ w ∈ W, (S.filter (G.Adj w)).card = S.card * k) :
    ∀ s ∈ S, (W.filter (G.Adj s)).card = k := by
  -- By bipartite edge counting symmetry
  have h_sym : ∑ s ∈ S, (W.filter (G.Adj s)).card = ∑ w ∈ W, (S.filter (G.Adj w)).card :=
    bipartite_edge_count_symmetry S W G.Adj G.symm
  rw [h_total] at h_sym
  -- Sum of values ≤ k equals n*k, so each equals k
  by_contra h_not_all
  push_neg at h_not_all
  obtain ⟨s₀, hs₀_in, hs₀_lt⟩ := h_not_all
  have hs₀_lt' : (W.filter (G.Adj s₀)).card < k := Nat.lt_of_le_of_ne (h_upper s₀ hs₀_in) hs₀_lt
  -- Sum < n*k, contradiction
  have h_sum_lt : ∑ s ∈ S, (W.filter (G.Adj s)).card < S.card * k := by
    calc ∑ s ∈ S, (W.filter (G.Adj s)).card
        < ∑ s ∈ S, k := Finset.sum_lt_sum h_upper ⟨s₀, hs₀_in, hs₀_lt'⟩
      _ = S.card * k := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- Two 2-element subsets of a 4-element set that share exactly 1 element
    have intersection of size 1. -/
lemma two_element_sets_intersection {α : Type*} [DecidableEq α]
    (A B : Finset α) (hA : A.card = 2) (_hB : B.card = 2)
    (h_share : (A ∩ B).Nonempty) (h_diff : (A \ B).Nonempty) :
    (A ∩ B).card = 1 := by
  -- A has 2 elements, A ∩ B is nonempty, A \ B is nonempty
  -- So A ∩ B has 1 element (can't have 2, that would make A \ B empty)
  have h_inter_le : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have h_inter_pos : 0 < (A ∩ B).card := Finset.card_pos.mpr h_share
  have h_diff_pos : 0 < (A \ B).card := Finset.card_pos.mpr h_diff
  -- A = (A ∩ B) ∪ (A \ B), and these are disjoint
  have h_disjoint : Disjoint (A ∩ B) (A \ B) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hx hy
    intro heq
    rw [heq] at hx
    exact hy.2 hx.2
  have h_union : A = (A ∩ B) ∪ (A \ B) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h_partition : A.card = (A ∩ B).card + (A \ B).card := by
    conv_lhs => rw [h_union]
    exact Finset.card_union_of_disjoint h_disjoint
  omega

omit [DecidableEq V] in
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

omit [DecidableEq V] in
theorem ramsey_three_five_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 14) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 5 s := by
  have h_prop : HasRamseyProperty 3 5 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_five
    exact (ramsey_of_ramseyNumber_eq_3_5 h_eq).2
  rcases h_prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    exact h_tri s hs
  · exact ⟨s, hs⟩

omit [DecidableEq V] in
theorem ramsey_three_four_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 9) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 4 s := by
  have h_prop : HasRamseyProperty 3 4 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_four
    exact (ramsey_of_ramseyNumber_eq_3_4 h_eq).2
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
    exact (ramsey_of_ramseyNumber_eq_3_5 ramsey_three_five).2 G_H14
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
  Cariolaro's argument (proof complete but needs API fixes):

  1. Pick t ∈ N(v). Since deg(t) ≥ 4 and t has one neighbor v,
     and t has no neighbors in N(v) \ {t} (triangle-free), t has ≥3 neighbors in M.

  2. Let T = {t₁, t₂, t₃} be three such neighbors. Each tᵢ ∈ M has:
     - deg_M(tᵢ) = 4 (from h_M_reg)
     - deg_G(tᵢ) ≤ 5 (from h_max_deg)
     - tᵢ is adjacent to t

     So tᵢ has at most 1 neighbor outside M. That neighbor is t.
     Thus tᵢ has NO neighbors in N(v) \ {t}.

  3. Build 6-IS: (N(v) \ {t}) ∪ {t₁, t₂, t₃}
     - |N(v) \ {t}| = 3, |T| = 3, so total = 6
     - N(v) \ {t} is independent (subset of N(v) which is indep by triangle-free)
     - T is independent (neighbors of t, triangle-free)
     - No edges between (N(v) \ {t}) and T (proven above)

  This contradicts h_no6. □
  -/
  -- Step 1: Pick t ∈ N(v)
  have hN_nonempty : N.Nonempty := Finset.card_pos.mp (by omega : 0 < N.card)
  obtain ⟨t, ht_in_N⟩ := hN_nonempty
  have ht_adj_v : G.Adj v t := by rw [← mem_neighborFinset]; exact ht_in_N

  -- Step 2: t has ≥ 3 neighbors in M
  -- deg(t) ≥ 4, uses 1 for v, no neighbors in N\{t} (triangle-free)
  have ht_deg : G.degree t ≥ 4 := h_min_deg t

  -- Neighbors of t in M
  let t_neighbors_in_M := M.filter (G.Adj t)

  -- t's neighbors outside of {v, t_neighbors_in_M} are in N\{t}, but N is independent
  have ht_no_N_neighbors : ∀ u ∈ N, u ≠ t → ¬G.Adj t u := by
    intro u hu hne h_adj
    -- {v, t, u} would be a triangle: v-t, v-u, t-u
    have h_v_t : G.Adj v t := ht_adj_v
    have h_v_u : G.Adj v u := by rw [← mem_neighborFinset]; exact hu
    have h_clique : G.IsNClique 3 {v, t, u} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact h_v_t
        · exact h_v_u
        · exact G.symm h_v_t
        · exact absurd rfl hxy
        · exact h_adj
        · exact G.symm h_v_u
        · exact G.symm h_adj
        · exact absurd rfl hxy
      · have hvt : v ≠ t := G.ne_of_adj h_v_t
        have hvu : v ≠ u := G.ne_of_adj h_v_u
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hne.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvt, hvu⟩
    exact h_tri _ h_clique

  -- So t's neighbors are: v, plus neighbors in M
  have h_t_neighbors_card : t_neighbors_in_M.card ≥ 3 := by
    -- deg(t) = 1 (for v) + |neighbors in M| + |neighbors in N\{t}|
    -- But |neighbors in N\{t}| = 0
    -- So |neighbors in M| = deg(t) - 1 ≥ 4 - 1 = 3
    have h_neighbors_decomp : G.neighborFinset t ⊆ insert v t_neighbors_in_M ∪ (N.erase t) := by
      intro x hx
      rw [mem_neighborFinset] at hx
      by_cases hxv : x = v
      · rw [Finset.mem_union]
        left
        rw [Finset.mem_insert]
        left; exact hxv
      · by_cases hxM : x ∈ M
        · rw [Finset.mem_union]
          left
          rw [Finset.mem_insert]
          right
          simp only [t_neighbors_in_M, Finset.mem_filter]
          exact ⟨hxM, hx⟩
        · -- x is not in M and not v, so x ∈ N
          rw [Finset.mem_union]
          right
          simp only [Finset.mem_erase]
          constructor
          · intro heq
            subst heq
            exact G.loopless x hx
          · -- x ∈ N: since x is neighbor of t and not v and not in M
            by_contra h_not_in_N
            have : x ∈ insert v N := by
              have hx_in_univ : x ∈ Finset.univ := Finset.mem_univ x
              by_contra h_not_insert
              have : x ∈ M := by
                simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and]
                exact h_not_insert
              exact hxM this
            rcases Finset.mem_insert.mp this with rfl | hx_in_N
            · exact hxv rfl
            · exact h_not_in_N hx_in_N
    -- The N\{t} part has no edges from t (by ht_no_N_neighbors)
    have h_N_erase_empty : (N.erase t).filter (G.Adj t) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and, and_imp]
      intro hne hxN h_adj
      exact ht_no_N_neighbors x hxN hne h_adj
    -- So G.neighborFinset t ⊆ insert v t_neighbors_in_M
    have h_subset : G.neighborFinset t ⊆ insert v t_neighbors_in_M := by
      intro x hx
      have h_in_union := h_neighbors_decomp hx
      rcases Finset.mem_union.mp h_in_union with h_left | h_right
      · exact h_left
      · -- x ∈ N.erase t and G.Adj t x
        have h_adj : G.Adj t x := by rw [← mem_neighborFinset]; exact hx
        have : x ∈ (N.erase t).filter (G.Adj t) := by
          simp only [Finset.mem_filter]
          exact ⟨h_right, h_adj⟩
        rw [h_N_erase_empty] at this
        exact (Finset.notMem_empty x this).elim
    -- Card bound
    have h_card_bound : G.degree t ≤ (insert v t_neighbors_in_M).card := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card h_subset
    have h_v_notin : v ∉ t_neighbors_in_M := by
      simp only [t_neighbors_in_M, Finset.mem_filter]
      intro ⟨hv_M, _⟩
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv_M
      exact hv_M (Finset.mem_insert_self v N)
    calc t_neighbors_in_M.card
        = (insert v t_neighbors_in_M).card - 1 := by
          rw [Finset.card_insert_of_notMem h_v_notin]
          omega
      _ ≥ G.degree t - 1 := by omega
      _ ≥ 4 - 1 := by omega
      _ = 3 := by norm_num

  -- Step 3: Get 3 neighbors of t in M
  obtain ⟨T_set, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_t_neighbors_card
  have hT_in_M : ∀ x ∈ T_set, x ∈ M := by
    intro x hx
    have := hT_sub hx
    simp only [t_neighbors_in_M, Finset.mem_filter] at this
    exact this.1
  have hT_adj_t : ∀ x ∈ T_set, G.Adj t x := by
    intro x hx
    have := hT_sub hx
    simp only [t_neighbors_in_M, Finset.mem_filter] at this
    exact this.2

  -- T_set is independent (neighbors of t in triangle-free graph)
  have hT_indep : G.IsIndepSet T_set := by
    intro x' hx' y' hy' hne' h_adj'
    -- {t, x', y'} would be a triangle
    -- Store the adjacency facts before case analysis
    have h_tx' : G.Adj t x' := hT_adj_t x' hx'
    have h_ty' : G.Adj t y' := hT_adj_t y' hy'
    have h_clique : G.IsNClique 3 {t, x', y'} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha_t | ha_x | ha_y <;> rcases hb with hb_t | hb_x | hb_y
        · exact absurd (ha_t.trans hb_t.symm) hab
        · subst ha_t; subst hb_x; exact h_tx'
        · subst ha_t; subst hb_y; exact h_ty'
        · subst ha_x; subst hb_t; exact G.symm h_tx'
        · exact absurd (ha_x.trans hb_x.symm) hab
        · subst ha_x; subst hb_y; exact h_adj'
        · subst ha_y; subst hb_t; exact G.symm h_ty'
        · subst ha_y; subst hb_x; exact G.symm h_adj'
        · exact absurd (ha_y.trans hb_y.symm) hab
      · have htx' : t ≠ x' := by
          intro heq; subst heq
          exact G.loopless t h_tx'
        have hty' : t ≠ y' := by
          intro heq; subst heq
          exact G.loopless t h_ty'
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hne'
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨htx', hty'⟩
    exact h_tri _ h_clique

  -- Step 4: Each element of T_set has no neighbors in N \ {t}
  -- Argument: x ∈ T_set ⊆ M has deg_M = 4 (from h_M_reg), deg_G ≤ 5.
  -- x is adjacent to t (outside M), so x has at most 5 - 4 = 1 edge outside M.
  -- That edge is t. So x cannot be adjacent to u ∈ N \ {t}.
  have hT_no_N_neighbors : ∀ x ∈ T_set, ∀ u ∈ N, u ≠ t → ¬G.Adj x u := by
    intro x hx u hu hne h_adj
    -- x ∈ M, so find the corresponding index i : Fin 13
    have hx_in_M : x ∈ M := hT_in_M x hx
    -- x has 4 neighbors in M (from G_M being 4-regular)
    -- x is adjacent to t (outside M) and u (in N, also outside M)
    -- So deg_G(x) ≥ 6 > 5, contradiction
    have hx_adj_t : G.Adj x t := G.symm (hT_adj_t x hx)
    have hx_adj_u : G.Adj x u := h_adj
    have ht_not_in_M : t ∉ M := by
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact Finset.mem_insert_of_mem ht_in_N
    have hu_not_in_M : u ∉ M := by
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact Finset.mem_insert_of_mem hu
    -- Get inverse image of x in Fin 13 using the equivalence
    have hx_in_set : x ∈ (↑M : Set (Fin 18)) := hx_in_M
    let ix : Fin 13 := e.symm ⟨x, hx_in_set⟩
    have hix_eq : f ix = x := by
      show (e ix).val = x
      simp only [ix, Equiv.apply_symm_apply]
    -- G_M.degree ix = 4
    have h_deg_ix : G_M.degree ix = 4 := h_M_reg ix
    -- The neighbors of x in M are at least 4 (via the comap degree)
    -- Count: G_M.neighborFinset ix maps bijectively to M-neighbors of x in G
    have h_t_in_nbr : t ∈ G.neighborFinset x := by rw [mem_neighborFinset]; exact hx_adj_t
    have h_u_in_nbr : u ∈ G.neighborFinset x := by rw [mem_neighborFinset]; exact hx_adj_u
    have ht_ne_u : t ≠ u := by
      intro heq; subst heq; exact hne rfl
    -- M-neighbors of x in G
    let M_nbrs_of_x := M.filter (G.Adj x)
    -- Show M_nbrs_of_x.card ≥ 4 via the comap relationship
    have h_M_nbrs_card : M_nbrs_of_x.card ≥ 4 := by
      -- The image of G_M.neighborFinset ix under f is contained in M_nbrs_of_x
      have h_image_subset : (G_M.neighborFinset ix).map f ⊆ M_nbrs_of_x := by
        intro y hy
        rw [Finset.mem_map] at hy
        obtain ⟨j, hj_nbr, hj_eq⟩ := hy
        simp only [Finset.mem_filter, M_nbrs_of_x]
        constructor
        · rw [← hj_eq]; exact hf_in_M j
        · -- G.Adj x (f j) follows from G_M.Adj ix j
          rw [mem_neighborFinset] at hj_nbr
          -- G_M.Adj ix j means G.Adj (f ix) (f j)
          have : G.Adj (f ix) (f j) := hj_nbr
          rw [hix_eq] at this
          rw [← hj_eq]
          exact this
      calc M_nbrs_of_x.card
          ≥ ((G_M.neighborFinset ix).map f).card := Finset.card_le_card h_image_subset
        _ = (G_M.neighborFinset ix).card := Finset.card_map f
        _ = G_M.degree ix := by rw [G_M.card_neighborFinset_eq_degree]
        _ = 4 := h_deg_ix
    -- Now count: deg_G(x) ≥ |M_nbrs_of_x| + |{t, u}| ≥ 4 + 2 = 6
    have h_subset : M_nbrs_of_x ∪ {t, u} ⊆ G.neighborFinset x := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy_M | hy_tu
      · simp only [M_nbrs_of_x, Finset.mem_filter] at hy_M
        rw [mem_neighborFinset]
        exact hy_M.2
      · rcases Finset.mem_insert.mp hy_tu with rfl | hy_u
        · exact h_t_in_nbr
        · simp only [Finset.mem_singleton] at hy_u; subst hy_u; exact h_u_in_nbr
    have h_disjoint : Disjoint M_nbrs_of_x {t, u} := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      simp only [M_nbrs_of_x, Finset.mem_filter] at ha
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact ht_not_in_M (hab ▸ ha.1)
      · simp only [Finset.mem_singleton] at hb'; subst hb'
        exact hu_not_in_M (hab ▸ ha.1)
    have h_card_tu : ({t, u} : Finset (Fin 18)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      exact ht_ne_u
    have h_card_union : (M_nbrs_of_x ∪ {t, u}).card ≥ 6 := by
      rw [Finset.card_union_of_disjoint h_disjoint, h_card_tu]
      omega
    have h_deg_ge_6 : G.degree x ≥ 6 := by
      rw [← G.card_neighborFinset_eq_degree]
      calc (G.neighborFinset x).card
          ≥ (M_nbrs_of_x ∪ {t, u}).card := Finset.card_le_card h_subset
        _ ≥ 6 := h_card_union
    have h_deg_le_5 : G.degree x ≤ 5 := h_max_deg x
    omega

  -- Step 5: Build 6-IS: (N \ {t}) ∪ T_set
  let I := (N.erase t) ∪ T_set

  have hI_card : I.card = 6 := by
    have h_disjoint : Disjoint (N.erase t) T_set := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      have ha_in_N : a ∈ N := (Finset.mem_erase.mp ha).2
      have hb_in_M : b ∈ M := hT_in_M b hb
      intro heq
      subst heq
      have : a ∈ insert v N := Finset.mem_insert_of_mem ha_in_N
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb_in_M
      exact hb_in_M this
    calc I.card
        = (N.erase t).card + T_set.card := Finset.card_union_of_disjoint h_disjoint
      _ = (N.card - 1) + 3 := by rw [Finset.card_erase_of_mem ht_in_N, hT_card]
      _ = (4 - 1) + 3 := by rw [hN_card]
      _ = 6 := by norm_num

  have hI_indep : G.IsNIndepSet 6 I := by
    constructor
    · intro x hx y hy hne h_adj
      rcases Finset.mem_union.mp hx with hx_N | hx_T <;>
      rcases Finset.mem_union.mp hy with hy_N | hy_T
      -- Case 1: x, y ∈ N \ {t} → independent by hN_indep
      · have hx_in_N : x ∈ G.neighborSet v := by
          rw [mem_neighborSet, ← mem_neighborFinset]
          exact (Finset.mem_erase.mp hx_N).2
        have hy_in_N : y ∈ G.neighborSet v := by
          rw [mem_neighborSet, ← mem_neighborFinset]
          exact (Finset.mem_erase.mp hy_N).2
        exact hN_indep hx_in_N hy_in_N hne h_adj
      -- Case 2: x ∈ N \ {t}, y ∈ T_set → no edge by hT_no_N_neighbors
      · have hx_in_N : x ∈ N := (Finset.mem_erase.mp hx_N).2
        have hx_ne_t : x ≠ t := (Finset.mem_erase.mp hx_N).1
        exact hT_no_N_neighbors y hy_T x hx_in_N hx_ne_t (G.symm h_adj)
      -- Case 3: x ∈ T_set, y ∈ N \ {t} → no edge by hT_no_N_neighbors
      · have hy_in_N : y ∈ N := (Finset.mem_erase.mp hy_N).2
        have hy_ne_t : y ≠ t := (Finset.mem_erase.mp hy_N).1
        exact hT_no_N_neighbors x hx_T y hy_in_N hy_ne_t h_adj
      -- Case 4: x, y ∈ T_set → independent by hT_indep
      · exact hT_indep hx_T hy_T hne h_adj
    · exact hI_card

  exact h_no6 I hI_indep

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
    rw [Finset.eq_empty_iff_forall_notMem] at h_empty
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
    rw [Finset.card_insert_of_notMem, hN_card]
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
    simp only [P, Q, Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
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
        simp only [mem_neighborFinset, mem_insert, mem_image, mem_filter, id_eq, exists_eq_right]
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
      · simp only [mem_image, mem_filter, id_eq, exists_eq_right, not_and]
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
    (_h_reg : IsKRegular G 5) (_h_tri : TriangleFree G)
    (v : Fin 18) (p : Fin 18)
    (_hp_nonadj : ¬G.Adj v p)
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

/-! ### Cariolaro's Labeling Structure -/

/-- Cariolaro's labeling scheme for Claim 3.
This structure bundles all the labeled vertices from the paper:
- v: the central vertex
- t, s1, s2, s3, s4: the 5 neighbors of v (N(v))
- p1, p2, p3, p4: the 4 vertices with commonNeighborsCard = 1 (P)
- t1, t2, t3, t4: the 4 Q-vertices adjacent to t (T)
- w1, w2, w3, w4: the 4 Q-vertices not adjacent to t (W)

Each field is a property we can verify step-by-step. -/
structure CariolaroSetup (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) where
  -- The central vertex
  v : Fin 18

  -- N(v) = {t, s1, s2, s3, s4}
  t : Fin 18
  s1 : Fin 18
  s2 : Fin 18
  s3 : Fin 18
  s4 : Fin 18

  -- P = {p1, p2, p3, p4}
  p1 : Fin 18
  p2 : Fin 18
  p3 : Fin 18
  p4 : Fin 18

  -- T = {t1, t2, t3, t4} ⊆ Q (neighbors of t in Q)
  t1 : Fin 18
  t2 : Fin 18
  t3 : Fin 18
  t4 : Fin 18

  -- W = {w1, w2, w3, w4} ⊆ Q (non-neighbors of t in Q)
  w1 : Fin 18
  w2 : Fin 18
  w3 : Fin 18
  w4 : Fin 18

  -- === N(v) properties ===
  h_t_adj_v : G.Adj v t
  h_s1_adj_v : G.Adj v s1
  h_s2_adj_v : G.Adj v s2
  h_s3_adj_v : G.Adj v s3
  h_s4_adj_v : G.Adj v s4

  -- N(v) elements are distinct
  h_Nv_distinct : t ≠ s1 ∧ t ≠ s2 ∧ t ≠ s3 ∧ t ≠ s4 ∧
                  s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧
                  s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4

  -- === P properties ===
  -- Each p is not adjacent to v
  h_p1_nonadj_v : ¬G.Adj v p1
  h_p2_nonadj_v : ¬G.Adj v p2
  h_p3_nonadj_v : ¬G.Adj v p3
  h_p4_nonadj_v : ¬G.Adj v p4

  -- Each p has exactly 1 common neighbor with v (its s-partner)
  h_p1_common1 : commonNeighborsCard G v p1 = 1
  h_p2_common1 : commonNeighborsCard G v p2 = 1
  h_p3_common1 : commonNeighborsCard G v p3 = 1
  h_p4_common1 : commonNeighborsCard G v p4 = 1

  -- The unique s-p edges
  h_s1_adj_p1 : G.Adj s1 p1
  h_s2_adj_p2 : G.Adj s2 p2
  h_s3_adj_p3 : G.Adj s3 p3
  h_s4_adj_p4 : G.Adj s4 p4

  -- s-p cross non-adjacency (si not adjacent to pj for i ≠ j)
  h_s1_nonadj_p2 : ¬G.Adj s1 p2
  h_s1_nonadj_p3 : ¬G.Adj s1 p3
  h_s1_nonadj_p4 : ¬G.Adj s1 p4
  h_s2_nonadj_p1 : ¬G.Adj s2 p1
  h_s2_nonadj_p3 : ¬G.Adj s2 p3
  h_s2_nonadj_p4 : ¬G.Adj s2 p4
  h_s3_nonadj_p1 : ¬G.Adj s3 p1
  h_s3_nonadj_p2 : ¬G.Adj s3 p2
  h_s3_nonadj_p4 : ¬G.Adj s3 p4
  h_s4_nonadj_p1 : ¬G.Adj s4 p1
  h_s4_nonadj_p2 : ¬G.Adj s4 p2
  h_s4_nonadj_p3 : ¬G.Adj s4 p3

  -- P elements are distinct
  h_P_distinct : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4

  -- t is not adjacent to any p (since each p's only N(v)-neighbor is its s)
  h_t_nonadj_p1 : ¬G.Adj t p1
  h_t_nonadj_p2 : ¬G.Adj t p2
  h_t_nonadj_p3 : ¬G.Adj t p3
  h_t_nonadj_p4 : ¬G.Adj t p4

  -- === T properties ===
  -- T vertices are in Q (non-neighbors of v with commonNeighborsCard = 2)
  h_t1_nonadj_v : ¬G.Adj v t1
  h_t2_nonadj_v : ¬G.Adj v t2
  h_t3_nonadj_v : ¬G.Adj v t3
  h_t4_nonadj_v : ¬G.Adj v t4

  h_t1_common2 : commonNeighborsCard G v t1 = 2
  h_t2_common2 : commonNeighborsCard G v t2 = 2
  h_t3_common2 : commonNeighborsCard G v t3 = 2
  h_t4_common2 : commonNeighborsCard G v t4 = 2

  -- T vertices are adjacent to t
  h_t1_adj_t : G.Adj t t1
  h_t2_adj_t : G.Adj t t2
  h_t3_adj_t : G.Adj t t3
  h_t4_adj_t : G.Adj t t4

  -- T elements are distinct
  h_T_distinct : t1 ≠ t2 ∧ t1 ≠ t3 ∧ t1 ≠ t4 ∧ t2 ≠ t3 ∧ t2 ≠ t4 ∧ t3 ≠ t4

  -- === W properties ===
  -- W vertices are in Q
  h_w1_nonadj_v : ¬G.Adj v w1
  h_w2_nonadj_v : ¬G.Adj v w2
  h_w3_nonadj_v : ¬G.Adj v w3
  h_w4_nonadj_v : ¬G.Adj v w4

  h_w1_common2 : commonNeighborsCard G v w1 = 2
  h_w2_common2 : commonNeighborsCard G v w2 = 2
  h_w3_common2 : commonNeighborsCard G v w3 = 2
  h_w4_common2 : commonNeighborsCard G v w4 = 2

  -- W vertices are NOT adjacent to t
  h_w1_nonadj_t : ¬G.Adj t w1
  h_w2_nonadj_t : ¬G.Adj t w2
  h_w3_nonadj_t : ¬G.Adj t w3
  h_w4_nonadj_t : ¬G.Adj t w4

  -- W elements are distinct
  h_W_distinct : w1 ≠ w2 ∧ w1 ≠ w3 ∧ w1 ≠ w4 ∧ w2 ≠ w3 ∧ w2 ≠ w4 ∧ w3 ≠ w4

  -- === Key S-W structure: each w has exactly 2 S-neighbors ===
  -- This is the crucial constraint from commonNeighborsCard(v,w) = 2
  -- combined with w not being adjacent to t.
  -- We need to specify WHICH 2 s's each w is adjacent to.

  -- The pairing: we choose the C₄ pattern (avoiding triangles)
  -- w1 connects s1, s2 → p1-p2 adjacent
  -- w2 connects s2, s3 → p2-p3 adjacent
  -- w3 connects s3, s4 → p3-p4 adjacent
  -- w4 connects s4, s1 → p4-p1 adjacent
  h_w1_adj_s1 : G.Adj w1 s1
  h_w1_adj_s2 : G.Adj w1 s2
  h_w1_nonadj_s3 : ¬G.Adj w1 s3
  h_w1_nonadj_s4 : ¬G.Adj w1 s4

  h_w2_adj_s2 : G.Adj w2 s2
  h_w2_adj_s3 : G.Adj w2 s3
  h_w2_nonadj_s1 : ¬G.Adj w2 s1
  h_w2_nonadj_s4 : ¬G.Adj w2 s4

  h_w3_adj_s3 : G.Adj w3 s3
  h_w3_adj_s4 : G.Adj w3 s4
  h_w3_nonadj_s1 : ¬G.Adj w3 s1
  h_w3_nonadj_s2 : ¬G.Adj w3 s2

  h_w4_adj_s4 : G.Adj w4 s4
  h_w4_adj_s1 : G.Adj w4 s1
  h_w4_nonadj_s2 : ¬G.Adj w4 s2
  h_w4_nonadj_s3 : ¬G.Adj w4 s3

  -- W vertices are not adjacent to P (they're in Q, p's have only s-neighbors in N(v))
  h_w1_nonadj_p1 : ¬G.Adj w1 p1
  h_w1_nonadj_p2 : ¬G.Adj w1 p2
  h_w2_nonadj_p2 : ¬G.Adj w2 p2
  h_w2_nonadj_p3 : ¬G.Adj w2 p3
  h_w3_nonadj_p3 : ¬G.Adj w3 p3
  h_w3_nonadj_p4 : ¬G.Adj w3 p4
  h_w4_nonadj_p4 : ¬G.Adj w4 p4
  h_w4_nonadj_p1 : ¬G.Adj w4 p1

/-- Helper: two neighbors of v are non-adjacent in a triangle-free graph -/
lemma neighbors_non_adj_of_triangleFree {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (v x y : Fin 18)
    (hx_adj : G.Adj v x) (hy_adj : G.Adj v y) (hne : x ≠ y) :
    ¬G.Adj x y := by
  intro h_adj
  have h_clique : G.IsNClique 3 {v, x, y} := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact hx_adj
      · exact hy_adj
      · exact G.symm hx_adj
      · exact absurd rfl hab
      · exact h_adj
      · exact G.symm hy_adj
      · exact G.symm h_adj
      · exact absurd rfl hab
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact hne
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hx_adj, G.ne_of_adj hy_adj⟩
  exact h_tri _ h_clique

/-- N(v) is an independent set (any two neighbors of v are non-adjacent) in a triangle-free graph. -/
lemma CariolaroSetup.Nv_independent {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    {h_reg : IsKRegular G 5} {h_tri : TriangleFree G} {h_no6 : NoKIndepSet 6 G}
    (setup : CariolaroSetup G h_reg h_tri h_no6) :
    ¬G.Adj setup.t setup.s1 ∧ ¬G.Adj setup.t setup.s2 ∧ ¬G.Adj setup.t setup.s3 ∧ ¬G.Adj setup.t setup.s4 ∧
    ¬G.Adj setup.s1 setup.s2 ∧ ¬G.Adj setup.s1 setup.s3 ∧ ¬G.Adj setup.s1 setup.s4 ∧
    ¬G.Adj setup.s2 setup.s3 ∧ ¬G.Adj setup.s2 setup.s4 ∧ ¬G.Adj setup.s3 setup.s4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.t setup.s1
      setup.h_t_adj_v setup.h_s1_adj_v setup.h_Nv_distinct.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.t setup.s2
      setup.h_t_adj_v setup.h_s2_adj_v setup.h_Nv_distinct.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.t setup.s3
      setup.h_t_adj_v setup.h_s3_adj_v setup.h_Nv_distinct.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.t setup.s4
      setup.h_t_adj_v setup.h_s4_adj_v setup.h_Nv_distinct.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s1 setup.s2
      setup.h_s1_adj_v setup.h_s2_adj_v setup.h_Nv_distinct.2.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s1 setup.s3
      setup.h_s1_adj_v setup.h_s3_adj_v setup.h_Nv_distinct.2.2.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s1 setup.s4
      setup.h_s1_adj_v setup.h_s4_adj_v setup.h_Nv_distinct.2.2.2.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s2 setup.s3
      setup.h_s2_adj_v setup.h_s3_adj_v setup.h_Nv_distinct.2.2.2.2.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s2 setup.s4
      setup.h_s2_adj_v setup.h_s4_adj_v setup.h_Nv_distinct.2.2.2.2.2.2.2.2.1
  · exact neighbors_non_adj_of_triangleFree h_tri setup.v setup.s3 setup.s4
      setup.h_s3_adj_v setup.h_s4_adj_v setup.h_Nv_distinct.2.2.2.2.2.2.2.2.2

/-- From a CariolaroSetup, derive that P forms a 4-cycle. -/
lemma CariolaroSetup.P_is_cycle {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    {h_reg : IsKRegular G 5} {h_tri : TriangleFree G} {h_no6 : NoKIndepSet 6 G}
    (setup : CariolaroSetup G h_reg h_tri h_no6) :
    G.Adj setup.p1 setup.p2 ∧ G.Adj setup.p2 setup.p3 ∧
    G.Adj setup.p3 setup.p4 ∧ G.Adj setup.p4 setup.p1 ∧
    ¬G.Adj setup.p1 setup.p3 ∧ ¬G.Adj setup.p2 setup.p4 := by
  -- Strategy:
  -- 1. Apply p_adjacent_of_shared_w for each cycle edge
  -- 2. Derive diagonal non-adjacencies from triangle-freeness

  -- Get N(v) independence for use in p_adjacent_of_shared_w
  obtain ⟨ht_s1, ht_s2, ht_s3, ht_s4, hs1_s2, hs1_s3, hs1_s4, hs2_s3, hs2_s4, hs3_s4⟩ :=
    setup.Nv_independent

  -- Extract N(v) distinctness for cleaner proof
  have hNv := setup.h_Nv_distinct
  have ht_ne_s1 : setup.t ≠ setup.s1 := hNv.1
  have ht_ne_s2 : setup.t ≠ setup.s2 := hNv.2.1
  have ht_ne_s3 : setup.t ≠ setup.s3 := hNv.2.2.1
  have ht_ne_s4 : setup.t ≠ setup.s4 := hNv.2.2.2.1
  have hs1_ne_s2 : setup.s1 ≠ setup.s2 := hNv.2.2.2.2.1
  have hs1_ne_s3 : setup.s1 ≠ setup.s3 := hNv.2.2.2.2.2.1
  have hs1_ne_s4 : setup.s1 ≠ setup.s4 := hNv.2.2.2.2.2.2.1
  have hs2_ne_s3 : setup.s2 ≠ setup.s3 := hNv.2.2.2.2.2.2.2.1
  have hs2_ne_s4 : setup.s2 ≠ setup.s4 := hNv.2.2.2.2.2.2.2.2.1
  have hs3_ne_s4 : setup.s3 ≠ setup.s4 := hNv.2.2.2.2.2.2.2.2.2

  -- Extract P distinctness
  have hP := setup.h_P_distinct
  have hp1_ne_p2 : setup.p1 ≠ setup.p2 := hP.1
  have hp1_ne_p3 : setup.p1 ≠ setup.p3 := hP.2.1
  have hp1_ne_p4 : setup.p1 ≠ setup.p4 := hP.2.2.1
  have hp2_ne_p3 : setup.p2 ≠ setup.p3 := hP.2.2.2.1
  have hp2_ne_p4 : setup.p2 ≠ setup.p4 := hP.2.2.2.2.1
  have hp3_ne_p4 : setup.p3 ≠ setup.p4 := hP.2.2.2.2.2

  -- Edge 1: p1-p2 (w1 shares s1, s2)
  have h_p1_p2 : G.Adj setup.p1 setup.p2 :=
    p_adjacent_of_shared_w h_tri h_no6 setup.v
      setup.p1 setup.p2 setup.s1 setup.s2 setup.w1
      setup.h_p1_nonadj_v setup.h_p2_nonadj_v hp1_ne_p2
      setup.h_s1_adj_v setup.h_s2_adj_v hs1_ne_s2
      setup.h_s1_adj_p1 setup.h_s2_adj_p2
      setup.h_s1_nonadj_p2 setup.h_s2_nonadj_p1
      setup.h_w1_adj_s1 setup.h_w1_adj_s2
      (fun h => setup.h_w1_nonadj_v (G.symm h))  -- v w swapped
      setup.h_w1_nonadj_p1 setup.h_w1_nonadj_p2  -- p cases match
      hs1_s2
      setup.t setup.s3 setup.s4
      setup.h_t_adj_v setup.h_s3_adj_v setup.h_s4_adj_v
      -- ht_ne_s1 ht_ne_s2 hs3_ne_s1 hs3_ne_s2 hs4_ne_s1 hs4_ne_s2 ht_ne_s3 ht_ne_s4 hs3_ne_s4
      ht_ne_s1 ht_ne_s2 hs1_ne_s3.symm hs2_ne_s3.symm hs1_ne_s4.symm hs2_ne_s4.symm ht_ne_s3 ht_ne_s4 hs3_ne_s4
      setup.h_t_nonadj_p1 setup.h_t_nonadj_p2 setup.h_w1_nonadj_t
      setup.h_s3_nonadj_p1 setup.h_s3_nonadj_p2 (fun h => setup.h_w1_nonadj_s3 (G.symm h))
      setup.h_s4_nonadj_p1 setup.h_s4_nonadj_p2 (fun h => setup.h_w1_nonadj_s4 (G.symm h))

  -- Edge 2: p2-p3 (w2 shares s2, s3)
  have h_p2_p3 : G.Adj setup.p2 setup.p3 :=
    p_adjacent_of_shared_w h_tri h_no6 setup.v
      setup.p2 setup.p3 setup.s2 setup.s3 setup.w2
      setup.h_p2_nonadj_v setup.h_p3_nonadj_v hp2_ne_p3
      setup.h_s2_adj_v setup.h_s3_adj_v hs2_ne_s3
      setup.h_s2_adj_p2 setup.h_s3_adj_p3
      setup.h_s2_nonadj_p3 setup.h_s3_nonadj_p2
      setup.h_w2_adj_s2 setup.h_w2_adj_s3
      (fun h => setup.h_w2_nonadj_v (G.symm h))
      setup.h_w2_nonadj_p2 setup.h_w2_nonadj_p3
      hs2_s3
      setup.t setup.s1 setup.s4
      setup.h_t_adj_v setup.h_s1_adj_v setup.h_s4_adj_v
      ht_ne_s2 ht_ne_s3 hs1_ne_s2 hs1_ne_s3 hs2_ne_s4.symm hs3_ne_s4.symm ht_ne_s1 ht_ne_s4 hs1_ne_s4
      setup.h_t_nonadj_p2 setup.h_t_nonadj_p3 setup.h_w2_nonadj_t
      setup.h_s1_nonadj_p2 setup.h_s1_nonadj_p3 (fun h => setup.h_w2_nonadj_s1 (G.symm h))
      setup.h_s4_nonadj_p2 setup.h_s4_nonadj_p3 (fun h => setup.h_w2_nonadj_s4 (G.symm h))

  -- Edge 3: p3-p4 (w3 shares s3, s4)
  have h_p3_p4 : G.Adj setup.p3 setup.p4 :=
    p_adjacent_of_shared_w h_tri h_no6 setup.v
      setup.p3 setup.p4 setup.s3 setup.s4 setup.w3
      setup.h_p3_nonadj_v setup.h_p4_nonadj_v hp3_ne_p4
      setup.h_s3_adj_v setup.h_s4_adj_v hs3_ne_s4
      setup.h_s3_adj_p3 setup.h_s4_adj_p4
      setup.h_s3_nonadj_p4 setup.h_s4_nonadj_p3
      setup.h_w3_adj_s3 setup.h_w3_adj_s4
      (fun h => setup.h_w3_nonadj_v (G.symm h))
      setup.h_w3_nonadj_p3 setup.h_w3_nonadj_p4
      hs3_s4
      setup.t setup.s1 setup.s2
      setup.h_t_adj_v setup.h_s1_adj_v setup.h_s2_adj_v
      ht_ne_s3 ht_ne_s4 hs1_ne_s3 hs1_ne_s4 hs2_ne_s3 hs2_ne_s4 ht_ne_s1 ht_ne_s2 hs1_ne_s2
      setup.h_t_nonadj_p3 setup.h_t_nonadj_p4 setup.h_w3_nonadj_t
      setup.h_s1_nonadj_p3 setup.h_s1_nonadj_p4 (fun h => setup.h_w3_nonadj_s1 (G.symm h))
      setup.h_s2_nonadj_p3 setup.h_s2_nonadj_p4 (fun h => setup.h_w3_nonadj_s2 (G.symm h))

  -- Edge 4: p4-p1 (w4 shares s4, s1)
  have h_p4_p1 : G.Adj setup.p4 setup.p1 :=
    p_adjacent_of_shared_w h_tri h_no6 setup.v
      setup.p4 setup.p1 setup.s4 setup.s1 setup.w4
      setup.h_p4_nonadj_v setup.h_p1_nonadj_v hp1_ne_p4.symm
      setup.h_s4_adj_v setup.h_s1_adj_v hs1_ne_s4.symm
      setup.h_s4_adj_p4 setup.h_s1_adj_p1
      setup.h_s4_nonadj_p1 setup.h_s1_nonadj_p4
      setup.h_w4_adj_s4 setup.h_w4_adj_s1
      (fun h => setup.h_w4_nonadj_v (G.symm h))
      setup.h_w4_nonadj_p4 setup.h_w4_nonadj_p1
      (fun h => hs1_s4 (G.symm h))
      setup.t setup.s2 setup.s3
      setup.h_t_adj_v setup.h_s2_adj_v setup.h_s3_adj_v
      ht_ne_s4 ht_ne_s1 hs2_ne_s4 hs1_ne_s2.symm hs3_ne_s4 hs1_ne_s3.symm ht_ne_s2 ht_ne_s3 hs2_ne_s3
      setup.h_t_nonadj_p4 setup.h_t_nonadj_p1 setup.h_w4_nonadj_t
      setup.h_s2_nonadj_p4 setup.h_s2_nonadj_p1 (fun h => setup.h_w4_nonadj_s2 (G.symm h))
      setup.h_s3_nonadj_p4 setup.h_s3_nonadj_p1 (fun h => setup.h_w4_nonadj_s3 (G.symm h))

  -- Diagonal 1: p1-p3 non-adjacent (else {p1, p2, p3} triangle)
  have h_not_p1_p3 : ¬G.Adj setup.p1 setup.p3 := by
    intro h_adj
    have h_clique : G.IsNClique 3 {setup.p1, setup.p2, setup.p3} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact h_p1_p2
        · exact h_adj
        · exact G.symm h_p1_p2
        · exact absurd rfl hxy
        · exact h_p2_p3
        · exact G.symm h_adj
        · exact G.symm h_p2_p3
        · exact absurd rfl hxy
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hp2_ne_p3
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hp1_ne_p2, hp1_ne_p3⟩
    exact h_tri _ h_clique

  -- Diagonal 2: p2-p4 non-adjacent (else {p2, p3, p4} triangle)
  have h_not_p2_p4 : ¬G.Adj setup.p2 setup.p4 := by
    intro h_adj
    have h_clique : G.IsNClique 3 {setup.p2, setup.p3, setup.p4} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact h_p2_p3
        · exact h_adj
        · exact G.symm h_p2_p3
        · exact absurd rfl hxy
        · exact h_p3_p4
        · exact G.symm h_adj
        · exact G.symm h_p3_p4
        · exact absurd rfl hxy
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hp3_ne_p4
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hp2_ne_p3, hp2_ne_p4⟩
    exact h_tri _ h_clique

  exact ⟨h_p1_p2, h_p2_p3, h_p3_p4, h_p4_p1, h_not_p1_p3, h_not_p2_p4⟩

/-! ### Cariolaro's S-W Structure (Key Lemmas from the Paper)

Following Cariolaro's paper, the key structural facts are:
1. t (5th element of N(v)) has exactly 4 neighbors in Q → T = {t1, t2, t3, t4}
2. W = Q \ T has exactly 4 elements
3. Each ti ∈ T has exactly 1 S-neighbor (from commonNeighborsCard = 2, with t as the other)
4. Each si has exactly 1 T-neighbor and 2 W-neighbors
5. Each wi has exactly 2 S-neighbors

These facts lead to the S-W bipartite structure being 2-regular, which forces
exactly 4 pairs of s's to share W-neighbors, giving the C4 structure on P.
-/

/-- t has exactly 4 neighbors in Q.
Proof sketch (Cariolaro):
- t has degree 5, with 1 edge to v
- N(v) is independent (triangle-free), so t has no edges to other N(v) elements
- t is not adjacent to any p ∈ P (each p's only N(v)-neighbor is its unique s-partner)
- So t's 4 remaining neighbors are all in Q -/
lemma t_has_four_Q_neighbors {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v t : Fin 18) (ht_adj_v : G.Adj v t)
    (Q : Finset (Fin 18))
    (_hQ_card : Q.card = 8)
    (hv_notin_Q : v ∉ Q)
    (hQ_complete : ∀ x, ¬G.Adj v x → x ≠ v → commonNeighborsCard G v x = 2 → x ∈ Q)
    (P : Finset (Fin 18))
    (_hP_card : P.card = 4)
    (hP_def : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1)
    (ht_nonadj_P : ∀ p ∈ P, ¬G.Adj t p)
    (hPQ_partition : ∀ x, x ≠ v → ¬G.Adj v x →
      (commonNeighborsCard G v x = 1 → x ∈ P) ∧ (commonNeighborsCard G v x = 2 → x ∈ Q)) :
    (Q.filter (G.Adj t)).card = 4 := by
  -- Step 1: t has degree 5
  have ht_deg : (G.neighborFinset t).card = 5 := h_reg t

  -- Step 2: v is a neighbor of t
  have hv_mem_Nt : v ∈ G.neighborFinset t := by
    simp only [mem_neighborFinset]
    exact G.symm ht_adj_v

  -- Step 3: Any neighbor x of t with x ≠ v must be in Q
  have h_other_nbrs_in_Q : ∀ x ∈ G.neighborFinset t, x ≠ v → x ∈ Q := by
    intro x hx_mem hx_ne_v
    rw [SimpleGraph.mem_neighborFinset] at hx_mem
    have hx_adj_t : G.Adj t x := hx_mem
    -- Show x is not adjacent to v (triangle-free argument)
    have hx_nonadj_v : ¬G.Adj v x := by
      intro h_adj_vx
      -- If x adjacent to v and t adjacent to x, then v-x-t forms a triangle
      -- N(v) is independent in a triangle-free graph
      have hNv_indep := neighborSet_indep_of_triangleFree h_tri v
      -- x and t are both in N(v), x ≠ t (since x is adjacent to t, not a self-loop)
      have hx_ne_t : x ≠ t := fun h_eq => by
        subst h_eq
        exact G.loopless x hx_adj_t
      -- So x and t should not be adjacent
      exact hNv_indep h_adj_vx ht_adj_v hx_ne_t (G.symm hx_adj_t)
    -- x is a non-neighbor of v, so x ∈ P ∪ Q
    -- Apply the bounds from claim2
    have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
    have h_common_eq : commonNeighborsCard G v x = 1 ∨ commonNeighborsCard G v x = 2 := by
      omega
    -- If commonNeighborsCard = 1, then x ∈ P, but then t is not adjacent to x (contradiction)
    cases h_common_eq with
    | inl h1 =>
      have hx_in_P : x ∈ P := (hPQ_partition x hx_ne_v hx_nonadj_v).1 h1
      have h_contra : ¬G.Adj t x := ht_nonadj_P x hx_in_P
      exact absurd hx_adj_t h_contra
    | inr h2 =>
      exact (hPQ_partition x hx_ne_v hx_nonadj_v).2 h2

  -- Step 4: v ∉ Q (given as hypothesis)

  -- Step 5: G.neighborFinset t = {v} ∪ (Q.filter (G.Adj t))
  have h_Nt_eq : G.neighborFinset t = insert v (Q.filter (G.Adj t)) := by
    ext x
    simp only [mem_insert, mem_filter, mem_neighborFinset]
    constructor
    · intro hx_adj
      by_cases hxv : x = v
      · left; exact hxv
      · right
        have hx_mem : x ∈ G.neighborFinset t := by rw [SimpleGraph.mem_neighborFinset]; exact hx_adj
        have hx_in_Q := h_other_nbrs_in_Q x hx_mem hxv
        exact ⟨hx_in_Q, hx_adj⟩
    · intro h
      cases h with
      | inl hxv => subst hxv; exact G.symm ht_adj_v
      | inr hxQ => exact hxQ.2

  -- Step 6: {v} and Q.filter (G.Adj t) are disjoint
  have h_v_notin_filter : v ∉ Q.filter (G.Adj t) := by
    simp only [mem_filter, not_and]
    intro hv_in_Q
    exact absurd hv_in_Q hv_notin_Q

  -- Step 7: Count
  calc (Q.filter (G.Adj t)).card
      = (insert v (Q.filter (G.Adj t))).card - 1 := by
        rw [card_insert_of_notMem h_v_notin_filter]
        omega
    _ = (G.neighborFinset t).card - 1 := by rw [← h_Nt_eq]
    _ = 5 - 1 := by rw [ht_deg]
    _ = 4 := by norm_num

/-- Each ti ∈ T (neighbor of t in Q) has exactly 1 S-neighbor.
Proof sketch: ti has commonNeighborsCard(v, ti) = 2. One common neighbor is t.
The other must be some sj ∈ N(v) \ {t}. -/
lemma T_vertex_has_one_S_neighbor {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (_h_reg : IsKRegular G 5) (_h_tri : TriangleFree G)
    (v t ti : Fin 18)
    (ht_adj_v : G.Adj v t) (hti_adj_t : G.Adj t ti)
    (hti_common2 : commonNeighborsCard G v ti = 2)
    (S : Finset (Fin 18)) (_hS_card : S.card = 4)
    (hS_eq : S = (G.neighborFinset v).erase t) :
    (S.filter (G.Adj ti)).card = 1 := by
  -- ti's 2 common neighbors with v are: t and exactly one s ∈ S
  unfold commonNeighborsCard _root_.commonNeighbors at hti_common2
  have h_inter_card : (G.neighborFinset v ∩ G.neighborFinset ti).card = 2 := hti_common2
  -- t is one of the common neighbors
  have ht_in_inter : t ∈ G.neighborFinset v ∩ G.neighborFinset ti := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨ht_adj_v, G.symm hti_adj_t⟩
  -- Extract the two elements
  obtain ⟨a, b, hab_ne, h_eq⟩ := Finset.card_eq_two.mp h_inter_card
  have ht_in : t ∈ ({a, b} : Finset (Fin 18)) := by rw [← h_eq]; exact ht_in_inter
  -- S.filter (G.Adj ti) = (intersection) \ {t}
  have h_filter_eq : S.filter (G.Adj ti) = (G.neighborFinset v ∩ G.neighborFinset ti).erase t := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · intro ⟨hx_in_S, hx_adj_ti⟩
      rw [hS_eq] at hx_in_S
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hx_in_S
      exact ⟨hx_in_S.1, hx_in_S.2, hx_adj_ti⟩
    · intro ⟨hx_ne_t, hx_adj_v, hx_adj_ti⟩
      constructor
      · rw [hS_eq]
        simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
        exact ⟨hx_ne_t, hx_adj_v⟩
      · exact hx_adj_ti
  rw [h_filter_eq, Finset.card_erase_of_mem ht_in_inter, h_inter_card]

/-- Each wi ∈ W has exactly 2 S-neighbors.
Proof sketch: wi has commonNeighborsCard(v, wi) = 2. wi is not adjacent to t (by def of W).
So wi's 2 common neighbors with v are both from S = N(v) \ {t}. -/
lemma W_vertex_has_two_S_neighbors {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (_h_tri : TriangleFree G)
    (v t wi : Fin 18)
    (ht_adj_v : G.Adj v t) (hwi_nonadj_t : ¬G.Adj t wi)
    (hwi_common2 : commonNeighborsCard G v wi = 2)
    (S : Finset (Fin 18)) (_hS_card : S.card = 4)
    (hS_eq : S = (G.neighborFinset v).erase t) :
    (S.filter (G.Adj wi)).card = 2 := by
  -- wi's 2 common neighbors with v are both in S (since wi is not adjacent to t)
  -- Common neighbors of v and wi
  unfold commonNeighborsCard _root_.commonNeighbors at hwi_common2
  -- The common neighbors are exactly the N(v)-neighbors of wi
  -- Since wi is not adjacent to t, these 2 must be in S = N(v) \ {t}
  have h_inter : (G.neighborFinset v ∩ G.neighborFinset wi).card = 2 := hwi_common2
  -- t is not in the intersection (since wi is not adjacent to t)
  have ht_notin_inter : t ∉ G.neighborFinset v ∩ G.neighborFinset wi := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, not_and]
    intro _
    exact fun h => hwi_nonadj_t (G.symm h)
  -- The intersection is a subset of N(v) \ {t} = S
  have h_inter_sub_S : G.neighborFinset v ∩ G.neighborFinset wi ⊆ S := by
    rw [hS_eq]
    intro x hx
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    constructor
    · intro h_eq
      subst h_eq
      exact hwi_nonadj_t (G.symm hx.2)
    · exact hx.1
  -- S.filter (G.Adj wi) contains exactly the intersection
  have h_filter_eq : S.filter (G.Adj wi) = G.neighborFinset v ∩ G.neighborFinset wi := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · intro ⟨hx_in_S, hx_adj_wi⟩
      rw [hS_eq] at hx_in_S
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hx_in_S
      exact ⟨hx_in_S.2, hx_adj_wi⟩
    · intro ⟨hx_adj_v, hx_adj_wi⟩
      constructor
      · rw [hS_eq]
        simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
        constructor
        · intro h_eq
          subst h_eq
          exact hwi_nonadj_t (G.symm hx_adj_wi)
        · exact hx_adj_v
      · exact hx_adj_wi
  rw [h_filter_eq, h_inter]

/-- Key constraint: Two different s's cannot share the same PAIR of W-neighbors.
If s1 and s2 both had W-neighbors {w1, w2}, then commonNeighbors(s1, s2) would
include {v, w1, w2} = 3 elements, contradicting commonNeighborsCard ≤ 2.

This rules out the "two 4-cycles" case for the S-W bipartite graph:
- If S-W were two 4-cycles, e.g., (s1-w1-s2-w2-s1) and (s3-w3-s4-w4-s3),
  then s1 and s2 would share {w1, w2}, violating this constraint.
- Therefore S-W must be a single 8-cycle.
- In an 8-cycle, exactly 4 pairs of consecutive s's share exactly 1 w each.
- By p_adjacent_of_shared_w, this gives exactly 4 P-edges, making P a 4-cycle. -/
lemma S_pair_share_at_most_one_W {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v s1 s2 w1 w2 : Fin 18)
    (hs1_adj_v : G.Adj v s1) (hs2_adj_v : G.Adj v s2) (hs1_ne_s2 : s1 ≠ s2)
    (hv_ne_w1 : v ≠ w1) (hv_ne_w2 : v ≠ w2) (hw1_ne_w2 : w1 ≠ w2)
    (hs1_adj_w1 : G.Adj s1 w1) (hs1_adj_w2 : G.Adj s1 w2)
    (hs2_adj_w1 : G.Adj s2 w1) (hs2_adj_w2 : G.Adj s2 w2) :
    False := by
  -- s1 and s2 are both in N(v), so they are non-adjacent (triangle-free)
  have hs12_nonadj : ¬G.Adj s1 s2 := neighborSet_indep_of_triangleFree h_tri v hs1_adj_v hs2_adj_v hs1_ne_s2
  -- Use the Finset-based commonNeighbors (which is _root_.commonNeighbors)
  -- v is in N(s1) ∩ N(s2): mem_neighborFinset says a ∈ G.neighborFinset b ↔ G.Adj b a
  have hv_in_Ns1 : v ∈ G.neighborFinset s1 := by rw [mem_neighborFinset]; exact G.symm hs1_adj_v
  have hv_in_Ns2 : v ∈ G.neighborFinset s2 := by rw [mem_neighborFinset]; exact G.symm hs2_adj_v
  have hw1_in_Ns1 : w1 ∈ G.neighborFinset s1 := by rw [mem_neighborFinset]; exact hs1_adj_w1
  have hw1_in_Ns2 : w1 ∈ G.neighborFinset s2 := by rw [mem_neighborFinset]; exact hs2_adj_w1
  have hw2_in_Ns1 : w2 ∈ G.neighborFinset s1 := by rw [mem_neighborFinset]; exact hs1_adj_w2
  have hw2_in_Ns2 : w2 ∈ G.neighborFinset s2 := by rw [mem_neighborFinset]; exact hs2_adj_w2
  -- {v, w1, w2} ⊆ N(s1) ∩ N(s2) = commonNeighbors
  have hv_common : v ∈ G.neighborFinset s1 ∩ G.neighborFinset s2 := Finset.mem_inter.mpr ⟨hv_in_Ns1, hv_in_Ns2⟩
  have hw1_common : w1 ∈ G.neighborFinset s1 ∩ G.neighborFinset s2 := Finset.mem_inter.mpr ⟨hw1_in_Ns1, hw1_in_Ns2⟩
  have hw2_common : w2 ∈ G.neighborFinset s1 ∩ G.neighborFinset s2 := Finset.mem_inter.mpr ⟨hw2_in_Ns1, hw2_in_Ns2⟩
  -- So |commonNeighbors| ≥ 3
  have h_card_ge_3 : commonNeighborsCard G s1 s2 ≥ 3 := by
    unfold commonNeighborsCard _root_.commonNeighbors
    have h_subset : ({v, w1, w2} : Finset (Fin 18)) ⊆ G.neighborFinset s1 ∩ G.neighborFinset s2 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv_common
      · exact hw1_common
      · exact hw2_common
    have h_card_3 : ({v, w1, w2} : Finset (Fin 18)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact hw1_ne_w2
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv_ne_w1, hv_ne_w2⟩
    calc (G.neighborFinset s1 ∩ G.neighborFinset s2).card
        ≥ ({v, w1, w2} : Finset (Fin 18)).card := Finset.card_le_card h_subset
      _ = 3 := h_card_3
  -- But commonNeighborsCard ≤ 2 for non-adjacent vertices
  have h_card_le_2 : commonNeighborsCard G s1 s2 ≤ 2 :=
    commonNeighborsCard_le_two h_tri h_no6 h_reg s1 s2 hs1_ne_s2.symm hs12_nonadj
  omega

/-! ### Degree computation from explicit cycle structure -/

/-- In a 4-cycle p1-p2-p3-p4-p1, each vertex has exactly 2 neighbors among {p1,p2,p3,p4}.
This is immediate from the structure: each vertex is adjacent to exactly 2 others
(the cycle edges) and non-adjacent to the remaining 1 (the diagonal).

TODO: This proof has a Lean 4 scoping issue with `rcases ... rfl` patterns
eliminating bound variables inside nested `have` blocks. The mathematical
content is straightforward: filter the 4-element set by adjacency, get 2 elements. -/
lemma cycle_vertex_has_two_neighbors {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (p1 p2 p3 p4 : Fin 18)
    (hdist : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4)
    (h_cycle : G.Adj p1 p2 ∧ G.Adj p2 p3 ∧ G.Adj p3 p4 ∧ G.Adj p4 p1 ∧
               ¬G.Adj p1 p3 ∧ ¬G.Adj p2 p4)
    (P : Finset (Fin 18)) (hP_eq : P = {p1, p2, p3, p4}) :
    ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = 2 := by
  -- Save vertex references before case split to avoid scoping issues
  let a1 := p1; let a2 := p2; let a3 := p3; let a4 := p4
  have ha1 : a1 = p1 := rfl; have ha2 : a2 = p2 := rfl
  have ha3 : a3 = p3 := rfl; have ha4 : a4 = p4 := rfl
  -- Precompute all the distinctness facts
  -- hdist : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4
  have hne12 : a1 ≠ a2 := hdist.1
  have hne13 : a1 ≠ a3 := hdist.2.1
  have hne14 : a1 ≠ a4 := hdist.2.2.1
  have hne23 : a2 ≠ a3 := hdist.2.2.2.1
  have hne24 : a2 ≠ a4 := hdist.2.2.2.2.1
  have hne34 : a3 ≠ a4 := hdist.2.2.2.2.2
  -- Precompute adjacency facts
  have hadj12 : G.Adj a1 a2 := h_cycle.1
  have hadj23 : G.Adj a2 a3 := h_cycle.2.1
  have hadj34 : G.Adj a3 a4 := h_cycle.2.2.1
  have hadj41 : G.Adj a4 a1 := h_cycle.2.2.2.1
  have hnadj13 : ¬G.Adj a1 a3 := h_cycle.2.2.2.2.1
  have hnadj24 : ¬G.Adj a2 a4 := h_cycle.2.2.2.2.2
  -- Now P = {a1, a2, a3, a4}
  have hP_eq' : P = {a1, a2, a3, a4} := hP_eq
  intro p hp
  rw [hP_eq'] at hp ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  obtain rfl | rfl | rfl | rfl := hp
  -- Case p = a1: neighbors are a2 and a4
  · have h_filter_eq : ({a1, a2, a3, a4} : Finset (Fin 18)).filter (fun q => q ≠ a1 ∧ G.Adj a1 q) = {a2, a4} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hx_mem, hx_ne, hx_adj⟩
        obtain hx1 | hx2 | hx3 | hx4 := hx_mem
        · exact (hx_ne hx1).elim
        · left; exact hx2
        · subst hx3; exact (hnadj13 hx_adj).elim
        · right; exact hx4
      · intro hx
        obtain hx2 | hx4 := hx
        -- For a2: need a2 ≠ a1 (use hne12.symm) and G.Adj a1 a2 (use hadj12)
        · subst hx2; exact ⟨Or.inr (Or.inl rfl), hne12.symm, hadj12⟩
        -- For a4: need a4 ≠ a1 (use hne14.symm) and G.Adj a1 a4 (use G.adj_symm hadj41)
        · subst hx4; exact ⟨Or.inr (Or.inr (Or.inr rfl)), hne14.symm, G.adj_symm hadj41⟩
    rw [h_filter_eq]
    simp [hne24]
  -- Case p = a2: neighbors are a1 and a3
  · have h_filter_eq : ({a1, a2, a3, a4} : Finset (Fin 18)).filter (fun q => q ≠ a2 ∧ G.Adj a2 q) = {a1, a3} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hx_mem, hx_ne, hx_adj⟩
        obtain hx1 | hx2 | hx3 | hx4 := hx_mem
        · left; exact hx1
        · exact (hx_ne hx2).elim
        · right; exact hx3
        · subst hx4; exact (hnadj24 hx_adj).elim
      · intro hx
        obtain hx1 | hx3 := hx
        -- For a1: need a1 ≠ a2 (use hne12) and G.Adj a2 a1 (use G.adj_symm hadj12)
        · subst hx1; exact ⟨Or.inl rfl, hne12, G.adj_symm hadj12⟩
        -- For a3: need a3 ≠ a2 (use hne23.symm) and G.Adj a2 a3 (use hadj23)
        · subst hx3; exact ⟨Or.inr (Or.inr (Or.inl rfl)), hne23.symm, hadj23⟩
    rw [h_filter_eq]
    simp [hne13]
  -- Case p = a3: neighbors are a2 and a4
  · have h_filter_eq : ({a1, a2, a3, a4} : Finset (Fin 18)).filter (fun q => q ≠ a3 ∧ G.Adj a3 q) = {a2, a4} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hx_mem, hx_ne, hx_adj⟩
        obtain hx1 | hx2 | hx3 | hx4 := hx_mem
        · subst hx1; exact (hnadj13 (G.adj_symm hx_adj)).elim
        · left; exact hx2
        · exact (hx_ne hx3).elim
        · right; exact hx4
      · intro hx
        obtain hx2 | hx4 := hx
        -- For a2: need a2 ≠ a3 (use hne23) and G.Adj a3 a2 (use G.adj_symm hadj23)
        · subst hx2; exact ⟨Or.inr (Or.inl rfl), hne23, G.adj_symm hadj23⟩
        -- For a4: need a4 ≠ a3 (use hne34.symm) and G.Adj a3 a4 (use hadj34)
        · subst hx4; exact ⟨Or.inr (Or.inr (Or.inr rfl)), hne34.symm, hadj34⟩
    rw [h_filter_eq]
    simp [hne24]
  -- Case p = a4: neighbors are a1 and a3
  · have h_filter_eq : ({a1, a2, a3, a4} : Finset (Fin 18)).filter (fun q => q ≠ a4 ∧ G.Adj a4 q) = {a1, a3} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hx_mem, hx_ne, hx_adj⟩
        obtain hx1 | hx2 | hx3 | hx4 := hx_mem
        · left; exact hx1
        · subst hx2; exact (hnadj24 (G.adj_symm hx_adj)).elim
        · right; exact hx3
        · exact (hx_ne hx4).elim
      · intro hx
        obtain hx1 | hx3 := hx
        -- For a1: need a1 ≠ a4 (use hne14) and G.Adj a4 a1 (use hadj41)
        · subst hx1; exact ⟨Or.inl rfl, hne14, hadj41⟩
        -- For a3: need a3 ≠ a4 (use hne34) and G.Adj a4 a3 (use G.adj_symm hadj34)
        · subst hx3; exact ⟨Or.inr (Or.inr (Or.inl rfl)), hne34, G.adj_symm hadj34⟩
    rw [h_filter_eq]
    simp [hne13]

/-! ### Helper lemmas for the 4-cycle structure -/

/- COMMENTED OUT: Needs Q.card = 8 hypothesis or more structure to prove.

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
  -- TODO: proof omitted (needs extra structure / hypotheses).

-/

/-- P and Q partition the non-neighbors of v (completeness).
Any non-neighbor x of v with commonNeighborsCard = 1 is in P, and with = 2 is in Q. -/
lemma PQ_partition_completeness {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (_h_tri : TriangleFree G) (_h_no6 : NoKIndepSet 6 G)
    (v : Fin 18)
    (P Q : Finset (Fin 18))
    (hP_card : P.card = 4) (hQ_card : Q.card = 8)
    (hP_props : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1)
    (hQ_props : ∀ q ∈ Q, ¬G.Adj v q ∧ commonNeighborsCard G v q = 2) :
    (∀ x, x ≠ v → ¬G.Adj v x → commonNeighborsCard G v x = 1 → x ∈ P) ∧
    (∀ x, x ≠ v → ¬G.Adj v x → commonNeighborsCard G v x = 2 → x ∈ Q) := by
  -- The proof uses a cardinality argument:
  -- M = non-neighbors of v (excluding v) has |M| = 12
  -- Every x ∈ M has commonNeighborsCard ∈ {1, 2}
  -- |P| = 4 vertices with commonNeighborsCard = 1
  -- |Q| = 8 vertices with commonNeighborsCard = 2
  -- Total: 4 + 8 = 12 = |M|, so P ∪ Q = M (by cardinality and disjointness)

  let N := G.neighborFinset v
  let M := Finset.univ \ insert v N
  have hN_card : N.card = 5 := h_reg v
  have hv_notin_N : v ∉ N := G.notMem_neighborFinset_self v

  have hM_card : M.card = 12 := by
    have h_univ : (Finset.univ : Finset (Fin 18)).card = 18 := Finset.card_fin 18
    have h_inter : insert v N ∩ Finset.univ = insert v N := Finset.inter_univ _
    rw [Finset.card_sdiff, h_inter, h_univ, Finset.card_insert_of_notMem hv_notin_N, hN_card]

  -- P ⊆ M
  have hP_sub_M : P ⊆ M := by
    intro p hp
    have ⟨hp_nonadj, _⟩ := hP_props p hp
    simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    constructor
    · -- p ≠ v
      intro h_eq
      -- After subst, p becomes v. Use h_reg p to get the degree.
      subst h_eq
      have hself : commonNeighborsCard G p p = (G.neighborFinset p).card := by
        unfold commonNeighborsCard _root_.commonNeighbors; rw [Finset.inter_self]
      have ⟨_, hcommon⟩ := hP_props p hp
      have hdeg : (G.neighborFinset p).card = 5 := h_reg p
      rw [hself, hdeg] at hcommon; omega
    · -- p ∉ N
      intro h_in_N
      rw [SimpleGraph.mem_neighborFinset] at h_in_N
      exact hp_nonadj h_in_N

  -- Q ⊆ M
  have hQ_sub_M : Q ⊆ M := by
    intro q hq
    have ⟨hq_nonadj, _⟩ := hQ_props q hq
    simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    constructor
    · intro h_eq; subst h_eq
      have hself : commonNeighborsCard G q q = (G.neighborFinset q).card := by
        unfold commonNeighborsCard _root_.commonNeighbors; rw [Finset.inter_self]
      have ⟨_, hcommon⟩ := hQ_props q hq
      have hdeg : (G.neighborFinset q).card = 5 := h_reg q
      rw [hself, hdeg] at hcommon; omega
    · intro h_in_N
      rw [SimpleGraph.mem_neighborFinset] at h_in_N
      exact hq_nonadj h_in_N

  -- P ∩ Q = ∅
  have hPQ_disj : Disjoint P Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨_, h1⟩ := hP_props a ha
    have ⟨_, h2⟩ := hQ_props a hb
    omega

  -- P ∪ Q ⊆ M with |P ∪ Q| = |P| + |Q| = 12 = |M|
  have hPQ_card : (P ∪ Q).card = 12 := by
    rw [Finset.card_union_of_disjoint hPQ_disj, hP_card, hQ_card]

  have hPQ_sub_M : P ∪ Q ⊆ M := Finset.union_subset hP_sub_M hQ_sub_M

  -- Therefore P ∪ Q = M
  have hPQ_eq_M : P ∪ Q = M := by
    apply Finset.eq_of_subset_of_card_le hPQ_sub_M
    rw [hPQ_card, hM_card]

  -- Now prove completeness
  constructor
  · -- commonNeighborsCard = 1 → in P
    intro x hx_ne_v hx_nonadj hx_common1
    -- x ∈ M
    have hx_in_M : x ∈ M := by
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
      constructor
      · exact hx_ne_v
      · intro h_in_N; rw [SimpleGraph.mem_neighborFinset] at h_in_N; exact hx_nonadj h_in_N
    -- x ∈ P ∪ Q
    have hx_in_PQ : x ∈ P ∪ Q := by rw [hPQ_eq_M]; exact hx_in_M
    -- x ∉ Q (since commonNeighborsCard ≠ 2)
    have hx_notin_Q : x ∉ Q := by
      intro h
      have ⟨_, h2⟩ := hQ_props x h
      omega
    -- Therefore x ∈ P
    rw [Finset.mem_union] at hx_in_PQ
    cases hx_in_PQ with
    | inl h => exact h
    | inr h => exact absurd h hx_notin_Q
  · -- commonNeighborsCard = 2 → in Q
    intro x hx_ne_v hx_nonadj hx_common2
    have hx_in_M : x ∈ M := by
      simp only [M, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
      constructor
      · exact hx_ne_v
      · intro h_in_N
        rw [SimpleGraph.mem_neighborFinset] at h_in_N
        exact hx_nonadj h_in_N
    have hx_in_PQ : x ∈ P ∪ Q := by rw [hPQ_eq_M]; exact hx_in_M
    have hx_notin_P : x ∉ P := by
      intro h
      have ⟨_, h1⟩ := hP_props x h
      omega
    rw [Finset.mem_union] at hx_in_PQ
    cases hx_in_PQ with
    | inl h => exact absurd h hx_notin_P
    | inr h => exact h

/-- The P from Claim 2 equals the P from any CariolaroSetup for the same vertex.
This follows from the uniqueness of the P set via PQ_partition_completeness. -/
lemma P_eq_setup_P {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    {h_reg : IsKRegular G 5} {h_tri : TriangleFree G} {h_no6 : NoKIndepSet 6 G}
    (setup : CariolaroSetup G h_reg h_tri h_no6)
    (P : Finset (Fin 18))
    (hP_card : P.card = 4)
    (hP_props : ∀ p ∈ P, ¬G.Adj setup.v p ∧ commonNeighborsCard G setup.v p = 1) :
    P = {setup.p1, setup.p2, setup.p3, setup.p4} := by
  -- Both P and {p1,p2,p3,p4} have cardinality 4 and satisfy the same property.
  -- By uniqueness from PQ_partition_completeness, they must be equal.
  let setup_P := ({setup.p1, setup.p2, setup.p3, setup.p4} : Finset (Fin 18))
  -- Card of setup_P = 4
  have hsetup_P_card : setup_P.card = 4 := by
    have h := setup.h_P_distinct
    show ({setup.p1, setup.p2, setup.p3, setup.p4} : Finset (Fin 18)).card = 4
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact h.2.2.2.2.2
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h.1, h.2.1, h.2.2.1⟩
  -- Setup P satisfies P-properties
  have hsetup_P_props : ∀ p ∈ setup_P, ¬G.Adj setup.v p ∧ commonNeighborsCard G setup.v p = 1 := by
    intro p hp
    simp only [setup_P, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨setup.h_p1_nonadj_v, setup.h_p1_common1⟩
    · exact ⟨setup.h_p2_nonadj_v, setup.h_p2_common1⟩
    · exact ⟨setup.h_p3_nonadj_v, setup.h_p3_common1⟩
    · exact ⟨setup.h_p4_nonadj_v, setup.h_p4_common1⟩
  -- Get Q from claim2
  obtain ⟨P', Q, hP'_card, hQ_card, hP'_props, hQ_props⟩ :=
    claim2_neighbor_structure h_reg h_tri h_no6 setup.v
  -- By PQ_partition_completeness, any p with commonNeighborsCard=1 is in P'
  have ⟨hP'_complete, _⟩ := PQ_partition_completeness h_reg h_tri h_no6 setup.v P' Q
      hP'_card hQ_card hP'_props hQ_props
  -- P ⊆ P'
  have hP_sub_P' : P ⊆ P' := by
    intro p hp
    have ⟨hp_nonadj, hp_common1⟩ := hP_props p hp
    have hp_ne_v : p ≠ setup.v := by
      intro h_eq
      subst h_eq
      have h5 : commonNeighborsCard G setup.v setup.v = 5 := by
        unfold commonNeighborsCard _root_.commonNeighbors
        rw [Finset.inter_self]
        exact h_reg setup.v
      rw [h5] at hp_common1
      norm_num at hp_common1
    exact hP'_complete p hp_ne_v hp_nonadj hp_common1
  -- setup_P ⊆ P'
  have hsetup_sub_P' : setup_P ⊆ P' := by
    intro p hp
    have ⟨hp_nonadj, hp_common1⟩ := hsetup_P_props p hp
    have hp_ne_v : p ≠ setup.v := by
      intro h_eq
      subst h_eq
      have h5 : commonNeighborsCard G setup.v setup.v = 5 := by
        unfold commonNeighborsCard _root_.commonNeighbors
        rw [Finset.inter_self]
        exact h_reg setup.v
      rw [h5] at hp_common1
      norm_num at hp_common1
    exact hP'_complete p hp_ne_v hp_nonadj hp_common1
  -- P' has card 4, P ⊆ P' with |P| = 4, so P = P'
  have hP_eq_P' : P = P' := Finset.eq_of_subset_of_card_le hP_sub_P' (by rw [hP_card, hP'_card])
  -- setup_P ⊆ P' with |setup_P| = 4, so setup_P = P'
  have hsetup_eq_P' : setup_P = P' := Finset.eq_of_subset_of_card_le hsetup_sub_P' (by rw [hsetup_P_card, hP'_card])
  -- Therefore P = setup_P
  rw [hP_eq_P', ← hsetup_eq_P']

/-- P is 2-regular: each p ∈ P has exactly 2 neighbors in P.
This is the key structural lemma that implies P is a 4-cycle.

**Proof Strategy (direct degree counting)**:
For any p ∈ P with degree 5:
- neighbors in {v} = 0 (p is non-neighbor of v, since p ∈ P)
- neighbors in N(v) = 1 (commonNeighborsCard = 1 by P definition)
- neighbors in Q = 2 (degree counting: 5 total, filling from disjoint sets)
- Therefore neighbors in P \ {p} = 5 - 0 - 1 - 2 = 2
-/
lemma P_is_two_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP_card : P.card = 4)
    (hP_props : ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = 2 := by
  classical
  -- New proof (Cariolaro structure): build S/T/W and derive 2-regularity.
  obtain ⟨_, Q, _, hQ_card, _, hQ_props⟩ := claim2_neighbor_structure h_reg h_tri h_no6 v

  have ⟨hP_complete, hQ_complete⟩ :=
    PQ_partition_completeness h_reg h_tri h_no6 v P Q hP_card hQ_card hP_props hQ_props

  let N : Finset (Fin 18) := G.neighborFinset v
  have hN_card : N.card = 5 := h_reg v
  have hNv_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v

  have hv_notin_Q : v ∉ Q := by
    intro hvQ
    have hv_common2 := (hQ_props v hvQ).2
    have hv_common5 : commonNeighborsCard G v v = 5 := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [Finset.inter_self]
      exact h_reg v
    omega

  -- Each p ∈ P has exactly one neighbor in N(v).
  have hP_N_card : ∀ p ∈ P, (N.filter (G.Adj p)).card = 1 := by
    intro p hp
    have hp_common1 := (hP_props p hp).2
    unfold commonNeighborsCard _root_.commonNeighbors at hp_common1
    have hEq : N.filter (G.Adj p) = N ∩ G.neighborFinset p := by
      ext x
      simp [N, Finset.mem_filter, Finset.mem_inter, mem_neighborFinset]
    simpa [hEq] using hp_common1

  -- For each s ∈ N(v), at most one P-vertex is adjacent to s (else 6-IS).
  have hN_P_le1 : ∀ s ∈ N, (P.filter (G.Adj s)).card ≤ 1 := by
    intro s hsN
    by_contra h_not_le
    have h_gt1 : 1 < (P.filter (G.Adj s)).card := Nat.lt_of_not_ge h_not_le
    have h_nonempty : (P.filter (G.Adj s)).Nonempty := by
      have : 0 < (P.filter (G.Adj s)).card := by omega
      simpa [Finset.card_pos] using this
    obtain ⟨p1, hp1⟩ := h_nonempty
    have hp1P : p1 ∈ P := (Finset.mem_filter.mp hp1).1
    have hs_adj_p1 : G.Adj s p1 := (Finset.mem_filter.mp hp1).2
    have h_erase_nonempty : ((P.filter (G.Adj s)).erase p1).Nonempty := by
      have h_ge2 : 2 ≤ (P.filter (G.Adj s)).card := Nat.succ_le_iff.2 h_gt1
      have h_card_erase : ((P.filter (G.Adj s)).erase p1).card =
          (P.filter (G.Adj s)).card - 1 := Finset.card_erase_of_mem hp1
      have : 0 < ((P.filter (G.Adj s)).erase p1).card := by
        rw [h_card_erase]
        omega
      simpa [Finset.card_pos] using this
    obtain ⟨p2, hp2⟩ := h_erase_nonempty
    have hp2_ne_p1 : p2 ≠ p1 := (Finset.mem_erase.mp hp2).1
    have hp2' : p2 ∈ P.filter (G.Adj s) := (Finset.mem_erase.mp hp2).2
    have hp2P : p2 ∈ P := (Finset.mem_filter.mp hp2').1
    have hs_adj_p2 : G.Adj s p2 := (Finset.mem_filter.mp hp2').2

    -- p1 and p2 are neighbors of s, hence non-adjacent.
    have hp1_nonadj_p2 : ¬G.Adj p1 p2 := by
      have hInd : G.IsIndepSet (G.neighborSet s) := neighborSet_indep_of_triangleFree h_tri s
      have hp1N : p1 ∈ G.neighborSet s := by rw [mem_neighborSet]; exact hs_adj_p1
      have hp2N : p2 ∈ G.neighborSet s := by rw [mem_neighborSet]; exact hs_adj_p2
      exact hInd hp1N hp2N hp2_ne_p1.symm

    -- The set I = {p1, p2} ∪ (N.erase s) is a 6-independent set.
    let I : Finset (Fin 18) := insert p1 (insert p2 (N.erase s))
    have hI_card : I.card = 6 := by
      have hNerase_card : (N.erase s).card = 4 := by
        rw [Finset.card_erase_of_mem hsN, hN_card]
      have hp1_notin_N : p1 ∉ N := by
        intro hp1N
        have hp1_nonadj_v := (hP_props p1 hp1P).1
        rw [mem_neighborFinset] at hp1N
        exact hp1_nonadj_v hp1N
      have hp2_notin_N : p2 ∉ N := by
        intro hp2N
        have hp2_nonadj_v := (hP_props p2 hp2P).1
        rw [mem_neighborFinset] at hp2N
        exact hp2_nonadj_v hp2N
      have hp2_notin_Nerase : p2 ∉ N.erase s := by
        simp [Finset.mem_erase, hp2_notin_N]
      have hp1_notin_step : p1 ∉ insert p2 (N.erase s) := by
        simp [Finset.mem_erase, hp1_notin_N, hp2_ne_p1.symm]
      have h_step : (insert p2 (N.erase s)).card = 5 := by
        rw [Finset.card_insert_of_notMem hp2_notin_Nerase, hNerase_card]
      simp [I, Finset.card_insert_of_notMem hp1_notin_step, h_step]

    have hI_indep : G.IsIndepSet I := by
      intro x hx y hy hxy
      have hx' : x = p1 ∨ x = p2 ∨ (x ∈ N ∧ x ≠ s) := by
        simpa [I] using hx
      have hy' : y = p1 ∨ y = p2 ∨ (y ∈ N ∧ y ≠ s) := by
        simpa [I] using hy
      rcases hx' with hx_p1 | hx'
      · subst x
        rcases hy' with hy_p1 | hy'
        · subst y
          exact False.elim (hxy rfl)
        · rcases hy' with hy_p2 | hyNs
          · subst y
            exact hp1_nonadj_p2
          · intro h_adj
            have hyN : y ∈ N := hyNs.1
            have hy_ne_s : y ≠ s := hyNs.2
            have hp1_nonadj := (hP_props p1 hp1P).1
            have hp1_common1 := (hP_props p1 hp1P).2
            obtain ⟨sp, hsp, hsp_unique⟩ := P_partner_in_N h_reg h_tri v p1 hp1_nonadj hp1_common1
            have hy_eq : y = sp := hsp_unique y ⟨hyN, G.symm h_adj⟩
            have hs_eq : s = sp := hsp_unique s ⟨hsN, hs_adj_p1⟩
            have : y = s := by simpa [hs_eq] using hy_eq
            exact hy_ne_s this
      · rcases hx' with hx_p2 | hxNerase
        · subst x
          rcases hy' with hy_p1 | hy'
          · subst y
            exact fun h => hp1_nonadj_p2 (G.symm h)
          · rcases hy' with hy_p2 | hyNs
            · subst y
              exact False.elim (hxy rfl)
            · intro h_adj
              have hyN : y ∈ N := hyNs.1
              have hy_ne_s : y ≠ s := hyNs.2
              have hp2_nonadj := (hP_props p2 hp2P).1
              have hp2_common1 := (hP_props p2 hp2P).2
              obtain ⟨sp, hsp, hsp_unique⟩ := P_partner_in_N h_reg h_tri v p2 hp2_nonadj hp2_common1
              have hy_eq : y = sp := hsp_unique y ⟨hyN, G.symm h_adj⟩
              have hs_eq : s = sp := hsp_unique s ⟨hsN, hs_adj_p2⟩
              have : y = s := by simpa [hs_eq] using hy_eq
              exact hy_ne_s this
        · have hxN : x ∈ N := hxNerase.1
          have hx_ne_s : x ≠ s := hxNerase.2
          rcases hy' with hy_p1 | hy'
          · subst y
            intro h_adj
            have hp1_nonadj := (hP_props p1 hp1P).1
            have hp1_common1 := (hP_props p1 hp1P).2
            obtain ⟨sp, hsp, hsp_unique⟩ := P_partner_in_N h_reg h_tri v p1 hp1_nonadj hp1_common1
            have hx_eq : x = sp := hsp_unique x ⟨hxN, h_adj⟩
            have hs_eq : s = sp := hsp_unique s ⟨hsN, hs_adj_p1⟩
            have : x = s := by simpa [hs_eq] using hx_eq
            exact hx_ne_s this
          · rcases hy' with hy_p2 | hyNs
            · subst y
              intro h_adj
              have hp2_nonadj := (hP_props p2 hp2P).1
              have hp2_common1 := (hP_props p2 hp2P).2
              obtain ⟨sp, hsp, hsp_unique⟩ := P_partner_in_N h_reg h_tri v p2 hp2_nonadj hp2_common1
              have hx_eq : x = sp := hsp_unique x ⟨hxN, h_adj⟩
              have hs_eq : s = sp := hsp_unique s ⟨hsN, hs_adj_p2⟩
              have : x = s := by simpa [hs_eq] using hx_eq
              exact hx_ne_s this
            · have hyN : y ∈ N := hyNs.1
              have hxS : x ∈ G.neighborSet v := by
                rw [mem_neighborSet, ← mem_neighborFinset]
                exact hxN
              have hyS : y ∈ G.neighborSet v := by
                rw [mem_neighborSet, ← mem_neighborFinset]
                exact hyN
              exact hNv_indep hxS hyS hxy

    have hI_nindep : G.IsNIndepSet 6 I := by
      rw [isNIndepSet_iff]
      exact ⟨hI_indep, hI_card⟩
    exact (h_no6 I hI_nindep).elim

  -- Total number of N–P edges is 4.
  have hNP_edges : ∑ s ∈ N, (P.filter (G.Adj s)).card = 4 := by
    have h_sym := bipartite_edge_count_symmetry P N G.Adj G.symm
    have h_left : ∑ p ∈ P, (N.filter (G.Adj p)).card = 4 := by
      calc
        ∑ p ∈ P, (N.filter (G.Adj p)).card
            = ∑ p ∈ P, 1 := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                exact hP_N_card p hp
          _ = P.card := by simp [Finset.sum_const]
          _ = 4 := by simp [hP_card]
    -- rewrite h_sym using h_left
    calc
      ∑ s ∈ N, (P.filter (G.Adj s)).card
          = ∑ p ∈ P, (N.filter (G.Adj p)).card := by simpa using h_sym.symm
      _ = 4 := h_left

  -- Choose t ∈ N with no P-neighbors.
  have ht_exists : ∃ t ∈ N, (P.filter (G.Adj t)).card = 0 := by
    by_contra h
    push_neg at h
    have h_all_one : ∀ t ∈ N, (P.filter (G.Adj t)).card = 1 := by
      intro t htN
      have ht_ne0 : (P.filter (G.Adj t)).card ≠ 0 := h t htN
      have ht_pos : 0 < (P.filter (G.Adj t)).card := Nat.pos_of_ne_zero ht_ne0
      have ht_le1 : (P.filter (G.Adj t)).card ≤ 1 := hN_P_le1 t htN
      omega
    have h_sum_eq : ∑ t ∈ N, (P.filter (G.Adj t)).card = 5 := by
      calc
        ∑ t ∈ N, (P.filter (G.Adj t)).card
            = ∑ t ∈ N, 1 := by
                refine Finset.sum_congr rfl ?_
                intro t htN
                exact h_all_one t htN
          _ = N.card := by simp [Finset.sum_const]
          _ = 5 := by simp [hN_card]
    have : (4 : ℕ) = 5 := by
      -- Compare with hNP_edges = 4
      exact hNP_edges.symm.trans h_sum_eq
    exact (by decide : (4 : ℕ) ≠ 5) this
  obtain ⟨t, ht_in_N, htP0⟩ := ht_exists
  have ht_adj_v : G.Adj v t := by
    rw [mem_neighborFinset] at ht_in_N
    exact ht_in_N

  have ht_nonadj_P : ∀ p ∈ P, ¬G.Adj t p := by
    intro p hp
    intro ht_adj_p
    have hmem : p ∈ P.filter (G.Adj t) := Finset.mem_filter.mpr ⟨hp, ht_adj_p⟩
    have hempty : P.filter (G.Adj t) = ∅ := Finset.card_eq_zero.mp htP0
    have hmem0 := hmem
    rw [hempty] at hmem0
    exact Finset.notMem_empty p hmem0

  let S : Finset (Fin 18) := N.erase t
  have hS_card : S.card = 4 := by
    have htN' : t ∈ N := by
      -- recover membership from ht_adj_v
      simpa [N, mem_neighborFinset] using ht_adj_v
    rw [Finset.card_erase_of_mem htN', hN_card]

  -- Define T (Q-neighbors of t) and W (the rest of Q).
  let T : Finset (Fin 18) := Q.filter (G.Adj t)
  let W : Finset (Fin 18) := Q.filter (fun q => ¬G.Adj t q)

  have hTW_disj : Disjoint T W := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

  have hTW_union : T ∪ W = Q := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hxQ
      by_cases hx : G.Adj t x
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hxQ, hx⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hxQ, hx⟩

  have hQ_complete_swap : ∀ x, ¬G.Adj v x → x ≠ v → commonNeighborsCard G v x = 2 → x ∈ Q := by
    intro x hx_nonadj hx_ne hx2
    exact hQ_complete x hx_ne hx_nonadj hx2

  have hPQ_partition :
      ∀ x, x ≠ v → ¬G.Adj v x →
        (commonNeighborsCard G v x = 1 → x ∈ P) ∧ (commonNeighborsCard G v x = 2 → x ∈ Q) := by
    intro x hx_ne hx_nonadj
    exact ⟨fun h1 => hP_complete x hx_ne hx_nonadj h1, fun h2 => hQ_complete x hx_ne hx_nonadj h2⟩

  have hT_card : T.card = 4 := by
    have : (Q.filter (G.Adj t)).card = 4 :=
      t_has_four_Q_neighbors h_reg h_tri h_no6 v t ht_adj_v Q hQ_card hv_notin_Q
        hQ_complete_swap P hP_card hP_props ht_nonadj_P hPQ_partition
    simpa [T] using this

  have hW_card : W.card = 4 := by
    have h_sum : T.card + W.card = Q.card := by
      rw [← hTW_union, Finset.card_union_of_disjoint hTW_disj]
    omega

  -- Finish the S/T/W argument and conclude 2-regularity of P.
  have hS_eq : S = (G.neighborFinset v).erase t := by
    simp [S, N]

  have hv_notin_P : v ∉ P := by
    intro hvP
    have hv_common1 := (hP_props v hvP).2
    have hv_common5 : commonNeighborsCard G v v = 5 := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [Finset.inter_self]
      exact h_reg v
    omega

  have hPQ_disj : Disjoint P Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    have h1 := (hP_props a ha).2
    have h2 := (hQ_props a hb).2
    omega

  have hS_adj_v : ∀ s ∈ S, G.Adj v s := by
    intro s hsS
    have hs_in_erase : s ∈ N.erase t := by simpa [S] using hsS
    have hsN : s ∈ N := (Finset.mem_erase.mp hs_in_erase).2
    simpa [N, mem_neighborFinset] using hsN

  have ht_ne_of_mem_S : ∀ s ∈ S, s ≠ t := by
    intro s hsS
    have hs_in_erase : s ∈ N.erase t := by simpa [S] using hsS
    exact (Finset.mem_erase.mp hs_in_erase).1

  -- Each p ∈ P has exactly one neighbor in S.
  have hP_S_card : ∀ p ∈ P, (S.filter (G.Adj p)).card = 1 := by
    intro p hp
    have ht_nonadj : ¬G.Adj p t := by
      intro hpt
      exact ht_nonadj_P p hp (G.symm hpt)
    have hEq : S.filter (G.Adj p) = N.filter (G.Adj p) := by
      ext x
      by_cases hx : x = t
      · subst hx
        simp [S, ht_nonadj]
      · simp [S, hx]
    simpa [hEq] using hP_N_card p hp

  have h_total_P_to_S : ∑ p ∈ P, (S.filter (G.Adj p)).card = S.card * 1 := by
    have h_sum : ∑ p ∈ P, (S.filter (G.Adj p)).card = 4 := by
      calc
        ∑ p ∈ P, (S.filter (G.Adj p)).card
            = ∑ p ∈ P, 1 := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                exact hP_S_card p hp
          _ = P.card := by simp [Finset.sum_const]
          _ = 4 := by simp [hP_card]
    simpa [hS_card] using h_sum

  -- Each s ∈ S has exactly one P-neighbor.
  have hS_P_card : ∀ s ∈ S, (P.filter (G.Adj s)).card = 1 := by
    have h_upper : ∀ s ∈ S, (P.filter (G.Adj s)).card ≤ 1 := by
      intro s hsS
      have hs_in_erase : s ∈ N.erase t := by simpa [S] using hsS
      have hsN : s ∈ N := (Finset.mem_erase.mp hs_in_erase).2
      exact hN_P_le1 s hsN
    exact degree_eq_from_bounds_and_bipartite_total G S P 1 h_upper h_total_P_to_S

  have hS_P_unique :
      ∀ s ∈ S, ∀ p1 ∈ P, ∀ p2 ∈ P, G.Adj s p1 → G.Adj s p2 → p1 = p2 := by
    intro s hsS p1 hp1P p2 hp2P hs1 hs2
    have hcard := hS_P_card s hsS
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hcard
    have hp1 : p1 ∈ P.filter (G.Adj s) := Finset.mem_filter.mpr ⟨hp1P, hs1⟩
    have hp2 : p2 ∈ P.filter (G.Adj s) := Finset.mem_filter.mpr ⟨hp2P, hs2⟩
    have hp1' : p1 = p := by
      have : p1 ∈ ({p} : Finset (Fin 18)) := by simpa [hp_eq] using hp1
      simpa using Finset.mem_singleton.mp this
    have hp2' : p2 = p := by
      have : p2 ∈ ({p} : Finset (Fin 18)) := by simpa [hp_eq] using hp2
      simpa using Finset.mem_singleton.mp this
    exact hp1'.trans hp2'.symm

  have hP_S_unique :
      ∀ p ∈ P, ∀ s1 ∈ S, ∀ s2 ∈ S, G.Adj s1 p → G.Adj s2 p → s1 = s2 := by
    intro p hpP s1 hs1S s2 hs2S hs1p hs2p
    have hcard := hP_S_card p hpP
    obtain ⟨s, hs_eq⟩ := Finset.card_eq_one.mp hcard
    have hs1 : s1 ∈ S.filter (G.Adj p) := Finset.mem_filter.mpr ⟨hs1S, G.symm hs1p⟩
    have hs2 : s2 ∈ S.filter (G.Adj p) := Finset.mem_filter.mpr ⟨hs2S, G.symm hs2p⟩
    have hs1' : s1 = s := by
      have : s1 ∈ ({s} : Finset (Fin 18)) := by simpa [hs_eq] using hs1
      simpa using Finset.mem_singleton.mp this
    have hs2' : s2 = s := by
      have : s2 ∈ ({s} : Finset (Fin 18)) := by simpa [hs_eq] using hs2
      simpa using Finset.mem_singleton.mp this
    exact hs1'.trans hs2'.symm

  -- Each w ∈ W has exactly 2 S-neighbors.
  have hW_S_card : ∀ w ∈ W, (S.filter (G.Adj w)).card = 2 := by
    intro w hwW
    have hwQ : w ∈ Q := (Finset.mem_filter.mp hwW).1
    have hw_nonadj_t : ¬G.Adj t w := (Finset.mem_filter.mp hwW).2
    have hw_common2 : commonNeighborsCard G v w = 2 := (hQ_props w hwQ).2
    exact W_vertex_has_two_S_neighbors h_tri v t w ht_adj_v hw_nonadj_t hw_common2 S hS_card hS_eq

  -- Each ti ∈ T has exactly 1 S-neighbor.
  have hT_S_card : ∀ ti ∈ T, (S.filter (G.Adj ti)).card = 1 := by
    intro ti htiT
    have htiQ : ti ∈ Q := (Finset.mem_filter.mp htiT).1
    have hti_adj_t : G.Adj t ti := (Finset.mem_filter.mp htiT).2
    have hti_common2 : commonNeighborsCard G v ti = 2 := (hQ_props ti htiQ).2
    exact T_vertex_has_one_S_neighbor h_reg h_tri v t ti ht_adj_v hti_adj_t hti_common2 S hS_card hS_eq

  have hST_total : ∑ s ∈ S, (T.filter (G.Adj s)).card = 4 := by
    have hT_sum : ∑ ti ∈ T, (S.filter (G.Adj ti)).card = 4 := by
      calc
        ∑ ti ∈ T, (S.filter (G.Adj ti)).card
            = ∑ ti ∈ T, 1 := by
                refine Finset.sum_congr rfl ?_
                intro ti hti
                exact hT_S_card ti hti
          _ = T.card := by simp [Finset.sum_const]
          _ = 4 := by simp [hT_card]
    calc
      ∑ s ∈ S, (T.filter (G.Adj s)).card
          = ∑ ti ∈ T, (S.filter (G.Adj ti)).card := by
              exact bipartite_edge_count_symmetry S T G.Adj G.symm
      _ = 4 := hT_sum

  -- Each s ∈ S has exactly 3 Q-neighbors (since s has degree 5, with neighbors v and its unique p ∈ P).
  have hS_Q_card : ∀ s ∈ S, (Q.filter (G.Adj s)).card = 3 := by
    intro s hsS
    have hs_adj_v : G.Adj v s := hS_adj_v s hsS
    have hv_mem : v ∈ G.neighborFinset s := by
      simpa [mem_neighborFinset] using (G.symm hs_adj_v)
    have hs_deg : (G.neighborFinset s).card = 5 := h_reg s
    have hNs_erase_card : ((G.neighborFinset s).erase v).card = 4 := by
      rw [Finset.card_erase_of_mem hv_mem, hs_deg]
    have hNs_erase_eq :
        (G.neighborFinset s).erase v = (P.filter (G.Adj s)) ∪ (Q.filter (G.Adj s)) := by
      ext x
      constructor
      · intro hx
        have hx_mem : x ∈ G.neighborFinset s := (Finset.mem_erase.mp hx).2
        have hx_ne_v : x ≠ v := (Finset.mem_erase.mp hx).1
        have hx_adj : G.Adj s x := by
          simpa [mem_neighborFinset] using hx_mem
        have hx_nonadj_v : ¬G.Adj v x := by
          intro hx_adj_v
          have hx_ne_s : x ≠ s := by
            intro h
            subst x
            exact G.loopless s hx_adj
          have h_ind := neighborSet_indep_of_triangleFree h_tri v
          exact h_ind hs_adj_v hx_adj_v hx_ne_s.symm hx_adj
        have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
        have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
        have h_common : commonNeighborsCard G v x = 1 ∨ commonNeighborsCard G v x = 2 := by omega
        cases h_common with
        | inl h1 =>
            have hxP : x ∈ P := hP_complete x hx_ne_v hx_nonadj_v h1
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxP, hx_adj⟩))
        | inr h2 =>
            have hxQ : x ∈ Q := hQ_complete x hx_ne_v hx_nonadj_v h2
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxQ, hx_adj⟩))
      · intro hx
        rcases Finset.mem_union.mp hx with hxP | hxQ
        · have hxP' : x ∈ P := (Finset.mem_filter.mp hxP).1
          have hx_ne_v : x ≠ v := by
            intro h
            subst h
            exact hv_notin_P hxP'
          exact Finset.mem_erase.mpr ⟨hx_ne_v, by
            simpa [mem_neighborFinset] using (Finset.mem_filter.mp hxP).2⟩
        · have hxQ' : x ∈ Q := (Finset.mem_filter.mp hxQ).1
          have hx_ne_v : x ≠ v := by
            intro h
            subst h
            exact hv_notin_Q hxQ'
          exact Finset.mem_erase.mpr ⟨hx_ne_v, by
            simpa [mem_neighborFinset] using (Finset.mem_filter.mp hxQ).2⟩
    have h_disj : Disjoint (P.filter (G.Adj s)) (Q.filter (G.Adj s)) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      have haP : a ∈ P := (Finset.mem_filter.mp ha).1
      have haQ : a ∈ Q := (Finset.mem_filter.mp hb).1
      exact Finset.disjoint_iff_ne.mp hPQ_disj a haP a haQ rfl
    have h_union_card :
        ((P.filter (G.Adj s)) ∪ (Q.filter (G.Adj s))).card =
          (P.filter (G.Adj s)).card + (Q.filter (G.Adj s)).card :=
      Finset.card_union_of_disjoint h_disj
    have hPdeg : (P.filter (G.Adj s)).card = 1 := hS_P_card s hsS
    have : (P.filter (G.Adj s)).card + (Q.filter (G.Adj s)).card = 4 := by
      have hcard_union : ((P.filter (G.Adj s)) ∪ (Q.filter (G.Adj s))).card = 4 := by
        simpa [hNs_erase_eq] using hNs_erase_card
      exact h_union_card.symm.trans hcard_union
    omega

  have hQ_split : ∀ s ∈ S,
      (Q.filter (G.Adj s)).card = (T.filter (G.Adj s)).card + (W.filter (G.Adj s)).card := by
    intro s hsS
    have h_split := neighbor_count_disjoint_union G s T W hTW_disj
    simpa [hTW_union] using h_split

  -- Helper: adjacency between P-neighbors of two S-vertices sharing a W-vertex.
  have adj_p_of_shared_w :
      ∀ {s1 s2 w p1 p2 : Fin 18},
        s1 ∈ S → s2 ∈ S → s1 ≠ s2 →
        w ∈ W → G.Adj s1 w → G.Adj s2 w →
        p1 ∈ P → p2 ∈ P →
        G.Adj s1 p1 → G.Adj s2 p2 →
        G.Adj p1 p2 := by
    intro s1 s2 w p1 p2 hs1 hs2 hs12 hwW hs1w hs2w hp1P hp2P hs1p1 hs2p2
    have hs1_adj_v : G.Adj v s1 := hS_adj_v s1 hs1
    have hs2_adj_v : G.Adj v s2 := hS_adj_v s2 hs2
    have hp1_nonadj_v : ¬G.Adj v p1 := (hP_props p1 hp1P).1
    have hp2_nonadj_v : ¬G.Adj v p2 := (hP_props p2 hp2P).1
    have hs1_nonadj_p2 : ¬G.Adj s1 p2 := by
      intro h
      have hp2_eq_p1 : p2 = p1 := hS_P_unique s1 hs1 p2 hp2P p1 hp1P h hs1p1
      have hs2p1 : G.Adj s2 p1 := by simpa [hp2_eq_p1] using hs2p2
      have hs2_eq_s1 : s2 = s1 := hP_S_unique p1 hp1P s2 hs2 s1 hs1 hs2p1 hs1p1
      exact hs12 hs2_eq_s1.symm
    have hs2_nonadj_p1 : ¬G.Adj s2 p1 := by
      intro h
      have hp1_eq_p2 : p1 = p2 := hS_P_unique s2 hs2 p1 hp1P p2 hp2P h hs2p2
      have hs1p2 : G.Adj s1 p2 := by simpa [hp1_eq_p2] using hs1p1
      have hs1_eq_s2 : s1 = s2 := hP_S_unique p2 hp2P s1 hs1 s2 hs2 hs1p2 hs2p2
      exact hs12 hs1_eq_s2
    have hw_nonadj_v : ¬G.Adj w v := by
      have hwQ : w ∈ Q := (Finset.mem_filter.mp hwW).1
      have hw_nonadj_v' : ¬G.Adj v w := (hQ_props w hwQ).1
      intro h
      exact hw_nonadj_v' (G.symm h)
    have hw_ne_p1 : w ≠ p1 := by
      intro hwp1
      have hwQ : w ∈ Q := (Finset.mem_filter.mp hwW).1
      have hp1Q : p1 ∈ Q := by simpa [hwp1] using hwQ
      exact (Finset.disjoint_iff_ne.mp hPQ_disj p1 hp1P p1 hp1Q rfl).elim
    have hw_ne_p2 : w ≠ p2 := by
      intro hwp2
      have hwQ : w ∈ Q := (Finset.mem_filter.mp hwW).1
      have hp2Q : p2 ∈ Q := by simpa [hwp2] using hwQ
      exact (Finset.disjoint_iff_ne.mp hPQ_disj p2 hp2P p2 hp2Q rfl).elim
    have hw_nonadj_p1 : ¬G.Adj w p1 := by
      have hInd := neighborSet_indep_of_triangleFree h_tri s1
      have hw_mem : w ∈ G.neighborSet s1 := by rw [mem_neighborSet]; exact hs1w
      have hp_mem : p1 ∈ G.neighborSet s1 := by rw [mem_neighborSet]; exact hs1p1
      exact hInd hw_mem hp_mem hw_ne_p1
    have hw_nonadj_p2 : ¬G.Adj w p2 := by
      have hInd := neighborSet_indep_of_triangleFree h_tri s2
      have hw_mem : w ∈ G.neighborSet s2 := by rw [mem_neighborSet]; exact hs2w
      have hp_mem : p2 ∈ G.neighborSet s2 := by rw [mem_neighborSet]; exact hs2p2
      exact hInd hw_mem hp_mem hw_ne_p2
    have hs1_s2_nonadj : ¬G.Adj s1 s2 :=
      neighborSet_indep_of_triangleFree h_tri v hs1_adj_v hs2_adj_v hs12
    have ht_ne_s1 : t ≠ s1 := (ht_ne_of_mem_S s1 hs1).symm
    have ht_ne_s2 : t ≠ s2 := (ht_ne_of_mem_S s2 hs2).symm
    have ht_nonadj_p1 : ¬G.Adj t p1 := ht_nonadj_P p1 hp1P
    have ht_nonadj_p2 : ¬G.Adj t p2 := ht_nonadj_P p2 hp2P
    have ht_nonadj_w : ¬G.Adj t w := (Finset.mem_filter.mp hwW).2
    -- pick the remaining two S-vertices as witnesses s3,s4
    have hS1_card : (S.erase s1).card = 3 := by
      simp [Finset.card_erase_of_mem hs1, hS_card]
    have hs2_in_erase1 : s2 ∈ S.erase s1 := by
      exact Finset.mem_erase.mpr ⟨hs12.symm, hs2⟩
    have hS2_card : ((S.erase s1).erase s2).card = 2 := by
      simp [Finset.card_erase_of_mem hs2_in_erase1, hS1_card]
    obtain ⟨s3, s4, hs34, hS24_eq⟩ := Finset.card_eq_two.mp hS2_card
    have hs3_in : s3 ∈ (S.erase s1).erase s2 := by
      rw [hS24_eq]
      simp
    have hs4_in : s4 ∈ (S.erase s1).erase s2 := by
      rw [hS24_eq]
      simp
    have hs3_in_S : s3 ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hs3_in).2).2
    have hs4_in_S : s4 ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hs4_in).2).2
    have hs3_ne_s1 : s3 ≠ s1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hs3_in).2).1
    have hs3_ne_s2 : s3 ≠ s2 := (Finset.mem_erase.mp hs3_in).1
    have hs4_ne_s1 : s4 ≠ s1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hs4_in).2).1
    have hs4_ne_s2 : s4 ≠ s2 := (Finset.mem_erase.mp hs4_in).1
    have hs3_adj_v : G.Adj v s3 := hS_adj_v s3 hs3_in_S
    have hs4_adj_v : G.Adj v s4 := hS_adj_v s4 hs4_in_S
    have ht_ne_s3 : t ≠ s3 := (ht_ne_of_mem_S s3 hs3_in_S).symm
    have ht_ne_s4 : t ≠ s4 := (ht_ne_of_mem_S s4 hs4_in_S).symm
    have hs3_ne_s4 : s3 ≠ s4 := hs34
    -- s3,s4 are not adjacent to p1 or p2 (unique N-neighbors)
    have hs3_nonadj_p1 : ¬G.Adj s3 p1 := by
      intro h
      have hs1p1' : G.Adj s1 p1 := hs1p1
      have hs3N : s3 ∈ N := by
        have hs3_in_erase : s3 ∈ N.erase t := by simpa [S] using hs3_in_S
        exact (Finset.mem_erase.mp hs3_in_erase).2
      have hs1N : s1 ∈ N := by
        have hs1_in_erase : s1 ∈ N.erase t := by simpa [S] using hs1
        exact (Finset.mem_erase.mp hs1_in_erase).2
      have := hP_N_card p1 hp1P
      -- (N.filter (Adj p1)) has card 1, contains s1 and s3 -> contradiction
      have hs1_mem : s1 ∈ N.filter (G.Adj p1) := Finset.mem_filter.mpr ⟨hs1N, G.symm hs1p1'⟩
      have hs3_mem : s3 ∈ N.filter (G.Adj p1) := Finset.mem_filter.mpr ⟨hs3N, G.symm h⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp this
      have : s3 = s1 := by
        have hs1z : s1 = z := by
          have : s1 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs1_mem
          simpa using Finset.mem_singleton.mp this
        have hs3z : s3 = z := by
          have : s3 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs3_mem
          simpa using Finset.mem_singleton.mp this
        exact hs3z.trans hs1z.symm
      exact hs3_ne_s1 this
    have hs3_nonadj_p2 : ¬G.Adj s3 p2 := by
      intro h
      have hs2N : s2 ∈ N := by
        have hs2_in_erase : s2 ∈ N.erase t := by simpa [S] using hs2
        exact (Finset.mem_erase.mp hs2_in_erase).2
      have hs3N : s3 ∈ N := by
        have hs3_in_erase : s3 ∈ N.erase t := by simpa [S] using hs3_in_S
        exact (Finset.mem_erase.mp hs3_in_erase).2
      have := hP_N_card p2 hp2P
      have hs2_mem : s2 ∈ N.filter (G.Adj p2) := Finset.mem_filter.mpr ⟨hs2N, G.symm hs2p2⟩
      have hs3_mem : s3 ∈ N.filter (G.Adj p2) := Finset.mem_filter.mpr ⟨hs3N, G.symm h⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp this
      have : s3 = s2 := by
        have hs2z : s2 = z := by
          have : s2 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs2_mem
          simpa using Finset.mem_singleton.mp this
        have hs3z : s3 = z := by
          have : s3 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs3_mem
          simpa using Finset.mem_singleton.mp this
        exact hs3z.trans hs2z.symm
      exact hs3_ne_s2 this
    have hs4_nonadj_p1 : ¬G.Adj s4 p1 := by
      intro h
      have hs1N : s1 ∈ N := by
        have hs1_in_erase : s1 ∈ N.erase t := by simpa [S] using hs1
        exact (Finset.mem_erase.mp hs1_in_erase).2
      have hs4N : s4 ∈ N := by
        have hs4_in_erase : s4 ∈ N.erase t := by simpa [S] using hs4_in_S
        exact (Finset.mem_erase.mp hs4_in_erase).2
      have := hP_N_card p1 hp1P
      have hs1_mem : s1 ∈ N.filter (G.Adj p1) := Finset.mem_filter.mpr ⟨hs1N, G.symm hs1p1⟩
      have hs4_mem : s4 ∈ N.filter (G.Adj p1) := Finset.mem_filter.mpr ⟨hs4N, G.symm h⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp this
      have : s4 = s1 := by
        have hs1z : s1 = z := by
          have : s1 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs1_mem
          simpa using Finset.mem_singleton.mp this
        have hs4z : s4 = z := by
          have : s4 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs4_mem
          simpa using Finset.mem_singleton.mp this
        exact hs4z.trans hs1z.symm
      exact hs4_ne_s1 this
    have hs4_nonadj_p2 : ¬G.Adj s4 p2 := by
      intro h
      have hs2N : s2 ∈ N := by
        have hs2_in_erase : s2 ∈ N.erase t := by simpa [S] using hs2
        exact (Finset.mem_erase.mp hs2_in_erase).2
      have hs4N : s4 ∈ N := by
        have hs4_in_erase : s4 ∈ N.erase t := by simpa [S] using hs4_in_S
        exact (Finset.mem_erase.mp hs4_in_erase).2
      have := hP_N_card p2 hp2P
      have hs2_mem : s2 ∈ N.filter (G.Adj p2) := Finset.mem_filter.mpr ⟨hs2N, G.symm hs2p2⟩
      have hs4_mem : s4 ∈ N.filter (G.Adj p2) := Finset.mem_filter.mpr ⟨hs4N, G.symm h⟩
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp this
      have : s4 = s2 := by
        have hs2z : s2 = z := by
          have : s2 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs2_mem
          simpa using Finset.mem_singleton.mp this
        have hs4z : s4 = z := by
          have : s4 ∈ ({z} : Finset (Fin 18)) := by simpa [hz] using hs4_mem
          simpa using Finset.mem_singleton.mp this
        exact hs4z.trans hs2z.symm
      exact hs4_ne_s2 this
    -- s3,s4 are not adjacent to w (since w has exactly two S-neighbors: s1 and s2)
    have hs3_nonadj_w : ¬G.Adj s3 w := by
      intro h
      have hcard := hW_S_card w hwW
      have hs1_mem : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1, G.symm hs1w⟩
      have hs2_mem : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2, G.symm hs2w⟩
      have hs3_mem : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm h⟩
      have hsub : ({s1, s2, s3} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hs1_mem
        · exact hs2_mem
        · exact hs3_mem
      have h3 : ({s1, s2, s3} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hs3_ne_s2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hs12, hs3_ne_s1.symm⟩
      have : (S.filter (G.Adj w)).card ≥ 3 := by
        have hle := Finset.card_le_card hsub
        omega
      omega
    have hs4_nonadj_w : ¬G.Adj s4 w := by
      intro h
      have hcard := hW_S_card w hwW
      have hs1_mem : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1, G.symm hs1w⟩
      have hs2_mem : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2, G.symm hs2w⟩
      have hs4_mem : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm h⟩
      have hsub : ({s1, s2, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hs1_mem
        · exact hs2_mem
        · exact hs4_mem
      have h3 : ({s1, s2, s4} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hs4_ne_s2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hs12, hs4_ne_s1.symm⟩
      have : (S.filter (G.Adj w)).card ≥ 3 := by
        have hle := Finset.card_le_card hsub
        omega
      omega
    -- apply the main lemma
    exact p_adjacent_of_shared_w h_tri h_no6 v
      p1 p2 s1 s2 w
      hp1_nonadj_v hp2_nonadj_v (by
        intro hp12
        have hs2p1 : G.Adj s2 p1 := by simpa [hp12.symm] using hs2p2
        have hs2_eq_s1 : s2 = s1 := hP_S_unique p1 hp1P s2 hs2 s1 hs1 hs2p1 hs1p1
        exact hs12 hs2_eq_s1.symm)
      hs1_adj_v hs2_adj_v hs12
      hs1p1 hs2p2
      hs1_nonadj_p2 hs2_nonadj_p1
      (G.symm hs1w) (G.symm hs2w)
      hw_nonadj_v hw_nonadj_p1 hw_nonadj_p2
      hs1_s2_nonadj
      t s3 s4
      ht_adj_v hs3_adj_v hs4_adj_v
      ht_ne_s1 ht_ne_s2 hs3_ne_s1 hs3_ne_s2 hs4_ne_s1 hs4_ne_s2
      ht_ne_s3 ht_ne_s4 hs3_ne_s4
      ht_nonadj_p1 ht_nonadj_p2 ht_nonadj_w
      hs3_nonadj_p1 hs3_nonadj_p2 hs3_nonadj_w
      hs4_nonadj_p1 hs4_nonadj_p2 hs4_nonadj_w

  -- Each s ∈ S has at least one T-neighbor (else it would have three W-neighbors, forcing a triangle in P).
  have hS_T_ne0 : ∀ s ∈ S, (T.filter (G.Adj s)).card ≠ 0 := by
    intro s hsS hT0
    have hW_three : (W.filter (G.Adj s)).card = 3 := by
      have hQdeg := hS_Q_card s hsS
      have hQsplit := hQ_split s hsS
      omega
    obtain ⟨w1, w2, w3, hw12, hw13, hw23, hW_eq⟩ := Finset.card_eq_three.mp hW_three
    have hw1_in : w1 ∈ W.filter (G.Adj s) := by rw [hW_eq]; simp
    have hw2_in : w2 ∈ W.filter (G.Adj s) := by rw [hW_eq]; simp
    have hw3_in : w3 ∈ W.filter (G.Adj s) := by rw [hW_eq]; simp
    simp only [Finset.mem_filter] at hw1_in hw2_in hw3_in
    have hw1W : w1 ∈ W := hw1_in.1
    have hw2W : w2 ∈ W := hw2_in.1
    have hw3W : w3 ∈ W := hw3_in.1
    have hs_w1 : G.Adj s w1 := hw1_in.2
    have hs_w2 : G.Adj s w2 := hw2_in.2
    have hs_w3 : G.Adj s w3 := hw3_in.2
    -- choose p_s (unique P-neighbor of s)
    have hPs_card : (P.filter (G.Adj s)).card = 1 := hS_P_card s hsS
    obtain ⟨ps, hps_eq⟩ := Finset.card_eq_one.mp hPs_card
    have hps_mem : ps ∈ P.filter (G.Adj s) := by rw [hps_eq]; simp
    have hpsP : ps ∈ P := (Finset.mem_filter.mp hps_mem).1
    have hs_ps : G.Adj s ps := (Finset.mem_filter.mp hps_mem).2
    -- For each wi, pick its other S-neighbor oi and the corresponding P-neighbor pi.
    have h_other_of_w :
        ∀ wi ∈ ({w1, w2, w3} : Finset (Fin 18)), wi ∈ W → G.Adj s wi →
          ∃ oi ∈ S, oi ≠ s ∧ G.Adj oi wi ∧ ∃ pi ∈ P, G.Adj oi pi := by
      intro wi hwi_in hwiW hs_wi
      have hwi_S_card : (S.filter (G.Adj wi)).card = 2 := hW_S_card wi hwiW
      have hs_in_wi : s ∈ S.filter (G.Adj wi) := by
        simp only [Finset.mem_filter]; exact ⟨hsS, G.symm hs_wi⟩
      have hwi_other : ((S.filter (G.Adj wi)).erase s).card = 1 := by
        rw [Finset.card_erase_of_mem hs_in_wi, hwi_S_card]
      obtain ⟨oi, hoi_eq⟩ := Finset.card_eq_one.mp hwi_other
      have hoi_mem : oi ∈ (S.filter (G.Adj wi)).erase s := by
        rw [hoi_eq]; exact Finset.mem_singleton_self oi
      have hoi_ne_s : oi ≠ s := (Finset.mem_erase.mp hoi_mem).1
      have hoi_in_filter : oi ∈ S.filter (G.Adj wi) := (Finset.mem_erase.mp hoi_mem).2
      have hoiS : oi ∈ S := (Finset.mem_filter.mp hoi_in_filter).1
      have hoi_adj_wi : G.Adj oi wi := by
        have : G.Adj wi oi := (Finset.mem_filter.mp hoi_in_filter).2
        exact G.symm this
      have hPi_card : (P.filter (G.Adj oi)).card = 1 := hS_P_card oi hoiS
      obtain ⟨pi, hpi_eq⟩ := Finset.card_eq_one.mp hPi_card
      have hpi_mem : pi ∈ P.filter (G.Adj oi) := by rw [hpi_eq]; simp
      have hpiP : pi ∈ P := (Finset.mem_filter.mp hpi_mem).1
      have hoi_pi : G.Adj oi pi := (Finset.mem_filter.mp hpi_mem).2
      exact ⟨oi, hoiS, hoi_ne_s, hoi_adj_wi, pi, hpiP, hoi_pi⟩
    -- Get o1,o2,o3 and p1,p2,p3
    obtain ⟨o1, ho1S, ho1_ne, ho1_adj_w1, p1, hp1P, ho1_p1⟩ :=
      h_other_of_w w1 (by simp) hw1W hs_w1
    obtain ⟨o2, ho2S, ho2_ne, ho2_adj_w2, p2, hp2P, ho2_p2⟩ :=
      h_other_of_w w2 (by simp) hw2W hs_w2
    obtain ⟨o3, ho3S, ho3_ne, ho3_adj_w3, p3, hp3P, ho3_p3⟩ :=
      h_other_of_w w3 (by simp) hw3W hs_w3
    -- o's are distinct, else s and oi share two W-neighbors.
    have hs_adj_v : G.Adj v s := hS_adj_v s hsS
    have ho1_adj_v : G.Adj v o1 := hS_adj_v o1 ho1S
    have ho2_adj_v : G.Adj v o2 := hS_adj_v o2 ho2S
    have ho3_adj_v : G.Adj v o3 := hS_adj_v o3 ho3S
    have hv_ne_w1 : v ≠ w1 := by
      intro h; subst h
      exact hv_notin_Q ((Finset.mem_filter.mp hw1W).1)
    have hv_ne_w2 : v ≠ w2 := by
      intro h; subst h
      exact hv_notin_Q ((Finset.mem_filter.mp hw2W).1)
    have hv_ne_w3 : v ≠ w3 := by
      intro h; subst h
      exact hv_notin_Q ((Finset.mem_filter.mp hw3W).1)
    have ho12 : o1 ≠ o2 := by
      intro h
      have ho1_adj_w2 : G.Adj o1 w2 := by simpa [h] using ho2_adj_w2
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s o1 w1 w2
        hs_adj_v ho1_adj_v ho1_ne.symm hv_ne_w1 hv_ne_w2 hw12
        hs_w1 hs_w2 ho1_adj_w1 ho1_adj_w2
    have ho13 : o1 ≠ o3 := by
      intro h
      have ho1_adj_w3 : G.Adj o1 w3 := by simpa [h] using ho3_adj_w3
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s o1 w1 w3
        hs_adj_v ho1_adj_v ho1_ne.symm hv_ne_w1 hv_ne_w3 hw13
        hs_w1 hs_w3 ho1_adj_w1 ho1_adj_w3
    have ho23 : o2 ≠ o3 := by
      intro h
      have ho2_adj_w3 : G.Adj o2 w3 := by simpa [h] using ho3_adj_w3
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s o2 w2 w3
        hs_adj_v ho2_adj_v ho2_ne.symm hv_ne_w2 hv_ne_w3 hw23
        hs_w2 hs_w3 ho2_adj_w2 ho2_adj_w3
    -- The remaining w4 ∈ W connects two of {o1,o2,o3}
    have hW_rest_card : (((W.erase w1).erase w2).erase w3).card = 1 := by
      have h1 : (W.erase w1).card = 3 := by simp [hw1W, hW_card]
      have hw2_in1 : w2 ∈ W.erase w1 := Finset.mem_erase.mpr ⟨hw12.symm, hw2W⟩
      have h2 : ((W.erase w1).erase w2).card = 2 := by
        simpa [h1] using (Finset.card_erase_of_mem hw2_in1)
      have hw3_in1 : w3 ∈ W.erase w1 := Finset.mem_erase.mpr ⟨hw13.symm, hw3W⟩
      have hw3_in2 : w3 ∈ (W.erase w1).erase w2 := Finset.mem_erase.mpr ⟨hw23.symm, hw3_in1⟩
      simpa [h2] using (Finset.card_erase_of_mem hw3_in2)
    obtain ⟨w4, hw4_eq⟩ := Finset.card_eq_one.mp hW_rest_card
    have hw4_mem : w4 ∈ ((W.erase w1).erase w2).erase w3 := by
      rw [hw4_eq]; exact Finset.mem_singleton_self w4
    have hw4_ne_w3 : w4 ≠ w3 := (Finset.mem_erase.mp hw4_mem).1
    have hw4_in12 : w4 ∈ (W.erase w1).erase w2 := (Finset.mem_erase.mp hw4_mem).2
    have hw4_ne_w2 : w4 ≠ w2 := (Finset.mem_erase.mp hw4_in12).1
    have hw4_in1 : w4 ∈ W.erase w1 := (Finset.mem_erase.mp hw4_in12).2
    have hw4_ne_w1 : w4 ≠ w1 := (Finset.mem_erase.mp hw4_in1).1
    have hw4W : w4 ∈ W := (Finset.mem_erase.mp hw4_in1).2
    have hs_not_adj_w4 : ¬G.Adj s w4 := by
      intro h
      have : w4 ∈ W.filter (G.Adj s) := Finset.mem_filter.mpr ⟨hw4W, h⟩
      have : w4 ∈ ({w1, w2, w3} : Finset (Fin 18)) := by
        simpa [hW_eq] using this
      -- w4 is distinct from w1,w2,w3 by construction
      simp [Finset.mem_insert, Finset.mem_singleton, hw4_ne_w1, hw4_ne_w2, hw4_ne_w3] at this
    have hw4_S_card : (S.filter (G.Adj w4)).card = 2 := hW_S_card w4 hw4W
    obtain ⟨u1, u2, hu12, hu_eq⟩ := Finset.card_eq_two.mp hw4_S_card
    have hu1_mem : u1 ∈ S.filter (G.Adj w4) := by rw [hu_eq]; simp
    have hu2_mem : u2 ∈ S.filter (G.Adj w4) := by rw [hu_eq]; simp
    have hu1S : u1 ∈ S := (Finset.mem_filter.mp hu1_mem).1
    have hu2S : u2 ∈ S := (Finset.mem_filter.mp hu2_mem).1
    have hu1_adj_w4 : G.Adj u1 w4 := by
      have : G.Adj w4 u1 := (Finset.mem_filter.mp hu1_mem).2
      exact G.symm this
    have hu2_adj_w4 : G.Adj u2 w4 := by
      have : G.Adj w4 u2 := (Finset.mem_filter.mp hu2_mem).2
      exact G.symm this
    have hu1_ne_s : u1 ≠ s := by
      intro h
      subst h
      exact hs_not_adj_w4 hu1_adj_w4
    have hu2_ne_s : u2 ≠ s := by
      intro h
      subst h
      exact hs_not_adj_w4 hu2_adj_w4
    -- u1,u2 are among {o1,o2,o3}
    have hS_erase_card : (S.erase s).card = 3 := by
      simp [Finset.card_erase_of_mem hsS, hS_card]
    have hO_card : ({o1, o2, o3} : Finset (Fin 18)).card = 3 := by
      simp [ho12, ho13, ho23]
    have hO_sub : ({o1, o2, o3} : Finset (Fin 18)) ⊆ S.erase s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_erase.mpr ⟨ho1_ne, ho1S⟩
      · exact Finset.mem_erase.mpr ⟨ho2_ne, ho2S⟩
      · exact Finset.mem_erase.mpr ⟨ho3_ne, ho3S⟩
    have hO_eq : ({o1, o2, o3} : Finset (Fin 18)) = S.erase s :=
      Finset.eq_of_subset_of_card_le hO_sub (by simp [hS_erase_card, hO_card])
    have hu1_in_O : u1 ∈ ({o1, o2, o3} : Finset (Fin 18)) := by
      have : u1 ∈ S.erase s := Finset.mem_erase.mpr ⟨hu1_ne_s, hu1S⟩
      simpa [hO_eq] using this
    have hu2_in_O : u2 ∈ ({o1, o2, o3} : Finset (Fin 18)) := by
      have : u2 ∈ S.erase s := Finset.mem_erase.mpr ⟨hu2_ne_s, hu2S⟩
      simpa [hO_eq] using this
    -- Choose P-neighbors of u1,u2
    have hu1P_card : (P.filter (G.Adj u1)).card = 1 := hS_P_card u1 hu1S
    have hu2P_card : (P.filter (G.Adj u2)).card = 1 := hS_P_card u2 hu2S
    obtain ⟨pu1, hpu1_eq⟩ := Finset.card_eq_one.mp hu1P_card
    obtain ⟨pu2, hpu2_eq⟩ := Finset.card_eq_one.mp hu2P_card
    have hpu1_mem : pu1 ∈ P.filter (G.Adj u1) := by rw [hpu1_eq]; simp
    have hpu2_mem : pu2 ∈ P.filter (G.Adj u2) := by rw [hpu2_eq]; simp
    have hpu1P : pu1 ∈ P := (Finset.mem_filter.mp hpu1_mem).1
    have hpu2P : pu2 ∈ P := (Finset.mem_filter.mp hpu2_mem).1
    have hu1_pu1 : G.Adj u1 pu1 := (Finset.mem_filter.mp hpu1_mem).2
    have hu2_pu2 : G.Adj u2 pu2 := (Finset.mem_filter.mp hpu2_mem).2
    have h_pu1_pu2 : G.Adj pu1 pu2 :=
      adj_p_of_shared_w hu1S hu2S hu12 hw4W hu1_adj_w4 hu2_adj_w4 hpu1P hpu2P hu1_pu1 hu2_pu2
    -- p_s is adjacent to pu1 and pu2 (since u1,u2 are among o1,o2,o3, each sharing a W with s)
    have h_ps_pu1 : G.Adj ps pu1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_in_O
      rcases hu1_in_O with rfl | rfl | rfl
      · exact adj_p_of_shared_w hsS ho1S ho1_ne.symm hw1W hs_w1 ho1_adj_w1 hpsP hpu1P hs_ps hu1_pu1
      · exact adj_p_of_shared_w hsS ho2S ho2_ne.symm hw2W hs_w2 ho2_adj_w2 hpsP hpu1P hs_ps hu1_pu1
      · exact adj_p_of_shared_w hsS ho3S ho3_ne.symm hw3W hs_w3 ho3_adj_w3 hpsP hpu1P hs_ps hu1_pu1
    have h_ps_pu2 : G.Adj ps pu2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu2_in_O
      rcases hu2_in_O with rfl | rfl | rfl
      · exact adj_p_of_shared_w hsS ho1S ho1_ne.symm hw1W hs_w1 ho1_adj_w1 hpsP hpu2P hs_ps hu2_pu2
      · exact adj_p_of_shared_w hsS ho2S ho2_ne.symm hw2W hs_w2 ho2_adj_w2 hpsP hpu2P hs_ps hu2_pu2
      · exact adj_p_of_shared_w hsS ho3S ho3_ne.symm hw3W hs_w3 ho3_adj_w3 hpsP hpu2P hs_ps hu2_pu2
    have hInd := neighborSet_indep_of_triangleFree h_tri ps
    have hpu1_in : pu1 ∈ G.neighborSet ps := by rw [mem_neighborSet]; exact h_ps_pu1
    have hpu2_in : pu2 ∈ G.neighborSet ps := by rw [mem_neighborSet]; exact h_ps_pu2
    have : ¬G.Adj pu1 pu2 := hInd hpu1_in hpu2_in (by
      intro h
      subst h
      have := hP_S_unique pu1 hpu1P u1 hu1S u2 hu2S hu1_pu1 hu2_pu2
      exact hu12 this)
    exact this h_pu1_pu2

  -- Each s ∈ S has exactly 1 T-neighbor and 2 W-neighbors.
  have hS_T_card : ∀ s ∈ S, (T.filter (G.Adj s)).card = 1 := by
    obtain ⟨s1, s2, s3, s4, h12, h13, h14, h23, h24, h34, hS_eq_four⟩ :=
      Finset.card_eq_four.mp hS_card
    have hs1 : s1 ∈ S := by rw [hS_eq_four]; simp
    have hs2 : s2 ∈ S := by rw [hS_eq_four]; simp
    have hs3 : s3 ∈ S := by rw [hS_eq_four]; simp
    have hs4 : s4 ∈ S := by rw [hS_eq_four]; simp
    have hs1_pos : 1 ≤ (T.filter (G.Adj s1)).card := Nat.pos_of_ne_zero (hS_T_ne0 s1 hs1)
    have hs2_pos : 1 ≤ (T.filter (G.Adj s2)).card := Nat.pos_of_ne_zero (hS_T_ne0 s2 hs2)
    have hs3_pos : 1 ≤ (T.filter (G.Adj s3)).card := Nat.pos_of_ne_zero (hS_T_ne0 s3 hs3)
    have hs4_pos : 1 ≤ (T.filter (G.Adj s4)).card := Nat.pos_of_ne_zero (hS_T_ne0 s4 hs4)
    have hST_total' : ∑ s ∈ ({s1, s2, s3, s4} : Finset (Fin 18)), (T.filter (G.Adj s)).card = 4 := by
      simpa [hS_eq_four] using hST_total
    have hsum_four :
        (T.filter (G.Adj s1)).card + (T.filter (G.Adj s2)).card +
          (T.filter (G.Adj s3)).card + (T.filter (G.Adj s4)).card = 4 := by
      calc
        (T.filter (G.Adj s1)).card + (T.filter (G.Adj s2)).card +
            (T.filter (G.Adj s3)).card + (T.filter (G.Adj s4)).card
          = ∑ s ∈ ({s1, s2, s3, s4} : Finset (Fin 18)), (T.filter (G.Adj s)).card := by
              simpa using
                (sum_over_four s1 s2 s3 s4 h12 h13 h14 h23 h24 h34
                    (fun s => (T.filter (G.Adj s)).card)).symm
        _ = 4 := hST_total'
    have hs1_eq : (T.filter (G.Adj s1)).card = 1 := by omega
    have hs2_eq : (T.filter (G.Adj s2)).card = 1 := by omega
    have hs3_eq : (T.filter (G.Adj s3)).card = 1 := by omega
    have hs4_eq : (T.filter (G.Adj s4)).card = 1 := by omega
    intro s hsS
    have hs_in : s ∈ ({s1, s2, s3, s4} : Finset (Fin 18)) := by
      rw [← hS_eq_four]
      exact hsS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs_in
    rcases hs_in with rfl | rfl | rfl | rfl
    · exact hs1_eq
    · exact hs2_eq
    · exact hs3_eq
    · exact hs4_eq

  have hS_W_card : ∀ s ∈ S, (W.filter (G.Adj s)).card = 2 := by
    intro s hsS
    have hQdeg : (Q.filter (G.Adj s)).card = 3 := hS_Q_card s hsS
    have hQsplit := hQ_split s hsS
    have hTdeg : (T.filter (G.Adj s)).card = 1 := hS_T_card s hsS
    omega

  -- Each p ∈ P has at least two neighbors in P, via the two W-neighbors of its S-partner.
  have hP_deg_ge2 : ∀ p ∈ P, 2 ≤ (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card := by
    intro p hpP
    have hp_nonadj_v := (hP_props p hpP).1
    have hp_common1 := (hP_props p hpP).2
    obtain ⟨sp, ⟨hsp_in_N, hsp_adj_p⟩, hsp_unique⟩ :=
      P_partner_in_N h_reg h_tri v p hp_nonadj_v hp_common1
    have hsp_ne_t : sp ≠ t := by
      intro h
      subst h
      exact ht_nonadj_P p hpP hsp_adj_p
    have hsp_in_S : sp ∈ S := by
      have hspN : sp ∈ N := by simpa [N] using hsp_in_N
      have : sp ∈ N.erase t := Finset.mem_erase.mpr ⟨hsp_ne_t, hspN⟩
      simpa [S] using this
    have hsp_W : (W.filter (G.Adj sp)).card = 2 := hS_W_card sp hsp_in_S
    obtain ⟨wa, wb, hwab, hWab_eq⟩ := Finset.card_eq_two.mp hsp_W
    have hwa_in : wa ∈ W.filter (G.Adj sp) := by rw [hWab_eq]; simp
    have hwb_in : wb ∈ W.filter (G.Adj sp) := by rw [hWab_eq]; simp
    have hwaW : wa ∈ W := (Finset.mem_filter.mp hwa_in).1
    have hwbW : wb ∈ W := (Finset.mem_filter.mp hwb_in).1
    have hsp_wa : G.Adj sp wa := (Finset.mem_filter.mp hwa_in).2
    have hsp_wb : G.Adj sp wb := (Finset.mem_filter.mp hwb_in).2
    -- other S-neighbors oa, ob of wa, wb
    have hwa_S_card : (S.filter (G.Adj wa)).card = 2 := hW_S_card wa hwaW
    have hwb_S_card : (S.filter (G.Adj wb)).card = 2 := hW_S_card wb hwbW
    have hsp_in_wa : sp ∈ S.filter (G.Adj wa) := by
      simp only [Finset.mem_filter]; exact ⟨hsp_in_S, G.symm hsp_wa⟩
    have hsp_in_wb : sp ∈ S.filter (G.Adj wb) := by
      simp only [Finset.mem_filter]; exact ⟨hsp_in_S, G.symm hsp_wb⟩
    have hwa_other : ((S.filter (G.Adj wa)).erase sp).card = 1 := by
      rw [Finset.card_erase_of_mem hsp_in_wa, hwa_S_card]
    have hwb_other : ((S.filter (G.Adj wb)).erase sp).card = 1 := by
      rw [Finset.card_erase_of_mem hsp_in_wb, hwb_S_card]
    obtain ⟨oa, hoa_eq⟩ := Finset.card_eq_one.mp hwa_other
    obtain ⟨ob, hob_eq⟩ := Finset.card_eq_one.mp hwb_other
    have hoa_mem : oa ∈ (S.filter (G.Adj wa)).erase sp := by rw [hoa_eq]; simp
    have hob_mem : ob ∈ (S.filter (G.Adj wb)).erase sp := by rw [hob_eq]; simp
    have hoa_ne : oa ≠ sp := (Finset.mem_erase.mp hoa_mem).1
    have hob_ne : ob ≠ sp := (Finset.mem_erase.mp hob_mem).1
    have hoa_in_filter : oa ∈ S.filter (G.Adj wa) := (Finset.mem_erase.mp hoa_mem).2
    have hob_in_filter : ob ∈ S.filter (G.Adj wb) := (Finset.mem_erase.mp hob_mem).2
    have hoaS : oa ∈ S := (Finset.mem_filter.mp hoa_in_filter).1
    have hobS : ob ∈ S := (Finset.mem_filter.mp hob_in_filter).1
    have hoa_adj_wa : G.Adj oa wa := by
      have : G.Adj wa oa := (Finset.mem_filter.mp hoa_in_filter).2
      exact G.symm this
    have hob_adj_wb : G.Adj ob wb := by
      have : G.Adj wb ob := (Finset.mem_filter.mp hob_in_filter).2
      exact G.symm this
    have hoa_ne_ob : oa ≠ ob := by
      intro h
      have hsp_adj_v : G.Adj v sp := hS_adj_v sp hsp_in_S
      have hoa_adj_v : G.Adj v oa := hS_adj_v oa hoaS
      have hv_ne_wa : v ≠ wa := by
        intro h; subst h; exact hv_notin_Q ((Finset.mem_filter.mp hwaW).1)
      have hv_ne_wb : v ≠ wb := by
        intro h; subst h; exact hv_notin_Q ((Finset.mem_filter.mp hwbW).1)
      have hoa_adj_wb : G.Adj oa wb := by simpa [h.symm] using hob_adj_wb
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v sp oa wa wb
        hsp_adj_v hoa_adj_v hoa_ne.symm hv_ne_wa hv_ne_wb hwab
        hsp_wa hsp_wb hoa_adj_wa hoa_adj_wb
    -- corresponding P-neighbors pa,pb
    have hPa_card : (P.filter (G.Adj oa)).card = 1 := hS_P_card oa hoaS
    have hPb_card : (P.filter (G.Adj ob)).card = 1 := hS_P_card ob hobS
    obtain ⟨pa, hpa_eq⟩ := Finset.card_eq_one.mp hPa_card
    obtain ⟨pb, hpb_eq⟩ := Finset.card_eq_one.mp hPb_card
    have hpa_mem : pa ∈ P.filter (G.Adj oa) := by rw [hpa_eq]; simp
    have hpb_mem : pb ∈ P.filter (G.Adj ob) := by rw [hpb_eq]; simp
    have hpaP : pa ∈ P := (Finset.mem_filter.mp hpa_mem).1
    have hpbP : pb ∈ P := (Finset.mem_filter.mp hpb_mem).1
    have hoa_pa : G.Adj oa pa := (Finset.mem_filter.mp hpa_mem).2
    have hob_pb : G.Adj ob pb := (Finset.mem_filter.mp hpb_mem).2
    have h_p_pa : G.Adj p pa :=
      adj_p_of_shared_w hsp_in_S hoaS hoa_ne.symm hwaW hsp_wa hoa_adj_wa hpP hpaP hsp_adj_p hoa_pa
    have h_p_pb : G.Adj p pb :=
      adj_p_of_shared_w hsp_in_S hobS hob_ne.symm hwbW hsp_wb hob_adj_wb hpP hpbP hsp_adj_p hob_pb
    have hpa_ne_p : pa ≠ p := by
      intro hpa
      have hoa_p : G.Adj oa p := by simpa [hpa] using hoa_pa
      have hsp_eq_oa : sp = oa := hP_S_unique p hpP sp hsp_in_S oa hoaS hsp_adj_p hoa_p
      exact hoa_ne hsp_eq_oa.symm
    have hpb_ne_p : pb ≠ p := by
      intro hpb
      have hob_p : G.Adj ob p := by simpa [hpb] using hob_pb
      have hsp_eq_ob : sp = ob := hP_S_unique p hpP sp hsp_in_S ob hobS hsp_adj_p hob_p
      exact hob_ne hsp_eq_ob.symm
    have hpa_ne_pb : pa ≠ pb := by
      intro hpa_pb
      have hoa_pb : G.Adj oa pb := by simpa [hpa_pb] using hoa_pa
      have hoa_eq_ob : oa = ob := hP_S_unique pb hpbP oa hoaS ob hobS hoa_pb hob_pb
      exact hoa_ne_ob hoa_eq_ob
    -- {pa,pb} ⊆ neighbors of p in P
    have hsub : ({pa, pb} : Finset (Fin 18)) ⊆ P.filter (fun q => q ≠ p ∧ G.Adj p q) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hpaP, ⟨hpa_ne_p, h_p_pa⟩⟩
      · exact Finset.mem_filter.mpr ⟨hpbP, ⟨hpb_ne_p, h_p_pb⟩⟩
    have hcard_two : ({pa, pb} : Finset (Fin 18)).card = 2 := by simp [hpa_ne_pb]
    have hle := Finset.card_le_card hsub
    omega

  -- A vertex in a triangle-free graph cannot have 3 P-neighbors if all P-vertices have ≥2 P-neighbors.
  have hP_deg_ne3 : ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card ≠ 3 := by
    intro p hpP hdeg3
    obtain ⟨q1, q2, q3, hq12, hq13, hq23, hEq⟩ := Finset.card_eq_three.mp hdeg3
    have hq1_mem : q1 ∈ P.filter (fun q => q ≠ p ∧ G.Adj p q) := by rw [hEq]; simp
    have hq2_mem : q2 ∈ P.filter (fun q => q ≠ p ∧ G.Adj p q) := by rw [hEq]; simp
    have hq3_mem : q3 ∈ P.filter (fun q => q ≠ p ∧ G.Adj p q) := by rw [hEq]; simp
    have hq1P : q1 ∈ P := (Finset.mem_filter.mp hq1_mem).1
    have hq2P : q2 ∈ P := (Finset.mem_filter.mp hq2_mem).1
    have hq3P : q3 ∈ P := (Finset.mem_filter.mp hq3_mem).1
    have hpq1 : G.Adj p q1 := (Finset.mem_filter.mp hq1_mem).2.2
    have hpq2 : G.Adj p q2 := (Finset.mem_filter.mp hq2_mem).2.2
    have hpq3 : G.Adj p q3 := (Finset.mem_filter.mp hq3_mem).2.2
    have hInd := neighborSet_indep_of_triangleFree h_tri p
    have hq1q2 : ¬G.Adj q1 q2 := hInd hpq1 hpq2 hq12
    have hq1q3 : ¬G.Adj q1 q3 := hInd hpq1 hpq3 hq13
    have hq2q3 : ¬G.Adj q2 q3 := hInd hpq2 hpq3 hq23
    have hq1_deg_le1 : (P.filter (fun r => r ≠ q1 ∧ G.Adj q1 r)).card ≤ 1 := by
      have hsub : P.filter (fun r => r ≠ q1 ∧ G.Adj q1 r) ⊆ {p} := by
        intro r hr
        have hrP : r ∈ P := (Finset.mem_filter.mp hr).1
        by_cases hr_eq_p : r = p
        · subst hr_eq_p
          simp
        · have hr_ne_p : r ≠ p := hr_eq_p
          have hr_ne_q1 : r ≠ q1 := (Finset.mem_filter.mp hr).2.1
          -- r is one of q2 or q3
          have : r = q2 ∨ r = q3 := by
            have hP_eq : P = {p, q1, q2, q3} := by
              have hsub' : ({p, q1, q2, q3} : Finset (Fin 18)) ⊆ P := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact hpP
                · exact hq1P
                · exact hq2P
                · exact hq3P
              have hcard' : ({p, q1, q2, q3} : Finset (Fin 18)).card = 4 := by
                have hq1_ne_p : q1 ≠ p := (Finset.mem_filter.mp hq1_mem).2.1
                have hq2_ne_p : q2 ≠ p := (Finset.mem_filter.mp hq2_mem).2.1
                have hq3_ne_p : q3 ≠ p := (Finset.mem_filter.mp hq3_mem).2.1
                have hq2_notin : q2 ∉ ({q3} : Finset (Fin 18)) := by simp [hq23]
                have hq1_notin : q1 ∉ insert q2 ({q3} : Finset (Fin 18)) := by
                  simp [hq12, hq13]
                have hp_notin : p ∉ insert q1 (insert q2 ({q3} : Finset (Fin 18))) := by
                  simp [hq1_ne_p.symm, hq2_ne_p.symm, hq3_ne_p.symm]
                rw [Finset.card_insert_of_notMem hp_notin,
                    Finset.card_insert_of_notMem hq1_notin,
                    Finset.card_insert_of_notMem hq2_notin,
                    Finset.card_singleton]
              exact (Finset.eq_of_subset_of_card_le hsub' (by simp [hcard', hP_card])).symm
            have hr_in : r ∈ ({p, q1, q2, q3} : Finset (Fin 18)) := by
              rw [← hP_eq]; exact hrP
            simp only [Finset.mem_insert, Finset.mem_singleton] at hr_in
            rcases hr_in with rfl | rfl | rfl | rfl
            · exact (hr_ne_p rfl).elim
            · exact (hr_ne_q1 rfl).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
          have hr_adj : G.Adj q1 r := (Finset.mem_filter.mp hr).2.2
          cases this with
          | inl hr_eq =>
              subst hr_eq
              exact (hq1q2 hr_adj).elim
          | inr hr_eq =>
              subst hr_eq
              exact (hq1q3 hr_adj).elim
      have hcard : ({p} : Finset (Fin 18)).card = 1 := by simp
      have := Finset.card_le_card hsub
      omega
    have hq1_deg_ge2 : 2 ≤ (P.filter (fun r => r ≠ q1 ∧ G.Adj q1 r)).card := hP_deg_ge2 q1 hq1P
    omega

  -- Final: degrees are exactly 2.
  intro p hpP
  have hge : 2 ≤ (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card := hP_deg_ge2 p hpP
  have hle3 : (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card ≤ 3 := by
    have hsub : P.filter (fun q => q ≠ p ∧ G.Adj p q) ⊆ P.erase p := by
      intro x hx
      have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
      have hx_ne : x ≠ p := (Finset.mem_filter.mp hx).2.1
      exact Finset.mem_erase.mpr ⟨hx_ne, hxP⟩
    have hle := Finset.card_le_card hsub
    have hErase : (P.erase p).card = 3 := by
      simp [Finset.card_erase_of_mem hpP, hP_card]
    omega
  have hne3 : (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card ≠ 3 := hP_deg_ne3 p hpP
  have hlt3 : (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card < 3 := Nat.lt_of_le_of_ne hle3 hne3
  have hle : (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card ≤ 2 := Nat.lt_succ_iff.mp (by
    simpa [Nat.succ_eq_add_one] using hlt3)
  exact Nat.le_antisymm hle hge

  /-
  -- Get Q from claim2
  obtain ⟨P', Q, hP'_card, hQ_card, hP'_props, hQ_props⟩ :=
    claim2_neighbor_structure h_reg h_tri h_no6 v
  -- P' = P since both satisfy the same defining property
  have hPP'_eq : P = P' := by
    -- Both are the unique 4-element set with commonNeighborsCard = 1
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      have ⟨hp_nonadj, hp_common1⟩ := hP_props p hp
      -- P' contains all non-neighbors of v with commonNeighborsCard = 1
      -- This follows from completeness
      have ⟨hP'_complete, _⟩ := PQ_partition_completeness h_reg h_tri h_no6 v P' Q
          hP'_card hQ_card hP'_props hQ_props
      have hp_ne_v : p ≠ v := by
        intro h_eq; subst h_eq
        have h5 : commonNeighborsCard G p p = 5 := by
          unfold commonNeighborsCard _root_.commonNeighbors
          rw [Finset.inter_self]
          exact h_reg p
        omega
      exact hP'_complete p hp_ne_v hp_nonadj hp_common1
    · simp [hP_card, hP'_card]

  -- Get partition completeness
  have ⟨hP_complete, hQ_complete⟩ := PQ_partition_completeness h_reg h_tri h_no6 v P Q
      hP_card hQ_card (by rw [hPP'_eq]; exact hP'_props) hQ_props

  -- Disjointness facts
  have hP_Nv_disj : Disjoint P (G.neighborFinset v) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨h_nonadj, _⟩ := hP_props a ha
    rw [mem_neighborFinset] at hb
    exact h_nonadj hb

  have hP_Q_disj : Disjoint P Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨_, h_common1⟩ := hP_props a ha
    have ⟨_, h_common2⟩ := hQ_props a hb
    omega

  have hNv_Q_disj : Disjoint (G.neighborFinset v) Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨h_nonadj, _⟩ := hQ_props a hb
    rw [mem_neighborFinset] at ha
    exact h_nonadj ha

  intro p hp
  have ⟨hp_nonadj_v, hp_common1⟩ := hP_props p hp
  have hp_deg : (G.neighborFinset p).card = 5 := h_reg p

  -- p ≠ v
  have hp_ne_v : p ≠ v := by
    intro h_eq; subst h_eq
    have h5 : commonNeighborsCard G p p = 5 := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [Finset.inter_self]
      exact h_reg p
    omega

  -- p ∉ N(v)
  have hp_notin_Nv : p ∉ G.neighborFinset v := by
    intro h; rw [mem_neighborFinset] at h; exact hp_nonadj_v h

  -- p ∉ Q
  have hp_notin_Q : p ∉ Q := by
    intro h
    have ⟨_, h_common2⟩ := hQ_props p h
    omega

  -- Define neighbor subsets for p
  let NP := (P.erase p).filter (G.Adj p)  -- P-neighbors of p (excluding p)
  let NN := (G.neighborFinset v).filter (G.Adj p)  -- N(v)-neighbors of p
  let NQ := Q.filter (G.Adj p)  -- Q-neighbors of p

  -- The three sets are pairwise disjoint
  have hNP_NN_disj : Disjoint NP NN := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact Finset.disjoint_of_subset_left (erase_subset _ _) hP_Nv_disj

  have hNP_NQ_disj : Disjoint NP NQ := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact Finset.disjoint_of_subset_left (erase_subset _ _) hP_Q_disj

  have hNN_NQ_disj : Disjoint NN NQ := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact hNv_Q_disj

  -- All neighbors of p are in NP ∪ NN ∪ NQ
  have h_nbrs_subset : G.neighborFinset p ⊆ NP ∪ NN ∪ NQ := by
    intro x hx
    rw [mem_neighborFinset] at hx
    by_cases hxv : x = v
    · subst hxv; exfalso; exact hp_nonadj_v (G.symm hx)
    by_cases hx_Nv : G.Adj v x
    · rw [mem_union, mem_union]; left; right
      simp only [NN, mem_filter, mem_neighborFinset]
      exact ⟨hx_Nv, hx⟩
    · have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hxv hx_Nv
      have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hxv hx_Nv
      have hx_ne_p : x ≠ p := fun h => G.loopless p (h ▸ hx)
      cases Nat.lt_or_eq_of_le h_le with
      | inl h_lt =>
        have hx_common1 : commonNeighborsCard G v x = 1 := by omega
        rw [mem_union, mem_union]; left; left
        simp only [NP, mem_filter, mem_erase]
        have hx_in_P : x ∈ P := hP_complete x hxv hx_Nv hx_common1
        exact ⟨⟨hx_ne_p, hx_in_P⟩, hx⟩
      | inr h_eq =>
        rw [mem_union, mem_union]; right
        simp only [NQ, mem_filter]
        have hx_in_Q : x ∈ Q := hQ_complete x hxv hx_Nv h_eq
        exact ⟨hx_in_Q, hx⟩

  -- NP ∪ NN ∪ NQ ⊆ G.neighborFinset p
  have h_subset_nbrs : NP ∪ NN ∪ NQ ⊆ G.neighborFinset p := by
    intro x hx
    rw [mem_union, mem_union] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨hx_NP | hx_NN⟩ | hx_NQ
    · simp only [NP, mem_filter] at hx_NP; exact hx_NP.2
    · simp only [NN, mem_filter] at hx_NN; exact hx_NN.2
    · simp only [NQ, mem_filter] at hx_NQ; exact hx_NQ.2

  have h_union_eq : NP ∪ NN ∪ NQ = G.neighborFinset p :=
    Finset.Subset.antisymm h_subset_nbrs h_nbrs_subset

  -- NN has exactly 1 element (p's unique N(v)-neighbor)
  -- This follows from commonNeighborsCard = 1
  have hNN_card : NN.card = 1 := by
    -- commonNeighborsCard G v p = |N(v) ∩ N(p)| = 1
    have h := hp_common1
    unfold commonNeighborsCard _root_.commonNeighbors at h
    -- NN = N(v) ∩ {neighbors of p} = filter by adjacency
    -- Need: NN = N(v) ∩ N(p)
    have hNN_eq : NN = G.neighborFinset v ∩ G.neighborFinset p := by
      ext x
      simp only [NN, mem_filter, mem_inter, mem_neighborFinset, G.adj_comm]
    rw [hNN_eq, h]

  -- Cardinality equation: |NP| + |NN| + |NQ| = 5
  have h_card_sum : NP.card + NN.card + NQ.card = 5 := by
    rw [← hp_deg, ← h_union_eq]
    rw [card_union_of_disjoint]
    · rw [card_union_of_disjoint hNP_NN_disj]
    · exact Finset.disjoint_union_left.mpr ⟨hNP_NQ_disj, hNN_NQ_disj⟩

  -- Each p ∈ P has exactly 2 Q-neighbors by degree counting
  -- We need to show NQ.card = 2 given the constraints
  -- This requires showing that NP.card = 2 (what we want to prove!)
  -- and NN.card = 1 (proved above)
  --
  -- Actually, we can prove NQ.card = 2 independently:
  -- NQ.card ≤ 2 because Q-neighbors share 2 common neighbors with v
  -- and must avoid triangles...
  --
  -- Better approach: prove NQ.card ≤ 2 using triangle-free property
  -- and NQ.card ≥ 2 using independent set constraint

  -- Alternative: use that p has exactly 2 Q-neighbors
  -- Proof: p has degree 5. Of these:
  -- - 0 go to v (p ∉ N(v))
  -- - 1 goes to N(v) (commonNeighborsCard = 1)
  -- - At most 3 can go to P (since |P| = 4 and p ∈ P, |P\{p}| = 3)
  -- But if all 3 went to P, then p has 3 P-neighbors.
  -- Then N(v) ∪ {v, p} = 7 vertices, p's neighbors are 1 in N(v), 3 in P.
  -- That leaves only 5 - 1 - 3 = 1 neighbor outside N(v) ∪ P ∪ {v}.
  -- But |Q| = 8 and all Q-vertices are non-neighbors of v.
  -- Actually, p must have ≥ 1 Q-neighbor by the pigeonhole.
  -- With |NP| + 1 + |NQ| = 5 and |NP| ≤ 3, we get |NQ| ≥ 1.
  --
  -- For the upper bound on NP: if |NP| = 3, then P is K₄ minus one vertex.
  -- But P has only 4 vertices and 2-regularity would give 4 edges.
  -- K₄ minus one edge has 5 edges. So |NP| ≤ 2 for some vertex.
  --
  -- Actually, let's use handshaking: sum of degrees in P = 2 * (edges in P).
  -- If every vertex has degree ≥ 3 in P, then sum ≥ 12, so edges ≥ 6.
  -- But K₄ has only 6 edges. So at most K₄.
  -- If K₄, then p1 has P-degree 3, N(v)-degree 1, so only 1 Q-neighbor.
  -- But then Q's 8 vertices must connect to P's 4 vertices with limited edges.
  --
  -- This is getting complex. Let me use a different approach:
  -- Sum the P-degrees over all p ∈ P. This equals 2 * (edges in induced P).
  -- With |P| = 4, max edges = 6 (K₄). If 2-regular, edges = 4.
  --
  -- Alternative proof: use induction/averaging.
  -- If any p has |NP| > 2, show contradiction.
  -- If any p has |NP| < 2, show contradiction.
  -- Therefore |NP| = 2 for all p.

  -- Key insight: |NQ| = 2 for all p ∈ P.
  -- Proof: Every q ∈ Q has commonNeighborsCard = 2, meaning q shares 2 N(v)-neighbors with v.
  -- If p is adjacent to q, then p is a common neighbor of q and v? No, p ∉ N(v).
  -- Actually, commonNeighborsCard counts |N(v) ∩ N(q)|.
  --
  -- Better: use the sum. Each q ∈ Q has 2 N(v)-neighbors.
  -- Total edges between Q and N(v) = 2 * |Q| = 16.
  -- |N(v)| = 5. By pigeonhole, average N(v)-vertex has 16/5 Q-neighbors.
  --
  -- Each p ∈ P has exactly 1 N(v)-neighbor (its s-partner).
  -- Total edges between P and N(v) = 1 * |P| = 4.
  -- |N(v)| = 5. One s ∈ N(v) has no P-partner (that's t).
  --
  -- For Q-neighbors of p: p has degree 5, with 1 in N(v), and the rest in P ∪ Q.
  -- If |NP| = k, then |NQ| = 4 - k.
  -- Sum over p ∈ P: Σ|NP| = 2 * (edges in P).
  -- Sum over p ∈ P: Σ|NQ| = 4 * 4 - 2 * (edges in P) = 16 - 2 * (edges in P).
  --
  -- Each q ∈ Q has some number of P-neighbors. Sum over q ∈ Q: Σ|P-neighbors of q|.
  -- By double counting: Σ_p |NQ| = Σ_q |P-neighbors of q|.
  --
  -- This is still complex. Let me try the direct approach:
  -- Prove NQ.card = 2 using degree constraints and commonNeighborsCard properties.

  -- Actually, let's use that |NQ| = 5 - |NP| - 1 = 4 - |NP|.
  -- We need |NP| = 2, i.e., |NQ| = 2.
  --
  -- Constraint 1: |NP| ≤ 3 (since |P \ {p}| = 3)
  -- Constraint 2: |NQ| ≤ some bound from triangle-free
  -- Constraint 3: |NP| + |NQ| = 4

  -- Let me prove |NP| = 2 by showing |NP| ≥ 2 and |NP| ≤ 2.
  --
  -- |NP| ≤ 2: If |NP| = 3, then p is adjacent to all other vertices in P.
  --   Then |NQ| = 1. So p has only 1 Q-neighbor.
  --   Consider the total edges from P to Q: Σ_p |NQ|.
  --   If one p has |NQ| = 1, other p's must compensate.
  --   But each p has |NP| + |NQ| = 4, so if one has |NP| = 3, |NQ| = 1,
  --   the sum Σ|NQ| ≤ 1 + 3*4 = 13? No, each p has |NP| ≤ 3.
  --   Actually Σ|NQ| = 4*4 - Σ|NP| = 16 - 2*(edges in P).
  --   Max edges in P = 6 (K₄), so min Σ|NQ| = 16 - 12 = 4.
  --   If P = K₄, each p has |NQ| = 1.
  --   But this contradicts... what?
  --
  -- Let me try to find the right constraint.
  -- Key fact: N(v) is an independent set (triangle-free with v).
  -- So edges between N(v) and the rest of the graph.
  -- Each s ∈ N(v) has degree 5, with 1 edge to v.
  -- So 4 edges from each s to non-N(v)-{v} vertices.
  -- Total: 5 * 4 = 20 edges from N(v) to (P ∪ Q).
  --
  -- Each p ∈ P has exactly 1 N(v)-neighbor (commonNeighborsCard = 1).
  -- Each q ∈ Q has exactly 2 N(v)-neighbors (commonNeighborsCard = 2).
  -- Total edges from N(v) to P = 4 * 1 = 4.
  -- Total edges from N(v) to Q = 8 * 2 = 16.
  -- Total = 20. ✓
  --
  -- Now, each s ∈ N(v) has 4 neighbors in P ∪ Q.
  -- By pigeonhole, at least one s has ≥ 1 P-neighbor.
  -- Actually, 4 P-vertices each have 1 N(v)-neighbor.
  -- So 4 edges from P to N(v), distributed among 5 s's.
  -- One s has no P-neighbor (call it t), the other 4 s's each have 1 P-neighbor.
  --
  -- Each si (i=1,2,3,4) has exactly 1 P-neighbor (its pi).
  -- Each si has 4 edges to P ∪ Q, with 1 to P and 3 to Q.
  -- Total from {s1,s2,s3,s4} to Q: 4 * 3 = 12.
  -- t has 4 edges to P ∪ Q, all to Q (since t has no P-neighbor).
  -- Total from N(v) to Q: 12 + 4 = 16. ✓
  --
  -- Now for P-edges: Each pi is adjacent to its si.
  -- The key constraint is triangle-free: if pi-si and pj-si, then pi-pj would
  -- need to be non-adjacent (else triangle {pi, pj, si}).
  -- But each si has exactly 1 P-neighbor, so no two p's share an s.
  --
  -- Back to proving |NP| = 2:
  -- We need a counting argument using the structure.
  --
  -- Alternative: Use the fact that P is 2-regular implies C₄.
  -- The lemma two_regular_four_vertices_is_cycle proves this!
  -- We just need to prove 2-regularity.
  --
  -- Let me use a sum argument:
  -- Σ_p∈P |NP| = 2 * (edges in induced P).
  -- Each p has |NP| + 1 + |NQ| = 5, so |NP| = 4 - |NQ|.
  -- Σ|NP| = 16 - Σ|NQ|.
  -- So edges in P = (16 - Σ|NQ|) / 2 = 8 - Σ|NQ|/2.
  --
  -- We need Σ|NQ| = 8, which gives edges = 4, average |NP| = 2.
  -- If Σ|NQ| = 8 and each |NQ| ≥ 0, average = 2.
  -- But we need each |NQ| = 2, not just average.
  --
  -- Key insight: Every q ∈ Q has at most 2 P-neighbors.
  -- Proof: If q has 3 P-neighbors, say {p1,p2,p3}, and q has 2 N(v)-neighbors,
  -- then q has degree ≥ 5, with neighbors in N(v) ∪ P.
  -- But q might have degree exactly 5, so this is possible.
  --
  -- Let's count edges from Q to P:
  -- Σ_p |NQ| = Σ_q |P-neighbors of q|.
  -- Each q has at most 3 P-neighbors (|P|=4, might be adjacent to 3).
  -- But triangle-free constrains this.
  --
  -- If q is adjacent to pi and pj (both in P), then pi-pj must be non-adjacent
  -- (else triangle {q, pi, pj}).
  --
  -- So q's P-neighbors form an independent set in the induced subgraph on P.
  -- Max independent set in K₄ has size 1.
  -- Max independent set in C₄ has size 2.
  -- Max independent set in a path on 4 vertices has size 2.
  --
  -- So each q has at most 2 P-neighbors!
  -- Therefore Σ_q |P-neighbors of q| ≤ 2 * 8 = 16.
  -- But Σ_p |NQ| = 16 - 2*(edges in P) ≤ 16 - 0 = 16.
  --
  -- If edges in P = 0, then Σ|NQ| = 16, but each q has ≤ 2 P-neighbors,
  -- and with 8 q's, max Σ = 16. So equality holds: each q has exactly 2 P-neighbors.
  -- And edges in P = 0 means P is an independent set.
  -- Then P ∪ N(v) = 9 vertices, with P independent.
  -- But N(v) is also independent (triangle-free).
  -- Are there edges between P and N(v)? Yes, exactly 4 (one per p).
  -- So P ∪ N(v) has 4 edges total.
  -- Is P ∪ N(v) an independent set? No, there are 4 edges.
  -- The largest independent set in P ∪ N(v) has size ≤ ?
  --
  -- Actually, if P is independent, then {p1,p2,p3,p4} is a 4-independent set.
  -- Can we extend it? We'd need a vertex not adjacent to any pi.
  -- v is adjacent to N(v), and N(v) has edges to P (4 total).
  -- Each si is adjacent to exactly 1 pi.
  -- t is not adjacent to any pi.
  -- So {p1,p2,p3,p4,t} would be 5-independent if P is independent.
  -- Is t adjacent to v? Yes! So no triangle, but t-v edge exists.
  -- Wait, t ∈ N(v), so t is adjacent to v.
  -- So {p1,p2,p3,p4,t} has no edges among p's (P independent) and no edges p-t.
  -- But this is a 5-independent set! Contradiction with NoKIndepSet 6?
  -- No, 5 < 6, so this is allowed.
  --
  -- Can we extend to 6? We'd need a 6th vertex not adjacent to any of {p1,p2,p3,p4,t}.
  -- From Q: each q is adjacent to 2 elements of N(v).
  -- If q is not adjacent to t, then q's N(v)-neighbors are among {s1,s2,s3,s4}.
  -- Such q has 2 si-neighbors.
  -- Is q adjacent to any pi? By triangle-free, q's P-neighbors form an indep set in P.
  -- With P independent, all of P is an indep set, so q can have up to 4 P-neighbors.
  -- But we showed q has at most 2 P-neighbors (from indep set in induced P structure).
  --
  -- Hmm, this is getting complicated. Let me try a cleaner approach.

  -- Simple approach: prove |NP| ≤ 2 using the bound on total P-edges.
  --
  -- Claim: edges in induced P ≥ 4.
  -- Proof: If edges < 4, then Σ|NP| < 8, so average |NP| < 2.
  --   Since |NP| ≤ 3 for each p, and Σ|NP| < 8 with 4 terms,
  --   at least one p has |NP| ≤ 1.
  --   Then |NQ| = 4 - |NP| ≥ 3 for that p.
  --   So that p has ≥ 3 Q-neighbors.
  --   But Q-neighbors of p must form an indep set in N(v)...
  --   Actually, I need to find a contradiction.
  --
  --   If p has 3 Q-neighbors q1, q2, q3, then by triangle-free,
  --   {q1,q2,q3} is independent (no edges among them).
  --   Also, p is a non-neighbor of v.
  --   Consider the set {p, q1, q2, q3}. All are non-neighbors of v.
  --   Is this set independent? We need q_i non-adjacent to q_j (yes) and p non-adjacent to q_i? No! p IS adjacent to q_i.
  --   So this doesn't give an indep set.
  --
  --   Different approach: if p has ≥ 3 Q-neighbors, consider common neighbors.
  --   p has 1 N(v)-neighbor (s).
  --   p has ≤ 1 P-neighbor (since |NP| ≤ 1).
  --   So p's 5 neighbors are: s, ≤1 in P, ≥3 in Q.
  --   The ≥3 Q-neighbors of p each have 2 N(v)-neighbors.
  --   If q is a Q-neighbor of p, does q share a neighbor with p in N(v)?
  --   q's N(v)-neighbors might include s or not.
  --
  --   Actually, let's think about s (p's unique N(v)-neighbor).
  --   s has degree 5: 1 to v, 1 to p, 3 to Q.
  --   So s has 3 Q-neighbors.
  --   If p has ≥ 3 Q-neighbors, do p and s share any Q-neighbor?
  --   If p-q and s-q for some q ∈ Q, then {p,s,q} is a triangle! Contradiction.
  --   So p's Q-neighbors and s's Q-neighbors are disjoint.
  --   p has ≥ 3 Q-neighbors, s has 3 Q-neighbors, total ≥ 6, but |Q| = 8.
  --   So ≥ 6 Q-vertices are covered, leaving ≤ 2.
  --   Those ≤ 2 are non-neighbors of both p and s.
  --
  --   Hmm, this doesn't immediately give a contradiction.
  --
  -- Let me try yet another approach: use commonNeighborsCard constraints.
  -- For p ∈ P with Q-neighbor q:
  -- commonNeighborsCard(q,p) = |N(q) ∩ N(p)|.
  -- q has 2 N(v)-neighbors. p has 1 N(v)-neighbor (s).
  -- If s is one of q's N(v)-neighbors, then s ∈ N(q) ∩ N(p)?
  -- s is adjacent to p (yes), s is adjacent to q (if s is q's neighbor).
  -- So if s ∈ N(q), then s ∈ N(q) ∩ N(p), so they share s.
  -- But we also need to check triangle-free: if p-q and p-s and q-s, then {p,q,s} triangle!
  -- So if p-q and p-s (given), then q-s is forbidden.
  -- Therefore q is NOT adjacent to s.
  -- So q's 2 N(v)-neighbors are from N(v) \ {s} = {other 4 elements including t}.
  --
  -- Great! So p's Q-neighbors avoid s.
  -- p's Q-neighbors' N(v)-neighbors are in N(v) \ {s} (4 elements).
  -- Each Q-neighbor of p has 2 N(v)-neighbors from this set of 4.
  -- If p has k Q-neighbors, they account for ≤ 2k N(v)-edges to this set of 4.
  -- But also, these k Q-neighbors might share N(v)-neighbors.
  --
  -- Also, the other p's (p2, p3, p4) have their own s-partners.
  -- Let S = {s1, s2, s3, s4} be the s-partners of P = {p1, p2, p3, p4}.
  -- For each pi, qi ∈ Q implies qi not adjacent to si (by triangle-free).
  --
  -- Total N(v)-edges to Q: each of the 5 N(v)-vertices has degree 5, with 1 to v.
  -- So 4 edges each to non-v non-N(v) vertices.
  -- Edges to P: 4 total (one per p).
  -- Edges to Q: 5*4 - 4 = 16. ✓
  --
  -- Now, each q ∈ Q has 2 N(v)-neighbors.
  -- For edges from S = {s1,s2,s3,s4} to Q:
  -- Each si has 4 non-v neighbors, with 1 to pi.
  -- So 3 edges from each si to Q. Total from S to Q: 12.
  -- Edges from t to Q: t has 4 non-v neighbors, all in Q (t has no P-neighbor).
  -- Total: 12 + 4 = 16. ✓
  --
  -- For each q ∈ Q: q has 2 N(v)-neighbors.
  -- Case 1: q is adjacent to t. Then q has 1 more N(v)-neighbor from S.
  -- Case 2: q is not adjacent to t. Then q has 2 N(v)-neighbors from S.
  --
  -- t has 4 Q-neighbors. Call them T = {t's 4 Q-neighbors}.
  -- W = Q \ T has |W| = 4 (the Q-vertices not adjacent to t).
  -- Each w ∈ W has 2 S-neighbors.
  -- Each ti ∈ T has 1 S-neighbor and t as the other N(v)-neighbor.
  --
  -- Edges from S to T: |T| * 1 = 4.
  -- Edges from S to W: |W| * 2 = 8.
  -- Total from S to Q: 12. ✓
  --
  -- Now, for p ∈ P with s-partner s ∈ S:
  -- p's Q-neighbors avoid s (by triangle-free).
  -- So p's Q-neighbors' S-edges avoid s.
  --
  -- If p's Q-neighbor q is in T (adjacent to t):
  --   q has 1 S-neighbor, not s. So q's S-neighbor is in S \ {s}.
  -- If p's Q-neighbor q is in W (not adjacent to t):
  --   q has 2 S-neighbors, neither is s. So q's S-neighbors are in S \ {s}.
  --
  -- Key constraint: If p (with s-partner s) has q as a Q-neighbor,
  -- then q's S-neighbors are in S \ {s}.
  --
  -- Let's count: How many Q-vertices have S-neighbors in S \ {si}?
  -- |S \ {si}| = 3.
  -- Each s ∈ S has 3 Q-neighbors. But wait, that's the total, not restricted.
  --
  -- Hmm, this is getting complex. Let me step back.
  --
  -- Key lemma we need: Each p ∈ P has exactly 2 Q-neighbors.
  --
  -- SIMPLEST PROOF:
  -- Σ_p∈P |Q-neighbors of p| = Σ_q∈Q |P-neighbors of q|.
  -- Each q ∈ Q has ≤ 2 P-neighbors (because q's P-neighbors form an indep set in induced P,
  -- and max indep set in any graph on 4 vertices is ≤ 2 when the graph has ≥ 4 edges).
  --
  -- Wait, that's backwards. Max indep set in a graph depends on the graph structure.
  -- In K₄: max indep set = 1.
  -- In C₄: max indep set = 2.
  -- In K₄ - edge: max indep set = 2.
  -- In empty graph on 4 vertices: max indep set = 4.
  --
  -- So max indep set ≤ 2 iff graph has ≥ ? edges.
  -- K₄ - edge has 5 edges and max indep = 2.
  -- C₄ has 4 edges and max indep = 2.
  -- K₄ - 2 non-adjacent edges has 4 edges and max indep = 2.
  -- Path on 4 vertices has 3 edges and max indep = 2.
  --
  -- Actually, max independent set ≤ 2 iff minimum vertex cover ≥ 2.
  -- For 4 vertices, min cover ≥ 2 iff there exist 2 non-adjacent vertices both with edges.
  -- This is true if the graph has ≥ 2 edges that don't share a vertex, i.e., a matching of size 2.
  --
  -- We need: induced P has a matching of size 2.
  -- Then max indep set in P ≤ 2.
  -- Then each q has ≤ 2 P-neighbors.
  -- Then Σ_q |P-neighbors| ≤ 16.
  -- And Σ_p |Q-neighbors| = Σ_q |P-neighbors| ≤ 16.
  -- With 4 p's, average ≤ 4.
  -- And |NP| + |NQ| = 4 for each p.
  -- So Σ|NP| + Σ|NQ| = 16.
  -- If Σ|NQ| ≤ 16, that's consistent but not tight.
  --
  -- Need: Σ|NQ| = 8, so Σ|NP| = 8, so edges in P = 4.
  -- This means P is 2-regular (average degree 2) with 4 edges.
  -- A 2-regular graph on 4 vertices is C₄.
  --
  -- So we need to prove edges in P ≤ 4 (then combined with the max indep argument).
  --
  -- Claim: If edges in P ≥ 5, then some q has ≤ 1 P-neighbor.
  -- Proof: edges ≥ 5 means Σ|NP| ≥ 10, so Σ|NQ| ≤ 6.
  --   Average |NQ| ≤ 1.5, so some p has |NQ| ≤ 1.
  --   Then Σ_q |P-neighbors| = Σ_p |NQ| ≤ 6.
  --   But we need Σ_q |P-neighbors| = 2 * 8 = 16 if each q has 2 P-neighbors.
  --   Contradiction!
  --
  -- Wait, let me re-examine. Σ_q |P-neighbors of q| should equal Σ_p |Q-neighbors of p|.
  -- If Σ_p |NQ| ≤ 6 (when edges in P ≥ 5), then Σ_q |P-neighbors| ≤ 6.
  -- Average P-neighbors per q ≤ 6/8 < 1.
  -- So some q has 0 P-neighbors.
  -- But is that a contradiction?
  --
  -- q with 0 P-neighbors has degree 5 with 2 in N(v) and 3 in Q \ {q}.
  -- That's possible. No immediate contradiction.
  --
  -- Let me try yet another approach. Maybe I should just prove the result
  -- by showing the sum is correct.
  --
  -- I'll use: Σ_p |NQ| = 8.
  -- Proof:
  -- Σ_q |P-neighbors| = Σ_p |NQ|.
  -- Each q has exactly 2 P-neighbors (to be proved).
  -- So Σ_q |P-neighbors| = 16. NO WAIT. If each q has 2 P-neighbors, sum = 16.
  -- But Σ_p |NQ| + Σ_p |NP| = 16 (since |NQ| + |NP| = 4 for each p).
  -- And Σ_p |NP| = 2 * edges in P.
  --
  -- So 16 = Σ_p |NQ| + 2 * edges.
  -- If Σ_p |NQ| = 16, then edges = 0.
  -- If Σ_p |NQ| = 8, then edges = 4.
  --
  -- We need to pin down the edges.
  --
  -- Alternative: prove edges = 4 directly.
  --
  -- I'll use the W-set structure. W = Q-vertices not adjacent to t.
  -- Each w ∈ W has 2 S-neighbors.
  -- |W| = 4 (since |Q| = 8 and |T| = 4).
  -- Total W-to-S edges: 8.
  -- |S| = 4. Average S-neighbor of W = 2.
  --
  -- If some w is adjacent to both si and sj (i ≠ j):
  --   Then consider {pi, pj, si, sj, w}.
  --   - pi adj si (s-partner)
  --   - pj adj sj (s-partner)
  --   - w adj si, w adj sj
  --   - si not adj sj (N(v) independent)
  --   - pi not adj v (p ∈ P)
  --   - What about pi adj pj?
  --
  --   5-vertex set: {pi, pj, si, sj, w}.
  --   Edges: pi-si, pj-sj, w-si, w-sj, and maybe pi-pj.
  --   For triangle-free: need no triangle.
  --   {pi, si, w}: pi-si, w-si, need NOT pi-w.
  --   {pj, sj, w}: pj-sj, w-sj, need NOT pj-w.
  --
  --   So w is NOT adjacent to pi or pj! (Since w-si-pi would form triangle with pi-w.)
  --
  --   Therefore, each w ∈ W has 0 P-neighbors among the p's whose s-partners are w's neighbors.
  --
  --   If w has S-neighbors {si, sj}, then w is NOT adjacent to pi or pj.
  --   So w's P-neighbors are among {pk, pl} = P \ {pi, pj}.
  --
  --   Each w "uses up" 2 s-partners, leaving 2 possible P-neighbors.
  --   With 4 w's and each eliminating 2 p's, what's the structure?
  --
  --   The W-to-S bipartite graph has 8 edges (each w has 2 S-neighbors).
  --   By the "marriage theorem" style analysis:
  --   If the W-S graph is a perfect matching doubled (each w matches to 2 distinct s's),
  --   we can analyze which p's are available to which w's.
  --
  -- KEY INSIGHT: w's P-neighbors are exactly the p's whose s-partners are NOT w's S-neighbors.
  -- If w has S-neighbors {si, sj}, then w's P-neighbors ⊆ {pk : sk ∉ {si, sj}}.
  -- This is a 2-element set {pk, pl}.
  --
  -- So each w ∈ W has at most 2 P-neighbors. ✓
  --
  -- For t's neighbors (the T set):
  -- Each ti ∈ T has 1 S-neighbor, say sk.
  -- By the same triangle argument, ti is NOT adjacent to pk.
  -- So ti's P-neighbors are among {p : s_p ≠ sk} = 3 elements.
  -- But ti is also adjacent to t, and t has no P-neighbors.
  -- So ti's P-neighbors ⊆ {3 p's}.
  --
  -- Hmm, T-vertices can have up to 3 P-neighbors. That's more than W.
  --
  -- Let's count more carefully.
  -- Each p has |NP| P-neighbors and |NQ| = 4 - |NP| Q-neighbors.
  -- p's Q-neighbors are split between T and W.
  --
  -- p's T-neighbors: ti ∈ T such that p-ti.
  --   For such ti, ti's S-neighbor sk must satisfy sk ≠ s_p (else triangle {p, s_p, ti}).
  --   So p's T-neighbors have S-neighbors in S \ {s_p}.
  --   There are 3 such s's in S \ {s_p}.
  --   Each of them is the S-neighbor of at most one ti (or maybe multiple if T-S not a matching).
  --
  -- Wait, is T-S a partial matching? Not necessarily.
  -- T has 4 elements, S has 4 elements.
  -- Each ti has 1 S-neighbor. So 4 T-S edges total.
  -- It could be a perfect matching, or some S-vertices could have multiple T-neighbors.
  --
  -- Similarly, W-S has 8 edges (each w has 2 S-neighbors), 4 vertices on each side.
  -- Average S-degree in W = 2.
  --
  -- Actually, let me use the total. N(v) to Q edges = 16.
  -- T-to-N(v): each ti has 2 N(v)-neighbors (t and one s). So T contributes 8 N(v)-edges.
  --   Wait, ti is a Q-vertex with 2 N(v)-neighbors. One is t, one is in S.
  --   So T-to-S edges = 4, T-to-t edges = 4.
  -- W-to-N(v): each w has 2 N(v)-neighbors, all in S. So W-to-S edges = 8.
  -- Total: 4 + 4 + 8 = 16. ✓
  --
  -- Now, for p ∈ P:
  -- p's Q-neighbors q must satisfy: q's S-neighbors don't include s_p.
  -- For T: ti's S-neighbor ≠ s_p.
  --   |{ti ∈ T : ti's S-neighbor ≠ s_p}| ≤ 4 (all of T if none use s_p).
  --   But actually, T-to-S edges = 4, and each ti has 1 S-neighbor.
  --   If the 4 T-to-S edges form a matching (each s has at most 1 T-neighbor),
  --   then exactly 1 ti has s_p as its S-neighbor (if s_p has a T-neighbor).
  --   So 3 ti's are available to p.
  --   If T-to-S is not a matching, could be fewer or more available.
  --
  -- For W: w's S-neighbors don't include s_p.
  --   |{w ∈ W : s_p ∉ w's S-neighbors}| depends on the W-S bipartite structure.
  --   W-to-S has 8 edges, |W| = |S| = 4.
  --   Each w has degree 2, each s has degree 8/4 = 2 on average.
  --   If every s has exactly 2 W-neighbors, then 2 w's have s_p as a neighbor.
  --   So 2 w's are NOT available to p (they'd form a triangle with s_p).
  --   And 2 w's ARE available to p.
  --
  -- So p has:
  --   T-neighbors: ≤ 3 (or ≤ 4 if s_p has no T-neighbor)
  --   W-neighbors: ≤ 2 (since 2 w's use s_p)
  --
  -- p's Q-neighbors ≤ 3 + 2 = 5. But |NQ| = 4 - |NP| ≤ 4, so that's consistent.
  --
  -- But this gives |NQ| ≤ 5, not tight.
  --
  -- Hmm, I need a tighter argument.
  --
  -- Let me try: prove |NQ| ≥ 2 for each p.
  -- Then with |NP| + |NQ| = 4 and |NQ| ≥ 2, we get |NP| ≤ 2.
  -- Combined with |NQ| ≤ ? giving |NP| ≥ ?, we could get |NP| = 2.
  --
  -- To prove |NQ| ≥ 2:
  -- Suppose |NQ| ≤ 1 for some p. Then |NP| ≥ 3.
  -- p has ≥ 3 P-neighbors, so p is adjacent to all other 3 p's.
  -- Then p, plus its 3 P-neighbors, plus v form a subgraph.
  -- p is non-adjacent to v (p ∈ P).
  -- The 3 P-neighbors of p are also non-adjacent to v.
  --
  -- Consider the 5-element set {p, p1, p2, p3} ∪ {s_p} where {p1,p2,p3} = P \ {p}.
  -- s_p is p's unique S-neighbor.
  -- s_p is adjacent to p.
  -- s_p is NOT adjacent to p1, p2, p3 (each has its own unique S-neighbor).
  -- Actually wait, s_p could be adjacent to some p_i if p_i happens to have s_p as its S-neighbor too.
  -- But each p has a UNIQUE S-neighbor, so no two p's share an S-neighbor? Let me check.
  --
  -- Actually, we need to verify: are S-partners unique?
  -- From the structure: each p ∈ P has commonNeighborsCard = 1, meaning p shares exactly 1 common neighbor with v.
  -- That common neighbor is p's unique S-neighbor.
  -- Two different p's could theoretically have the same S-neighbor s if s is adjacent to both p's.
  -- But then s and v would both be adjacent to these two p's? No, v is not adjacent to any p.
  -- So commonNeighbors(v, p1) = {s} and commonNeighbors(v, p2) = {s} would mean s ∈ N(v) ∩ N(p1) and s ∈ N(v) ∩ N(p2).
  -- So s is adjacent to both p1 and p2.
  -- Triangle {s, p1, p2}? Need p1-p2 adjacent. If so, triangle! Contradicts triangle-free.
  -- So if two p's share an S-neighbor, they are NOT adjacent.
  --
  -- Case: p is adjacent to all other p's (|NP| = 3).
  -- Then none of the other p's share p's S-neighbor.
  -- So s_p is adjacent ONLY to p among P.
  -- The other 3 p's have distinct S-neighbors s_1, s_2, s_3.
  -- So S = {s_p, s_1, s_2, s_3} are all distinct.
  --
  -- Now, p has |NQ| ≤ 1. Say p has Q-neighbor q (or 0 if |NQ| = 0).
  -- p's neighbors: s_p, p1, p2, p3, maybe q. That's 4 or 5.
  -- If p has only 4 neighbors (no Q-neighbor), then p's degree = 4. But h_reg says degree = 5. Contradiction!
  -- So p has exactly 1 Q-neighbor q, and degree = 1 + 3 + 1 = 5. ✓
  --
  -- q is a Q-neighbor of p. q has 2 N(v)-neighbors in S.
  -- q cannot have s_p as a neighbor (else triangle {p, s_p, q}).
  -- So q's S-neighbors are among {s_1, s_2, s_3}.
  --
  -- Consider the 5-element set {p, s_p, p1, s_1, q}.
  -- Edges: p-s_p, p-p1, p1-s_1, q-s_1 (if s_1 is one of q's S-neighbors).
  -- This is getting complicated.
  --
  -- Let me use the independent set argument.
  -- Suppose |NP| = 3 for some p. Then p is adjacent to 3 other p's.
  -- Consider P as a graph. p has degree 3. The other 3 p's have at least degree 1 (adjacent to p).
  -- Sum of degrees ≥ 3 + 1 + 1 + 1 = 6. So edges ≥ 3.
  --
  -- Now, if P has one vertex of degree 3, the other 3 form an induced subgraph.
  -- Let {p1, p2, p3} = P \ {p}. Each is adjacent to p.
  -- The induced subgraph on {p1, p2, p3} can have 0, 1, 2, or 3 edges.
  --
  -- Edges in P = (edges within {p1,p2,p3}) + 3.
  -- If {p1,p2,p3} has 0 edges, P has 3 edges, Σ|NP| = 6, average = 1.5.
  -- Then Σ|NQ| = 16 - 6 = 10, average = 2.5.
  -- So some p has |NQ| ≥ 3.
  -- But then |NP| = 4 - |NQ| ≤ 1 for that p.
  -- So we have both |NP| = 3 and |NP| ≤ 1, which means different p's.
  --
  -- Actually, let me think about this more carefully.
  -- We have p with |NP| = 3 (adjacent to all others).
  -- The other 3 p's (call them p1, p2, p3) each have |NP| = 1 + (edges within {p1,p2,p3}).
  -- If {p1,p2,p3} has 0 internal edges, each of p1, p2, p3 has |NP| = 1.
  -- So their |NQ| = 3 each.
  --
  -- Total |NQ|: p has 1, p1,p2,p3 each have 3. Total = 10.
  -- Total edges P-to-Q = 10.
  --
  -- Now, each q ∈ Q can have at most how many P-neighbors?
  -- q's P-neighbors form an independent set in the induced subgraph on P.
  -- P has edges: p-p1, p-p2, p-p3, and maybe some within {p1,p2,p3}.
  --
  -- If {p1,p2,p3} is independent (0 internal edges):
  --   P's max independent set: {p1, p2, p3} has size 3 (all are mutually non-adjacent).
  --   So q can have up to 3 P-neighbors.
  --
  -- But wait, we also have the triangle constraint on q.
  -- q can't be adjacent to both p and any pi (else q-p-pi... but wait, is p-pi an edge? Yes!)
  -- So if q is adjacent to p, then q cannot be adjacent to any pi (else triangle).
  -- Conversely, if q is adjacent to some pi, q might or might not be adjacent to p.
  --
  -- Case: q is adjacent to p. Then q's only P-neighbor is p (can't have any pi due to triangles with p-pi edge).
  -- Case: q is not adjacent to p. Then q's P-neighbors are among {p1, p2, p3}. Since these form an indep set, q can have up to 3 of them.
  --
  -- Let A = {q ∈ Q : q adj p} and B = Q \ A = {q ∈ Q : q not adj p}.
  -- |A| = |NQ| for p = 1 (by our assumption).
  -- |B| = 7.
  -- q ∈ A contributes 1 P-edge (to p).
  -- q ∈ B contributes ≤ 3 P-edges (to p1, p2, p3 which are independent).
  --
  -- Total P-Q edges = 1 + (edges from B to {p1,p2,p3}).
  -- Also, total P-Q edges = |NQ| for p + Σ_{p1,p2,p3} |NQ| = 1 + 3 + 3 + 3 = 10.
  -- So edges from B to {p1,p2,p3} = 9.
  -- |B| = 7. Average edges per q ∈ B = 9/7 ≈ 1.3.
  -- With max 3 per q, this is achievable.
  --
  -- But let's check consistency with the S-neighbor structure.
  -- p's unique S-neighbor is s_p.
  -- q ∈ A (adjacent to p) cannot be adjacent to s_p (else triangle).
  -- So q's N(v)-neighbors are in N(v) \ {s_p}.
  -- |A| = 1, so 1 q uses neighbors in N(v) \ {s_p}.
  --
  -- For q ∈ B (not adjacent to p):
  -- If q is adjacent to pi, then q cannot be adjacent to s_i (pi's S-partner) by triangle-free.
  -- So q's N(v)-neighbors avoid the S-partners of q's P-neighbors.
  -- If q has 3 P-neighbors (all of p1,p2,p3), then q's N(v)-neighbors avoid s_1, s_2, s_3.
  -- q has 2 N(v)-neighbors, and they must be from N(v) \ {s_1, s_2, s_3} = {s_p, t}.
  -- But |{s_p, t}| = 2. So q's N(v)-neighbors are exactly {s_p, t}.
  -- How many such q's are there?
  -- q must be adjacent to t and s_p.
  -- t has 4 Q-neighbors (the T set). s_p has ... how many Q-neighbors?
  -- s_p has degree 5: 1 to v, 1 to p, 3 to Q.
  -- So s_p has 3 Q-neighbors.
  --
  -- q adjacent to both t and s_p: |T ∩ (s_p's Q-neighbors)| = ?
  -- T = {t's 4 Q-neighbors}.
  -- s_p's Q-neighbors: 3 q's.
  -- Intersection: |T ∩ (s_p's 3 Q-nbrs)| ≤ min(4, 3) = 3.
  --
  -- For q ∈ T ∩ (s_p's Q-nbrs):
  --   q is adjacent to t, so q ∈ T.
  --   q is adjacent to s_p.
  --   q's N(v)-neighbors are {t, s_p}.
  --   q's P-neighbors avoid s_p (already not adjacent to p since q ∈ B).
  --   Wait, does q avoid p's S-partner s_p? If q-s_p, then q-p would form a triangle with p-s_p. Yes, so q is not adjacent to p. ✓
  --   q's P-neighbors also avoid s_1, s_2, s_3 if q is adjacent to p1, p2, p3.
  --   But q's N(v)-neighbors are {t, s_p}, so q is NOT adjacent to s_1, s_2, s_3. ✓ consistent.
  --   So q can be adjacent to p1, p2, p3 (all 3).
  --
  -- So q's with N(v)-neighbors {t, s_p} can have 3 P-neighbors (p1, p2, p3).
  -- How many such q's? |T ∩ (s_p's Q-nbrs)|.
  --
  -- Let's denote x = |T ∩ (s_p's Q-nbrs)|.
  -- These x q's can each have up to 3 P-neighbors.
  --
  -- For the other 7 - x q's in B:
  --   They have N(v)-neighbors that include some of {s_1, s_2, s_3}.
  --   If q's N(v)-neighbors include s_i, then q is not adjacent to p_i.
  --   So each reduces the potential P-neighbors.
  --
  -- This is getting very detailed. Let me just trust that the structure forces |NP| = 2.
  --
  -- Actually, the key insight is: if some p has |NP| = 3, we can derive a contradiction
  -- using the NoKIndepSet 6 constraint. Let me try that.
  --
  -- Suppose p has |NP| = 3 (adjacent to p1, p2, p3).
  -- Then {p1, p2, p3} is an independent set in the induced P (since p is adjacent to all,
  -- and any edge within {p1,p2,p3} would give p degree > 3 in P, but degree in full graph is 5,
  -- with 1 to s_p and 1 to Q... wait, that's only 5 if there are no edges in {p1,p2,p3}).
  --
  -- Actually, let me reconsider. p has:
  -- - 1 S-neighbor (s_p)
  -- - 3 P-neighbors (p1, p2, p3)
  -- - 1 Q-neighbor (since degree = 5)
  --
  -- If there were an edge within {p1, p2, p3}, say p1-p2, then that doesn't affect p's degree.
  -- But it affects p1 and p2's degrees.
  -- p1 has degree 5 = 1 (s_1) + |NP| (P-nbrs) + |NQ| (Q-nbrs).
  -- p1's P-neighbors include p (given) and maybe p2, p3.
  -- If p1-p2, then p1's P-neighbors are at least {p, p2}, so |NP| ≥ 2.
  -- If also p1-p3, |NP| ≥ 3.
  --
  -- Let me assume the simplest case: {p1, p2, p3} has 0 internal edges (it's independent).
  -- Then:
  -- - p has |NP| = 3, |NQ| = 1.
  -- - p1 has |NP| = 1 (only p), |NQ| = 3.
  -- - Same for p2, p3.
  --
  -- Consider the set {p1, p2, p3, q1, q2} where q1, q2 are Q-neighbors of p1.
  -- {p1, p2, p3} is independent.
  -- q1, q2 are adjacent to p1 but what about p2, p3?
  -- q1's P-neighbors: q1 is adjacent to p1. Triangle-free says q1 is not adjacent to s_1 (p1's S-partner).
  --   q1's N(v)-neighbors avoid s_1.
  --   q1 could be adjacent to p2 if q1's N(v)-neighbors avoid s_2.
  --   But q1 has only 2 N(v)-neighbors. If q1 avoids s_1 and s_2, then q1's N(v)-neighbors are in {s_p, s_3, t}.
  --   That's a 3-element set, and q1 picks 2.
  --
  -- This is very case-dependent. Let me use a parity/counting argument.
  --
  -- Independent set argument:
  -- We want to find a 6-independent set in G to get a contradiction.
  -- {p1, p2, p3} is a 3-independent set (assuming independent).
  -- Can we extend it?
  --
  -- Vertices not adjacent to any of {p1, p2, p3}:
  -- - v: adjacent to none (since p_i ∈ P, non-neighbors of v). ✓
  -- - s_p: adjacent to p but not to p1, p2, p3 (each has unique S-partner). ✓
  -- - t: adjacent to v but not to any p_i (each p_i's unique S-neighbor is s_i ≠ t). ✓
  --   Wait, is t adjacent to any p_i? t ∈ N(v), and p_i's common neighbors with v form a single element s_i.
  --   So t is NOT a common neighbor of v and p_i. That means t is not adjacent to p_i. ✓
  --
  -- So far, {p1, p2, p3, v, s_p, t} are pairwise non-adjacent? Let's check:
  -- - p1, p2, p3: mutually non-adjacent (we assumed independent).
  -- - v: not adjacent to p_i (P ⊆ non-neighbors of v). ✓
  -- - s_p: not adjacent to p1, p2, p3 (unique S-partners). And s_p-v? Yes, s_p ∈ N(v), so s_p adj v. ✗
  --
  -- So {p1, p2, p3, v, s_p} has edge s_p-v. Not an independent set.
  --
  -- Try {p1, p2, p3, t}:
  -- - p_i not adj t (as shown above). ✓
  -- - p_i not adj p_j (independent). ✓
  -- This is a 4-independent set.
  --
  -- Can we extend to 5?
  -- Need a vertex x not adjacent to any of {p1, p2, p3, t}.
  -- x could be v (not adj to p_i, but v adj t since t ∈ N(v)). ✗
  -- x could be s_p (not adj to p1,p2,p3, but is s_p adj t?).
  --   s_p and t are both in N(v). N(v) is independent (triangle-free). So s_p not adj t. ✓
  --   So {p1, p2, p3, t, s_p} is a 5-independent set.
  --
  -- Can we extend to 6?
  -- Need x not adjacent to any of {p1, p2, p3, t, s_p}.
  -- x could be:
  -- - v: adj t. ✗
  -- - s_i (i ≠ p): adj p_i. ✗
  -- - p: adj p1, p2, p3. ✗
  -- - q ∈ Q: q has 2 N(v)-neighbors, possibly including t or s_p.
  --   If q adj t, then q ∉ our independent set extension.
  --   If q adj s_p, same.
  --   If q not adj t and q not adj s_p, then q's N(v)-neighbors are in {s_1, s_2, s_3}.
  --   q has 2 N(v)-neighbors from {s_1, s_2, s_3}.
  --   q's P-neighbors: q cannot be adjacent to p_i if q adj s_i (triangle).
  --   So if q adj s_1 and s_2, then q not adj p1 or p2.
  --   If q is also not adj p3... when?
  --   q is not adj p3 if q adj s_3 or just by not being adjacent.
  --   If q's N(v)-neighbors are {s_1, s_2}, then q is not adj s_3, so no constraint from that.
  --   But q could still be adj p3 (no S-based constraint).
  --
  -- So q with N(v)-neighbors {s_1, s_2}:
  --   q not adj p1 (since q-s_1 and s_1-p_1 would give triangle with q-p_1).
  --   q not adj p2 (same reason).
  --   q not adj t (given: q's N(v)-neighbors are {s_1, s_2}, not including t).
  --   q not adj s_p (given: q's N(v)-neighbors are {s_1, s_2}, not including s_p).
  --   q possibly adj p3.
  --
  -- If q is also not adj p3, then {p1, p2, p3, t, s_p, q} is a 6-independent set. Contradiction with NoKIndepSet 6!
  --
  -- So we need: for all q ∈ Q with N(v)-neighbors {s_1, s_2}, q IS adj p3.
  --
  -- How many such q's are there?
  -- W = Q \ T (not adj t). Each w ∈ W has 2 S-neighbors.
  -- |W| = 4.
  -- We want w with S-neighbors {s_1, s_2} (not including s_p or s_3).
  --
  -- Hmm, depends on the specific W-S bipartite structure.
  -- But we have 4 w's and 4 s's. Each w picks 2 s's. Total: 8 edges.
  -- It's possible that no w has S-neighbors {s_1, s_2} (avoiding s_p and s_3).
  --
  -- Actually, let me re-examine. S = {s_p, s_1, s_2, s_3} and we want to avoid s_p.
  -- Oh wait, s_p is one of the 4 S-elements! Let me re-label.
  --
  -- Let S = {s_1, s_2, s_3, s_4} be the 4 S-partners of P = {p_1, p_2, p_3, p_4}.
  -- Wait, but we called one of them "s_p" for the p with |NP| = 3.
  -- Let me be more careful. We have P = {p, p_1, p_2, p_3} where p has |NP| = 3.
  -- Their S-partners are {s, s_1, s_2, s_3} where s = s_p is p's partner.
  --
  -- So S = {s, s_1, s_2, s_3}.
  -- N(v) = S ∪ {t} = {s, s_1, s_2, s_3, t}.
  --
  -- For q ∈ W (not adj t):
  --   q's N(v)-neighbors are 2 elements from S.
  --   q not adj p_i if s_i ∈ q's N(v)-neighbors.
  --   q not adj p if s ∈ q's N(v)-neighbors.
  --
  -- We want a q ∈ W with:
  --   - s ∉ q's N(v)-neighbors (so no constraint on p from this).
  --   - s_1, s_2 ∈ q's N(v)-neighbors (so q not adj p_1, p_2).
  --   - q not adj p_3.
  --
  -- If q's N(v)-neighbors = {s_1, s_2}, then q not adj p_1, p_2. No constraint from s.
  -- We also need q not adj p_3 and q not adj p.
  --
  -- q not adj p: p has |NQ| = 1, so p has only 1 Q-neighbor. If that neighbor is not this q, then q not adj p.
  --   With 8 Q-vertices and p having only 1 Q-neighbor, 7 q's are not adj p.
  --   So most q's satisfy this.
  --
  -- q not adj p_3: Triangle constraint says if q adj s_3, then q not adj p_3.
  --   But q's N(v)-neighbors are {s_1, s_2}, so s_3 ∉ q's neighbors.
  --   So no S-based constraint prevents q adj p_3. We need q to just happen to not be adj p_3.
  --
  -- The question is: can ALL w's with N(v)-neighbors not including s or s_3 be adjacent to p_3?
  --
  -- W has 4 elements. Each has 2 S-neighbors from {s, s_1, s_2, s_3}.
  -- Total W-S edges: 8.
  --
  -- If w's S-neighbors avoid s and s_3, then S-neighbors ⊆ {s_1, s_2}.
  -- Each such w has S-neighbors {s_1, s_2} (the only 2-element subset of {s_1, s_2} is {s_1, s_2} itself).
  --
  -- How many w's have S-neighbors {s_1, s_2}?
  -- W-S bipartite graph: |W| = |S| = 4. Degree sequence of W: all 2's.
  -- Degree sequence of S: sums to 8, so average 2. Could be (2,2,2,2) or (3,2,2,1) or (3,3,1,1) etc.
  --
  -- Case: S-degrees are (2,2,2,2). Each s has exactly 2 W-neighbors.
  -- Then for s_1 and s_2: the 2 W-neighbors of s_1 and the 2 of s_2.
  -- A w with neighbors {s_1, s_2} is in both neighborhoods.
  -- |{s_1's W-nbrs} ∩ {s_2's W-nbrs}| = ?
  -- By inclusion-exclusion: |∩| = |s_1's| + |s_2's| - |∪| = 2 + 2 - |∪|.
  -- |∪| ≤ 4 (since |W| = 4).
  -- If ∪ = W, then |∩| = 0.
  -- If ∪ < W, then |∩| > 0.
  --
  -- For the (2,2,2,2) degree sequence, it's possible to have a 2-regular bipartite graph on 4+4 vertices.
  -- Example: s_1 - w_1, w_2. s_2 - w_3, w_4. s_3 - w_1, w_3. s_4 - w_2, w_4.
  --   Check: each w has 2 S-neighbors. w_1: s_1, s_3. w_2: s_1, s_4. w_3: s_2, s_3. w_4: s_2, s_4.
  --   No w has neighbors {s_1, s_2}. Good for this subcase.
  --
  -- Another example: s_1 - w_1, w_2. s_2 - w_1, w_2. s_3 - w_3, w_4. s_4 - w_3, w_4.
  --   w_1: s_1, s_2. w_2: s_1, s_2. w_3: s_3, s_4. w_4: s_3, s_4.
  --   Here, w_1 and w_2 have neighbors {s_1, s_2}. These would give the 6-independent set!
  --
  -- So the structure depends on the specific W-S bipartite configuration.
  --
  -- Key insight: If ANY w has S-neighbors {s_1, s_2} (avoiding both s and s_3), AND that w is not adjacent to p_3 or p,
  -- we get a 6-independent set contradiction.
  --
  -- For this w:
  --   - w not adj p_1, p_2 (since w adj s_1, s_2 gives triangles).
  --   - w not adj t (w ∈ W means not adj t).
  --   - w not adj s (since w's S-neighbors are {s_1, s_2}, not including s).
  --   - Need w not adj p and w not adj p_3.
  --
  -- p has only 1 Q-neighbor. So ≤ 1 element of W is adjacent to p.
  -- With |W| = 4 and ≤ 1 adjacent to p, ≥ 3 w's are not adjacent to p.
  --
  -- For w not adj p_3:
  --   p_3 has |NQ| = 3 (since |NP| = 1).
  --   So p_3 has 3 Q-neighbors.
  --   At most 3 w's are adjacent to p_3.
  --   With |W| = 4, ≥ 1 w is not adjacent to p_3.
  --
  -- Combined: we need w not adj p AND w not adj p_3.
  -- |W| = 4.
  -- |{w adj p}| ≤ 1.
  -- |{w adj p_3}| ≤ 3.
  -- |{w not adj p AND w not adj p_3}| = |W| - |{w adj p}| - |{w adj p_3}| + |{w adj p AND w adj p_3}|.
  -- ≥ 4 - 1 - 3 + 0 = 0.
  -- So at least 0 such w's. Not guaranteed.
  --
  -- But actually, {w adj p} ⊆ T∪W = Q? And |{w adj p}| = (number of p's Q-neighbors in W).
  -- p has 1 Q-neighbor. That neighbor is in T or W.
  -- If in T, then |{w adj p}| = 0.
  -- If in W, then |{w adj p}| = 1.
  --
  -- Similarly, p_3's 3 Q-neighbors are distributed between T and W.
  -- |{w adj p_3}| = (p_3's Q-neighbors in W).
  --
  -- If p's Q-neighbor is in T:
  --   |{w not adj p}| = 4.
  --   |{w adj p_3}| = (p_3's W-neighbors).
  --   Need: exists w with S-neighbors {s_1, s_2} (or any 2-subset avoiding s and s_3) and w not adj p_3.
  --
  -- This is getting very detailed, but the key point is:
  -- The constraints are tight enough that SOME w must form the 6-independent set,
  -- giving a contradiction.
  --
  -- Given the complexity, let me just trust that the counting works out and
  -- prove |NP| = 2 by other means or accept this as a TODO.
  --
  -- Actually, let me take a step back. The mathematical content is:
  -- If G is 5-regular, triangle-free, with no 6-independent set on 18 vertices,
  -- then for any v and the sets P, Q, each p ∈ P has exactly 2 P-neighbors.
  --
  -- This is a known result from Cariolaro's paper. The formalization is complex
  -- but the mathematical validity is established.
  --
  -- For now, let me leave a proof gap with a detailed TODO explaining the proof.

  -- Claim: NP.card = 2
  -- This is the key result. We prove it via counting arguments and independent set constraints.
  -- The detailed proof involves:
  -- 1. If |NP| = 3 for some p, then P \ {p} is independent, and we can construct
  --    a 6-independent set using {P \ {p}} ∪ {t, s_p, w} for suitable w ∈ W.
  -- 2. If |NP| ≤ 1 for some p, then |NQ| ≥ 3, and similar counting shows too many Q-edges.
  -- 3. Therefore |NP| = 2 for all p ∈ P.

  -- The result that (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = NP.card is immediate
  -- since NP = (P.erase p).filter (G.Adj p) and P.erase p = P.filter (· ≠ p).
  have hNP_eq_goal : (P.filter (fun q => q ≠ p ∧ G.Adj p q)).card = NP.card := by
    congr 1
    ext x
    simp only [NP, mem_filter, mem_erase, and_assoc]
    tauto
  rw [hNP_eq_goal]

  -- NP.card = 5 - 1 - NQ.card = 4 - NQ.card
  -- We need to show NQ.card = 2, then NP.card = 2.
  have h_eq : NP.card = 4 - NQ.card := by omega

  -- Step 1: NQ.card ≤ 4 (from NP.card ≥ 0 and sum = 4)
  have hNQ_le4 : NQ.card ≤ 4 := by omega

  -- Step 2: NQ.card ≤ 2 using independence constraint
  -- If NQ.card ≥ 3, then p has 3+ Q-neighbors forming a 3-IS (triangle-free).
  -- Combined with v (not adjacent to Q-vertices), we get a 4-IS.
  -- p's unique N(v)-neighbor s is not adjacent to Q-vertices (would form triangle with p).
  -- This leads to a contradiction with 6-IS.
  have hNQ_le2 : NQ.card ≤ 2 := by
    by_contra h_gt2
    push_neg at h_gt2
    -- NQ.card ≥ 3: extract 3 Q-neighbors using two_lt_card_iff
    have h3 : 2 < NQ.card := by omega
    obtain ⟨q1, q2, q3, hq1_in, hq2_in, hq3_in, hq_ne12, hq_ne13, hq_ne23⟩ :=
      Finset.two_lt_card_iff.mp h3
    simp only [NQ, mem_filter] at hq1_in hq2_in hq3_in
    have hq1_Q : q1 ∈ Q := hq1_in.1
    have hq2_Q : q2 ∈ Q := hq2_in.1
    have hq3_Q : q3 ∈ Q := hq3_in.1
    have hp_adj_q1 : G.Adj p q1 := hq1_in.2
    have hp_adj_q2 : G.Adj p q2 := hq2_in.2
    have hp_adj_q3 : G.Adj p q3 := hq3_in.2
    -- Q-properties: qi ∈ Q means qi not adjacent to v
    have hq1_nonadj_v : ¬G.Adj v q1 := (hQ_props q1 hq1_Q).1
    have hq2_nonadj_v : ¬G.Adj v q2 := (hQ_props q2 hq2_Q).1
    have hq3_nonadj_v : ¬G.Adj v q3 := (hQ_props q3 hq3_Q).1
    -- qi are pairwise non-adjacent (otherwise triangle with p)
    have hq12_nonadj : ¬G.Adj q1 q2 := by
      intro h
      have h_clique : G.IsNClique 3 {p, q1, q2} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hp_adj_q1
          · exact hp_adj_q2
          · exact G.symm hp_adj_q1
          · exact absurd rfl hab
          · exact h
          · exact G.symm hp_adj_q2
          · exact G.symm h
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hq_ne12
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hp_adj_q1), (G.ne_of_adj hp_adj_q2)⟩
      exact h_tri _ h_clique
    have hq13_nonadj : ¬G.Adj q1 q3 := by
      intro h
      have h_clique : G.IsNClique 3 {p, q1, q3} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hp_adj_q1
          · exact hp_adj_q3
          · exact G.symm hp_adj_q1
          · exact absurd rfl hab
          · exact h
          · exact G.symm hp_adj_q3
          · exact G.symm h
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hq_ne13
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hp_adj_q1), (G.ne_of_adj hp_adj_q3)⟩
      exact h_tri _ h_clique
    have hq23_nonadj : ¬G.Adj q2 q3 := by
      intro h
      have h_clique : G.IsNClique 3 {p, q2, q3} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hp_adj_q2
          · exact hp_adj_q3
          · exact G.symm hp_adj_q2
          · exact absurd rfl hab
          · exact h
          · exact G.symm hp_adj_q3
          · exact G.symm h
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hq_ne23
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hp_adj_q2), (G.ne_of_adj hp_adj_q3)⟩
      exact h_tri _ h_clique
    -- v ≠ qi (since p ~ qi but p ≁ v)
    have hv_ne_q1 : v ≠ q1 := fun h => hp_nonadj_v (G.symm (h ▸ hp_adj_q1))
    have hv_ne_q2 : v ≠ q2 := fun h => hp_nonadj_v (G.symm (h ▸ hp_adj_q2))
    have hv_ne_q3 : v ≠ q3 := fun h => hp_nonadj_v (G.symm (h ▸ hp_adj_q3))
    -- p's unique N(v)-neighbor
    have hNN_nonempty : NN.Nonempty := by rw [← Finset.card_pos]; simp [hNN_card]
    obtain ⟨s, hs_in_NN⟩ := hNN_nonempty
    simp only [NN, mem_filter, mem_neighborFinset] at hs_in_NN
    have hs_adj_v : G.Adj v s := hs_in_NN.1
    have hs_adj_p : G.Adj s p := G.symm hs_in_NN.2
    -- s is not adjacent to qi (would form triangle s-p-qi)
    have hs_nonadj_q1 : ¬G.Adj s q1 := by
      intro h
      have h_clique : G.IsNClique 3 {s, p, q1} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hs_adj_p
          · exact h
          · exact G.symm hs_adj_p
          · exact absurd rfl hab
          · exact hp_adj_q1
          · exact G.symm h
          · exact G.symm hp_adj_q1
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hp_adj_q1)
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hs_adj_p), (G.ne_of_adj h)⟩
      exact h_tri _ h_clique
    have hs_nonadj_q2 : ¬G.Adj s q2 := by
      intro h
      have h_clique : G.IsNClique 3 {s, p, q2} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hs_adj_p
          · exact h
          · exact G.symm hs_adj_p
          · exact absurd rfl hab
          · exact hp_adj_q2
          · exact G.symm h
          · exact G.symm hp_adj_q2
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hp_adj_q2)
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hs_adj_p), (G.ne_of_adj h)⟩
      exact h_tri _ h_clique
    have hs_nonadj_q3 : ¬G.Adj s q3 := by
      intro h
      have h_clique : G.IsNClique 3 {s, p, q3} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
          · exact absurd rfl hab
          · exact hs_adj_p
          · exact h
          · exact G.symm hs_adj_p
          · exact absurd rfl hab
          · exact hp_adj_q3
          · exact G.symm h
          · exact G.symm hp_adj_q3
          · exact absurd rfl hab
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hp_adj_q3)
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(G.ne_of_adj hs_adj_p), (G.ne_of_adj h)⟩
      exact h_tri _ h_clique
    -- s ≠ qi (s ∈ N(v) but qi ∉ N(v), so v ~ s but v ≁ qi)
    have hs_ne_q1 : s ≠ q1 := fun h => hq1_nonadj_v (h ▸ hs_adj_v)
    have hs_ne_q2 : s ≠ q2 := fun h => hq2_nonadj_v (h ▸ hs_adj_v)
    have hs_ne_q3 : s ≠ q3 := fun h => hq3_nonadj_v (h ▸ hs_adj_v)
    -- p ≠ qi
    have hp_ne_q1 : p ≠ q1 := G.ne_of_adj hp_adj_q1
    have hp_ne_q2 : p ≠ q2 := G.ne_of_adj hp_adj_q2
    have hp_ne_q3 : p ≠ q3 := G.ne_of_adj hp_adj_q3

    -- {v, s, q1, q2, q3} is a 5-IS (all pairwise non-adjacent)
    -- Need to extend to 6-IS by finding one more vertex from P \ {p}

    -- CARIOLARO'S CONSTRUCTION 3:
    -- P \ {p} has 3 vertices, each with exactly 1 N(v)-neighbor.
    -- If any two share the same N(v)-neighbor, we get a 6-IS.

    -- Extract P \ {p} = {a, b, c}
    have hP_erase_card_loc : (P.erase p).card = 3 := by
      rw [Finset.card_erase_of_mem hp, hP_card]
    obtain ⟨a, b, c, hab, hac, hbc, hPerase_eq⟩ := Finset.card_eq_three.mp hP_erase_card_loc
    have ha_in : a ∈ P.erase p := by rw [hPerase_eq]; simp
    have hb_in : b ∈ P.erase p := by rw [hPerase_eq]; simp
    have hc_in : c ∈ P.erase p := by rw [hPerase_eq]; simp
    have ha_P : a ∈ P := (Finset.mem_erase.mp ha_in).2
    have hb_P : b ∈ P := (Finset.mem_erase.mp hb_in).2
    have hc_P : c ∈ P := (Finset.mem_erase.mp hc_in).2

    -- Each has exactly 1 N(v)-neighbor (by P-property)
    have ha_common1 : commonNeighborsCard G v a = 1 := (hP_props a ha_P).2
    have hb_common1 : commonNeighborsCard G v b = 1 := (hP_props b hb_P).2
    have hc_common1 : commonNeighborsCard G v c = 1 := (hP_props c hc_P).2

    -- Get the unique N(v)-neighbors for each
    have ha_Nv_ex : ∃ s_a, G.neighborFinset v ∩ G.neighborFinset a = {s_a} := by
      unfold commonNeighborsCard _root_.commonNeighbors at ha_common1
      exact Finset.card_eq_one.mp ha_common1
    obtain ⟨s_a, hs_a_eq⟩ := ha_Nv_ex
    have hb_Nv_ex : ∃ s_b, G.neighborFinset v ∩ G.neighborFinset b = {s_b} := by
      unfold commonNeighborsCard _root_.commonNeighbors at hb_common1
      exact Finset.card_eq_one.mp hb_common1
    obtain ⟨s_b, hs_b_eq⟩ := hb_Nv_ex
    have hc_Nv_ex : ∃ s_c, G.neighborFinset v ∩ G.neighborFinset c = {s_c} := by
      unfold commonNeighborsCard _root_.commonNeighbors at hc_common1
      exact Finset.card_eq_one.mp hc_common1
    obtain ⟨s_c, hs_c_eq⟩ := hc_Nv_ex

    -- If any two of {a, b, c} share the same N(v)-neighbor, we get a 6-IS
    -- TODO: Implement Cariolaro's Construction 3 for all cases
    -- (old placeholder removed)

  -- Step 3: NQ.card ≥ 2 using independence constraint
  -- If NQ.card ≤ 1, then NP.card ≥ 3, so p is adjacent to ≥3 other P-vertices.
  -- Triangle-free means those 3 P-neighbors are pairwise non-adjacent (3-IS).
  -- With v, we get 4-IS. Extend to 6-IS → contradiction.
  have hNQ_ge2 : NQ.card ≥ 2 := by
    by_contra h_lt2
    push_neg at h_lt2
    -- NQ.card ≤ 1 → NP.card ≥ 3
    have hNP_ge3 : NP.card ≥ 3 := by omega
    -- P \ {p} has exactly 3 elements
    have hP_erase_card : (P.erase p).card = 3 := by
      rw [Finset.card_erase_of_mem hp, hP_card]
    -- NP ⊆ P.erase p, so if NP.card ≥ 3 and (P.erase p).card = 3, then NP = P.erase p
    have hNP_eq : NP = P.erase p := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; simp only [NP, mem_filter, mem_erase] at hx ⊢; exact hx.1
      · rw [hP_erase_card]; exact hNP_ge3
    -- p is adjacent to all other P-vertices
    have hp_adj_all : ∀ q ∈ P, q ≠ p → G.Adj p q := by
      intro q hq hne
      have : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hne, hq⟩
      rw [← hNP_eq] at this
      simp only [NP, mem_filter, mem_erase] at this
      exact this.2
    -- Triangle-free: the 3 other P-vertices are pairwise non-adjacent
    -- Extract the 3 other P-vertices
    obtain ⟨a, b, c, hab, hac, hbc, hPerase_eq⟩ := Finset.card_eq_three.mp hP_erase_card
    have ha_in : a ∈ P.erase p := by rw [hPerase_eq]; simp
    have hb_in : b ∈ P.erase p := by rw [hPerase_eq]; simp
    have hc_in : c ∈ P.erase p := by rw [hPerase_eq]; simp
    have ha_P : a ∈ P := (Finset.mem_erase.mp ha_in).2
    have hb_P : b ∈ P := (Finset.mem_erase.mp hb_in).2
    have hc_P : c ∈ P := (Finset.mem_erase.mp hc_in).2
    have ha_ne_p : a ≠ p := (Finset.mem_erase.mp ha_in).1
    have hb_ne_p : b ≠ p := (Finset.mem_erase.mp hb_in).1
    have hc_ne_p : c ≠ p := (Finset.mem_erase.mp hc_in).1
    have hp_adj_a : G.Adj p a := hp_adj_all a ha_P ha_ne_p
    have hp_adj_b : G.Adj p b := hp_adj_all b hb_P hb_ne_p
    have hp_adj_c : G.Adj p c := hp_adj_all c hc_P hc_ne_p
    -- a, b, c are pairwise non-adjacent (would form triangle with p)
    have hab_nonadj : ¬G.Adj a b := by
      intro h
      have h_clique : G.IsNClique 3 {p, a, b} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact hp_adj_a
          · exact hp_adj_b
          · exact G.symm hp_adj_a
          · exact absurd rfl hxy
          · exact h
          · exact G.symm hp_adj_b
          · exact G.symm h
          · exact absurd rfl hxy
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hab
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨ha_ne_p.symm, hb_ne_p.symm⟩
      exact h_tri _ h_clique
    have hac_nonadj : ¬G.Adj a c := by
      intro h
      have h_clique : G.IsNClique 3 {p, a, c} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact hp_adj_a
          · exact hp_adj_c
          · exact G.symm hp_adj_a
          · exact absurd rfl hxy
          · exact h
          · exact G.symm hp_adj_c
          · exact G.symm h
          · exact absurd rfl hxy
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hac
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨ha_ne_p.symm, hc_ne_p.symm⟩
      exact h_tri _ h_clique
    have hbc_nonadj : ¬G.Adj b c := by
      intro h
      have h_clique : G.IsNClique 3 {p, b, c} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact hp_adj_b
          · exact hp_adj_c
          · exact G.symm hp_adj_b
          · exact absurd rfl hxy
          · exact h
          · exact G.symm hp_adj_c
          · exact G.symm h
          · exact absurd rfl hxy
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hbc
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hb_ne_p.symm, hc_ne_p.symm⟩
      exact h_tri _ h_clique
    -- P-properties: a, b, c not adjacent to v
    have ha_nonadj_v : ¬G.Adj v a := (hP_props a ha_P).1
    have hb_nonadj_v : ¬G.Adj v b := (hP_props b hb_P).1
    have hc_nonadj_v : ¬G.Adj v c := (hP_props c hc_P).1
    -- {v, a, b, c} is a 4-IS
    -- Need 2 more vertices independent from these 4 and from each other

    -- Key counting argument:
    -- For q ∈ Q, we have deg(q) = 5 = deg_Nv(q) + deg_P(q) + deg_Q(q)
    -- where deg_Nv(q) = 2 (since q ∈ Q → commonNeighborsCard G v q = 2)
    -- So deg_P(q) + deg_Q(q) = 3.

    -- Step 1: Prove NQ.card = 1 (not 0) using parity
    -- If NQ.card = 0, then for all q: deg_P(q) = deg_abc(q) and deg_Q(q) = 3 - deg_abc(q)
    -- sum of deg_Q(q) = sum of (3 - deg_abc(q)) = 3 * 8 - 9 = 15
    -- But sum of degrees in Q must be even (= 2 * |E_Q|), contradiction!
    -- So NQ.card ≥ 1. Combined with NQ.card ≤ 1, we get NQ.card = 1.

    -- Step 2: With NQ.card = 1, let q0 be the unique Q-neighbor of p
    -- For q0: deg_Q(q0) = 3 - (1 + deg_abc(q0)) = 2 - deg_abc(q0)
    -- For q ≠ q0: deg_Q(q) = 3 - deg_abc(q)
    -- sum of deg_Q = (2 - deg_abc(q0)) + sum_{q≠q0} (3 - deg_abc(q)) = 23 - 9 = 14
    -- So Q has exactly 7 edges among 8 vertices.

    -- Step 3: Find 2 vertices q1, q2 ∈ Q with:
    --   - deg_abc(q1) = 0 and deg_abc(q2) = 0 (not adjacent to a, b, c)
    --   - q1 ≁ q2 (not adjacent to each other)
    -- If deg_abc(qi) = 0, then deg_Q(qi) = 3 (if qi ≠ q0) or 2 (if qi = q0).

    -- The full construction requires analyzing Q's structure with 8 vertices and 7 edges,
    -- showing that among vertices with low deg_abc, at least 2 are non-adjacent.
    -- This requires case analysis on the distribution of degrees and the specific edge structure.

    -- (old placeholder removed)

  -- Combine bounds
  omega
  -/

/-- A 2-regular graph on 4 vertices is a 4-cycle (C₄).
This is a graph-theoretic fact: 4 vertices with each having degree 2
forms a single cycle of length 4. -/
lemma two_regular_four_vertices_is_cycle
    {α : Type*} [DecidableEq α] [Fintype α]
    (P : Finset α) (hP_card : P.card = 4)
    (adj : α → α → Prop) [DecidableRel adj]
    (h_symm : ∀ x y, adj x y → adj y x)
    (_h_irrefl : ∀ x, ¬adj x x)
    (h_2reg : ∀ p ∈ P, (P.filter (fun q => q ≠ p ∧ adj p q)).card = 2) :
    ∃ (p1 p2 p3 p4 : α),
      p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4 ∧
      P = {p1, p2, p3, p4} ∧
      adj p1 p2 ∧ adj p2 p3 ∧ adj p3 p4 ∧ adj p4 p1 ∧
      ¬adj p1 p3 ∧ ¬adj p2 p4 := by
  classical
  -- pick an arbitrary vertex p1
  have hP_nonempty : P.Nonempty := by
    apply Finset.card_pos.mp
    simp [hP_card]
  rcases hP_nonempty with ⟨p1, hp1P⟩

  -- neighbors of p1 inside P: exactly two, call them p2 and p4
  set N1 : Finset α := P.filter (fun q => q ≠ p1 ∧ adj p1 q)
  have hN1_card : N1.card = 2 := h_2reg _ hp1P
  obtain ⟨p2, p4, hp2p4, hN1_eq⟩ := Finset.card_eq_two.mp hN1_card
  have hp2N1 : p2 ∈ N1 := by
    rw [hN1_eq]
    simp
  have hp4N1 : p4 ∈ N1 := by
    rw [hN1_eq]
    simp
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
    simp [P1, hp4P0, hp2ne4.symm]
  have hP2_card : P2.card = 1 := by simp [P2, hp4P1, hP1_card]
  obtain ⟨p3, hP2_eq⟩ := Finset.card_eq_one.mp hP2_card
  have hp3P2 : p3 ∈ P2 := by
    rw [hP2_eq]
    simp
  have hp3P1 : p3 ∈ P1 := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P2
  have hp3P0 : p3 ∈ P0 := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P1
  have hp3P : p3 ∈ P := Finset.mem_of_subset (Finset.erase_subset _ _) hp3P0
  have hp3ne4 : p3 ≠ p4 := (Finset.mem_erase.mp (by simpa [P2] using hp3P2)).1
  have hp3ne2 : p3 ≠ p2 := (Finset.mem_erase.mp (by simpa [P1] using hp3P1)).1
  have hp3ne1 : p3 ≠ p1 := (Finset.mem_erase.mp (by simpa [P0] using hp3P0)).1
  
  -- p3 is not adjacent to p1, otherwise it would be in N1
  have h_not_adj_13 : ¬adj p1 p3 := by
    intro h
    have hmem : p3 ∈ N1 := Finset.mem_filter.mpr ⟨hp3P, hp3ne1, h⟩
    have : p3 ∈ ({p2, p4} : Finset α) := by
      rw [hN1_eq] at hmem
      exact hmem
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
  have hErase3_eq : ({p1, p2, p4} : Finset α) = P.erase p3 := by
    apply Finset.eq_of_subset_of_card_le hsubset_erase3
    -- goal: (P.erase p3).card ≤ ({p1, p2, p4} : Finset α).card
    simp [hP_erase3_card, h_card_three]

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
    -- card bound: ({p2, p4}).card ≤ N3.card, both sides are 2
    simp [hN3_card, hp2ne4]
  have hp3p2 : adj p3 p2 := by
    have : p2 ∈ N3 := by
      rw [hN3_eq]
      simp
    exact (Finset.mem_filter.mp this).2.2
  have hp3p4 : adj p3 p4 := by
    have : p4 ∈ N3 := by
      rw [hN3_eq]
      simp
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
      simp [hN2_card, hcard]
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
    have h4_notin : s4 ∉ ({} : Finset (Fin 18)) := Finset.notMem_empty s4
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

/-! ### Existence of CariolaroSetup -/

set_option maxHeartbeats 800000 in
/-- Existence of a CariolaroSetup for any counterexample graph, centered at any vertex v.
This is the central construction that bundles the S-W bipartite structure.
The proof requires careful constraint tracking of the T/W partition of Q. -/
lemma exists_CariolaroSetup_at {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) :
    ∃ setup : CariolaroSetup G h_reg h_tri h_no6, setup.v = v := by
  classical
  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 1: Get P (4 vertices with common=1) and Q (8 vertices with common=2)
  -- ═══════════════════════════════════════════════════════════════════════════
  obtain ⟨P, Q, hP_card, hQ_card, hP_props, hQ_props⟩ :=
    claim2_neighbor_structure h_reg h_tri h_no6 v

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 2: Get the 4-cycle structure p1-p2-p3-p4-p1 from claim3
  -- ═══════════════════════════════════════════════════════════════════════════
  obtain ⟨p1, p2, p3, p4, hp_ne12, hp_ne13, hp_ne14, hp_ne23, hp_ne24, hp_ne34,
          hP_eq, h_adj_p1p2, h_adj_p2p3, h_adj_p3p4, h_adj_p4p1, h_nonadj_p1p3, h_nonadj_p2p4⟩ :=
    claim3_four_cycle h_reg h_tri h_no6 v P ⟨hP_card, hP_props⟩

  -- Extract P properties
  have hp1_in_P : p1 ∈ P := by rw [hP_eq]; simp
  have hp2_in_P : p2 ∈ P := by rw [hP_eq]; simp
  have hp3_in_P : p3 ∈ P := by rw [hP_eq]; simp
  have hp4_in_P : p4 ∈ P := by rw [hP_eq]; simp
  have ⟨hp1_nonadj_v, hp1_common1⟩ := hP_props p1 hp1_in_P
  have ⟨hp2_nonadj_v, hp2_common1⟩ := hP_props p2 hp2_in_P
  have ⟨hp3_nonadj_v, hp3_common1⟩ := hP_props p3 hp3_in_P
  have ⟨hp4_nonadj_v, hp4_common1⟩ := hP_props p4 hp4_in_P

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 3: Get s-partners for each p using P_partner_in_N
  -- ═══════════════════════════════════════════════════════════════════════════
  obtain ⟨s1, ⟨hs1_in_N, hs1_adj_p1⟩, hs1_unique⟩ := P_partner_in_N h_reg h_tri v p1 hp1_nonadj_v hp1_common1
  obtain ⟨s2, ⟨hs2_in_N, hs2_adj_p2⟩, hs2_unique⟩ := P_partner_in_N h_reg h_tri v p2 hp2_nonadj_v hp2_common1
  obtain ⟨s3, ⟨hs3_in_N, hs3_adj_p3⟩, hs3_unique⟩ := P_partner_in_N h_reg h_tri v p3 hp3_nonadj_v hp3_common1
  obtain ⟨s4, ⟨hs4_in_N, hs4_adj_p4⟩, hs4_unique⟩ := P_partner_in_N h_reg h_tri v p4 hp4_nonadj_v hp4_common1

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 3b: Prove all s-partners are pairwise distinct
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Setup for the distinct_helper approach
  let N := G.neighborFinset v
  have hN_card : N.card = 5 := h_reg v
  have hN_indep : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v

  -- Helper: if two p's share the same s-partner, contradiction
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
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p1 := And.intro hx hadj
    exact hne (hs1_unique x h_and)
  have h2_unique : ∀ x, x ∈ N → x ≠ s2 → ¬G.Adj x p2 := by
    intro x hx hne hadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p2 := And.intro hx hadj
    exact hne (hs2_unique x h_and)
  have h3_unique : ∀ x, x ∈ N → x ≠ s3 → ¬G.Adj x p3 := by
    intro x hx hne hadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p3 := And.intro hx hadj
    exact hne (hs3_unique x h_and)
  have h4_unique : ∀ x, x ∈ N → x ≠ s4 → ¬G.Adj x p4 := by
    intro x hx hne hadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p4 := And.intro hx hadj
    exact hne (hs4_unique x h_and)

  -- All 6 pairwise distinctness facts
  have hs_ne12 : s1 ≠ s2 := by
    intro h_eq; subst h_eq
    exact distinct_helper p1 p2 s1 hp_ne12 hp1_nonadj_v hp2_nonadj_v hs1_in_N hs1_adj_p1 hs2_adj_p2 h1_unique h2_unique
  have hs_ne13 : s1 ≠ s3 := by
    intro h_eq; subst h_eq
    exact distinct_helper p1 p3 s1 hp_ne13 hp1_nonadj_v hp3_nonadj_v hs1_in_N hs1_adj_p1 hs3_adj_p3 h1_unique h3_unique
  have hs_ne14 : s1 ≠ s4 := by
    intro h_eq; subst h_eq
    exact distinct_helper p1 p4 s1 hp_ne14 hp1_nonadj_v hp4_nonadj_v hs1_in_N hs1_adj_p1 hs4_adj_p4 h1_unique h4_unique
  have hs_ne23 : s2 ≠ s3 := by
    intro h_eq; subst h_eq
    exact distinct_helper p2 p3 s2 hp_ne23 hp2_nonadj_v hp3_nonadj_v hs2_in_N hs2_adj_p2 hs3_adj_p3 h2_unique h3_unique
  have hs_ne24 : s2 ≠ s4 := by
    intro h_eq; subst h_eq
    exact distinct_helper p2 p4 s2 hp_ne24 hp2_nonadj_v hp4_nonadj_v hs2_in_N hs2_adj_p2 hs4_adj_p4 h2_unique h4_unique
  have hs_ne34 : s3 ≠ s4 := by
    intro h_eq; subst h_eq
    exact distinct_helper p3 p4 s3 hp_ne34 hp3_nonadj_v hp4_nonadj_v hs3_in_N hs3_adj_p3 hs4_adj_p4 h3_unique h4_unique

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 4: Get t as the remaining element of N(v) \ {s1, s2, s3, s4}
  -- ═══════════════════════════════════════════════════════════════════════════

  -- {s1, s2, s3, s4} ⊆ N
  have hS_sub_N : {s1, s2, s3, s4} ⊆ N := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hs1_in_N
    · exact hs2_in_N
    · exact hs3_in_N
    · exact hs4_in_N

  have hS_card : ({s1, s2, s3, s4} : Finset (Fin 18)).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hs_ne34]
    · simp [hs_ne23, hs_ne24]
    · simp [hs_ne12, hs_ne13, hs_ne14]

  -- N \ {s1, s2, s3, s4} has exactly 1 element
  have h_diff_card : (N \ {s1, s2, s3, s4}).card = 1 := by
    simp only [Finset.card_sdiff_of_subset hS_sub_N, hN_card, hS_card]

  have h_diff_nonempty : (N \ {s1, s2, s3, s4}).Nonempty := by
    rw [← card_pos]; omega

  obtain ⟨t, ht_mem⟩ := h_diff_nonempty
  have ht_in_N : t ∈ N := (mem_sdiff.mp ht_mem).1
  have ht_ne_s1 : t ≠ s1 := by
    intro h; have := (mem_sdiff.mp ht_mem).2; simp [h] at this
  have ht_ne_s2 : t ≠ s2 := by
    intro h; have := (mem_sdiff.mp ht_mem).2; simp [h] at this
  have ht_ne_s3 : t ≠ s3 := by
    intro h; have := (mem_sdiff.mp ht_mem).2; simp [h] at this
  have ht_ne_s4 : t ≠ s4 := by
    intro h; have := (mem_sdiff.mp ht_mem).2; simp [h] at this

  have ht_adj_v : G.Adj v t := by rw [← mem_neighborFinset]; exact ht_in_N

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 5: Split Q into T (neighbors of t in Q) and W (non-neighbors of t in Q)
  -- ═══════════════════════════════════════════════════════════════════════════
  let T := Q.filter (G.Adj t)
  let W := Q.filter (fun q => ¬G.Adj t q)

  have hTW_disj : Disjoint T W := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    simp only [T, W, mem_filter] at ha hb
    subst h_eq; exact hb.2 ha.2

  have hTW_union : T ∪ W = Q := by
    ext x; simp only [T, W, mem_union, mem_filter]
    constructor
    · intro h; cases h with | inl hl => exact hl.1 | inr hr => exact hr.1
    · intro hx; by_cases h : G.Adj t x <;> simp [hx, h]

  -- t is not adjacent to any p ∈ P (each p's unique N(v)-neighbor is its s-partner)
  have ht_nonadj_p1 : ¬G.Adj t p1 := by
    intro h
    have h_witness : t ∈ G.neighborFinset v ∧ G.Adj t p1 := ⟨ht_in_N, h⟩
    have h_eq : t = s1 := hs1_unique t h_witness
    exact ht_ne_s1 h_eq

  have ht_nonadj_p2 : ¬G.Adj t p2 := by
    intro h
    have h_witness : t ∈ G.neighborFinset v ∧ G.Adj t p2 := ⟨ht_in_N, h⟩
    exact ht_ne_s2 (hs2_unique t h_witness)

  have ht_nonadj_p3 : ¬G.Adj t p3 := by
    intro h
    have h_witness : t ∈ G.neighborFinset v ∧ G.Adj t p3 := ⟨ht_in_N, h⟩
    exact ht_ne_s3 (hs3_unique t h_witness)

  have ht_nonadj_p4 : ¬G.Adj t p4 := by
    intro h
    have h_witness : t ∈ G.neighborFinset v ∧ G.Adj t p4 := ⟨ht_in_N, h⟩
    exact ht_ne_s4 (hs4_unique t h_witness)

  -- |T| = 4 (t has 4 Q-neighbors)
  have hT_card : T.card = 4 := by
    -- Use t_has_four_Q_neighbors
    have ⟨hP_complete, hQ_complete⟩ := PQ_partition_completeness h_reg h_tri h_no6 v P Q
        hP_card hQ_card hP_props hQ_props
    have hv_notin_Q : v ∉ Q := by
      intro hv
      have ⟨_, h_common2⟩ := hQ_props v hv
      have h_common5 : commonNeighborsCard G v v = 5 := by
        unfold commonNeighborsCard _root_.commonNeighbors
        rw [Finset.inter_self]
        exact h_reg v
      omega
    exact t_has_four_Q_neighbors h_reg h_tri h_no6 v t ht_adj_v Q hQ_card
      (by
        intro hv
        have ⟨_, h_common2⟩ := hQ_props v hv
        have h_common5 : commonNeighborsCard G v v = 5 := by
          unfold commonNeighborsCard _root_.commonNeighbors
          rw [Finset.inter_self]
          exact h_reg v
        omega)
      (fun x hx hxv hx2 => hQ_complete x hxv hx hx2)
      P hP_card hP_props
      (by
        intro p hp
        rw [hP_eq, mem_insert, mem_insert, mem_insert, mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact ht_nonadj_p1
        · exact ht_nonadj_p2
        · exact ht_nonadj_p3
        · exact ht_nonadj_p4)
      (fun x hxv hx_nadj => ⟨hP_complete x hxv hx_nadj, hQ_complete x hxv hx_nadj⟩)

  have hW_card : W.card = 4 := by
    have h_sum : T.card + W.card = Q.card := by
      rw [← hTW_union, card_union_of_disjoint hTW_disj]
    omega

  -- W membership characterization (analogous to hW_def in other lemmas)
  have ⟨_, hQ_complete'⟩ := PQ_partition_completeness h_reg h_tri h_no6 v P Q
      hP_card hQ_card hP_props hQ_props
  have hW_props : ∀ x, x ∈ W ↔ ¬G.Adj v x ∧ commonNeighborsCard G v x = 2 ∧ ¬G.Adj t x := by
    intro x
    constructor
    · intro hx_in_W
      have hx_in_Q : x ∈ Q := (mem_filter.mp hx_in_W).1
      have hx_nonadj_t : ¬G.Adj t x := (mem_filter.mp hx_in_W).2
      have ⟨hv_nonadj, h_common2⟩ := hQ_props x hx_in_Q
      exact ⟨hv_nonadj, h_common2, hx_nonadj_t⟩
    · intro ⟨hx_nonadj_v, hx_common2, hx_nonadj_t⟩
      rw [mem_filter]
      constructor
      · -- x ∈ Q: need x not adj v and commonNeighborsCard = 2
        have hx_ne_v : x ≠ v := by
          intro h_eq
          -- If x = v, then commonNeighborsCard G v x = commonNeighborsCard G v v = 5
          have : commonNeighborsCard G v x = 5 := by
            rw [h_eq]; unfold commonNeighborsCard _root_.commonNeighbors
            rw [Finset.inter_self]; exact h_reg v
          omega  -- 5 = 2 is a contradiction with hx_common2
        exact hQ_complete' x hx_ne_v hx_nonadj_v hx_common2
      · exact hx_nonadj_t

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 5a: T is independent (neighbors of t in triangle-free graph)
  -- ═══════════════════════════════════════════════════════════════════════════
  have hT_indep : G.IsIndepSet T := by
    intro ti hti tj htj hne h_adj
    -- ti, tj both adjacent to t, and ti ~ tj
    -- Then {t, ti, tj} is a triangle, contradicting h_tri
    have hti_adj_t : G.Adj t ti := (mem_filter.mp hti).2
    have htj_adj_t : G.Adj t tj := (mem_filter.mp htj).2
    have h_clique : G.IsNClique 3 {t, ti, tj} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro a ha b hb hab
        simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact absurd rfl hab
        · exact hti_adj_t
        · exact htj_adj_t
        · exact G.symm hti_adj_t
        · exact absurd rfl hab
        · exact h_adj
        · exact G.symm htj_adj_t
        · exact G.symm h_adj
        · exact absurd rfl hab
      · rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        · simp only [mem_singleton]; exact hne
        · simp only [mem_insert, mem_singleton, not_or]
          exact ⟨G.ne_of_adj hti_adj_t, G.ne_of_adj htj_adj_t⟩
    exact h_tri _ h_clique

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 5b: Each p ∈ P has exactly 1 T-neighbor and exactly 1 W-neighbor
  -- This is the P-T/P-W perfect matching property, crucial for the final step.
  --
  -- Proof sketch:
  -- a) Each p has ≥1 T-neighbor: if p had 0, then {v, p} ∪ T is 6 independent
  --    - v not adj to p (p ∈ P = non-neighbors of v)
  --    - v not adj to ti (ti ∈ Q = non-neighbors of v)
  --    - p not adj to ti (by assumption)
  --    - ti not adj to tj (T independent from Step 5a)
  -- b) Each p has ≤1 T-neighbor: uses double-counting
  --    - Each ti ∈ T has degree 5 with 1 neighbor t, 2 S-neighbors, so ≤2 P-neighbors
  --    - Actually stronger: each ti has exactly 1 S-neighbor (by t_vertex_has_one_S_neighbor)
  --    - So each ti has at most 5-1-1-2 = 1 P-neighbor? No, let's count differently.
  --    - Sum over T of |P-neighbors| ≤ |T| * max_deg_to_P ≤ 4 * 1 = 4
  --    - Sum over P of |T-neighbors| = Sum over T of |P-neighbors| ≤ 4
  --    - So average |T-neighbors| per p ≤ 1. With each p ≥ 1, each must be exactly 1.
  -- c) Since each p has 2 Q-neighbors (degree - 2 P-neighbors - 1 N(v)-neighbor)
  --    and Q = T ∪ W disjoint, 1 T-neighbor + 1 W-neighbor = 2.
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Each p ∈ P has at least 1 T-neighbor (else 6-independent-set)
  have hp_has_T_neighbor : ∀ p ∈ P, (T.filter (G.Adj p)).Nonempty := by
    intro p hp
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty, ← Finset.card_eq_zero] at h_empty
    -- p has 0 T-neighbors
    -- Construct 6-independent-set: {v, p} ∪ T
    -- First get facts about p
    have ⟨hp_nonadj_v, hp_common1⟩ := hP_props p hp
    have hp_notin_T : p ∉ T := by
      simp only [T, mem_filter]
      intro ⟨hp_Q, _⟩
      have ⟨_, hp_common2⟩ := hQ_props p hp_Q
      omega
    have hv_notin_T : v ∉ T := by
      intro hv_T
      have ⟨hv_Q, _⟩ := mem_filter.mp hv_T
      have ⟨_, hv_common2⟩ := hQ_props v hv_Q
      -- commonNeighborsCard G v v = |N(v)| = 5 ≠ 2
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp only [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self,
                   G.card_neighborFinset_eq_degree, h_reg v]
      omega
    have hv_ne_p : v ≠ p := by
      intro h_eq
      -- If v = p, then common1 ≠ common5
      have hp_common5 : commonNeighborsCard G p p = 5 := by
        simp only [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self,
                   G.card_neighborFinset_eq_degree, h_reg p]
      rw [h_eq] at hp_common1
      omega
    have hp_no_T_nbr : ∀ ti ∈ T, ¬G.Adj p ti := by
      intro ti hti h_adj
      have hti_in_filter : ti ∈ T.filter (G.Adj p) := mem_filter.mpr ⟨hti, h_adj⟩
      rw [Finset.card_eq_zero] at h_empty
      exact Finset.notMem_empty ti (h_empty ▸ hti_in_filter)

    have h6IS : G.IsNIndepSet 6 ({v, p} ∪ T) := by
      rw [isNIndepSet_iff]
      constructor
      · -- Independence
        intro x hx y hy hne
        have hx : x ∈ ({v, p} ∪ T : Finset (Fin 18)) := by simpa using hx
        have hy : y ∈ ({v, p} ∪ T : Finset (Fin 18)) := by simpa using hy
        have hx' := Finset.mem_union.mp hx
        have hy' := Finset.mem_union.mp hy
        rcases hx' with hx_vp | hx_T
        · simp only [mem_insert, mem_singleton] at hx_vp
          rcases hx_vp with rfl | rfl
          · -- x = v
            rcases hy' with hy_vp | hy_T
            · simp only [mem_insert, mem_singleton] at hy_vp
              rcases hy_vp with rfl | rfl
              · exact absurd rfl hne
              · -- y = p: v not adj to p (p ∈ P)
                exact hp_nonadj_v
            · -- y ∈ T ⊆ Q: v not adj to y
              have ⟨hy_Q, _⟩ := mem_filter.mp hy_T
              have ⟨hy_nonadj_v, _⟩ := hQ_props y hy_Q
              exact hy_nonadj_v
          · -- x = p
            rcases hy' with hy_vp | hy_T
            · simp only [mem_insert, mem_singleton] at hy_vp
              rcases hy_vp with rfl | rfl
              · -- y = v
                exact fun h => hp_nonadj_v (G.symm h)
              · exact absurd rfl hne
            · -- y ∈ T: p not adj to y (by assumption h_empty)
              exact hp_no_T_nbr y hy_T
        · -- x ∈ T
          rcases hy' with hy_vp | hy_T
          · simp only [mem_insert, mem_singleton] at hy_vp
            rcases hy_vp with rfl | rfl
            · -- y = v
              have ⟨hx_Q, _⟩ := mem_filter.mp hx_T
              have ⟨hx_nonadj_v, _⟩ := hQ_props x hx_Q
              exact fun h => hx_nonadj_v (G.symm h)
            · -- y = p
              exact fun h => hp_no_T_nbr x hx_T (G.symm h)
          · -- x, y ∈ T: use T-independence
            exact hT_indep hx_T hy_T hne
      · -- Card = 6
        have hvp_disj_T : Disjoint ({v, p} : Finset (Fin 18)) T := by
          rw [Finset.disjoint_iff_ne]
          intro a ha b hb h_eq
          simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hv_notin_T (h_eq ▸ hb)
          · exact hp_notin_T (h_eq ▸ hb)
        rw [card_union_of_disjoint hvp_disj_T, card_insert_of_notMem, card_singleton, hT_card]
        simp only [mem_singleton]; exact hv_ne_p
    exact h_no6 _ h6IS

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 5c: Each p ∈ P has exactly 1 T-neighbor (P-T perfect matching)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Proof: We know each p has ≥1 T-neighbor (from hp_has_T_neighbor).
  -- To show each has exactly 1, we use double-counting:
  --   Sum over P of |T-neighbors| = Sum over T of |P-neighbors|
  -- Left side ≥ 4 (since each of 4 p's has ≥1 T-neighbor).
  -- For right side: each ti ∈ T has degree 5 with neighbors:
  --   - t (1 neighbor in N(v))
  --   - exactly 1 sj ∈ S (from t_vertex_has_one_S_neighbor)
  --   - ti ∈ Q, so ti not adj to v
  --   - remaining 3 neighbors in P ∪ W
  -- Key: P and T are both independent sets.
  -- If ti had ≥2 P-neighbors, say p_i, p_j, then t-ti-p_i and t-ti-p_j share ti.
  -- But this doesn't directly give a contradiction...
  --
  -- Alternative argument: Consider the T-to-P bipartite edges.
  -- - |T| = 4, |P| = 4
  -- - Each ti ∈ T has exactly 1 S-neighbor (t_vertex_has_one_S_neighbor)
  -- - ti's neighbors: t (1), some sj (1), and 3 more in P ∪ W ∪ other Q
  -- - But ti ∈ Q means ti not adj v, and ti not adj any other tk ∈ T (T indep)
  -- - So ti's 3 remaining neighbors are in P ∪ W
  --
  -- Actually, the counting argument is:
  -- - Total P-T edges = Sum over T of |P ∩ N(ti)| = Sum over P of |T ∩ N(pj)|
  -- - Right side ≥ 4 (each pj has ≥1 T-neighbor)
  -- - Left side: each ti has at most (5 - 1 - 1) = 3 neighbors outside {t, si}
  --   where si is ti's unique S-neighbor
  -- - But we need ti's P-neighbors specifically...
  --
  -- KEY INSIGHT: If any p has ≥2 T-neighbors, then the sum ≥ 2 + 3*1 = 5.
  -- But sum = |P-T edges|. We need to show |P-T edges| ≤ 4.
  --
  -- CLAIM: |P-T edges| ≤ 4.
  -- Proof: Each ti ∈ T has exactly 2 common neighbors with v (ti ∈ Q).
  -- Those 2 are in N(v) = {t, s1, s2, s3, s4}. Since ti ~ t, the other is some sj.
  -- For any p ∈ P with ti ~ p: sj would need to be p's S-partner (else triangle).
  -- But wait, if p ~ ti and sj ~ ti and sj ~ p, we need sj = sp (p's partner).
  -- Since each p has unique S-partner, and |S| = 4, |P| = 4, |T| = 4,
  -- and each ti has exactly 1 S-neighbor, the mapping ti → si is bijective.
  -- Therefore each ti's P-neighbor (if any) must have si as its S-partner.
  -- Since each sp has exactly 1 p, and each ti has 1 si, |P-T edges| = 4.
  --
  -- This proves each p has exactly 1 T-neighbor.
  -- (The formal proof requires the detailed bijection argument above)

  -- ═══════════════════════════════════════════════════════════════════════════
  -- BIPARTITE EDGE COUNTING LEMMA (Double Counting / Handshake Lemma)
  -- Both sums count |E(P,T)| from different perspectives
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Step 3: Bipartite edge count equality
  have bipartite_edge_count_eq :
      P.sum (fun p => (T.filter (G.Adj p)).card) =
      T.sum (fun ti => (P.filter (G.Adj ti)).card) := by
    classical
    -- Use existing bipartite_edge_count_symmetry lemma (line 109)
    -- It proves: ∑ a ∈ A, (B.filter (R a)).card = ∑ b ∈ B, (A.filter (R b)).card
    -- Specialize with A := P, B := T, R := G.Adj, hR := G.symm
    simpa using
      (bipartite_edge_count_symmetry
        (A := P) (B := T)
        (R := G.Adj)
        (hR := G.symm))

  -- Note: A full proof that `P`–`T` edges form a perfect matching is not needed to
  -- construct `CariolaroSetup`; we only use the `S`–`W` structure below.

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 6: Extract t1, t2, t3, t4 from T and w1, w2, w3, w4 from W
  -- This requires showing the S-W bipartite structure is an 8-cycle and choosing
  -- the specific labeling. This is the most complex part of the construction.
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Define S = {s1, s2, s3, s4} (the s-partners, which is N(v) \ {t})
  let S := ({s1, s2, s3, s4} : Finset (Fin 18))

  -- S = N(v) \ {t}
  have hS_eq_erase : S = N.erase t := by
    ext x
    simp only [S, mem_insert, mem_singleton, mem_erase]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨ht_ne_s1.symm, hs1_in_N⟩
      · exact ⟨ht_ne_s2.symm, hs2_in_N⟩
      · exact ⟨ht_ne_s3.symm, hs3_in_N⟩
      · exact ⟨ht_ne_s4.symm, hs4_in_N⟩
    · intro ⟨hx_ne_t, hx_in_N⟩
      -- x ∈ N(v) and x ≠ t means x ∈ {s1, s2, s3, s4}
      -- Key: |N| = 5, |S| = 4, S ⊆ N, so N \ S = {t}
      have hS_card : S.card = 4 := by
        have h1 : s4 ∉ (∅ : Finset (Fin 18)) := Finset.notMem_empty s4
        have h2 : s3 ∉ ({s4} : Finset (Fin 18)) := by
          simp only [mem_singleton]; exact hs_ne34
        have h3 : s2 ∉ ({s3, s4} : Finset (Fin 18)) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hs_ne23, hs_ne24⟩
        have h4 : s1 ∉ ({s2, s3, s4} : Finset (Fin 18)) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hs_ne12, hs_ne13, hs_ne14⟩
        simp only [S, card_insert_of_notMem h4, card_insert_of_notMem h3,
                   card_insert_of_notMem h2, card_singleton]
      have hS_sub_N : S ⊆ N := by
        intro y hy
        simp only [S, mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hs1_in_N
        · exact hs2_in_N
        · exact hs3_in_N
        · exact hs4_in_N
      have h_diff_card : (N \ S).card = 1 := by
        rw [Finset.card_sdiff_of_subset hS_sub_N, hN_card, hS_card]
      have ht_in_diff : t ∈ N \ S := by
        simp only [mem_sdiff, S, mem_insert, mem_singleton, not_or]
        exact ⟨ht_in_N, ht_ne_s1, ht_ne_s2, ht_ne_s3, ht_ne_s4⟩
      have h_diff_single : N \ S = {t} := by
        rw [Finset.card_eq_one] at h_diff_card
        obtain ⟨z, hz⟩ := h_diff_card
        rw [hz] at ht_in_diff
        simp only [mem_singleton] at ht_in_diff
        rw [hz, ← ht_in_diff]
      -- x ∉ N \ S (since N \ S = {t} and x ≠ t)
      have hx_notin_diff : x ∉ N \ S := by
        rw [h_diff_single]
        simp only [mem_singleton]
        exact hx_ne_t
      -- So x ∈ S
      rw [mem_sdiff, not_and_or, not_not] at hx_notin_diff
      rcases hx_notin_diff with hx_notin_N | hx_in_S
      · exact (hx_notin_N hx_in_N).elim
      · simp only [S, mem_insert, mem_singleton] at hx_in_S
        exact hx_in_S

  -- STEP 6a: Extract t1, t2, t3, t4 from T
  -- T has 4 elements, so we can extract them
  have hT_nonempty : T.Nonempty := card_pos.mp (by omega : 0 < T.card)
  obtain ⟨t1, ht1_mem⟩ := hT_nonempty

  have hT_erase1 : (T.erase t1).card = 3 := by rw [card_erase_of_mem ht1_mem, hT_card]
  have hT_nonempty2 : (T.erase t1).Nonempty := card_pos.mp (by omega)
  obtain ⟨t2, ht2_mem⟩ := hT_nonempty2
  have ht2_in_T : t2 ∈ T := mem_of_mem_erase ht2_mem
  have ht1_ne_t2 : t1 ≠ t2 := fun h => (mem_erase.mp ht2_mem).1 h.symm

  have hT_erase2 : ((T.erase t1).erase t2).card = 2 := by rw [card_erase_of_mem ht2_mem, hT_erase1]
  have hT_nonempty3 : ((T.erase t1).erase t2).Nonempty := card_pos.mp (by omega)
  obtain ⟨t3, ht3_mem⟩ := hT_nonempty3
  have ht3_in_erase1 : t3 ∈ T.erase t1 := mem_of_mem_erase ht3_mem
  have ht3_in_T : t3 ∈ T := mem_of_mem_erase ht3_in_erase1
  have ht2_ne_t3 : t2 ≠ t3 := fun h => (mem_erase.mp ht3_mem).1 h.symm
  have ht1_ne_t3 : t1 ≠ t3 := fun h => (mem_erase.mp ht3_in_erase1).1 h.symm

  have hT_erase3 : (((T.erase t1).erase t2).erase t3).card = 1 := by rw [card_erase_of_mem ht3_mem, hT_erase2]
  have hT_nonempty4 : (((T.erase t1).erase t2).erase t3).Nonempty := card_pos.mp (by omega)
  obtain ⟨t4, ht4_mem⟩ := hT_nonempty4
  have ht4_in_erase2 : t4 ∈ (T.erase t1).erase t2 := mem_of_mem_erase ht4_mem
  have ht4_in_erase1 : t4 ∈ T.erase t1 := mem_of_mem_erase ht4_in_erase2
  have ht4_in_T : t4 ∈ T := mem_of_mem_erase ht4_in_erase1
  have ht3_ne_t4 : t3 ≠ t4 := fun h => (mem_erase.mp ht4_mem).1 h.symm
  have ht2_ne_t4 : t2 ≠ t4 := fun h => (mem_erase.mp ht4_in_erase2).1 h.symm
  have ht1_ne_t4 : t1 ≠ t4 := fun h => (mem_erase.mp ht4_in_erase1).1 h.symm

  -- T properties from being in T
  have ht1_props : t1 ∈ Q ∧ G.Adj t t1 := by simp only [T, mem_filter] at ht1_mem; exact ht1_mem
  have ht2_props : t2 ∈ Q ∧ G.Adj t t2 := by simp only [T, mem_filter] at ht2_in_T; exact ht2_in_T
  have ht3_props : t3 ∈ Q ∧ G.Adj t t3 := by simp only [T, mem_filter] at ht3_in_T; exact ht3_in_T
  have ht4_props : t4 ∈ Q ∧ G.Adj t t4 := by simp only [T, mem_filter] at ht4_in_T; exact ht4_in_T

  -- Q properties for ti
  have ht1_Q_props := hQ_props t1 ht1_props.1
  have ht2_Q_props := hQ_props t2 ht2_props.1
  have ht3_Q_props := hQ_props t3 ht3_props.1
  have ht4_Q_props := hQ_props t4 ht4_props.1

  -- STEP 6b: Extract w1, w2, w3, w4 from W
  have hW_nonempty : W.Nonempty := card_pos.mp (by omega : 0 < W.card)
  obtain ⟨w1, hw1_mem⟩ := hW_nonempty

  have hW_erase1 : (W.erase w1).card = 3 := by rw [card_erase_of_mem hw1_mem, hW_card]
  have hW_nonempty2 : (W.erase w1).Nonempty := card_pos.mp (by omega)
  obtain ⟨w2, hw2_mem⟩ := hW_nonempty2
  have hw2_in_W : w2 ∈ W := mem_of_mem_erase hw2_mem
  have hw1_ne_w2 : w1 ≠ w2 := fun h => (mem_erase.mp hw2_mem).1 h.symm

  have hW_erase2 : ((W.erase w1).erase w2).card = 2 := by rw [card_erase_of_mem hw2_mem, hW_erase1]
  have hW_nonempty3 : ((W.erase w1).erase w2).Nonempty := card_pos.mp (by omega)
  obtain ⟨w3, hw3_mem⟩ := hW_nonempty3
  have hw3_in_erase1 : w3 ∈ W.erase w1 := mem_of_mem_erase hw3_mem
  have hw3_in_W : w3 ∈ W := mem_of_mem_erase hw3_in_erase1
  have hw2_ne_w3 : w2 ≠ w3 := fun h => (mem_erase.mp hw3_mem).1 h.symm
  have hw1_ne_w3 : w1 ≠ w3 := fun h => (mem_erase.mp hw3_in_erase1).1 h.symm

  have hW_erase3 : (((W.erase w1).erase w2).erase w3).card = 1 := by rw [card_erase_of_mem hw3_mem, hW_erase2]
  have hW_nonempty4 : (((W.erase w1).erase w2).erase w3).Nonempty := card_pos.mp (by omega)
  obtain ⟨w4, hw4_mem⟩ := hW_nonempty4
  have hw4_in_erase2 : w4 ∈ (W.erase w1).erase w2 := mem_of_mem_erase hw4_mem
  have hw4_in_erase1 : w4 ∈ W.erase w1 := mem_of_mem_erase hw4_in_erase2
  have hw4_in_W : w4 ∈ W := mem_of_mem_erase hw4_in_erase1
  have hw3_ne_w4 : w3 ≠ w4 := fun h => (mem_erase.mp hw4_mem).1 h.symm
  have hw2_ne_w4 : w2 ≠ w4 := fun h => (mem_erase.mp hw4_in_erase2).1 h.symm
  have hw1_ne_w4 : w1 ≠ w4 := fun h => (mem_erase.mp hw4_in_erase1).1 h.symm

  -- W properties from being in W
  have hw1_props : w1 ∈ Q ∧ ¬G.Adj t w1 := by simp only [W, mem_filter] at hw1_mem; exact hw1_mem
  have hw2_props : w2 ∈ Q ∧ ¬G.Adj t w2 := by simp only [W, mem_filter] at hw2_in_W; exact hw2_in_W
  have hw3_props : w3 ∈ Q ∧ ¬G.Adj t w3 := by simp only [W, mem_filter] at hw3_in_W; exact hw3_in_W
  have hw4_props : w4 ∈ Q ∧ ¬G.Adj t w4 := by simp only [W, mem_filter] at hw4_in_W; exact hw4_in_W

  -- Q properties for wi
  have hw1_Q_props := hQ_props w1 hw1_props.1
  have hw2_Q_props := hQ_props w2 hw2_props.1
  have hw3_Q_props := hQ_props w3 hw3_props.1
  have hw4_Q_props := hQ_props w4 hw4_props.1

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 6c: Prove each s has exactly 2 W-neighbors
  --
  -- Key insight: If some s has 3 W-neighbors, its P-partner would have 3 P-neighbors
  -- (via p_adjacent_of_shared_w), contradicting the 4-cycle structure.
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Define S formally
  let S := ({s1, s2, s3, s4} : Finset (Fin 18))

  have hS_card : S.card = 4 := by
    have h1 : s4 ∉ (∅ : Finset (Fin 18)) := Finset.notMem_empty s4
    have h2 : s3 ∉ ({s4} : Finset (Fin 18)) := by simp only [mem_singleton]; exact hs_ne34
    have h3 : s2 ∉ ({s3, s4} : Finset (Fin 18)) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne23, hs_ne24⟩
    have h4 : s1 ∉ ({s2, s3, s4} : Finset (Fin 18)) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne12, hs_ne13, hs_ne14⟩
    simp only [S, card_insert_of_notMem h4, card_insert_of_notMem h3,
               card_insert_of_notMem h2, card_singleton]

  have hs1_in_S : s1 ∈ S := by simp only [S, mem_insert, mem_singleton, true_or]
  have hs2_in_S : s2 ∈ S := by simp only [S, mem_insert, mem_singleton, true_or, or_true]
  have hs3_in_S : s3 ∈ S := by simp only [S, mem_insert, mem_singleton, true_or, or_true]
  have hs4_in_S : s4 ∈ S := by simp only [S, mem_insert, mem_singleton, or_true]

  -- S = N(v) \ {t}
  have hS_eq : S = N.erase t := by
    ext x
    simp only [S, mem_insert, mem_singleton, mem_erase]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨ht_ne_s1.symm, hs1_in_N⟩
      · exact ⟨ht_ne_s2.symm, hs2_in_N⟩
      · exact ⟨ht_ne_s3.symm, hs3_in_N⟩
      · exact ⟨ht_ne_s4.symm, hs4_in_N⟩
    · intro ⟨hx_ne_t, hx_in_N⟩
      -- x ∈ N(v) and x ≠ t, so x must be one of s1, s2, s3, s4
      -- The goal after simp is: x = s1 ∨ x = s2 ∨ x = s3 ∨ x = s4
      have hS_sub_N : S ⊆ N := by
        intro y hy
        simp only [S, mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> assumption
      have h_diff_card : (N \ S).card = 1 := by
        rw [Finset.card_sdiff_of_subset hS_sub_N, hN_card, hS_card]
      have ht_in_diff : t ∈ N \ S := by
        rw [mem_sdiff]
        constructor
        · exact ht_in_N
        · simp only [S, mem_insert, mem_singleton, not_or]
          exact ⟨ht_ne_s1, ht_ne_s2, ht_ne_s3, ht_ne_s4⟩
      have h_diff_single : N \ S = {t} := by
        rw [Finset.card_eq_one] at h_diff_card
        obtain ⟨z, hz⟩ := h_diff_card
        rw [hz] at ht_in_diff
        simp only [mem_singleton] at ht_in_diff
        rw [hz, ← ht_in_diff]
      have hx_notin_diff : x ∉ N \ S := by
        rw [h_diff_single]; simp only [mem_singleton]; exact hx_ne_t
      -- Need to show x ∈ S. By contradiction, if x ∉ S, then x ∈ N \ S = {t}
      -- But x ≠ t, contradiction.
      by_contra h_not_in_S'
      have hx_in_S_false : x ∉ S := by
        simp only [S, mem_insert, mem_singleton, not_or] at h_not_in_S' ⊢
        push_neg
        exact h_not_in_S'
      have hx_in_diff : x ∈ N \ S := mem_sdiff.mpr ⟨hx_in_N, hx_in_S_false⟩
      exact hx_notin_diff hx_in_diff

  -- Each W has exactly 2 S-neighbors
  have hW_S_neighbors : ∀ wi ∈ W, (S.filter (G.Adj wi)).card = 2 := by
    intro wi hwi
    have hwi_props := (hW_props wi).mp hwi
    exact W_vertex_has_two_S_neighbors h_tri v t wi ht_adj_v hwi_props.2.2 hwi_props.2.1 S hS_card hS_eq

  -- Uniqueness for S-partners (si not adjacent to pj for i ≠ j)
  -- h*_unique : ∀ x, x ∈ N → x ≠ s* → ¬G.Adj x p*
  -- So to prove s1 not adj p2, we use h2_unique with s1 ≠ s2
  have hs1_nonadj_p2 : ¬G.Adj s1 p2 := h2_unique s1 hs1_in_N hs_ne12
  have hs1_nonadj_p3 : ¬G.Adj s1 p3 := h3_unique s1 hs1_in_N hs_ne13
  have hs1_nonadj_p4 : ¬G.Adj s1 p4 := h4_unique s1 hs1_in_N hs_ne14
  have hs2_nonadj_p1 : ¬G.Adj s2 p1 := h1_unique s2 hs2_in_N hs_ne12.symm
  have hs2_nonadj_p3 : ¬G.Adj s2 p3 := h3_unique s2 hs2_in_N hs_ne23
  have hs2_nonadj_p4 : ¬G.Adj s2 p4 := h4_unique s2 hs2_in_N hs_ne24
  have hs3_nonadj_p1 : ¬G.Adj s3 p1 := h1_unique s3 hs3_in_N hs_ne13.symm
  have hs3_nonadj_p2 : ¬G.Adj s3 p2 := h2_unique s3 hs3_in_N hs_ne23.symm
  have hs3_nonadj_p4 : ¬G.Adj s3 p4 := h4_unique s3 hs3_in_N hs_ne34
  have hs4_nonadj_p1 : ¬G.Adj s4 p1 := h1_unique s4 hs4_in_N hs_ne14.symm
  have hs4_nonadj_p2 : ¬G.Adj s4 p2 := h2_unique s4 hs4_in_N hs_ne24.symm
  have hs4_nonadj_p3 : ¬G.Adj s4 p3 := h3_unique s4 hs4_in_N hs_ne34.symm

  -- t is not adjacent to any w ∈ W (by definition of W)
  have ht_nonadj_w : ∀ wi ∈ W, ¬G.Adj t wi := by
    intro wi hwi
    exact (hW_props wi).mp hwi |>.2.2

  -- N(v) is independent (triangle-free)
  have hN_indep_pairs : ∀ sa sb, sa ∈ N → sb ∈ N → sa ≠ sb → ¬G.Adj sa sb := by
    intro sa sb hsa hsb hne
    have h_set : sa ∈ G.neighborSet v := by rw [mem_neighborFinset] at hsa; exact hsa
    have h_set' : sb ∈ G.neighborSet v := by rw [mem_neighborFinset] at hsb; exact hsb
    exact hN_indep h_set h_set' hne

  -- Key lemma: If si shares a W-neighbor with sj, then pi and pj are adjacent
  -- (This follows from p_adjacent_of_shared_w once we establish the prerequisites)

  -- CRITICAL: Prove each si has ≤ 2 W-neighbors
  -- Suppose s1 has 3 W-neighbors. Then s1 shares a W with s2, s3, and s4.
  -- By p_adjacent_of_shared_w, p1 would be adjacent to p2, p3, p4.
  -- But in a 4-cycle, p1 has exactly 2 neighbors (p2 and p4), not 3.
  -- Contradiction!

  have hs1_W_le2 : (W.filter (G.Adj s1)).card ≤ 2 := by
    -- Proof by contradiction using S_pair_share_at_most_one_W and p_adjacent_of_shared_w
    -- If s1 has ≥3 W-neighbors, extract wa, wb, wc. Each has 2 S-neighbors (one is s1).
    -- The "other" neighbors oa, ob, oc are in {s2, s3, s4}.
    -- Pigeonhole: collision → S_pair_share_at_most_one_W; bijective → one is s3 → p1~p3.
    by_contra h_ge3
    push_neg at h_ge3
    obtain ⟨wa, wb, wc, hwa_mem, hwb_mem, hwc_mem, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp h_ge3
    simp only [Finset.mem_filter] at hwa_mem hwb_mem hwc_mem
    -- Each wi has exactly 2 S-neighbors
    have hwa_S := hW_S_neighbors wa hwa_mem.1
    have hwb_S := hW_S_neighbors wb hwb_mem.1
    have hwc_S := hW_S_neighbors wc hwc_mem.1
    -- s1 is one of each wi's S-neighbors
    have hs1_wa : s1 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwa_mem.2⟩
    have hs1_wb : s1 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwb_mem.2⟩
    have hs1_wc : s1 ∈ S.filter (G.Adj wc) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwc_mem.2⟩
    -- Each "other" set has cardinality 1
    have hwa_other : ((S.filter (G.Adj wa)).erase s1).card = 1 := by
      rw [Finset.card_erase_of_mem hs1_wa, hwa_S]
    have hwb_other : ((S.filter (G.Adj wb)).erase s1).card = 1 := by
      rw [Finset.card_erase_of_mem hs1_wb, hwb_S]
    have hwc_other : ((S.filter (G.Adj wc)).erase s1).card = 1 := by
      rw [Finset.card_erase_of_mem hs1_wc, hwc_S]
    -- Extract the "other" S-neighbors
    obtain ⟨oa, hoa_eq⟩ := Finset.card_eq_one.mp hwa_other
    obtain ⟨ob, hob_eq⟩ := Finset.card_eq_one.mp hwb_other
    obtain ⟨oc, hoc_eq⟩ := Finset.card_eq_one.mp hwc_other
    -- Get membership properties
    have hoa_mem : oa ∈ (S.filter (G.Adj wa)).erase s1 := by rw [hoa_eq]; exact Finset.mem_singleton_self _
    have hob_mem : ob ∈ (S.filter (G.Adj wb)).erase s1 := by rw [hob_eq]; exact Finset.mem_singleton_self _
    have hoc_mem : oc ∈ (S.filter (G.Adj wc)).erase s1 := by rw [hoc_eq]; exact Finset.mem_singleton_self _
    simp only [Finset.mem_erase, Finset.mem_filter] at hoa_mem hob_mem hoc_mem
    -- Key facts
    have hoa_ne_s1 : oa ≠ s1 := hoa_mem.1
    have hob_ne_s1 : ob ≠ s1 := hob_mem.1
    have hoc_ne_s1 : oc ≠ s1 := hoc_mem.1
    have hoa_in_S : oa ∈ S := hoa_mem.2.1
    have hob_in_S : ob ∈ S := hob_mem.2.1
    have hoc_in_S : oc ∈ S := hoc_mem.2.1
    have hwa_oa : G.Adj wa oa := hoa_mem.2.2
    have hwb_ob : G.Adj wb ob := hob_mem.2.2
    have hwc_oc : G.Adj wc oc := hoc_mem.2.2
    -- v adjacencies
    have hs1_adj_v : G.Adj v s1 := by rw [← SimpleGraph.mem_neighborFinset]; exact hs1_in_N
    have hoa_adj_v : G.Adj v oa := by
      rw [hS_eq] at hoa_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoa_in_S).2
    have hob_adj_v : G.Adj v ob := by
      rw [hS_eq] at hob_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hob_in_S).2
    have hoc_adj_v : G.Adj v oc := by
      rw [hS_eq] at hoc_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoc_in_S).2
    -- W vertices are non-neighbors of v
    have hwa_Q := (hW_props wa).mp hwa_mem.1
    have hwb_Q := (hW_props wb).mp hwb_mem.1
    have hwc_Q := (hW_props wc).mp hwc_mem.1
    -- Prove v ≠ wa,wb,wc via commonNeighborsCard contradiction (5 ≠ 2)
    have hv_ne_wa : v ≠ wa := by
      intro h_eq
      have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wa).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
      omega
    have hv_ne_wb : v ≠ wb := by
      intro h_eq
      have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wb).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
      omega
    have hv_ne_wc : v ≠ wc := by
      intro h_eq
      have h_common : commonNeighborsCard G v wc = 2 := hwc_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wc).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wc
      omega
    -- Pigeonhole: check if any two "other" S-neighbors are equal
    by_cases h_ab : oa = ob
    · -- oa = ob: s1 and oa share wa and wb → S_pair_share_at_most_one_W
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 oa wa wb
        hs1_adj_v hoa_adj_v hoa_ne_s1.symm hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 (G.symm hwa_oa) (h_ab ▸ G.symm hwb_ob)
    · by_cases h_ac : oa = oc
      · -- oa = oc: s1 and oa share wa and wc → S_pair_share_at_most_one_W
        exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 oa wa wc
          hs1_adj_v hoa_adj_v hoa_ne_s1.symm hv_ne_wa hv_ne_wc hac
          hwa_mem.2 hwc_mem.2 (G.symm hwa_oa) (h_ac ▸ G.symm hwc_oc)
      · by_cases h_bc : ob = oc
        · -- ob = oc: s1 and ob share wb and wc → S_pair_share_at_most_one_W
          exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 ob wb wc
            hs1_adj_v hob_adj_v hob_ne_s1.symm hv_ne_wb hv_ne_wc hbc
            hwb_mem.2 hwc_mem.2 (G.symm hwb_ob) (h_bc ▸ G.symm hwc_oc)
        · -- Bijective case: oa, ob, oc all distinct in {s2, s3, s4}
            -- Since {oa, ob, oc} ⊆ {s2, s3, s4} are all distinct, one must be s3
            -- Then w shares s1 and s3, so p_adjacent_of_shared_w gives p1 ~ p3
            -- This contradicts h_nonadj_p1p3
            -- Key insight: collision cases are handled above; bijective case uses p_adjacent_of_shared_w
            -- TODO: Avoid rfl patterns to prevent variable shadowing; use explicit hypotheses h_oa_s* instead
            have hoa_cases : oa = s2 ∨ oa = s3 ∨ oa = s4 := by
              have h' : oa = s1 ∨ oa = s2 ∨ oa = s3 ∨ oa = s4 := by simpa [S] using hoa_in_S
              rcases h' with h | h | h | h
              · exact (hoa_ne_s1 h).elim
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
            have hob_cases : ob = s2 ∨ ob = s3 ∨ ob = s4 := by
              have h' : ob = s1 ∨ ob = s2 ∨ ob = s3 ∨ ob = s4 := by simpa [S] using hob_in_S
              rcases h' with h | h | h | h
              · exact (hob_ne_s1 h).elim
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
            have hoc_cases : oc = s2 ∨ oc = s3 ∨ oc = s4 := by
              have h' : oc = s1 ∨ oc = s2 ∨ oc = s3 ∨ oc = s4 := by simpa [S] using hoc_in_S
              rcases h' with h | h | h | h
              · exact (hoc_ne_s1 h).elim
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)

            have h_some_s3 : oa = s3 ∨ ob = s3 ∨ oc = s3 := by
              by_contra h_none
              push_neg at h_none
              have hoa_24 : oa = s2 ∨ oa = s4 := by
                rcases hoa_cases with h2 | h3 | h4
                · exact Or.inl h2
                · exact (h_none.1 h3).elim
                · exact Or.inr h4
              have hob_24 : ob = s2 ∨ ob = s4 := by
                rcases hob_cases with h2 | h3 | h4
                · exact Or.inl h2
                · exact (h_none.2.1 h3).elim
                · exact Or.inr h4
              have hoc_24 : oc = s2 ∨ oc = s4 := by
                rcases hoc_cases with h2 | h3 | h4
                · exact Or.inl h2
                · exact (h_none.2.2 h3).elim
                · exact Or.inr h4

              let O : Finset (Fin 18) := ({oa, ob, oc} : Finset (Fin 18))
              have hO_card : O.card = 3 := by
                have hoa_not : oa ∉ insert ob ({oc} : Finset (Fin 18)) := by
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨h_ab, h_ac⟩
                have hob_not : ob ∉ ({oc} : Finset (Fin 18)) := by
                  simp only [Finset.mem_singleton]
                  exact h_bc
                simp [O, hoa_not, hob_not]
              have hO_sub : O ⊆ ({s2, s4} : Finset (Fin 18)) := by
                intro x hx
                simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · rcases hoa_24 with h2 | h4
                  · simp [h2]
                  · simp [h4]
                · rcases hob_24 with h2 | h4
                  · simp [h2]
                  · simp [h4]
                · rcases hoc_24 with h2 | h4
                  · simp [h2]
                  · simp [h4]
              have h_le := Finset.card_le_card hO_sub
              have h24 : ({s2, s4} : Finset (Fin 18)).card = 2 := by
                simp [hs_ne24]
              omega

            have contra_of_shared_w (w : Fin 18) (hwW : w ∈ W)
                (hw_adj_s1 : G.Adj w s1) (hw_adj_s3 : G.Adj w s3) :
                False := by
              have hw_Q := (hW_props w).mp hwW
              have hw_nonadj_v : ¬G.Adj w v := fun h => hw_Q.1 (G.symm h)
              have hw_nonadj_t : ¬G.Adj t w := fun h => hw_Q.2.2 h
              -- w is not adjacent to p1/p3 (else triangle with s1/s3)
              have hw_nonadj_p1 : ¬G.Adj w p1 := by
                intro h_adj
                have h_tri_set : G.IsNClique 3 {p1, s1, w} := by
                  constructor
                  · intro a ha b hb hab
                    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                    · exact absurd rfl hab
                    · exact G.symm hs1_adj_p1
                    · exact G.symm h_adj
                    · exact hs1_adj_p1
                    · exact absurd rfl hab
                    · exact G.symm hw_adj_s1
                    · exact h_adj
                    · exact hw_adj_s1
                    · exact absurd rfl hab
                  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                    · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s1).symm
                    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                      exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
                exact h_tri {p1, s1, w} h_tri_set
              have hw_nonadj_p3 : ¬G.Adj w p3 := by
                intro h_adj
                have h_tri_set : G.IsNClique 3 {p3, s3, w} := by
                  constructor
                  · intro a ha b hb hab
                    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                    · exact absurd rfl hab
                    · exact G.symm hs3_adj_p3
                    · exact G.symm h_adj
                    · exact hs3_adj_p3
                    · exact absurd rfl hab
                    · exact G.symm hw_adj_s3
                    · exact h_adj
                    · exact hw_adj_s3
                    · exact absurd rfl hab
                  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                    · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s3).symm
                    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                      exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
                exact h_tri {p3, s3, w} h_tri_set

              have hs1_s3_nonadj : ¬G.Adj s1 s3 :=
                hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13

              -- w has exactly 2 S-neighbors; since s1 and s3 are both neighbors, it cannot be adjacent to s2/s4
              have hw_S_card : (S.filter (G.Adj w)).card = 2 := hW_S_neighbors w hwW
              have hs2_nonadj_w : ¬G.Adj s2 w := by
                intro h_adj
                have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, hw_adj_s1⟩
                have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, hw_adj_s3⟩
                have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm h_adj⟩
                have h_three : ({s1, s3, s2} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl
                  · exact hs1_in_f
                  · exact hs3_in_f
                  · exact hs2_in_f
                have h_three_card : ({s1, s3, s2} : Finset (Fin 18)).card = 3 := by
                  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact hs_ne23.symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨hs_ne13, hs_ne12⟩
                have h_le := Finset.card_le_card h_three
                omega
              have hs4_nonadj_w : ¬G.Adj s4 w := by
                intro h_adj
                have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, hw_adj_s1⟩
                have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, hw_adj_s3⟩
                have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm h_adj⟩
                have h_three : ({s1, s3, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl
                  · exact hs1_in_f
                  · exact hs3_in_f
                  · exact hs4_in_f
                have h_three_card : ({s1, s3, s4} : Finset (Fin 18)).card = 3 := by
                  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact hs_ne34
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨hs_ne13, hs_ne14⟩
                have h_le := Finset.card_le_card h_three
                omega

              have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
                p1 p3 s1 s3 w
                hp1_nonadj_v hp3_nonadj_v hp_ne13
                (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
                hs1_adj_p1 hs3_adj_p3
                hs1_nonadj_p3 hs3_nonadj_p1
                hw_adj_s1 hw_adj_s3
                hw_nonadj_v hw_nonadj_p1 hw_nonadj_p3
                hs1_s3_nonadj
                t s2 s4
                ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
                ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
                ht_ne_s2 ht_ne_s4 hs_ne24
                (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) hw_nonadj_t
                hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_w
                hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_w
              exact h_nonadj_p1p3 h_p1_p3

            rcases h_some_s3 with h | h | h
            · -- oa = s3, so wa shares s1 and s3
              have hwa_adj_s3 : G.Adj wa s3 := by simpa [h] using hwa_oa
              exact contra_of_shared_w wa hwa_mem.1 (G.symm hwa_mem.2) hwa_adj_s3
            · -- ob = s3, so wb shares s1 and s3
              have hwb_adj_s3 : G.Adj wb s3 := by simpa [h] using hwb_ob
              exact contra_of_shared_w wb hwb_mem.1 (G.symm hwb_mem.2) hwb_adj_s3
            · -- oc = s3, so wc shares s1 and s3
              have hwc_adj_s3 : G.Adj wc s3 := by simpa [h] using hwc_oc
              exact contra_of_shared_w wc hwc_mem.1 (G.symm hwc_mem.2) hwc_adj_s3

  -- Similarly for s2 (same proof structure as s1)
  have hs2_W_le2 : (W.filter (G.Adj s2)).card ≤ 2 := by
    by_contra h_ge3
    push_neg at h_ge3
    obtain ⟨wa, wb, wc, hwa_mem, hwb_mem, hwc_mem, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp h_ge3
    simp only [Finset.mem_filter] at hwa_mem hwb_mem hwc_mem
    have hwa_S := hW_S_neighbors wa hwa_mem.1
    have hwb_S := hW_S_neighbors wb hwb_mem.1
    have hwc_S := hW_S_neighbors wc hwc_mem.1
    have hs2_wa : s2 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwa_mem.2⟩
    have hs2_wb : s2 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwb_mem.2⟩
    have hs2_wc : s2 ∈ S.filter (G.Adj wc) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwc_mem.2⟩
    have hwa_other : ((S.filter (G.Adj wa)).erase s2).card = 1 := by
      rw [Finset.card_erase_of_mem hs2_wa, hwa_S]
    have hwb_other : ((S.filter (G.Adj wb)).erase s2).card = 1 := by
      rw [Finset.card_erase_of_mem hs2_wb, hwb_S]
    have hwc_other : ((S.filter (G.Adj wc)).erase s2).card = 1 := by
      rw [Finset.card_erase_of_mem hs2_wc, hwc_S]
    obtain ⟨oa, hoa_eq⟩ := Finset.card_eq_one.mp hwa_other
    obtain ⟨ob, hob_eq⟩ := Finset.card_eq_one.mp hwb_other
    obtain ⟨oc, hoc_eq⟩ := Finset.card_eq_one.mp hwc_other
    have hoa_mem : oa ∈ (S.filter (G.Adj wa)).erase s2 := by rw [hoa_eq]; exact Finset.mem_singleton_self _
    have hob_mem : ob ∈ (S.filter (G.Adj wb)).erase s2 := by rw [hob_eq]; exact Finset.mem_singleton_self _
    have hoc_mem : oc ∈ (S.filter (G.Adj wc)).erase s2 := by rw [hoc_eq]; exact Finset.mem_singleton_self _
    simp only [Finset.mem_erase, Finset.mem_filter] at hoa_mem hob_mem hoc_mem
    have hoa_ne_s2 : oa ≠ s2 := hoa_mem.1
    have hob_ne_s2 : ob ≠ s2 := hob_mem.1
    have hoc_ne_s2 : oc ≠ s2 := hoc_mem.1
    have hoa_in_S : oa ∈ S := hoa_mem.2.1
    have hob_in_S : ob ∈ S := hob_mem.2.1
    have hoc_in_S : oc ∈ S := hoc_mem.2.1
    have hwa_oa : G.Adj wa oa := hoa_mem.2.2
    have hwb_ob : G.Adj wb ob := hob_mem.2.2
    have hwc_oc : G.Adj wc oc := hoc_mem.2.2
    have hs2_adj_v : G.Adj v s2 := by rw [← SimpleGraph.mem_neighborFinset]; exact hs2_in_N
    have hoa_adj_v : G.Adj v oa := by
      rw [hS_eq] at hoa_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoa_in_S).2
    have hob_adj_v : G.Adj v ob := by
      rw [hS_eq] at hob_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hob_in_S).2
    have hoc_adj_v : G.Adj v oc := by
      rw [hS_eq] at hoc_in_S
      rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoc_in_S).2
    have hwa_Q := (hW_props wa).mp hwa_mem.1
    have hwb_Q := (hW_props wb).mp hwb_mem.1
    have hwc_Q := (hW_props wc).mp hwc_mem.1
    have hv_ne_wa : v ≠ wa := by
      intro h_eq
      have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wa).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
      omega
    have hv_ne_wb : v ≠ wb := by
      intro h_eq
      have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wb).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
      omega
    have hv_ne_wc : v ≠ wc := by
      intro h_eq
      have h_common : commonNeighborsCard G v wc = 2 := hwc_Q.2.1
      rw [h_eq] at h_common
      unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wc).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wc
      omega
    by_cases h_ab : oa = ob
    · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s2 oa wa wb
        hs2_adj_v hoa_adj_v hoa_ne_s2.symm hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 (G.symm hwa_oa) (h_ab ▸ G.symm hwb_ob)
    · by_cases h_ac : oa = oc
      · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s2 oa wa wc
          hs2_adj_v hoa_adj_v hoa_ne_s2.symm hv_ne_wa hv_ne_wc hac
          hwa_mem.2 hwc_mem.2 (G.symm hwa_oa) (h_ac ▸ G.symm hwc_oc)
      · by_cases h_bc : ob = oc
        · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s2 ob wb wc
            hs2_adj_v hob_adj_v hob_ne_s2.symm hv_ne_wb hv_ne_wc hbc
            hwb_mem.2 hwc_mem.2 (G.symm hwb_ob) (h_bc ▸ G.symm hwc_oc)
        · -- Bijective case: oa, ob, oc all distinct in {s1, s3, s4}
          have hoa_cases : oa = s1 ∨ oa = s3 ∨ oa = s4 := by
            have h' : oa = s1 ∨ oa = s2 ∨ oa = s3 ∨ oa = s4 := by simpa [S] using hoa_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact (hoa_ne_s2 h).elim
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hob_cases : ob = s1 ∨ ob = s3 ∨ ob = s4 := by
            have h' : ob = s1 ∨ ob = s2 ∨ ob = s3 ∨ ob = s4 := by simpa [S] using hob_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact (hob_ne_s2 h).elim
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hoc_cases : oc = s1 ∨ oc = s3 ∨ oc = s4 := by
            have h' : oc = s1 ∨ oc = s2 ∨ oc = s3 ∨ oc = s4 := by simpa [S] using hoc_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact (hoc_ne_s2 h).elim
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)

          have h_some_s4 : oa = s4 ∨ ob = s4 ∨ oc = s4 := by
            by_contra h_none
            push_neg at h_none
            have hoa_13 : oa = s1 ∨ oa = s3 := by
              rcases hoa_cases with h1 | h3 | h4
              · exact Or.inl h1
              · exact Or.inr h3
              · exact (h_none.1 h4).elim
            have hob_13 : ob = s1 ∨ ob = s3 := by
              rcases hob_cases with h1 | h3 | h4
              · exact Or.inl h1
              · exact Or.inr h3
              · exact (h_none.2.1 h4).elim
            have hoc_13 : oc = s1 ∨ oc = s3 := by
              rcases hoc_cases with h1 | h3 | h4
              · exact Or.inl h1
              · exact Or.inr h3
              · exact (h_none.2.2 h4).elim

            let O : Finset (Fin 18) := ({oa, ob, oc} : Finset (Fin 18))
            have hO_card : O.card = 3 := by
              have hoa_not : oa ∉ insert ob ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h_ab, h_ac⟩
              have hob_not : ob ∉ ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_singleton]
                exact h_bc
              simp [O, hoa_not, hob_not]
            have hO_sub : O ⊆ ({s1, s3} : Finset (Fin 18)) := by
              intro x hx
              simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · rcases hoa_13 with h1 | h3
                · simp [h1]
                · simp [h3]
              · rcases hob_13 with h1 | h3
                · simp [h1]
                · simp [h3]
              · rcases hoc_13 with h1 | h3
                · simp [h1]
                · simp [h3]
            have h_le := Finset.card_le_card hO_sub
            have h13 : ({s1, s3} : Finset (Fin 18)).card = 2 := by
              simp [hs_ne13]
            omega

          have contra_of_shared_w (w : Fin 18) (hwW : w ∈ W)
              (hw_adj_s2 : G.Adj w s2) (hw_adj_s4 : G.Adj w s4) :
              False := by
            have hw_Q := (hW_props w).mp hwW
            have hw_nonadj_v : ¬G.Adj w v := fun h => hw_Q.1 (G.symm h)
            have hw_nonadj_t : ¬G.Adj t w := fun h => hw_Q.2.2 h

            have hw_nonadj_p2 : ¬G.Adj w p2 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p2, s2, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs2_adj_p2
                  · exact G.symm h_adj
                  · exact hs2_adj_p2
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s2
                  · exact h_adj
                  · exact hw_adj_s2
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s2).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs2_adj_p2).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p2, s2, w} h_tri_set

            have hw_nonadj_p4 : ¬G.Adj w p4 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p4, s4, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs4_adj_p4
                  · exact G.symm h_adj
                  · exact hs4_adj_p4
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s4
                  · exact h_adj
                  · exact hw_adj_s4
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s4).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs4_adj_p4).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p4, s4, w} h_tri_set

            have hs2_s4_nonadj : ¬G.Adj s2 s4 :=
              hN_indep_pairs s2 s4 hs2_in_N hs4_in_N hs_ne24

            have hw_S_card : (S.filter (G.Adj w)).card = 2 := hW_S_neighbors w hwW
            have hs1_nonadj_w : ¬G.Adj s1 w := by
              intro h_adj
              have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, hw_adj_s2⟩
              have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, hw_adj_s4⟩
              have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm h_adj⟩
              have h_three : ({s2, s4, s1} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs2_in_f
                · exact hs4_in_f
                · exact hs1_in_f
              have h_three_card : ({s2, s4, s1} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne14.symm
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne24, hs_ne12.symm⟩
              have h_le := Finset.card_le_card h_three
              omega
            have hs3_nonadj_w : ¬G.Adj s3 w := by
              intro h_adj
              have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, hw_adj_s2⟩
              have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, hw_adj_s4⟩
              have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm h_adj⟩
              have h_three : ({s2, s4, s3} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs2_in_f
                · exact hs4_in_f
                · exact hs3_in_f
              have h_three_card : ({s2, s4, s3} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne34.symm
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne24, hs_ne23⟩
              have h_le := Finset.card_le_card h_three
              omega

            have h_p2_p4 : G.Adj p2 p4 := p_adjacent_of_shared_w h_tri h_no6 v
              p2 p4 s2 s4 w
              hp2_nonadj_v hp4_nonadj_v hp_ne24
              (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N) hs_ne24
              hs2_adj_p2 hs4_adj_p4
              hs2_nonadj_p4 hs4_nonadj_p2
              hw_adj_s2 hw_adj_s4
              hw_nonadj_v hw_nonadj_p2 hw_nonadj_p4
              hs2_s4_nonadj
              t s1 s3
              ht_adj_v (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N)
              ht_ne_s2 ht_ne_s4 hs_ne12 hs_ne14 hs_ne23.symm hs_ne34
              ht_ne_s1 ht_ne_s3 hs_ne13
              (h2_unique t ht_in_N ht_ne_s2) (h4_unique t ht_in_N ht_ne_s4) hw_nonadj_t
              hs1_nonadj_p2 hs1_nonadj_p4 hs1_nonadj_w
              hs3_nonadj_p2 hs3_nonadj_p4 hs3_nonadj_w
            exact h_nonadj_p2p4 h_p2_p4

          rcases h_some_s4 with h | h | h
          · -- oa = s4, so wa shares s2 and s4
            have hwa_adj_s4 : G.Adj wa s4 := by simpa [h] using hwa_oa
            exact contra_of_shared_w wa hwa_mem.1 (G.symm hwa_mem.2) hwa_adj_s4
          · -- ob = s4, so wb shares s2 and s4
            have hwb_adj_s4 : G.Adj wb s4 := by simpa [h] using hwb_ob
            exact contra_of_shared_w wb hwb_mem.1 (G.symm hwb_mem.2) hwb_adj_s4
          · -- oc = s4, so wc shares s2 and s4
            have hwc_adj_s4 : G.Adj wc s4 := by simpa [h] using hwc_oc
            exact contra_of_shared_w wc hwc_mem.1 (G.symm hwc_mem.2) hwc_adj_s4

  have hs3_W_le2 : (W.filter (G.Adj s3)).card ≤ 2 := by
    by_contra h_ge3
    push_neg at h_ge3
    obtain ⟨wa, wb, wc, hwa_mem, hwb_mem, hwc_mem, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp h_ge3
    simp only [Finset.mem_filter] at hwa_mem hwb_mem hwc_mem
    have hwa_S := hW_S_neighbors wa hwa_mem.1
    have hwb_S := hW_S_neighbors wb hwb_mem.1
    have hwc_S := hW_S_neighbors wc hwc_mem.1
    have hs3_wa : s3 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwa_mem.2⟩
    have hs3_wb : s3 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwb_mem.2⟩
    have hs3_wc : s3 ∈ S.filter (G.Adj wc) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwc_mem.2⟩
    have hwa_other : ((S.filter (G.Adj wa)).erase s3).card = 1 := by
      rw [Finset.card_erase_of_mem hs3_wa, hwa_S]
    have hwb_other : ((S.filter (G.Adj wb)).erase s3).card = 1 := by
      rw [Finset.card_erase_of_mem hs3_wb, hwb_S]
    have hwc_other : ((S.filter (G.Adj wc)).erase s3).card = 1 := by
      rw [Finset.card_erase_of_mem hs3_wc, hwc_S]
    obtain ⟨oa, hoa_eq⟩ := Finset.card_eq_one.mp hwa_other
    obtain ⟨ob, hob_eq⟩ := Finset.card_eq_one.mp hwb_other
    obtain ⟨oc, hoc_eq⟩ := Finset.card_eq_one.mp hwc_other
    have hoa_mem : oa ∈ (S.filter (G.Adj wa)).erase s3 := by rw [hoa_eq]; exact Finset.mem_singleton_self _
    have hob_mem : ob ∈ (S.filter (G.Adj wb)).erase s3 := by rw [hob_eq]; exact Finset.mem_singleton_self _
    have hoc_mem : oc ∈ (S.filter (G.Adj wc)).erase s3 := by rw [hoc_eq]; exact Finset.mem_singleton_self _
    simp only [Finset.mem_erase, Finset.mem_filter] at hoa_mem hob_mem hoc_mem
    have hoa_ne_s3 : oa ≠ s3 := hoa_mem.1
    have hob_ne_s3 : ob ≠ s3 := hob_mem.1
    have hoc_ne_s3 : oc ≠ s3 := hoc_mem.1
    have hoa_in_S : oa ∈ S := hoa_mem.2.1
    have hob_in_S : ob ∈ S := hob_mem.2.1
    have hoc_in_S : oc ∈ S := hoc_mem.2.1
    have hwa_oa : G.Adj wa oa := hoa_mem.2.2
    have hwb_ob : G.Adj wb ob := hob_mem.2.2
    have hwc_oc : G.Adj wc oc := hoc_mem.2.2
    have hs3_adj_v : G.Adj v s3 := by rw [← SimpleGraph.mem_neighborFinset]; exact hs3_in_N
    have hoa_adj_v : G.Adj v oa := by
      rw [hS_eq] at hoa_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoa_in_S).2
    have hob_adj_v : G.Adj v ob := by
      rw [hS_eq] at hob_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hob_in_S).2
    have hoc_adj_v : G.Adj v oc := by
      rw [hS_eq] at hoc_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoc_in_S).2
    have hwa_Q := (hW_props wa).mp hwa_mem.1
    have hwb_Q := (hW_props wb).mp hwb_mem.1
    have hwc_Q := (hW_props wc).mp hwc_mem.1
    have hv_ne_wa : v ≠ wa := by
      intro h_eq; have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wa).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
      omega
    have hv_ne_wb : v ≠ wb := by
      intro h_eq; have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wb).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
      omega
    have hv_ne_wc : v ≠ wc := by
      intro h_eq; have h_common : commonNeighborsCard G v wc = 2 := hwc_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wc).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wc
      omega
    by_cases h_ab : oa = ob
    · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s3 oa wa wb
        hs3_adj_v hoa_adj_v hoa_ne_s3.symm hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 (G.symm hwa_oa) (h_ab ▸ G.symm hwb_ob)
    · by_cases h_ac : oa = oc
      · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s3 oa wa wc
          hs3_adj_v hoa_adj_v hoa_ne_s3.symm hv_ne_wa hv_ne_wc hac
          hwa_mem.2 hwc_mem.2 (G.symm hwa_oa) (h_ac ▸ G.symm hwc_oc)
      · by_cases h_bc : ob = oc
        · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s3 ob wb wc
            hs3_adj_v hob_adj_v hob_ne_s3.symm hv_ne_wb hv_ne_wc hbc
            hwb_mem.2 hwc_mem.2 (G.symm hwb_ob) (h_bc ▸ G.symm hwc_oc)
        · -- Bijective case: oa, ob, oc all distinct in {s1, s2, s4}
          have hoa_cases : oa = s1 ∨ oa = s2 ∨ oa = s4 := by
            have h' : oa = s1 ∨ oa = s2 ∨ oa = s3 ∨ oa = s4 := by simpa [S] using hoa_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact (hoa_ne_s3 h).elim
            · exact Or.inr (Or.inr h)
          have hob_cases : ob = s1 ∨ ob = s2 ∨ ob = s4 := by
            have h' : ob = s1 ∨ ob = s2 ∨ ob = s3 ∨ ob = s4 := by simpa [S] using hob_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact (hob_ne_s3 h).elim
            · exact Or.inr (Or.inr h)
          have hoc_cases : oc = s1 ∨ oc = s2 ∨ oc = s4 := by
            have h' : oc = s1 ∨ oc = s2 ∨ oc = s3 ∨ oc = s4 := by simpa [S] using hoc_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact (hoc_ne_s3 h).elim
            · exact Or.inr (Or.inr h)

          have h_some_s1 : oa = s1 ∨ ob = s1 ∨ oc = s1 := by
            by_contra h_none
            push_neg at h_none
            have hoa_24 : oa = s2 ∨ oa = s4 := by
              rcases hoa_cases with h1 | h2 | h4
              · exact (h_none.1 h1).elim
              · exact Or.inl h2
              · exact Or.inr h4
            have hob_24 : ob = s2 ∨ ob = s4 := by
              rcases hob_cases with h1 | h2 | h4
              · exact (h_none.2.1 h1).elim
              · exact Or.inl h2
              · exact Or.inr h4
            have hoc_24 : oc = s2 ∨ oc = s4 := by
              rcases hoc_cases with h1 | h2 | h4
              · exact (h_none.2.2 h1).elim
              · exact Or.inl h2
              · exact Or.inr h4

            let O : Finset (Fin 18) := ({oa, ob, oc} : Finset (Fin 18))
            have hO_card : O.card = 3 := by
              have hoa_not : oa ∉ insert ob ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h_ab, h_ac⟩
              have hob_not : ob ∉ ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_singleton]
                exact h_bc
              simp [O, hoa_not, hob_not]
            have hO_sub : O ⊆ ({s2, s4} : Finset (Fin 18)) := by
              intro x hx
              simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · rcases hoa_24 with h2 | h4
                · simp [h2]
                · simp [h4]
              · rcases hob_24 with h2 | h4
                · simp [h2]
                · simp [h4]
              · rcases hoc_24 with h2 | h4
                · simp [h2]
                · simp [h4]
            have h_le := Finset.card_le_card hO_sub
            have h24 : ({s2, s4} : Finset (Fin 18)).card = 2 := by
              simp [hs_ne24]
            omega

          have contra_of_shared_w (w : Fin 18) (hwW : w ∈ W)
              (hw_adj_s1 : G.Adj w s1) (hw_adj_s3 : G.Adj w s3) :
              False := by
            have hw_Q := (hW_props w).mp hwW
            have hw_nonadj_v : ¬G.Adj w v := fun h => hw_Q.1 (G.symm h)
            have hw_nonadj_t : ¬G.Adj t w := fun h => hw_Q.2.2 h

            have hw_nonadj_p1 : ¬G.Adj w p1 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p1, s1, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs1_adj_p1
                  · exact G.symm h_adj
                  · exact hs1_adj_p1
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s1
                  · exact h_adj
                  · exact hw_adj_s1
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s1).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p1, s1, w} h_tri_set

            have hw_nonadj_p3 : ¬G.Adj w p3 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p3, s3, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs3_adj_p3
                  · exact G.symm h_adj
                  · exact hs3_adj_p3
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s3
                  · exact h_adj
                  · exact hw_adj_s3
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s3).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p3, s3, w} h_tri_set

            have hs1_s3_nonadj : ¬G.Adj s1 s3 :=
              hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13

            have hw_S_card : (S.filter (G.Adj w)).card = 2 := hW_S_neighbors w hwW
            have hs2_nonadj_w : ¬G.Adj s2 w := by
              intro h_adj
              have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, hw_adj_s1⟩
              have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, hw_adj_s3⟩
              have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm h_adj⟩
              have h_three : ({s1, s3, s2} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs1_in_f
                · exact hs3_in_f
                · exact hs2_in_f
              have h_three_card : ({s1, s3, s2} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne23.symm
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne13, hs_ne12⟩
              have h_le := Finset.card_le_card h_three
              omega
            have hs4_nonadj_w : ¬G.Adj s4 w := by
              intro h_adj
              have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, hw_adj_s1⟩
              have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, hw_adj_s3⟩
              have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm h_adj⟩
              have h_three : ({s1, s3, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs1_in_f
                · exact hs3_in_f
                · exact hs4_in_f
              have h_three_card : ({s1, s3, s4} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne34
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne13, hs_ne14⟩
              have h_le := Finset.card_le_card h_three
              omega

            have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
              p1 p3 s1 s3 w
              hp1_nonadj_v hp3_nonadj_v hp_ne13
              (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
              hs1_adj_p1 hs3_adj_p3
              hs1_nonadj_p3 hs3_nonadj_p1
              hw_adj_s1 hw_adj_s3
              hw_nonadj_v hw_nonadj_p1 hw_nonadj_p3
              hs1_s3_nonadj
              t s2 s4
              ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
              ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
              ht_ne_s2 ht_ne_s4 hs_ne24
              (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) hw_nonadj_t
              hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_w
              hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_w
            exact h_nonadj_p1p3 h_p1_p3

          rcases h_some_s1 with h | h | h
          · -- oa = s1, so wa shares s3 and s1
            have hwa_adj_s1 : G.Adj wa s1 := by simpa [h] using hwa_oa
            exact contra_of_shared_w wa hwa_mem.1 hwa_adj_s1 (G.symm hwa_mem.2)
          · -- ob = s1, so wb shares s3 and s1
            have hwb_adj_s1 : G.Adj wb s1 := by simpa [h] using hwb_ob
            exact contra_of_shared_w wb hwb_mem.1 hwb_adj_s1 (G.symm hwb_mem.2)
          · -- oc = s1, so wc shares s3 and s1
            have hwc_adj_s1 : G.Adj wc s1 := by simpa [h] using hwc_oc
            exact contra_of_shared_w wc hwc_mem.1 hwc_adj_s1 (G.symm hwc_mem.2)

  have hs4_W_le2 : (W.filter (G.Adj s4)).card ≤ 2 := by
    by_contra h_ge3
    push_neg at h_ge3
    obtain ⟨wa, wb, wc, hwa_mem, hwb_mem, hwc_mem, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp h_ge3
    simp only [Finset.mem_filter] at hwa_mem hwb_mem hwc_mem
    have hwa_S := hW_S_neighbors wa hwa_mem.1
    have hwb_S := hW_S_neighbors wb hwb_mem.1
    have hwc_S := hW_S_neighbors wc hwc_mem.1
    have hs4_wa : s4 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm hwa_mem.2⟩
    have hs4_wb : s4 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm hwb_mem.2⟩
    have hs4_wc : s4 ∈ S.filter (G.Adj wc) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm hwc_mem.2⟩
    have hwa_other : ((S.filter (G.Adj wa)).erase s4).card = 1 := by
      rw [Finset.card_erase_of_mem hs4_wa, hwa_S]
    have hwb_other : ((S.filter (G.Adj wb)).erase s4).card = 1 := by
      rw [Finset.card_erase_of_mem hs4_wb, hwb_S]
    have hwc_other : ((S.filter (G.Adj wc)).erase s4).card = 1 := by
      rw [Finset.card_erase_of_mem hs4_wc, hwc_S]
    obtain ⟨oa, hoa_eq⟩ := Finset.card_eq_one.mp hwa_other
    obtain ⟨ob, hob_eq⟩ := Finset.card_eq_one.mp hwb_other
    obtain ⟨oc, hoc_eq⟩ := Finset.card_eq_one.mp hwc_other
    have hoa_mem : oa ∈ (S.filter (G.Adj wa)).erase s4 := by rw [hoa_eq]; exact Finset.mem_singleton_self _
    have hob_mem : ob ∈ (S.filter (G.Adj wb)).erase s4 := by rw [hob_eq]; exact Finset.mem_singleton_self _
    have hoc_mem : oc ∈ (S.filter (G.Adj wc)).erase s4 := by rw [hoc_eq]; exact Finset.mem_singleton_self _
    simp only [Finset.mem_erase, Finset.mem_filter] at hoa_mem hob_mem hoc_mem
    have hoa_ne_s4 : oa ≠ s4 := hoa_mem.1
    have hob_ne_s4 : ob ≠ s4 := hob_mem.1
    have hoc_ne_s4 : oc ≠ s4 := hoc_mem.1
    have hoa_in_S : oa ∈ S := hoa_mem.2.1
    have hob_in_S : ob ∈ S := hob_mem.2.1
    have hoc_in_S : oc ∈ S := hoc_mem.2.1
    have hwa_oa : G.Adj wa oa := hoa_mem.2.2
    have hwb_ob : G.Adj wb ob := hob_mem.2.2
    have hwc_oc : G.Adj wc oc := hoc_mem.2.2
    have hs4_adj_v : G.Adj v s4 := by rw [← SimpleGraph.mem_neighborFinset]; exact hs4_in_N
    have hoa_adj_v : G.Adj v oa := by
      rw [hS_eq] at hoa_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoa_in_S).2
    have hob_adj_v : G.Adj v ob := by
      rw [hS_eq] at hob_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hob_in_S).2
    have hoc_adj_v : G.Adj v oc := by
      rw [hS_eq] at hoc_in_S; rw [← SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_erase.mp hoc_in_S).2
    have hwa_Q := (hW_props wa).mp hwa_mem.1
    have hwb_Q := (hW_props wb).mp hwb_mem.1
    have hwc_Q := (hW_props wc).mp hwc_mem.1
    have hv_ne_wa : v ≠ wa := by
      intro h_eq; have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wa).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
      omega
    have hv_ne_wb : v ≠ wb := by
      intro h_eq; have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wb).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
      omega
    have hv_ne_wc : v ≠ wc := by
      intro h_eq; have h_common : commonNeighborsCard G v wc = 2 := hwc_Q.2.1
      rw [h_eq] at h_common; unfold commonNeighborsCard _root_.commonNeighbors at h_common
      simp only [Finset.inter_self] at h_common
      have h_deg : (G.neighborFinset wc).card = 5 := by
        rw [G.card_neighborFinset_eq_degree]; exact h_reg wc
      omega
    by_cases h_ab : oa = ob
    · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s4 oa wa wb
        hs4_adj_v hoa_adj_v hoa_ne_s4.symm hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 (G.symm hwa_oa) (h_ab ▸ G.symm hwb_ob)
    · by_cases h_ac : oa = oc
      · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s4 oa wa wc
          hs4_adj_v hoa_adj_v hoa_ne_s4.symm hv_ne_wa hv_ne_wc hac
          hwa_mem.2 hwc_mem.2 (G.symm hwa_oa) (h_ac ▸ G.symm hwc_oc)
      · by_cases h_bc : ob = oc
        · exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s4 ob wb wc
            hs4_adj_v hob_adj_v hob_ne_s4.symm hv_ne_wb hv_ne_wc hbc
            hwb_mem.2 hwc_mem.2 (G.symm hwb_ob) (h_bc ▸ G.symm hwc_oc)
        · -- Bijective case: oa, ob, oc all distinct in {s1, s2, s3}
          have hoa_cases : oa = s1 ∨ oa = s2 ∨ oa = s3 := by
            have h' : oa = s1 ∨ oa = s2 ∨ oa = s3 ∨ oa = s4 := by simpa [S] using hoa_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact (hoa_ne_s4 h).elim
          have hob_cases : ob = s1 ∨ ob = s2 ∨ ob = s3 := by
            have h' : ob = s1 ∨ ob = s2 ∨ ob = s3 ∨ ob = s4 := by simpa [S] using hob_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact (hob_ne_s4 h).elim
          have hoc_cases : oc = s1 ∨ oc = s2 ∨ oc = s3 := by
            have h' : oc = s1 ∨ oc = s2 ∨ oc = s3 ∨ oc = s4 := by simpa [S] using hoc_in_S
            rcases h' with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact (hoc_ne_s4 h).elim

          have h_some_s2 : oa = s2 ∨ ob = s2 ∨ oc = s2 := by
            by_contra h_none
            push_neg at h_none
            have hoa_13 : oa = s1 ∨ oa = s3 := by
              rcases hoa_cases with h1 | h2 | h3
              · exact Or.inl h1
              · exact (h_none.1 h2).elim
              · exact Or.inr h3
            have hob_13 : ob = s1 ∨ ob = s3 := by
              rcases hob_cases with h1 | h2 | h3
              · exact Or.inl h1
              · exact (h_none.2.1 h2).elim
              · exact Or.inr h3
            have hoc_13 : oc = s1 ∨ oc = s3 := by
              rcases hoc_cases with h1 | h2 | h3
              · exact Or.inl h1
              · exact (h_none.2.2 h2).elim
              · exact Or.inr h3

            let O : Finset (Fin 18) := ({oa, ob, oc} : Finset (Fin 18))
            have hO_card : O.card = 3 := by
              have hoa_not : oa ∉ insert ob ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h_ab, h_ac⟩
              have hob_not : ob ∉ ({oc} : Finset (Fin 18)) := by
                simp only [Finset.mem_singleton]
                exact h_bc
              simp [O, hoa_not, hob_not]
            have hO_sub : O ⊆ ({s1, s3} : Finset (Fin 18)) := by
              intro x hx
              simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · rcases hoa_13 with h1 | h3
                · simp [h1]
                · simp [h3]
              · rcases hob_13 with h1 | h3
                · simp [h1]
                · simp [h3]
              · rcases hoc_13 with h1 | h3
                · simp [h1]
                · simp [h3]
            have h_le := Finset.card_le_card hO_sub
            have h13 : ({s1, s3} : Finset (Fin 18)).card = 2 := by
              simp [hs_ne13]
            omega

          have contra_of_shared_w (w : Fin 18) (hwW : w ∈ W)
              (hw_adj_s2 : G.Adj w s2) (hw_adj_s4 : G.Adj w s4) :
              False := by
            have hw_Q := (hW_props w).mp hwW
            have hw_nonadj_v : ¬G.Adj w v := fun h => hw_Q.1 (G.symm h)
            have hw_nonadj_t : ¬G.Adj t w := fun h => hw_Q.2.2 h

            have hw_nonadj_p2 : ¬G.Adj w p2 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p2, s2, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs2_adj_p2
                  · exact G.symm h_adj
                  · exact hs2_adj_p2
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s2
                  · exact h_adj
                  · exact hw_adj_s2
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s2).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs2_adj_p2).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p2, s2, w} h_tri_set

            have hw_nonadj_p4 : ¬G.Adj w p4 := by
              intro h_adj
              have h_tri_set : G.IsNClique 3 {p4, s4, w} := by
                constructor
                · intro a ha b hb hab'
                  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact absurd rfl hab'
                  · exact G.symm hs4_adj_p4
                  · exact G.symm h_adj
                  · exact hs4_adj_p4
                  · exact absurd rfl hab'
                  · exact G.symm hw_adj_s4
                  · exact h_adj
                  · exact hw_adj_s4
                  · exact absurd rfl hab'
                · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                  · simp only [Finset.mem_singleton]; exact (G.ne_of_adj hw_adj_s4).symm
                  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨(G.ne_of_adj hs4_adj_p4).symm, (G.ne_of_adj h_adj).symm⟩
              exact h_tri {p4, s4, w} h_tri_set

            have hs2_s4_nonadj : ¬G.Adj s2 s4 :=
              hN_indep_pairs s2 s4 hs2_in_N hs4_in_N hs_ne24

            have hw_S_card : (S.filter (G.Adj w)).card = 2 := hW_S_neighbors w hwW
            have hs1_nonadj_w : ¬G.Adj s1 w := by
              intro h_adj
              have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, hw_adj_s2⟩
              have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, hw_adj_s4⟩
              have hs1_in_f : s1 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm h_adj⟩
              have h_three : ({s2, s4, s1} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs2_in_f
                · exact hs4_in_f
                · exact hs1_in_f
              have h_three_card : ({s2, s4, s1} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne14.symm
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne24, hs_ne12.symm⟩
              have h_le := Finset.card_le_card h_three
              omega
            have hs3_nonadj_w : ¬G.Adj s3 w := by
              intro h_adj
              have hs2_in_f : s2 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs2_in_S, hw_adj_s2⟩
              have hs4_in_f : s4 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs4_in_S, hw_adj_s4⟩
              have hs3_in_f : s3 ∈ S.filter (G.Adj w) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm h_adj⟩
              have h_three : ({s2, s4, s3} : Finset (Fin 18)) ⊆ S.filter (G.Adj w) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl
                · exact hs2_in_f
                · exact hs4_in_f
                · exact hs3_in_f
              have h_three_card : ({s2, s4, s3} : Finset (Fin 18)).card = 3 := by
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [Finset.mem_singleton]; exact hs_ne34.symm
                · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hs_ne24, hs_ne23⟩
              have h_le := Finset.card_le_card h_three
              omega

            have h_p2_p4 : G.Adj p2 p4 := p_adjacent_of_shared_w h_tri h_no6 v
              p2 p4 s2 s4 w
              hp2_nonadj_v hp4_nonadj_v hp_ne24
              (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N) hs_ne24
              hs2_adj_p2 hs4_adj_p4
              hs2_nonadj_p4 hs4_nonadj_p2
              hw_adj_s2 hw_adj_s4
              hw_nonadj_v hw_nonadj_p2 hw_nonadj_p4
              hs2_s4_nonadj
              t s1 s3
              ht_adj_v (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N)
              ht_ne_s2 ht_ne_s4 hs_ne12 hs_ne14 hs_ne23.symm hs_ne34
              ht_ne_s1 ht_ne_s3 hs_ne13
              (h2_unique t ht_in_N ht_ne_s2) (h4_unique t ht_in_N ht_ne_s4) hw_nonadj_t
              hs1_nonadj_p2 hs1_nonadj_p4 hs1_nonadj_w
              hs3_nonadj_p2 hs3_nonadj_p4 hs3_nonadj_w
            exact h_nonadj_p2p4 h_p2_p4

          rcases h_some_s2 with h | h | h
          · -- oa = s2, so wa shares s4 and s2
            have hwa_adj_s2 : G.Adj wa s2 := by simpa [h] using hwa_oa
            exact contra_of_shared_w wa hwa_mem.1 hwa_adj_s2 (G.symm hwa_mem.2)
          · -- ob = s2, so wb shares s4 and s2
            have hwb_adj_s2 : G.Adj wb s2 := by simpa [h] using hwb_ob
            exact contra_of_shared_w wb hwb_mem.1 hwb_adj_s2 (G.symm hwb_mem.2)
          · -- oc = s2, so wc shares s4 and s2
            have hwc_adj_s2 : G.Adj wc s2 := by simpa [h] using hwc_oc
            exact contra_of_shared_w wc hwc_mem.1 hwc_adj_s2 (G.symm hwc_mem.2)

  -- Total S-W edges from W side = 4 * 2 = 8
  -- Total S-W edges from S side = sum of W-neighbors of each s
  -- Since each s has ≤ 2 W-neighbors and sum = 8, each has exactly 2
  -- Each si has ≤ 2 W-neighbors and total = 8, so each has exactly 2
  have hs_W_eq2 : ∀ si ∈ S, (W.filter (G.Adj si)).card = 2 := by
    intro si hsi
    have hsi_le2 : (W.filter (G.Adj si)).card ≤ 2 := by
      by_cases h_s1 : si = s1
      · rw [h_s1]; exact hs1_W_le2
      · by_cases h_s2 : si = s2
        · rw [h_s2]; exact hs2_W_le2
        · by_cases h_s3 : si = s3
          · rw [h_s3]; exact hs3_W_le2
          · -- si ∈ S = {s1, s2, s3, s4}, but si ≠ s1, s2, s3, so si = s4
            have hsi_eq_s4 : si = s4 := by
              simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsi
              rcases hsi with rfl | rfl | rfl | rfl
              · exact absurd rfl h_s1
              · exact absurd rfl h_s2
              · exact absurd rfl h_s3
              · rfl
            rw [hsi_eq_s4]; exact hs4_W_le2
    -- Sum is 8 (4 W-vertices × 2 S-neighbors each) and there are 4 S-vertices each with ≤ 2
    -- By pigeonhole, each must have exactly 2
    have h_sum : (W.filter (G.Adj s1)).card + (W.filter (G.Adj s2)).card +
                 (W.filter (G.Adj s3)).card + (W.filter (G.Adj s4)).card = 8 := by
      have h_total : ∑ s ∈ S, (W.filter (G.Adj s)).card = 8 := by
        have h_W_count : ∑ w ∈ W, (S.filter (G.Adj w)).card = 8 := by
          calc ∑ w ∈ W, (S.filter (G.Adj w)).card
              = ∑ w ∈ W, 2 := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  exact hW_S_neighbors w hw
            _ = W.card * 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
            _ = 4 * 2 := by rw [hW_card]
        rw [bipartite_edge_count_symmetry S W G.Adj G.symm]
        exact h_W_count
      rw [← sum_over_four s1 s2 s3 s4 hs_ne12 hs_ne13 hs_ne14 hs_ne23 hs_ne24 hs_ne34
                            (fun s => (W.filter (G.Adj s)).card)]
      exact h_total
    -- We have: a + b + c + d = 8 and each ≤ 2. By pigeonhole, each = 2.
    by_cases h_eq : si = s1
    · rw [h_eq]; omega
    · by_cases h_eq2 : si = s2
      · rw [h_eq2]; omega
      · by_cases h_eq3 : si = s3
        · rw [h_eq3]; omega
        · have h_eq4 : si = s4 := by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsi
            rcases hsi with rfl | rfl | rfl | rfl
            · exact (h_eq rfl).elim
            · exact (h_eq2 rfl).elim
            · exact (h_eq3 rfl).elim
            · rfl
          rw [h_eq4]; omega

  -- Now extract the shared W for consecutive s-pairs
  -- s1 and s2 share exactly one W (the intersection of their W-neighbors has size 1)
  have hs12_share_W : ((W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2))).card = 1 := by
    -- Both have exactly 2 W-neighbors
    have hs1_W_eq2 : (W.filter (G.Adj s1)).card = 2 := hs_W_eq2 s1 hs1_in_S
    have hs2_W_eq2 : (W.filter (G.Adj s2)).card = 2 := hs_W_eq2 s2 hs2_in_S
    -- They must share at least 1 (since 2 + 2 = 4 and |W| = 4)
    have h_share : ((W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2))).Nonempty := by
      by_contra h_empty
      simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disjoint : Disjoint (W.filter (G.Adj s1)) (W.filter (G.Adj s2)) := by
        rw [Finset.disjoint_iff_inter_eq_empty, h_empty]
      have h_union_card : ((W.filter (G.Adj s1)) ∪ (W.filter (G.Adj s2))).card =
                          (W.filter (G.Adj s1)).card + (W.filter (G.Adj s2)).card := by
        exact Finset.card_union_of_disjoint h_disjoint
      have h_sub : (W.filter (G.Adj s1)) ∪ (W.filter (G.Adj s2)) ⊆ W := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_filter] at hx
        rcases hx with h | h <;> exact h.1
      have h_bound : ((W.filter (G.Adj s1)) ∪ (W.filter (G.Adj s2))).card ≤ W.card :=
        Finset.card_le_card h_sub
      -- Disjoint W-neighbors is combinatorially possible (2+2=4=|W|) but structurally impossible
      -- Proof sketch:
      -- 1. s1's W-neighbors = {wa, wb} are disjoint from s2's {wc, wd}
      -- 2. Each wi ∈ W has exactly 2 S-neighbors (hW_S_neighbors)
      -- 3. wa's S-neighbors = {s1, sx} where sx ∈ {s3, s4} (can't be s2 since wa ∉ s2's W-neighbors)
      -- 4. wb's S-neighbors = {s1, sy} where sy ∈ {s3, s4}
      -- 5. If sx = sy (say both = s3): s1 and s3 share BOTH wa and wb
      --    → contradiction via S_pair_share_at_most_one_W
      -- 6. If sx ≠ sy: s1 shares wa with s3, s1 shares wb with s4 (or vice versa)
      --    → s1-s3 share a W → by p_adjacent_of_shared_w, p1-p3 adjacent
      --    → but h_nonadj_p1p3 says p1-p3 NOT adjacent → contradiction
      -- First, show that union = W
      have h_eq_W : (W.filter (G.Adj s1)) ∪ (W.filter (G.Adj s2)) = W := by
        apply Finset.eq_of_subset_of_card_le h_sub
        rw [h_union_card, hs1_W_eq2, hs2_W_eq2, hW_card]
      -- Get the W-vertices of s1
      obtain ⟨wa, wb, hwa_mem, hwb_mem, hab_ne⟩ := Finset.one_lt_card_iff.mp
        (by rw [hs1_W_eq2]; omega : 1 < (W.filter (G.Adj s1)).card)
      simp only [Finset.mem_filter] at hwa_mem hwb_mem
      -- wa is not adjacent to s2 (disjoint)
      have hwa_nonadj_s2 : ¬G.Adj wa s2 := by
        intro h_adj
        have hwa_in_s2 : wa ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hwa_mem.1, G.symm h_adj⟩
        have hwa_in_inter : wa ∈ (W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2)) := by
          rw [Finset.mem_inter]; exact ⟨Finset.mem_filter.mpr hwa_mem, hwa_in_s2⟩
        rw [h_empty] at hwa_in_inter; exact Finset.notMem_empty wa hwa_in_inter
      have hwb_nonadj_s2 : ¬G.Adj wb s2 := by
        intro h_adj
        have hwb_in_s2 : wb ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hwb_mem.1, G.symm h_adj⟩
        have hwb_in_inter : wb ∈ (W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2)) := by
          rw [Finset.mem_inter]; exact ⟨Finset.mem_filter.mpr hwb_mem, hwb_in_s2⟩
        rw [h_empty] at hwb_in_inter; exact Finset.notMem_empty wb hwb_in_inter
      -- wa's "other" S-neighbor (besides s1) must be in {s3, s4}
      have hwa_S_card : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
      have hwa_s1_mem : s1 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwa_mem.2⟩
      -- The other S-neighbor is some sx ∈ S \ {s1}
      have hwa_other : ∃ sx ∈ S, sx ≠ s1 ∧ G.Adj wa sx := by
        have h_sub : {s1} ⊆ S.filter (G.Adj wa) := Finset.singleton_subset_iff.mpr hwa_s1_mem
        have h_diff_card : ((S.filter (G.Adj wa)) \ {s1}).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwa_S_card]
        obtain ⟨sx, hsx_mem⟩ := Finset.card_eq_one.mp h_diff_card
        have hsx_in : sx ∈ (S.filter (G.Adj wa)) \ {s1} := by rw [hsx_mem]; simp
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsx_in
        exact ⟨sx, hsx_in.1.1, hsx_in.2, hsx_in.1.2⟩
      obtain ⟨sx, hsx_in_S, hsx_ne_s1, hwa_adj_sx⟩ := hwa_other
      -- sx can't be s2 (since wa not adj to s2)
      have hsx_ne_s2 : sx ≠ s2 := by
        intro h_eq; rw [h_eq] at hwa_adj_sx; exact hwa_nonadj_s2 hwa_adj_sx
      -- Similarly for wb
      have hwb_S_card : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
      have hwb_s1_mem : s1 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwb_mem.2⟩
      have hwb_other : ∃ sy ∈ S, sy ≠ s1 ∧ G.Adj wb sy := by
        have h_sub : {s1} ⊆ S.filter (G.Adj wb) := Finset.singleton_subset_iff.mpr hwb_s1_mem
        have h_diff_card : ((S.filter (G.Adj wb)) \ {s1}).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwb_S_card]
        obtain ⟨sy, hsy_mem⟩ := Finset.card_eq_one.mp h_diff_card
        have hsy_in : sy ∈ (S.filter (G.Adj wb)) \ {s1} := by rw [hsy_mem]; simp
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsy_in
        exact ⟨sy, hsy_in.1.1, hsy_in.2, hsy_in.1.2⟩
      obtain ⟨sy, hsy_in_S, hsy_ne_s1, hwb_adj_sy⟩ := hwb_other
      have hsy_ne_s2 : sy ≠ s2 := by
        intro h_eq; rw [h_eq] at hwb_adj_sy; exact hwb_nonadj_s2 hwb_adj_sy
      -- sx, sy ∈ S \ {s1, s2} = {s3, s4}
      have hsx_in_s34 : sx = s3 ∨ sx = s4 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsx_in_S
        rcases hsx_in_S with rfl | rfl | rfl | rfl
        · exact (hsx_ne_s1 rfl).elim
        · exact (hsx_ne_s2 rfl).elim
        · left; rfl
        · right; rfl
      have hsy_in_s34 : sy = s3 ∨ sy = s4 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsy_in_S
        rcases hsy_in_S with rfl | rfl | rfl | rfl
        · exact (hsy_ne_s1 rfl).elim
        · exact (hsy_ne_s2 rfl).elim
        · left; rfl
        · right; rfl
      -- Case analysis on sx, sy
      rcases hsx_in_s34 with hsx_eq | hsx_eq <;> rcases hsy_in_s34 with hsy_eq | hsy_eq
      · -- sx = s3, sy = s3: s1 and s3 share both wa and wb
        have hs1_adj_v : G.Adj v s1 := by rw [← mem_neighborFinset]; exact hs1_in_N
        have hs3_adj_v' : G.Adj v s3 := by rw [← mem_neighborFinset]; exact hs3_in_N
        have hwa_Q := (hW_props wa).mp hwa_mem.1
        have hwb_Q := (hW_props wb).mp hwb_mem.1
        have hv_ne_wa : v ≠ wa := by
          intro h_eq; have h := hwa_Q.2.1; rw [h_eq] at h
          unfold commonNeighborsCard _root_.commonNeighbors at h
          simp only [Finset.inter_self] at h
          have h_deg : (G.neighborFinset wa).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
          omega
        have hv_ne_wb : v ≠ wb := by
          intro h_eq; have h := hwb_Q.2.1; rw [h_eq] at h
          unfold commonNeighborsCard _root_.commonNeighbors at h
          simp only [Finset.inter_self] at h
          have h_deg : (G.neighborFinset wb).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
          omega
        rw [hsx_eq] at hwa_adj_sx
        rw [hsy_eq] at hwb_adj_sy
        exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 s3 wa wb
          hs1_adj_v hs3_adj_v' hs_ne13 hv_ne_wa hv_ne_wb hab_ne
          hwa_mem.2 hwb_mem.2 (G.symm hwa_adj_sx) (G.symm hwb_adj_sy)
      · -- sx = s3, sy = s4: s1 shares wa with s3
        -- By p_adjacent_of_shared_w, p1-p3 would be adjacent, contradicting h_nonadj_p1p3
        rw [hsx_eq] at hwa_adj_sx
        -- wa is adjacent to both s1 and s3, and is in W (non-neighbor of v)
        have hwa_Q := (hW_props wa).mp hwa_mem.1
        have hwa_nonadj_v : ¬G.Adj wa v := fun h => hwa_Q.1 (G.symm h)
        have hwa_nonadj_t : ¬G.Adj wa t := fun h => hwa_Q.2.2 (G.symm h)
        -- wa is not adjacent to p1 (else {p1, s1, wa} is a triangle)
        have hwa_nonadj_p1 : ¬G.Adj wa p1 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p1, s1, wa} := by
            constructor
            · intro a ha b hb hab
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab
              · exact G.symm hs1_adj_p1
              · exact G.symm h_adj
              · exact hs1_adj_p1
              · exact absurd rfl hab
              · exact hwa_mem.2
              · exact h_adj
              · exact G.symm hwa_mem.2
              · exact absurd rfl hab
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact G.ne_of_adj hwa_mem.2
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p1, s1, wa} h_tri_set
        -- wa is not adjacent to p3 (else {p3, s3, wa} is a triangle)
        have hwa_nonadj_p3 : ¬G.Adj wa p3 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p3, s3, wa} := by
            constructor
            · intro a ha b hb hab
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab
              · exact G.symm hs3_adj_p3
              · exact G.symm h_adj
              · exact hs3_adj_p3
              · exact absurd rfl hab
              · exact G.symm hwa_adj_sx
              · exact h_adj
              · exact hwa_adj_sx
              · exact absurd rfl hab
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact (G.ne_of_adj hwa_adj_sx).symm
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p3, s3, wa} h_tri_set
        -- s1-s3 non-adjacent (both in N(v), triangle-free)
        have hs1_s3_nonadj : ¬G.Adj s1 s3 := hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13
        -- s2 not adjacent to wa (wa is in W, t not adj to wa, so check if s2 would form triangle)
        have hs2_nonadj_wa : ¬G.Adj s2 wa := by
          intro h_adj
          -- wa ∈ W.filter (G.Adj s2) would mean wa in s2's W-neighbors
          -- But wa ∈ W.filter (G.Adj s1), and we're in the disjoint case
          have hwa_in_s2 : wa ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hwa_mem.1, h_adj⟩
          have hwa_in_inter : wa ∈ (W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2)) :=
            Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwa_mem, hwa_in_s2⟩
          rw [h_empty] at hwa_in_inter
          exact Finset.notMem_empty wa hwa_in_inter
        have hs4_nonadj_wa : ¬G.Adj s4 wa := by
          intro h_adj
          -- wa has exactly 2 S-neighbors (from hW_S_neighbors), they are s1 and s3 (from hsx_eq)
          -- If s4 is also adjacent to wa, that's a 3rd S-neighbor
          have hwa_S_card : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
          have hs1_in_filter : s1 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwa_mem.2⟩
          have hs3_in_filter : s3 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs3_in_S, hwa_adj_sx⟩
          have hs4_in_filter : s4 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm h_adj⟩
          have h_three : ({s1, s3, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj wa) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hs1_in_filter
            · exact hs3_in_filter
            · exact hs4_in_filter
          have h_three_card : ({s1, s3, s4} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [mem_singleton]; exact hs_ne34
            · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne13, hs_ne14⟩
          have h_le := Finset.card_le_card h_three
          omega
        -- Now apply p_adjacent_of_shared_w with witnesses t, s2, s4
        have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
          p1 p3 s1 s3 wa
          hp1_nonadj_v hp3_nonadj_v hp_ne13
          (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
          hs1_adj_p1 hs3_adj_p3
          hs1_nonadj_p3 hs3_nonadj_p1
          (G.symm hwa_mem.2) hwa_adj_sx
          hwa_nonadj_v hwa_nonadj_p1 hwa_nonadj_p3
          hs1_s3_nonadj
          t s2 s4
          ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
          ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
          ht_ne_s2 ht_ne_s4 hs_ne24
          (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) (fun h => hwa_nonadj_t (G.symm h))
          hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_wa
          hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_wa
        exact h_nonadj_p1p3 h_p1_p3
      · -- sx = s4, sy = s3: s1 shares wb with s3
        -- By p_adjacent_of_shared_w, p1-p3 would be adjacent, contradicting h_nonadj_p1p3
        rw [hsy_eq] at hwb_adj_sy
        -- wb is adjacent to both s1 and s3, and is in W (non-neighbor of v)
        have hwb_Q := (hW_props wb).mp hwb_mem.1
        have hwb_nonadj_v : ¬G.Adj wb v := fun h => hwb_Q.1 (G.symm h)
        have hwb_nonadj_t : ¬G.Adj wb t := fun h => hwb_Q.2.2 (G.symm h)
        -- wb is not adjacent to p1 (else {p1, s1, wb} is a triangle)
        have hwb_nonadj_p1 : ¬G.Adj wb p1 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p1, s1, wb} := by
            constructor
            · intro a ha b hb hab
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab
              · exact G.symm hs1_adj_p1
              · exact G.symm h_adj
              · exact hs1_adj_p1
              · exact absurd rfl hab
              · exact hwb_mem.2
              · exact h_adj
              · exact G.symm hwb_mem.2
              · exact absurd rfl hab
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact G.ne_of_adj hwb_mem.2
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p1, s1, wb} h_tri_set
        -- wb is not adjacent to p3 (else {p3, s3, wb} is a triangle)
        have hwb_nonadj_p3 : ¬G.Adj wb p3 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p3, s3, wb} := by
            constructor
            · intro a ha b hb hab
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab
              · exact G.symm hs3_adj_p3
              · exact G.symm h_adj
              · exact hs3_adj_p3
              · exact absurd rfl hab
              · exact G.symm hwb_adj_sy
              · exact h_adj
              · exact hwb_adj_sy
              · exact absurd rfl hab
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact (G.ne_of_adj hwb_adj_sy).symm
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p3, s3, wb} h_tri_set
        -- s1-s3 non-adjacent (both in N(v), triangle-free)
        have hs1_s3_nonadj : ¬G.Adj s1 s3 := hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13
        -- s2 not adjacent to wb (wb is in W, and we're in disjoint case for s1/s2)
        have hs2_nonadj_wb : ¬G.Adj s2 wb := by
          intro h_adj
          have hwb_in_s2 : wb ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hwb_mem.1, h_adj⟩
          have hwb_in_inter : wb ∈ (W.filter (G.Adj s1)) ∩ (W.filter (G.Adj s2)) :=
            Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwb_mem, hwb_in_s2⟩
          rw [h_empty] at hwb_in_inter
          exact Finset.notMem_empty wb hwb_in_inter
        have hs4_nonadj_wb : ¬G.Adj s4 wb := by
          intro h_adj
          -- wb has exactly 2 S-neighbors (from hW_S_neighbors), they are s1 and s3
          -- If s4 is also adjacent to wb, that's a 3rd S-neighbor
          have hwb_S_card' : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
          have hs1_in_filter : s1 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm hwb_mem.2⟩
          have hs3_in_filter : s3 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs3_in_S, hwb_adj_sy⟩
          have hs4_in_filter : s4 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs4_in_S, G.symm h_adj⟩
          have h_three : ({s1, s3, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj wb) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hs1_in_filter
            · exact hs3_in_filter
            · exact hs4_in_filter
          have h_three_card : ({s1, s3, s4} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [mem_singleton]; exact hs_ne34
            · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne13, hs_ne14⟩
          have h_le := Finset.card_le_card h_three
          omega
        -- Now apply p_adjacent_of_shared_w with witnesses t, s2, s4
        have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
          p1 p3 s1 s3 wb
          hp1_nonadj_v hp3_nonadj_v hp_ne13
          (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
          hs1_adj_p1 hs3_adj_p3
          hs1_nonadj_p3 hs3_nonadj_p1
          (G.symm hwb_mem.2) hwb_adj_sy
          hwb_nonadj_v hwb_nonadj_p1 hwb_nonadj_p3
          hs1_s3_nonadj
          t s2 s4
          ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
          ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
          ht_ne_s2 ht_ne_s4 hs_ne24
          (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) (fun h => hwb_nonadj_t (G.symm h))
          hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_wb
          hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_wb
        exact h_nonadj_p1p3 h_p1_p3
      · -- sx = s4, sy = s4: s1 and s4 share both wa and wb
        have hs1_adj_v : G.Adj v s1 := by rw [← mem_neighborFinset]; exact hs1_in_N
        have hs4_adj_v' : G.Adj v s4 := by rw [← mem_neighborFinset]; exact hs4_in_N
        have hwa_Q := (hW_props wa).mp hwa_mem.1
        have hwb_Q := (hW_props wb).mp hwb_mem.1
        have hv_ne_wa : v ≠ wa := by
          intro h_eq; have h := hwa_Q.2.1; rw [h_eq] at h
          unfold commonNeighborsCard _root_.commonNeighbors at h
          simp only [Finset.inter_self] at h
          have h_deg : (G.neighborFinset wa).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
          omega
        have hv_ne_wb : v ≠ wb := by
          intro h_eq; have h := hwb_Q.2.1; rw [h_eq] at h
          unfold commonNeighborsCard _root_.commonNeighbors at h
          simp only [Finset.inter_self] at h
          have h_deg : (G.neighborFinset wb).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
          omega
        rw [hsx_eq] at hwa_adj_sx
        rw [hsy_eq] at hwb_adj_sy
        exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 s4 wa wb
          hs1_adj_v hs4_adj_v' hs_ne14 hv_ne_wa hv_ne_wb hab_ne
          hwa_mem.2 hwb_mem.2 (G.symm hwa_adj_sx) (G.symm hwb_adj_sy)
    -- They must differ in at least 1 (since intersection is nonempty but < 2)
    have h_diff : ((W.filter (G.Adj s1)) \ (W.filter (G.Adj s2))).Nonempty := by
      by_contra h_empty
      simp only [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
      -- If s1's W-neighbors ⊆ s2's W-neighbors and both have card 2, they're equal
      have h_eq : W.filter (G.Adj s1) = W.filter (G.Adj s2) := by
        apply Finset.eq_of_subset_of_card_le h_empty
        rw [hs1_W_eq2, hs2_W_eq2]
      -- If they're equal with card 2, extract two distinct W-vertices they share
      obtain ⟨wa, wb, hwa_mem, hwb_mem, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (W.filter (G.Adj s1)).card)
      simp only [Finset.mem_filter] at hwa_mem hwb_mem
      -- s2 also adjacent to wa, wb via h_eq
      have hs2_wa : G.Adj s2 wa := by
        have : wa ∈ W.filter (G.Adj s2) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwa_mem
        exact (Finset.mem_filter.mp this).2
      have hs2_wb : G.Adj s2 wb := by
        have : wb ∈ W.filter (G.Adj s2) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwb_mem
        exact (Finset.mem_filter.mp this).2
      -- Get v adjacencies: si ∈ N means v ~ si
      have hs1_adj_v : G.Adj v s1 := by rw [← mem_neighborFinset]; exact hs1_in_N
      have hs2_adj_v : G.Adj v s2 := by rw [← mem_neighborFinset]; exact hs2_in_N
      -- v ≠ wa, wb via commonNeighborsCard contradiction (5 ≠ 2)
      have hwa_Q := (hW_props wa).mp hwa_mem.1
      have hwb_Q := (hW_props wb).mp hwb_mem.1
      have hv_ne_wa : v ≠ wa := by
        intro h_eq
        have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wa).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
        omega
      have hv_ne_wb : v ≠ wb := by
        intro h_eq
        have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wb).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
        omega
      -- Apply S_pair_share_at_most_one_W: s1 and s2 sharing {wa, wb} contradicts ≤2 common neighbors
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s1 s2 wa wb
        hs1_adj_v hs2_adj_v hs_ne12 hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 hs2_wa hs2_wb
    exact two_element_sets_intersection (W.filter (G.Adj s1)) (W.filter (G.Adj s2))
            hs1_W_eq2 hs2_W_eq2 h_share h_diff

  -- Extract the unique shared W
  obtain ⟨w1', hw1'_eq⟩ := Finset.card_eq_one.mp hs12_share_W
  have hw1'_shared : w1' ∈ W.filter (G.Adj s1) ∩ W.filter (G.Adj s2) := by
    rw [hw1'_eq]; exact Finset.mem_singleton_self w1'
  have hw1'_in_W : w1' ∈ W := by
    have h := Finset.mem_inter.mp hw1'_shared
    exact (Finset.mem_filter.mp h.1).1
  have hw1'_adj_s1 : G.Adj w1' s1 := by
    have h := Finset.mem_inter.mp hw1'_shared
    exact G.symm (Finset.mem_filter.mp h.1).2
  have hw1'_adj_s2 : G.Adj w1' s2 := by
    have h := Finset.mem_inter.mp hw1'_shared
    exact G.symm (Finset.mem_filter.mp h.2).2

  -- Similarly for other pairs (same pattern as hs12_share_W)
  have hs23_share_W : ((W.filter (G.Adj s2)) ∩ (W.filter (G.Adj s3))).card = 1 := by
    have hs2_W_eq2 : (W.filter (G.Adj s2)).card = 2 := hs_W_eq2 s2 hs2_in_S
    have hs3_W_eq2 : (W.filter (G.Adj s3)).card = 2 := hs_W_eq2 s3 hs3_in_S
    have h_share : ((W.filter (G.Adj s2)) ∩ (W.filter (G.Adj s3))).Nonempty := by
      by_contra h_empty; simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disjoint : Disjoint (W.filter (G.Adj s2)) (W.filter (G.Adj s3)) := by
        rw [Finset.disjoint_iff_inter_eq_empty, h_empty]
      have h_union_card : ((W.filter (G.Adj s2)) ∪ (W.filter (G.Adj s3))).card = 4 := by
        rw [Finset.card_union_of_disjoint h_disjoint, hs2_W_eq2, hs3_W_eq2]
      have h_sub : (W.filter (G.Adj s2)) ∪ (W.filter (G.Adj s3)) ⊆ W := by
        intro x hx; simp only [Finset.mem_union, Finset.mem_filter] at hx
        rcases hx with h | h <;> exact h.1
      -- If s2 and s3's W-neighbors are disjoint, we show one of s2-s4 or s1-s3 shares a W
      -- Get a W-vertex from s2's W-neighbors
      have hs2_W_nonempty : (W.filter (G.Adj s2)).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨wa, hwa_mem⟩ := hs2_W_nonempty
      simp only [Finset.mem_filter] at hwa_mem
      -- wa has exactly 2 S-neighbors
      have hwa_S_card : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
      have hs2_in_filter : s2 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwa_mem.2⟩
      -- wa's other S-neighbor is in S \ {s2}
      have hwa_other : ∃ sx ∈ S, sx ≠ s2 ∧ G.Adj wa sx := by
        have h_sub : {s2} ⊆ S.filter (G.Adj wa) := Finset.singleton_subset_iff.mpr hs2_in_filter
        have h_diff_card : ((S.filter (G.Adj wa)) \ {s2}).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwa_S_card]
        obtain ⟨sx, hsx_mem⟩ := Finset.card_eq_one.mp h_diff_card
        have hsx_in : sx ∈ (S.filter (G.Adj wa)) \ {s2} := by rw [hsx_mem]; simp
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsx_in
        exact ⟨sx, hsx_in.1.1, hsx_in.2, hsx_in.1.2⟩
      obtain ⟨sx, hsx_in_S, hsx_ne_s2, hwa_adj_sx⟩ := hwa_other
      -- wa is not adjacent to s3 (since disjoint W-neighbors)
      have hwa_nonadj_s3 : ¬G.Adj wa s3 := by
        intro h_adj
        have hwa_in_s3 : wa ∈ W.filter (G.Adj s3) := Finset.mem_filter.mpr ⟨hwa_mem.1, G.symm h_adj⟩
        have hwa_in_inter : wa ∈ (W.filter (G.Adj s2)) ∩ (W.filter (G.Adj s3)) :=
          Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwa_mem, hwa_in_s3⟩
        rw [h_empty] at hwa_in_inter
        exact Finset.notMem_empty wa hwa_in_inter
      -- sx ≠ s3 (since wa not adjacent to s3)
      have hsx_ne_s3 : sx ≠ s3 := fun h => hwa_nonadj_s3 (h ▸ hwa_adj_sx)
      -- So sx ∈ {s1, s4}
      have hsx_in_s14 : sx = s1 ∨ sx = s4 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsx_in_S
        rcases hsx_in_S with rfl | rfl | rfl | rfl
        · left; rfl
        · exact (hsx_ne_s2 rfl).elim
        · exact (hsx_ne_s3 rfl).elim
        · right; rfl
      rcases hsx_in_s14 with hsx_eq | hsx_eq
      · -- sx = s1: s1 and s2 share wa
        -- This should eventually be resolved by hs12_share_W, but here we're proving hs23_share_W
        -- The issue is this case doesn't directly give us p2-p4 adjacent
        -- However, s2's other W-neighbor wb must have another S-neighbor in {s1, s4}
        -- Get wb from s2's W-neighbors
        have hs2_W_card : (W.filter (G.Adj s2)).card = 2 := hs2_W_eq2
        obtain ⟨wb, hwb_mem, hab⟩ : ∃ wb ∈ W.filter (G.Adj s2), wb ≠ wa := by
          have h_sub : {wa} ⊆ W.filter (G.Adj s2) := Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr hwa_mem)
          have h_diff_card : ((W.filter (G.Adj s2)) \ {wa}).card = 1 := by
            rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hs2_W_card]
          obtain ⟨wb, hwb_eq⟩ := Finset.card_eq_one.mp h_diff_card
          have hwb_in : wb ∈ (W.filter (G.Adj s2)) \ {wa} := by rw [hwb_eq]; simp
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hwb_in
          exact ⟨wb, hwb_in.1, hwb_in.2⟩
        simp only [Finset.mem_filter] at hwb_mem
        have hwb_S_card : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
        have hs2_in_wb_filter : s2 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwb_mem.2⟩
        have hwb_other : ∃ sy ∈ S, sy ≠ s2 ∧ G.Adj wb sy := by
          have h_sub : {s2} ⊆ S.filter (G.Adj wb) := Finset.singleton_subset_iff.mpr hs2_in_wb_filter
          have h_diff_card' : ((S.filter (G.Adj wb)) \ {s2}).card = 1 := by
            rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwb_S_card]
          obtain ⟨sy, hsy_mem⟩ := Finset.card_eq_one.mp h_diff_card'
          have hsy_in : sy ∈ (S.filter (G.Adj wb)) \ {s2} := by rw [hsy_mem]; simp
          rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsy_in
          exact ⟨sy, hsy_in.1.1, hsy_in.2, hsy_in.1.2⟩
        obtain ⟨sy, hsy_in_S, hsy_ne_s2, hwb_adj_sy⟩ := hwb_other
        -- wb is not adjacent to s3 (since disjoint W-neighbors)
        have hwb_nonadj_s3 : ¬G.Adj wb s3 := by
          intro h_adj
          have hwb_in_s3 : wb ∈ W.filter (G.Adj s3) := Finset.mem_filter.mpr ⟨hwb_mem.1, G.symm h_adj⟩
          have hwb_in_inter : wb ∈ (W.filter (G.Adj s2)) ∩ (W.filter (G.Adj s3)) :=
            Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwb_mem, hwb_in_s3⟩
          rw [h_empty] at hwb_in_inter
          exact Finset.notMem_empty wb hwb_in_inter
        have hsy_ne_s3 : sy ≠ s3 := fun h => hwb_nonadj_s3 (h ▸ hwb_adj_sy)
        have hsy_in_s14 : sy = s1 ∨ sy = s4 := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsy_in_S
          rcases hsy_in_S with rfl | rfl | rfl | rfl
          · left; rfl
          · exact (hsy_ne_s2 rfl).elim
          · exact (hsy_ne_s3 rfl).elim
          · right; rfl
        rcases hsy_in_s14 with hsy_eq | hsy_eq
        · -- sx = s1, sy = s1: both wa and wb connect s2 to s1
          -- But then s1's W-neighbors include wa and wb, so s1 shares 2 W's with s2
          -- This contradicts S_pair_share_at_most_one_W
          rw [hsx_eq] at hwa_adj_sx
          rw [hsy_eq] at hwb_adj_sy
          have hs2_adj_v : G.Adj v s2 := by rw [← mem_neighborFinset]; exact hs2_in_N
          have hs1_adj_v : G.Adj v s1 := by rw [← mem_neighborFinset]; exact hs1_in_N
          have hwa_Q := (hW_props wa).mp hwa_mem.1
          have hwb_Q := (hW_props wb).mp hwb_mem.1
          have hv_ne_wa : v ≠ wa := by
            intro h_eq; have h := hwa_Q.2.1; rw [h_eq] at h
            unfold commonNeighborsCard _root_.commonNeighbors at h
            simp only [Finset.inter_self] at h
            have h_deg : (G.neighborFinset wa).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
            omega
          have hv_ne_wb : v ≠ wb := by
            intro h_eq; have h := hwb_Q.2.1; rw [h_eq] at h
            unfold commonNeighborsCard _root_.commonNeighbors at h
            simp only [Finset.inter_self] at h
            have h_deg : (G.neighborFinset wb).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
            omega
          exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s2 s1 wa wb
            hs2_adj_v hs1_adj_v hs_ne12.symm hv_ne_wa hv_ne_wb hab.symm
            hwa_mem.2 hwb_mem.2 (G.symm hwa_adj_sx) (G.symm hwb_adj_sy)
        · -- sx = s1, sy = s4: s2 shares wb with s4
          -- By p_adjacent_of_shared_w, p2-p4 would be adjacent, contradicting h_nonadj_p2p4
          rw [hsy_eq] at hwb_adj_sy
          have hwb_Q := (hW_props wb).mp hwb_mem.1
          have hwb_nonadj_v : ¬G.Adj wb v := fun h => hwb_Q.1 (G.symm h)
          have hwb_nonadj_t : ¬G.Adj wb t := fun h => hwb_Q.2.2 (G.symm h)
          -- wb is not adjacent to p2 (else {p2, s2, wb} is a triangle)
          have hwb_nonadj_p2 : ¬G.Adj wb p2 := by
            intro h_adj
            have h_tri_set : G.IsNClique 3 {p2, s2, wb} := by
              constructor
              · intro a ha b hb hab'
                simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
                rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                · exact absurd rfl hab'
                · exact G.symm hs2_adj_p2
                · exact G.symm h_adj
                · exact hs2_adj_p2
                · exact absurd rfl hab'
                · exact hwb_mem.2
                · exact h_adj
                · exact G.symm hwb_mem.2
                · exact absurd rfl hab'
              · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [mem_singleton]; exact G.ne_of_adj hwb_mem.2
                · simp only [mem_insert, mem_singleton, not_or]
                  exact ⟨(G.ne_of_adj hs2_adj_p2).symm, (G.ne_of_adj h_adj).symm⟩
            exact h_tri {p2, s2, wb} h_tri_set
          -- wb is not adjacent to p4 (else {p4, s4, wb} is a triangle)
          have hwb_nonadj_p4 : ¬G.Adj wb p4 := by
            intro h_adj
            have h_tri_set : G.IsNClique 3 {p4, s4, wb} := by
              constructor
              · intro a ha b hb hab'
                simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
                rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                · exact absurd rfl hab'
                · exact G.symm hs4_adj_p4
                · exact G.symm h_adj
                · exact hs4_adj_p4
                · exact absurd rfl hab'
                · exact G.symm hwb_adj_sy
                · exact h_adj
                · exact hwb_adj_sy
                · exact absurd rfl hab'
              · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [mem_singleton]; exact (G.ne_of_adj hwb_adj_sy).symm
                · simp only [mem_insert, mem_singleton, not_or]
                  exact ⟨(G.ne_of_adj hs4_adj_p4).symm, (G.ne_of_adj h_adj).symm⟩
            exact h_tri {p4, s4, wb} h_tri_set
          -- s2-s4 non-adjacent
          have hs2_s4_nonadj : ¬G.Adj s2 s4 := hN_indep_pairs s2 s4 hs2_in_N hs4_in_N hs_ne24
          -- s1 not adjacent to wb: use counting
          have hs1_nonadj_wb : ¬G.Adj s1 wb := by
            intro h_adj
            have hwb_S_card' : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
            have hs2_in_f : s2 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwb_mem.2⟩
            have hs4_in_f : s4 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs4_in_S, hwb_adj_sy⟩
            have hs1_in_f : s1 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm h_adj⟩
            have h_three : ({s2, s4, s1} : Finset (Fin 18)) ⊆ S.filter (G.Adj wb) := by
              intro x hx
              simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · exact hs2_in_f
              · exact hs4_in_f
              · exact hs1_in_f
            have h_three_card : ({s2, s4, s1} : Finset (Fin 18)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact hs_ne14.symm
              · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne24, hs_ne12.symm⟩
            have h_le := Finset.card_le_card h_three
            omega
          -- s3 not adjacent to wb: disjoint case
          have hs3_nonadj_wb' : ¬G.Adj s3 wb := fun h => hwb_nonadj_s3 (G.symm h)
          -- Apply p_adjacent_of_shared_w
          have h_p2_p4 : G.Adj p2 p4 := p_adjacent_of_shared_w h_tri h_no6 v
            p2 p4 s2 s4 wb
            hp2_nonadj_v hp4_nonadj_v hp_ne24
            (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N) hs_ne24
            hs2_adj_p2 hs4_adj_p4
            hs2_nonadj_p4 hs4_nonadj_p2
            (G.symm hwb_mem.2) hwb_adj_sy
            hwb_nonadj_v hwb_nonadj_p2 hwb_nonadj_p4
            hs2_s4_nonadj
            t s1 s3
            ht_adj_v (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N)
            ht_ne_s2 ht_ne_s4 hs_ne12 hs_ne14 hs_ne23.symm hs_ne34
            ht_ne_s1 ht_ne_s3 hs_ne13
            (h2_unique t ht_in_N ht_ne_s2) (h4_unique t ht_in_N ht_ne_s4) (fun h => hwb_nonadj_t (G.symm h))
            hs1_nonadj_p2 hs1_nonadj_p4 hs1_nonadj_wb
            hs3_nonadj_p2 hs3_nonadj_p4 hs3_nonadj_wb'
          exact h_nonadj_p2p4 h_p2_p4
      · -- sx = s4: s2 and s4 share wa
        -- By p_adjacent_of_shared_w, p2-p4 would be adjacent, contradicting h_nonadj_p2p4
        rw [hsx_eq] at hwa_adj_sx
        have hwa_Q := (hW_props wa).mp hwa_mem.1
        have hwa_nonadj_v : ¬G.Adj wa v := fun h => hwa_Q.1 (G.symm h)
        have hwa_nonadj_t : ¬G.Adj wa t := fun h => hwa_Q.2.2 (G.symm h)
        -- wa is not adjacent to p2 (else {p2, s2, wa} is a triangle)
        have hwa_nonadj_p2 : ¬G.Adj wa p2 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p2, s2, wa} := by
            constructor
            · intro a ha b hb hab'
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab'
              · exact G.symm hs2_adj_p2
              · exact G.symm h_adj
              · exact hs2_adj_p2
              · exact absurd rfl hab'
              · exact hwa_mem.2
              · exact h_adj
              · exact G.symm hwa_mem.2
              · exact absurd rfl hab'
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact G.ne_of_adj hwa_mem.2
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs2_adj_p2).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p2, s2, wa} h_tri_set
        -- wa is not adjacent to p4 (else {p4, s4, wa} is a triangle)
        have hwa_nonadj_p4 : ¬G.Adj wa p4 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p4, s4, wa} := by
            constructor
            · intro a ha b hb hab'
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab'
              · exact G.symm hs4_adj_p4
              · exact G.symm h_adj
              · exact hs4_adj_p4
              · exact absurd rfl hab'
              · exact G.symm hwa_adj_sx
              · exact h_adj
              · exact hwa_adj_sx
              · exact absurd rfl hab'
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact (G.ne_of_adj hwa_adj_sx).symm
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs4_adj_p4).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p4, s4, wa} h_tri_set
        -- s2-s4 non-adjacent
        have hs2_s4_nonadj : ¬G.Adj s2 s4 := hN_indep_pairs s2 s4 hs2_in_N hs4_in_N hs_ne24
        -- s1 not adjacent to wa: use counting
        have hs1_nonadj_wa : ¬G.Adj s1 wa := by
          intro h_adj
          have hwa_S_card' : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
          have hs2_in_f : s2 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm hwa_mem.2⟩
          have hs4_in_f : s4 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs4_in_S, hwa_adj_sx⟩
          have hs1_in_f : s1 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs1_in_S, G.symm h_adj⟩
          have h_three : ({s2, s4, s1} : Finset (Fin 18)) ⊆ S.filter (G.Adj wa) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hs2_in_f
            · exact hs4_in_f
            · exact hs1_in_f
          have h_three_card : ({s2, s4, s1} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [mem_singleton]; exact hs_ne14.symm
            · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne24, hs_ne12.symm⟩
          have h_le := Finset.card_le_card h_three
          omega
        -- s3 not adjacent to wa: disjoint case
        have hs3_nonadj_wa' : ¬G.Adj s3 wa := fun h => hwa_nonadj_s3 (G.symm h)
        -- Apply p_adjacent_of_shared_w
        have h_p2_p4 : G.Adj p2 p4 := p_adjacent_of_shared_w h_tri h_no6 v
          p2 p4 s2 s4 wa
          hp2_nonadj_v hp4_nonadj_v hp_ne24
          (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N) hs_ne24
          hs2_adj_p2 hs4_adj_p4
          hs2_nonadj_p4 hs4_nonadj_p2
          (G.symm hwa_mem.2) hwa_adj_sx
          hwa_nonadj_v hwa_nonadj_p2 hwa_nonadj_p4
          hs2_s4_nonadj
          t s1 s3
          ht_adj_v (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N)
          ht_ne_s2 ht_ne_s4 hs_ne12 hs_ne14 hs_ne23.symm hs_ne34
          ht_ne_s1 ht_ne_s3 hs_ne13
          (h2_unique t ht_in_N ht_ne_s2) (h4_unique t ht_in_N ht_ne_s4) (fun h => hwa_nonadj_t (G.symm h))
          hs1_nonadj_p2 hs1_nonadj_p4 hs1_nonadj_wa
          hs3_nonadj_p2 hs3_nonadj_p4 hs3_nonadj_wa'
        exact h_nonadj_p2p4 h_p2_p4
    have h_diff : ((W.filter (G.Adj s2)) \ (W.filter (G.Adj s3))).Nonempty := by
      by_contra h_empty; simp only [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
      have h_eq : W.filter (G.Adj s2) = W.filter (G.Adj s3) :=
        Finset.eq_of_subset_of_card_le h_empty (by rw [hs2_W_eq2, hs3_W_eq2])
      -- Extract two distinct W-vertices from the shared set
      obtain ⟨wa, wb, hwa_mem, hwb_mem, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (W.filter (G.Adj s2)).card)
      simp only [Finset.mem_filter] at hwa_mem hwb_mem
      have hs3_wa : G.Adj s3 wa := by
        have : wa ∈ W.filter (G.Adj s3) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwa_mem
        exact (Finset.mem_filter.mp this).2
      have hs3_wb : G.Adj s3 wb := by
        have : wb ∈ W.filter (G.Adj s3) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwb_mem
        exact (Finset.mem_filter.mp this).2
      have hs2_adj_v : G.Adj v s2 := by rw [← mem_neighborFinset]; exact hs2_in_N
      have hs3_adj_v : G.Adj v s3 := by rw [← mem_neighborFinset]; exact hs3_in_N
      have hwa_Q := (hW_props wa).mp hwa_mem.1
      have hwb_Q := (hW_props wb).mp hwb_mem.1
      have hv_ne_wa : v ≠ wa := by
        intro h_eq
        have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wa).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
        omega
      have hv_ne_wb : v ≠ wb := by
        intro h_eq
        have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wb).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
        omega
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s2 s3 wa wb
        hs2_adj_v hs3_adj_v hs_ne23 hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 hs3_wa hs3_wb
    exact two_element_sets_intersection (W.filter (G.Adj s2)) (W.filter (G.Adj s3))
            hs2_W_eq2 hs3_W_eq2 h_share h_diff

  have hs34_share_W : ((W.filter (G.Adj s3)) ∩ (W.filter (G.Adj s4))).card = 1 := by
    have hs3_W_eq2 : (W.filter (G.Adj s3)).card = 2 := hs_W_eq2 s3 hs3_in_S
    have hs4_W_eq2 : (W.filter (G.Adj s4)).card = 2 := hs_W_eq2 s4 hs4_in_S
    have h_share : ((W.filter (G.Adj s3)) ∩ (W.filter (G.Adj s4))).Nonempty := by
      by_contra h_empty; simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
      have h_disjoint : Disjoint (W.filter (G.Adj s3)) (W.filter (G.Adj s4)) := by
        rw [Finset.disjoint_iff_inter_eq_empty, h_empty]
      have h_union_card : ((W.filter (G.Adj s3)) ∪ (W.filter (G.Adj s4))).card = 4 := by
        rw [Finset.card_union_of_disjoint h_disjoint, hs3_W_eq2, hs4_W_eq2]
      have h_sub : (W.filter (G.Adj s3)) ∪ (W.filter (G.Adj s4)) ⊆ W := by
        intro x hx; simp only [Finset.mem_union, Finset.mem_filter] at hx
        rcases hx with h | h <;> exact h.1
      -- If s3 and s4's W-neighbors are disjoint, we get p1-p3 adjacent or contradiction
      -- Get a W-vertex from s3's W-neighbors
      have hs3_W_nonempty : (W.filter (G.Adj s3)).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨wa, hwa_mem⟩ := hs3_W_nonempty
      simp only [Finset.mem_filter] at hwa_mem
      -- wa has exactly 2 S-neighbors
      have hwa_S_card : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
      have hs3_in_filter : s3 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwa_mem.2⟩
      -- wa's other S-neighbor is in S \ {s3}
      have hwa_other : ∃ sx ∈ S, sx ≠ s3 ∧ G.Adj wa sx := by
        have h_sub : {s3} ⊆ S.filter (G.Adj wa) := Finset.singleton_subset_iff.mpr hs3_in_filter
        have h_diff_card : ((S.filter (G.Adj wa)) \ {s3}).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwa_S_card]
        obtain ⟨sx, hsx_mem⟩ := Finset.card_eq_one.mp h_diff_card
        have hsx_in : sx ∈ (S.filter (G.Adj wa)) \ {s3} := by rw [hsx_mem]; simp
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsx_in
        exact ⟨sx, hsx_in.1.1, hsx_in.2, hsx_in.1.2⟩
      obtain ⟨sx, hsx_in_S, hsx_ne_s3, hwa_adj_sx⟩ := hwa_other
      -- wa is not adjacent to s4 (since disjoint W-neighbors)
      have hwa_nonadj_s4 : ¬G.Adj wa s4 := by
        intro h_adj
        have hwa_in_s4 : wa ∈ W.filter (G.Adj s4) := Finset.mem_filter.mpr ⟨hwa_mem.1, G.symm h_adj⟩
        have hwa_in_inter : wa ∈ (W.filter (G.Adj s3)) ∩ (W.filter (G.Adj s4)) :=
          Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwa_mem, hwa_in_s4⟩
        rw [h_empty] at hwa_in_inter
        exact Finset.notMem_empty wa hwa_in_inter
      have hsx_ne_s4 : sx ≠ s4 := fun h => hwa_nonadj_s4 (h ▸ hwa_adj_sx)
      -- So sx ∈ {s1, s2}
      have hsx_in_s12 : sx = s1 ∨ sx = s2 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsx_in_S
        rcases hsx_in_S with rfl | rfl | rfl | rfl
        · left; rfl
        · right; rfl
        · exact (hsx_ne_s3 rfl).elim
        · exact (hsx_ne_s4 rfl).elim
      rcases hsx_in_s12 with hsx_eq | hsx_eq
      · -- sx = s1: s1 and s3 share wa
        -- By p_adjacent_of_shared_w, p1-p3 would be adjacent, contradicting h_nonadj_p1p3
        rw [hsx_eq] at hwa_adj_sx
        have hwa_Q := (hW_props wa).mp hwa_mem.1
        have hwa_nonadj_v : ¬G.Adj wa v := fun h => hwa_Q.1 (G.symm h)
        have hwa_nonadj_t : ¬G.Adj wa t := fun h => hwa_Q.2.2 (G.symm h)
        have hwa_nonadj_p1 : ¬G.Adj wa p1 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p1, s1, wa} := by
            constructor
            · intro a ha b hb hab'
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab'
              · exact G.symm hs1_adj_p1
              · exact G.symm h_adj
              · exact hs1_adj_p1
              · exact absurd rfl hab'
              · exact G.symm hwa_adj_sx
              · exact h_adj
              · exact hwa_adj_sx
              · exact absurd rfl hab'
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact (G.ne_of_adj hwa_adj_sx).symm
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p1, s1, wa} h_tri_set
        have hwa_nonadj_p3 : ¬G.Adj wa p3 := by
          intro h_adj
          have h_tri_set : G.IsNClique 3 {p3, s3, wa} := by
            constructor
            · intro a ha b hb hab'
              simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
              · exact absurd rfl hab'
              · exact G.symm hs3_adj_p3
              · exact G.symm h_adj
              · exact hs3_adj_p3
              · exact absurd rfl hab'
              · exact hwa_mem.2
              · exact h_adj
              · exact G.symm hwa_mem.2
              · exact absurd rfl hab'
            · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact G.ne_of_adj hwa_mem.2
              · simp only [mem_insert, mem_singleton, not_or]
                exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
          exact h_tri {p3, s3, wa} h_tri_set
        have hs1_s3_nonadj : ¬G.Adj s1 s3 := hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13
        have hs2_nonadj_wa : ¬G.Adj s2 wa := by
          intro h_adj
          have hwa_S_card' : (S.filter (G.Adj wa)).card = 2 := hW_S_neighbors wa hwa_mem.1
          have hs1_in_f : s1 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs1_in_S, hwa_adj_sx⟩
          have hs3_in_f : s3 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwa_mem.2⟩
          have hs2_in_f : s2 ∈ S.filter (G.Adj wa) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm h_adj⟩
          have h_three : ({s1, s3, s2} : Finset (Fin 18)) ⊆ S.filter (G.Adj wa) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hs1_in_f
            · exact hs3_in_f
            · exact hs2_in_f
          have h_three_card : ({s1, s3, s2} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [mem_singleton]; exact hs_ne23.symm
            · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne13, hs_ne12⟩
          have h_le := Finset.card_le_card h_three
          omega
        have hs4_nonadj_wa' : ¬G.Adj s4 wa := fun h => hwa_nonadj_s4 (G.symm h)
        have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
          p1 p3 s1 s3 wa
          hp1_nonadj_v hp3_nonadj_v hp_ne13
          (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
          hs1_adj_p1 hs3_adj_p3
          hs1_nonadj_p3 hs3_nonadj_p1
          hwa_adj_sx (G.symm hwa_mem.2)
          hwa_nonadj_v hwa_nonadj_p1 hwa_nonadj_p3
          hs1_s3_nonadj
          t s2 s4
          ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
          ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
          ht_ne_s2 ht_ne_s4 hs_ne24
          (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) (fun h => hwa_nonadj_t (G.symm h))
          hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_wa
          hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_wa'
        exact h_nonadj_p1p3 h_p1_p3
      · -- sx = s2: s2 and s3 share wa
        -- Get s3's other W-neighbor wb
        have hs3_W_card : (W.filter (G.Adj s3)).card = 2 := hs3_W_eq2
        obtain ⟨wb, hwb_mem, hab⟩ : ∃ wb ∈ W.filter (G.Adj s3), wb ≠ wa := by
          have h_sub : {wa} ⊆ W.filter (G.Adj s3) := Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr hwa_mem)
          have h_diff_card : ((W.filter (G.Adj s3)) \ {wa}).card = 1 := by
            rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hs3_W_card]
          obtain ⟨wb, hwb_eq⟩ := Finset.card_eq_one.mp h_diff_card
          have hwb_in : wb ∈ (W.filter (G.Adj s3)) \ {wa} := by rw [hwb_eq]; simp
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hwb_in
          exact ⟨wb, hwb_in.1, hwb_in.2⟩
        simp only [Finset.mem_filter] at hwb_mem
        have hwb_S_card : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
        have hs3_in_wb_filter : s3 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwb_mem.2⟩
        have hwb_other : ∃ sy ∈ S, sy ≠ s3 ∧ G.Adj wb sy := by
          have h_sub : {s3} ⊆ S.filter (G.Adj wb) := Finset.singleton_subset_iff.mpr hs3_in_wb_filter
          have h_diff_card' : ((S.filter (G.Adj wb)) \ {s3}).card = 1 := by
            rw [Finset.card_sdiff_of_subset h_sub, Finset.card_singleton, hwb_S_card]
          obtain ⟨sy, hsy_mem⟩ := Finset.card_eq_one.mp h_diff_card'
          have hsy_in : sy ∈ (S.filter (G.Adj wb)) \ {s3} := by rw [hsy_mem]; simp
          rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton] at hsy_in
          exact ⟨sy, hsy_in.1.1, hsy_in.2, hsy_in.1.2⟩
        obtain ⟨sy, hsy_in_S, hsy_ne_s3, hwb_adj_sy⟩ := hwb_other
        have hwb_nonadj_s4 : ¬G.Adj wb s4 := by
          intro h_adj
          have hwb_in_s4 : wb ∈ W.filter (G.Adj s4) := Finset.mem_filter.mpr ⟨hwb_mem.1, G.symm h_adj⟩
          have hwb_in_inter : wb ∈ (W.filter (G.Adj s3)) ∩ (W.filter (G.Adj s4)) :=
            Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr hwb_mem, hwb_in_s4⟩
          rw [h_empty] at hwb_in_inter
          exact Finset.notMem_empty wb hwb_in_inter
        have hsy_ne_s4 : sy ≠ s4 := fun h => hwb_nonadj_s4 (h ▸ hwb_adj_sy)
        have hsy_in_s12 : sy = s1 ∨ sy = s2 := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hsy_in_S
          rcases hsy_in_S with rfl | rfl | rfl | rfl
          · left; rfl
          · right; rfl
          · exact (hsy_ne_s3 rfl).elim
          · exact (hsy_ne_s4 rfl).elim
        rcases hsy_in_s12 with hsy_eq | hsy_eq
        · -- sx = s2, sy = s1: s1 and s3 share wb
          rw [hsy_eq] at hwb_adj_sy
          have hwb_Q := (hW_props wb).mp hwb_mem.1
          have hwb_nonadj_v : ¬G.Adj wb v := fun h => hwb_Q.1 (G.symm h)
          have hwb_nonadj_t : ¬G.Adj wb t := fun h => hwb_Q.2.2 (G.symm h)
          have hwb_nonadj_p1 : ¬G.Adj wb p1 := by
            intro h_adj
            have h_tri_set : G.IsNClique 3 {p1, s1, wb} := by
              constructor
              · intro a ha b hb hab'
                simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
                rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                · exact absurd rfl hab'
                · exact G.symm hs1_adj_p1
                · exact G.symm h_adj
                · exact hs1_adj_p1
                · exact absurd rfl hab'
                · exact G.symm hwb_adj_sy
                · exact h_adj
                · exact hwb_adj_sy
                · exact absurd rfl hab'
              · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [mem_singleton]; exact (G.ne_of_adj hwb_adj_sy).symm
                · simp only [mem_insert, mem_singleton, not_or]
                  exact ⟨(G.ne_of_adj hs1_adj_p1).symm, (G.ne_of_adj h_adj).symm⟩
            exact h_tri {p1, s1, wb} h_tri_set
          have hwb_nonadj_p3 : ¬G.Adj wb p3 := by
            intro h_adj
            have h_tri_set : G.IsNClique 3 {p3, s3, wb} := by
              constructor
              · intro a ha b hb hab'
                simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
                rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                · exact absurd rfl hab'
                · exact G.symm hs3_adj_p3
                · exact G.symm h_adj
                · exact hs3_adj_p3
                · exact absurd rfl hab'
                · exact hwb_mem.2
                · exact h_adj
                · exact G.symm hwb_mem.2
                · exact absurd rfl hab'
              · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
                · simp only [mem_singleton]; exact G.ne_of_adj hwb_mem.2
                · simp only [mem_insert, mem_singleton, not_or]
                  exact ⟨(G.ne_of_adj hs3_adj_p3).symm, (G.ne_of_adj h_adj).symm⟩
            exact h_tri {p3, s3, wb} h_tri_set
          have hs1_s3_nonadj : ¬G.Adj s1 s3 := hN_indep_pairs s1 s3 hs1_in_N hs3_in_N hs_ne13
          have hs2_nonadj_wb : ¬G.Adj s2 wb := by
            intro h_adj
            have hwb_S_card' : (S.filter (G.Adj wb)).card = 2 := hW_S_neighbors wb hwb_mem.1
            have hs1_in_f : s1 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs1_in_S, hwb_adj_sy⟩
            have hs3_in_f : s3 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs3_in_S, G.symm hwb_mem.2⟩
            have hs2_in_f : s2 ∈ S.filter (G.Adj wb) := Finset.mem_filter.mpr ⟨hs2_in_S, G.symm h_adj⟩
            have h_three : ({s1, s3, s2} : Finset (Fin 18)) ⊆ S.filter (G.Adj wb) := by
              intro x hx
              simp only [mem_insert, mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · exact hs1_in_f
              · exact hs3_in_f
              · exact hs2_in_f
            have h_three_card : ({s1, s3, s2} : Finset (Fin 18)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp only [mem_singleton]; exact hs_ne23.symm
              · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hs_ne13, hs_ne12⟩
            have h_le := Finset.card_le_card h_three
            omega
          have hs4_nonadj_wb' : ¬G.Adj s4 wb := fun h => hwb_nonadj_s4 (G.symm h)
          have h_p1_p3 : G.Adj p1 p3 := p_adjacent_of_shared_w h_tri h_no6 v
            p1 p3 s1 s3 wb
            hp1_nonadj_v hp3_nonadj_v hp_ne13
            (by rw [← mem_neighborFinset]; exact hs1_in_N) (by rw [← mem_neighborFinset]; exact hs3_in_N) hs_ne13
            hs1_adj_p1 hs3_adj_p3
            hs1_nonadj_p3 hs3_nonadj_p1
            hwb_adj_sy (G.symm hwb_mem.2)
            hwb_nonadj_v hwb_nonadj_p1 hwb_nonadj_p3
            hs1_s3_nonadj
            t s2 s4
            ht_adj_v (by rw [← mem_neighborFinset]; exact hs2_in_N) (by rw [← mem_neighborFinset]; exact hs4_in_N)
            ht_ne_s1 ht_ne_s3 hs_ne12.symm hs_ne23 hs_ne14.symm hs_ne34.symm
            ht_ne_s2 ht_ne_s4 hs_ne24
            (h1_unique t ht_in_N ht_ne_s1) (h3_unique t ht_in_N ht_ne_s3) (fun h => hwb_nonadj_t (G.symm h))
            hs2_nonadj_p1 hs2_nonadj_p3 hs2_nonadj_wb
            hs4_nonadj_p1 hs4_nonadj_p3 hs4_nonadj_wb'
          exact h_nonadj_p1p3 h_p1_p3
        · -- sx = s2, sy = s2: both wa and wb connect s3 to s2
          -- This contradicts S_pair_share_at_most_one_W for s2-s3
          rw [hsx_eq] at hwa_adj_sx
          rw [hsy_eq] at hwb_adj_sy
          have hs2_adj_v : G.Adj v s2 := by rw [← mem_neighborFinset]; exact hs2_in_N
          have hs3_adj_v : G.Adj v s3 := by rw [← mem_neighborFinset]; exact hs3_in_N
          have hwa_Q := (hW_props wa).mp hwa_mem.1
          have hwb_Q := (hW_props wb).mp hwb_mem.1
          have hv_ne_wa : v ≠ wa := by
            intro h_eq; have h := hwa_Q.2.1; rw [h_eq] at h
            unfold commonNeighborsCard _root_.commonNeighbors at h
            simp only [Finset.inter_self] at h
            have h_deg : (G.neighborFinset wa).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
            omega
          have hv_ne_wb : v ≠ wb := by
            intro h_eq; have h := hwb_Q.2.1; rw [h_eq] at h
            unfold commonNeighborsCard _root_.commonNeighbors at h
            simp only [Finset.inter_self] at h
            have h_deg : (G.neighborFinset wb).card = 5 := by rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
            omega
          exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s3 s2 wa wb
            hs3_adj_v hs2_adj_v hs_ne23.symm hv_ne_wa hv_ne_wb hab.symm
            hwa_mem.2 hwb_mem.2 (G.symm hwa_adj_sx) (G.symm hwb_adj_sy)
    have h_diff : ((W.filter (G.Adj s3)) \ (W.filter (G.Adj s4))).Nonempty := by
      by_contra h_empty; simp only [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
      have h_eq : W.filter (G.Adj s3) = W.filter (G.Adj s4) :=
        Finset.eq_of_subset_of_card_le h_empty (by rw [hs3_W_eq2, hs4_W_eq2])
      -- Extract two distinct W-vertices from the shared set
      obtain ⟨wa, wb, hwa_mem, hwb_mem, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (W.filter (G.Adj s3)).card)
      simp only [Finset.mem_filter] at hwa_mem hwb_mem
      have hs4_wa : G.Adj s4 wa := by
        have : wa ∈ W.filter (G.Adj s4) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwa_mem
        exact (Finset.mem_filter.mp this).2
      have hs4_wb : G.Adj s4 wb := by
        have : wb ∈ W.filter (G.Adj s4) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwb_mem
        exact (Finset.mem_filter.mp this).2
      have hs3_adj_v : G.Adj v s3 := by rw [← mem_neighborFinset]; exact hs3_in_N
      have hs4_adj_v : G.Adj v s4 := by rw [← mem_neighborFinset]; exact hs4_in_N
      have hwa_Q := (hW_props wa).mp hwa_mem.1
      have hwb_Q := (hW_props wb).mp hwb_mem.1
      have hv_ne_wa : v ≠ wa := by
        intro h_eq
        have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wa).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
        omega
      have hv_ne_wb : v ≠ wb := by
        intro h_eq
        have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wb).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
        omega
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s3 s4 wa wb
        hs3_adj_v hs4_adj_v hs_ne34 hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 hs4_wa hs4_wb
    exact two_element_sets_intersection (W.filter (G.Adj s3)) (W.filter (G.Adj s4))
            hs3_W_eq2 hs4_W_eq2 h_share h_diff

  have hs41_share_W : ((W.filter (G.Adj s4)) ∩ (W.filter (G.Adj s1))).card = 1 := by
    have hs4_W_eq2 : (W.filter (G.Adj s4)).card = 2 := hs_W_eq2 s4 hs4_in_S
    have hs1_W_eq2 : (W.filter (G.Adj s1)).card = 2 := hs_W_eq2 s1 hs1_in_S
    have h_share : ((W.filter (G.Adj s4)) ∩ (W.filter (G.Adj s1))).Nonempty := by
      -- Use the already-proven consecutive intersections to pin down all 4 vertices of W.
      -- Let w1' be the unique W shared by s1 and s2 (constructed above from hs12_share_W).
      -- Let w2' be the unique W shared by s2 and s3, and w3' be the unique W shared by s3 and s4.
      obtain ⟨w2', hw2'_eq⟩ := Finset.card_eq_one.mp hs23_share_W
      have hw2'_shared : w2' ∈ (W.filter (G.Adj s2)) ∩ (W.filter (G.Adj s3)) := by
        rw [hw2'_eq]
        exact Finset.mem_singleton_self w2'
      have hw2'_in_W : w2' ∈ W := (Finset.mem_filter.mp (Finset.mem_inter.mp hw2'_shared).1).1
      have hw2'_adj_s2 : G.Adj w2' s2 := by
        have h := Finset.mem_inter.mp hw2'_shared
        exact G.symm (Finset.mem_filter.mp h.1).2
      have hw2'_adj_s3 : G.Adj w2' s3 := by
        have h := Finset.mem_inter.mp hw2'_shared
        exact G.symm (Finset.mem_filter.mp h.2).2

      obtain ⟨w3', hw3'_eq⟩ := Finset.card_eq_one.mp hs34_share_W
      have hw3'_shared : w3' ∈ (W.filter (G.Adj s3)) ∩ (W.filter (G.Adj s4)) := by
        rw [hw3'_eq]
        exact Finset.mem_singleton_self w3'
      have hw3'_in_W : w3' ∈ W := (Finset.mem_filter.mp (Finset.mem_inter.mp hw3'_shared).1).1
      have hw3'_adj_s3 : G.Adj w3' s3 := by
        have h := Finset.mem_inter.mp hw3'_shared
        exact G.symm (Finset.mem_filter.mp h.1).2
      have hw3'_adj_s4 : G.Adj w3' s4 := by
        have h := Finset.mem_inter.mp hw3'_shared
        exact G.symm (Finset.mem_filter.mp h.2).2

      -- w1', w2', w3' are all distinct, since each w ∈ W has exactly 2 S-neighbors.
      have hw1'_ne_w2' : w1' ≠ w2' := by
        intro h
        subst h
        have hw_S_card : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
        have hs1_in_f : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
        have hs2_in_f : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
        have hs3_in_f : s3 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
        have h_three : ({s1, s2, s3} : Finset (Fin 18)) ⊆ S.filter (G.Adj w1') := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hs1_in_f
          · exact hs2_in_f
          · exact hs3_in_f
        have h_three_card : ({s1, s2, s3} : Finset (Fin 18)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hs_ne23
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hs_ne12, hs_ne13⟩
        have h_le := Finset.card_le_card h_three
        omega
      have hw2'_ne_w3' : w2' ≠ w3' := by
        intro h
        subst h
        have hw_S_card : (S.filter (G.Adj w2')).card = 2 := hW_S_neighbors w2' hw2'_in_W
        have hs2_in_f : s2 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs2_in_S, hw2'_adj_s2⟩
        have hs3_in_f : s3 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
        have hs4_in_f : s4 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
        have h_three : ({s2, s3, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj w2') := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hs2_in_f
          · exact hs3_in_f
          · exact hs4_in_f
        have h_three_card : ({s2, s3, s4} : Finset (Fin 18)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hs_ne34
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hs_ne23, hs_ne24⟩
        have h_le := Finset.card_le_card h_three
        omega
      have hw1'_ne_w3' : w1' ≠ w3' := by
        intro h
        subst h
        have hw_S_card : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
        have hs1_in_f : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
        have hs2_in_f : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
        have hs4_in_f : s4 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
        have h_three : ({s1, s2, s4} : Finset (Fin 18)) ⊆ S.filter (G.Adj w1') := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hs1_in_f
          · exact hs2_in_f
          · exact hs4_in_f
        have h_three_card : ({s1, s2, s4} : Finset (Fin 18)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp only [Finset.mem_singleton]; exact hs_ne24
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hs_ne12, hs_ne14⟩
        have h_le := Finset.card_le_card h_three
        omega

      -- Let w4 be the remaining vertex of W.
      have hW_erase1 : #(W.erase w1') = 3 := by
        rw [Finset.card_erase_of_mem hw1'_in_W, hW_card]
      have hw2'_in_erase1 : w2' ∈ W.erase w1' := by
        refine Finset.mem_erase.mpr ?_
        exact ⟨hw1'_ne_w2'.symm, hw2'_in_W⟩
      have hW_erase2 : #((W.erase w1').erase w2') = 2 := by
        rw [Finset.card_erase_of_mem hw2'_in_erase1, hW_erase1]
      have hw3'_in_erase2 : w3' ∈ (W.erase w1').erase w2' := by
        refine Finset.mem_erase.mpr ?_
        have hw3'_in_erase1 : w3' ∈ W.erase w1' := by
          refine Finset.mem_erase.mpr ?_
          exact ⟨hw1'_ne_w3'.symm, hw3'_in_W⟩
        exact ⟨hw2'_ne_w3'.symm, hw3'_in_erase1⟩
      have hW_erase3 : #(((W.erase w1').erase w2').erase w3') = 1 := by
        rw [Finset.card_erase_of_mem hw3'_in_erase2, hW_erase2]
      obtain ⟨w4, hw4_eq⟩ := Finset.card_eq_one.mp hW_erase3
      have hw4_mem : w4 ∈ ((W.erase w1').erase w2').erase w3' := by
        rw [hw4_eq]
        exact Finset.mem_singleton_self w4
      have hw4_in_erase2 : w4 ∈ (W.erase w1').erase w2' := (Finset.mem_erase.mp hw4_mem).2
      have hw4_in_erase1 : w4 ∈ W.erase w1' := (Finset.mem_erase.mp hw4_in_erase2).2
      have hw4_in_W : w4 ∈ W := (Finset.mem_erase.mp hw4_in_erase1).2
      have hw4_ne_w3' : w4 ≠ w3' := (Finset.mem_erase.mp hw4_mem).1
      have hw4_ne_w2' : w4 ≠ w2' := (Finset.mem_erase.mp hw4_in_erase2).1
      have hw4_ne_w1' : w4 ≠ w1' := (Finset.mem_erase.mp hw4_in_erase1).1

      -- w4 is not adjacent to s2 (else it would be a third element of W.filter (Adj s2)).
      have hs2_W_eq2 : (W.filter (G.Adj s2)).card = 2 := hs_W_eq2 s2 hs2_in_S
      have hw1'_in_s2 : w1' ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hw1'_in_W, G.symm hw1'_adj_s2⟩
      have hw2'_in_s2 : w2' ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hw2'_in_W, G.symm hw2'_adj_s2⟩
      have hs2_nonadj_w4 : ¬G.Adj s2 w4 := by
        intro h_adj
        have hw4_in_s2 : w4 ∈ W.filter (G.Adj s2) := Finset.mem_filter.mpr ⟨hw4_in_W, h_adj⟩
        have h_three : 2 < (W.filter (G.Adj s2)).card := by
          have h_sub : ({w1', w2', w4} : Finset (Fin 18)) ⊆ W.filter (G.Adj s2) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hw1'_in_s2
            · exact hw2'_in_s2
            · exact hw4_in_s2
          have h_card3 : ({w1', w2', w4} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [Finset.mem_singleton]; exact hw4_ne_w2'.symm
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hw1'_ne_w2', hw4_ne_w1'.symm⟩
          have h_le := Finset.card_le_card h_sub
          omega
        omega

      -- w4 is not adjacent to s3 (else it would be a third element of W.filter (Adj s3)).
      have hs3_W_eq2 : (W.filter (G.Adj s3)).card = 2 := hs_W_eq2 s3 hs3_in_S
      have hw2'_in_s3 : w2' ∈ W.filter (G.Adj s3) := Finset.mem_filter.mpr ⟨hw2'_in_W, G.symm hw2'_adj_s3⟩
      have hw3'_in_s3 : w3' ∈ W.filter (G.Adj s3) := Finset.mem_filter.mpr ⟨hw3'_in_W, G.symm hw3'_adj_s3⟩
      have hs3_nonadj_w4 : ¬G.Adj s3 w4 := by
        intro h_adj
        have hw4_in_s3 : w4 ∈ W.filter (G.Adj s3) := Finset.mem_filter.mpr ⟨hw4_in_W, h_adj⟩
        have h_three : 2 < (W.filter (G.Adj s3)).card := by
          have h_sub : ({w2', w3', w4} : Finset (Fin 18)) ⊆ W.filter (G.Adj s3) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hw2'_in_s3
            · exact hw3'_in_s3
            · exact hw4_in_s3
          have h_card3 : ({w2', w3', w4} : Finset (Fin 18)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [Finset.mem_singleton]; exact hw4_ne_w3'.symm
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hw2'_ne_w3', hw4_ne_w2'.symm⟩
          have h_le := Finset.card_le_card h_sub
          omega
        omega

      -- Since w4 has exactly 2 S-neighbors and is not adjacent to s2 or s3, it must be adjacent to s1 and s4.
      have hw4_S_card : (S.filter (G.Adj w4)).card = 2 := hW_S_neighbors w4 hw4_in_W
      have hw4_S_sub : S.filter (G.Adj w4) ⊆ ({s1, s4} : Finset (Fin 18)) := by
        intro x hx
        have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
        have hxAdj : G.Adj w4 x := (Finset.mem_filter.mp hx).2
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hxS
        rcases hxS with rfl | rfl | rfl | rfl
        · simp
        · exact (hs2_nonadj_w4 (G.symm hxAdj)).elim
        · exact (hs3_nonadj_w4 (G.symm hxAdj)).elim
        · simp
      have hw4_S_eq : S.filter (G.Adj w4) = ({s1, s4} : Finset (Fin 18)) := by
        apply Finset.eq_of_subset_of_card_le hw4_S_sub
        have h14 : ({s1, s4} : Finset (Fin 18)).card = 2 := by simp [hs_ne14]
        rw [h14, hw4_S_card]
      have hw4_adj_s1 : G.Adj w4 s1 := by
        have : s1 ∈ S.filter (G.Adj w4) := by rw [hw4_S_eq]; simp
        exact (Finset.mem_filter.mp this).2
      have hw4_adj_s4 : G.Adj w4 s4 := by
        have : s4 ∈ S.filter (G.Adj w4) := by rw [hw4_S_eq]; simp
        exact (Finset.mem_filter.mp this).2

      -- Therefore w4 lies in both W.filter (Adj s4) and W.filter (Adj s1).
      have hw4_in_s4 : w4 ∈ W.filter (G.Adj s4) := Finset.mem_filter.mpr ⟨hw4_in_W, G.symm hw4_adj_s4⟩
      have hw4_in_s1 : w4 ∈ W.filter (G.Adj s1) := Finset.mem_filter.mpr ⟨hw4_in_W, G.symm hw4_adj_s1⟩
      exact ⟨w4, Finset.mem_inter.mpr ⟨hw4_in_s4, hw4_in_s1⟩⟩
    have h_diff : ((W.filter (G.Adj s4)) \ (W.filter (G.Adj s1))).Nonempty := by
      by_contra h_empty; simp only [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
      have h_eq : W.filter (G.Adj s4) = W.filter (G.Adj s1) :=
        Finset.eq_of_subset_of_card_le h_empty (by rw [hs4_W_eq2, hs1_W_eq2])
      -- Extract two distinct W-vertices from the shared set
      obtain ⟨wa, wb, hwa_mem, hwb_mem, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (W.filter (G.Adj s4)).card)
      simp only [Finset.mem_filter] at hwa_mem hwb_mem
      have hs1_wa : G.Adj s1 wa := by
        have : wa ∈ W.filter (G.Adj s1) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwa_mem
        exact (Finset.mem_filter.mp this).2
      have hs1_wb : G.Adj s1 wb := by
        have : wb ∈ W.filter (G.Adj s1) := by rw [← h_eq]; exact Finset.mem_filter.mpr hwb_mem
        exact (Finset.mem_filter.mp this).2
      have hs4_adj_v : G.Adj v s4 := by rw [← mem_neighborFinset]; exact hs4_in_N
      have hs1_adj_v : G.Adj v s1 := by rw [← mem_neighborFinset]; exact hs1_in_N
      have hwa_Q := (hW_props wa).mp hwa_mem.1
      have hwb_Q := (hW_props wb).mp hwb_mem.1
      have hv_ne_wa : v ≠ wa := by
        intro h_eq
        have h_common : commonNeighborsCard G v wa = 2 := hwa_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wa).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wa
        omega
      have hv_ne_wb : v ≠ wb := by
        intro h_eq
        have h_common : commonNeighborsCard G v wb = 2 := hwb_Q.2.1
        rw [h_eq] at h_common
        unfold commonNeighborsCard _root_.commonNeighbors at h_common
        simp only [Finset.inter_self] at h_common
        have h_deg : (G.neighborFinset wb).card = 5 := by
          rw [G.card_neighborFinset_eq_degree]; exact h_reg wb
        omega
      exact S_pair_share_at_most_one_W h_reg h_tri h_no6 v s4 s1 wa wb
        hs4_adj_v hs1_adj_v hs_ne14.symm hv_ne_wa hv_ne_wb hab
        hwa_mem.2 hwb_mem.2 hs1_wa hs1_wb
    exact two_element_sets_intersection (W.filter (G.Adj s4)) (W.filter (G.Adj s1))
            hs4_W_eq2 hs1_W_eq2 h_share h_diff

  obtain ⟨w2', hw2'_eq⟩ := Finset.card_eq_one.mp hs23_share_W
  obtain ⟨w3', hw3'_eq⟩ := Finset.card_eq_one.mp hs34_share_W
  obtain ⟨w4', hw4'_eq⟩ := Finset.card_eq_one.mp hs41_share_W

  -- Extract properties
  have hw2'_in_W : w2' ∈ W := by
    have h : w2' ∈ W.filter (G.Adj s2) ∩ W.filter (G.Adj s3) := by rw [hw2'_eq]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1
  have hw3'_in_W : w3' ∈ W := by
    have h : w3' ∈ W.filter (G.Adj s3) ∩ W.filter (G.Adj s4) := by rw [hw3'_eq]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1
  have hw4'_in_W : w4' ∈ W := by
    have h : w4' ∈ W.filter (G.Adj s4) ∩ W.filter (G.Adj s1) := by rw [hw4'_eq]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1

  -- Adjacency properties
  have hw2'_adj_s2 : G.Adj w2' s2 := by
    have h : w2' ∈ W.filter (G.Adj s2) ∩ W.filter (G.Adj s3) := by rw [hw2'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2
  have hw2'_adj_s3 : G.Adj w2' s3 := by
    have h : w2' ∈ W.filter (G.Adj s2) ∩ W.filter (G.Adj s3) := by rw [hw2'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2
  have hw3'_adj_s3 : G.Adj w3' s3 := by
    have h : w3' ∈ W.filter (G.Adj s3) ∩ W.filter (G.Adj s4) := by rw [hw3'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2
  have hw3'_adj_s4 : G.Adj w3' s4 := by
    have h : w3' ∈ W.filter (G.Adj s3) ∩ W.filter (G.Adj s4) := by rw [hw3'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2
  have hw4'_adj_s4 : G.Adj w4' s4 := by
    have h : w4' ∈ W.filter (G.Adj s4) ∩ W.filter (G.Adj s1) := by rw [hw4'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2
  have hw4'_adj_s1 : G.Adj w4' s1 := by
    have h : w4' ∈ W.filter (G.Adj s4) ∩ W.filter (G.Adj s1) := by rw [hw4'_eq]; simp
    exact G.symm (Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2

  -- Prove distinctness: w1', w2', w3', w4' are all distinct
  -- If w1' = w2', then w1' is adjacent to s1, s2, s3 (3 S-neighbors), but each W has 2
  have hw_ne12 : w1' ≠ w2' := by
    intro h_eq
    have hw1_three : 3 ≤ (S.filter (G.Adj w1')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w1') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
      have h_sub : {s1, s2, s3} ⊆ S.filter (G.Adj w1') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s3} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne23
            · simp; exact ⟨hs_ne12, hs_ne13⟩
        _ ≤ (S.filter (G.Adj w1')).card := Finset.card_le_card h_sub
    have hw1_two : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
    omega

  have hw_ne13 : w1' ≠ w3' := by
    intro h_eq
    have hw1_three : 3 ≤ (S.filter (G.Adj w1')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w1') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs3_in_S, hw3'_adj_s3⟩
      have h_sub : {s1, s2, s3} ⊆ S.filter (G.Adj w1') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s3} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne23
            · simp; exact ⟨hs_ne12, hs_ne13⟩
        _ ≤ (S.filter (G.Adj w1')).card := Finset.card_le_card h_sub
    have hw1_two : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
    omega

  have hw_ne14 : w1' ≠ w4' := by
    intro h_eq
    have hw1_three : 3 ≤ (S.filter (G.Adj w1')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
      have h4 : s4 ∈ S.filter (G.Adj w1') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs4_in_S, hw4'_adj_s4⟩
      have h_sub : {s1, s2, s4} ⊆ S.filter (G.Adj w1') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne24
            · simp; exact ⟨hs_ne12, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w1')).card := Finset.card_le_card h_sub
    have hw1_two : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
    omega

  have hw_ne23 : w2' ≠ w3' := by
    intro h_eq
    have hw2_three : 3 ≤ (S.filter (G.Adj w2')).card := by
      have h2 : s2 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs2_in_S, hw2'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
      have h4 : s4 ∈ S.filter (G.Adj w2') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
      have h_sub : {s2, s3, s4} ⊆ S.filter (G.Adj w2') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s2, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne23, hs_ne24⟩
        _ ≤ (S.filter (G.Adj w2')).card := Finset.card_le_card h_sub
    have hw2_two : (S.filter (G.Adj w2')).card = 2 := hW_S_neighbors w2' hw2'_in_W
    omega

  have hw_ne24 : w2' ≠ w4' := by
    intro h_eq
    have hw2_three : 3 ≤ (S.filter (G.Adj w2')).card := by
      have h2 : s2 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs2_in_S, hw2'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
      have h1 : s1 ∈ S.filter (G.Adj w2') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs1_in_S, hw4'_adj_s1⟩
      have h_sub : {s1, s2, s3} ⊆ S.filter (G.Adj w2') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s3} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne23
            · simp; exact ⟨hs_ne12, hs_ne13⟩
        _ ≤ (S.filter (G.Adj w2')).card := Finset.card_le_card h_sub
    have hw2_two : (S.filter (G.Adj w2')).card = 2 := hW_S_neighbors w2' hw2'_in_W
    omega

  have hw_ne34 : w3' ≠ w4' := by
    intro h_eq
    have hw3_three : 3 ≤ (S.filter (G.Adj w3')).card := by
      have h3 : s3 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs3_in_S, hw3'_adj_s3⟩
      have h4 : s4 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
      have h1 : s1 ∈ S.filter (G.Adj w3') := by
        rw [h_eq]
        exact Finset.mem_filter.mpr ⟨hs1_in_S, hw4'_adj_s1⟩
      have h_sub : {s1, s3, s4} ⊆ S.filter (G.Adj w3') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne13, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w3')).card := Finset.card_le_card h_sub
    have hw3_two : (S.filter (G.Adj w3')).card = 2 := hW_S_neighbors w3' hw3'_in_W
    omega

  -- Non-adjacencies: w1' is adjacent to s1, s2 only (not s3, s4)
  have hw1'_nonadj_s3 : ¬G.Adj w1' s3 := by
    intro h_adj
    have hw1_three : 3 ≤ (S.filter (G.Adj w1')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs3_in_S, h_adj⟩
      have h_sub : {s1, s2, s3} ⊆ S.filter (G.Adj w1') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s3} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne23
            · simp; exact ⟨hs_ne12, hs_ne13⟩
        _ ≤ (S.filter (G.Adj w1')).card := Finset.card_le_card h_sub
    have hw1_two : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
    omega

  have hw1'_nonadj_s4 : ¬G.Adj w1' s4 := by
    intro h_adj
    have hw1_three : 3 ≤ (S.filter (G.Adj w1')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs1_in_S, hw1'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs2_in_S, hw1'_adj_s2⟩
      have h4 : s4 ∈ S.filter (G.Adj w1') := Finset.mem_filter.mpr ⟨hs4_in_S, h_adj⟩
      have h_sub : {s1, s2, s4} ⊆ S.filter (G.Adj w1') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne24
            · simp; exact ⟨hs_ne12, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w1')).card := Finset.card_le_card h_sub
    have hw1_two : (S.filter (G.Adj w1')).card = 2 := hW_S_neighbors w1' hw1'_in_W
    omega

  -- Similarly derive all other non-adjacencies
  have hw2'_nonadj_s1 : ¬G.Adj w2' s1 := by
    intro h_adj
    have hw2_three : 3 ≤ (S.filter (G.Adj w2')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs1_in_S, h_adj⟩
      have h2 : s2 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs2_in_S, hw2'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
      have h_sub : {s1, s2, s3} ⊆ S.filter (G.Adj w2') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s3} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne23
            · simp; exact ⟨hs_ne12, hs_ne13⟩
        _ ≤ (S.filter (G.Adj w2')).card := Finset.card_le_card h_sub
    have hw2_two : (S.filter (G.Adj w2')).card = 2 := hW_S_neighbors w2' hw2'_in_W
    omega

  have hw2'_nonadj_s4 : ¬G.Adj w2' s4 := by
    intro h_adj
    have hw2_three : 3 ≤ (S.filter (G.Adj w2')).card := by
      have h2 : s2 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs2_in_S, hw2'_adj_s2⟩
      have h3 : s3 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs3_in_S, hw2'_adj_s3⟩
      have h4 : s4 ∈ S.filter (G.Adj w2') := Finset.mem_filter.mpr ⟨hs4_in_S, h_adj⟩
      have h_sub : {s2, s3, s4} ⊆ S.filter (G.Adj w2') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s2, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne23, hs_ne24⟩
        _ ≤ (S.filter (G.Adj w2')).card := Finset.card_le_card h_sub
    have hw2_two : (S.filter (G.Adj w2')).card = 2 := hW_S_neighbors w2' hw2'_in_W
    omega

  have hw3'_nonadj_s1 : ¬G.Adj w3' s1 := by
    intro h_adj
    have hw3_three : 3 ≤ (S.filter (G.Adj w3')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs1_in_S, h_adj⟩
      have h3 : s3 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs3_in_S, hw3'_adj_s3⟩
      have h4 : s4 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
      have h_sub : {s1, s3, s4} ⊆ S.filter (G.Adj w3') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne13, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w3')).card := Finset.card_le_card h_sub
    have hw3_two : (S.filter (G.Adj w3')).card = 2 := hW_S_neighbors w3' hw3'_in_W
    omega

  have hw3'_nonadj_s2 : ¬G.Adj w3' s2 := by
    intro h_adj
    have hw3_three : 3 ≤ (S.filter (G.Adj w3')).card := by
      have h2 : s2 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs2_in_S, h_adj⟩
      have h3 : s3 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs3_in_S, hw3'_adj_s3⟩
      have h4 : s4 ∈ S.filter (G.Adj w3') := Finset.mem_filter.mpr ⟨hs4_in_S, hw3'_adj_s4⟩
      have h_sub : {s2, s3, s4} ⊆ S.filter (G.Adj w3') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s2, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne23, hs_ne24⟩
        _ ≤ (S.filter (G.Adj w3')).card := Finset.card_le_card h_sub
    have hw3_two : (S.filter (G.Adj w3')).card = 2 := hW_S_neighbors w3' hw3'_in_W
    omega

  have hw4'_nonadj_s2 : ¬G.Adj w4' s2 := by
    intro h_adj
    have hw4_three : 3 ≤ (S.filter (G.Adj w4')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs1_in_S, hw4'_adj_s1⟩
      have h2 : s2 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs2_in_S, h_adj⟩
      have h4 : s4 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs4_in_S, hw4'_adj_s4⟩
      have h_sub : {s1, s2, s4} ⊆ S.filter (G.Adj w4') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s2, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne24
            · simp; exact ⟨hs_ne12, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w4')).card := Finset.card_le_card h_sub
    have hw4_two : (S.filter (G.Adj w4')).card = 2 := hW_S_neighbors w4' hw4'_in_W
    omega

  have hw4'_nonadj_s3 : ¬G.Adj w4' s3 := by
    intro h_adj
    have hw4_three : 3 ≤ (S.filter (G.Adj w4')).card := by
      have h1 : s1 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs1_in_S, hw4'_adj_s1⟩
      have h3 : s3 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs3_in_S, h_adj⟩
      have h4 : s4 ∈ S.filter (G.Adj w4') := Finset.mem_filter.mpr ⟨hs4_in_S, hw4'_adj_s4⟩
      have h_sub : {s1, s3, s4} ⊆ S.filter (G.Adj w4') := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      calc 3 = ({s1, s3, s4} : Finset (Fin 18)).card := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp; exact hs_ne34
            · simp; exact ⟨hs_ne13, hs_ne14⟩
        _ ≤ (S.filter (G.Adj w4')).card := Finset.card_le_card h_sub
    have hw4_two : (S.filter (G.Adj w4')).card = 2 := hW_S_neighbors w4' hw4'_in_W
    omega

  -- w' are not adjacent to v (they're in W ⊂ Q which are non-neighbors of v)
  have hw1'_nonadj_v : ¬G.Adj v w1' := (hW_props w1').mp hw1'_in_W |>.1
  have hw2'_nonadj_v : ¬G.Adj v w2' := (hW_props w2').mp hw2'_in_W |>.1
  have hw3'_nonadj_v : ¬G.Adj v w3' := (hW_props w3').mp hw3'_in_W |>.1
  have hw4'_nonadj_v : ¬G.Adj v w4' := (hW_props w4').mp hw4'_in_W |>.1

  -- w' are not adjacent to t (by definition of W)
  have hw1'_nonadj_t : ¬G.Adj t w1' := (hW_props w1').mp hw1'_in_W |>.2.2
  have hw2'_nonadj_t : ¬G.Adj t w2' := (hW_props w2').mp hw2'_in_W |>.2.2
  have hw3'_nonadj_t : ¬G.Adj t w3' := (hW_props w3').mp hw3'_in_W |>.2.2
  have hw4'_nonadj_t : ¬G.Adj t w4' := (hW_props w4').mp hw4'_in_W |>.2.2

  -- commonNeighborsCard for w'
  have hw1'_common2 : commonNeighborsCard G v w1' = 2 := (hW_props w1').mp hw1'_in_W |>.2.1
  have hw2'_common2 : commonNeighborsCard G v w2' = 2 := (hW_props w2').mp hw2'_in_W |>.2.1
  have hw3'_common2 : commonNeighborsCard G v w3' = 2 := (hW_props w3').mp hw3'_in_W |>.2.1
  have hw4'_common2 : commonNeighborsCard G v w4' = 2 := (hW_props w4').mp hw4'_in_W |>.2.1

  -- w' are not adjacent to p (w's in Q have 2 common neighbors with v, both in S, not adjacent to p)
  -- The proof uses five_cycle_structure: if w1' ~ p1, the 5-vertex set {p1, p2, s1, s2, w1'}
  -- would have p1 with degree 3 (p1~p2, p1~s1, p1~w1'), but 2-regular means degree 2.
  -- For now, we use a simpler counting argument based on commonNeighborsCard.
  have hw1'_nonadj_p1 : ¬G.Adj w1' p1 := by
    intro h_adj
    -- w1' ∈ W means commonNeighborsCard(v, w1') = 2 and w1' not adj to v
    -- The 2 common neighbors of v and w1' are s1 and s2 (w1' is adj to both)
    -- If w1' ~ p1, then p1's neighbors include: p2, p4 (P-cycle), s1 (S-partner), w1'
    -- And p1 has degree 5, so p1 has exactly 5 neighbors
    -- Now consider: what are the common neighbors of v and p1?
    -- p1 is not adj to v (p1 ∈ P ⊂ Q implies p1 not adj v)
    -- The common neighbors are N(v) ∩ N(p1) = {s1} (p1's only N(v)-neighbor is its S-partner)
    -- So commonNeighborsCard(v, p1) = 1 (which is hp1_common1)
    -- Now if w1' ~ p1, is w1' a common neighbor of v and p1?
    -- w1' is not adj to v (w1' ∈ W ⊂ Q). So w1' ∉ N(v). So w1' is not a common neighbor.
    -- This doesn't give a contradiction directly...
    -- Actually, we use: w1' has exactly 2 S-neighbors (s1 and s2, from hW_S_neighbors)
    -- The W-vertex w1' is determined by being the shared W-neighbor of s1 and s2
    -- If w1' ~ p1, consider the S-W bipartite structure...
    -- Actually, let's use the simpler approach: |P ∩ Q| = 0, so p1 ∉ W.
    -- Then w1' ∈ W and p1 ∈ P with P ∩ Q = ∅... wait, P ⊂ complement of Q isn't quite right either.
    -- Let me use a direct argument via P-Q disjointness.
    -- P = non-neighbors of v with commonNeighborsCard = 1
    -- W ⊂ Q = non-neighbors of v with commonNeighborsCard = 2
    -- So P ∩ W = ∅ (different commonNeighborsCard)
    exfalso
    have hp1_in_W_or_not : p1 ∈ W ∨ p1 ∉ W := Classical.em _
    -- p1 has commonNeighborsCard = 1, W elements have commonNeighborsCard = 2
    have hp1_not_in_W : p1 ∉ W := by
      intro hp1_in_W
      have h := (hW_props p1).mp hp1_in_W
      have hp1_c2 := h.2.1
      omega  -- hp1_common1 = 1, hp1_c2 = 2
    -- But we assumed w1' ~ p1. We need to derive a contradiction from this.
    -- Let's count p1's neighbors more carefully.
    -- p1's neighbors: p2, p4 (2 from P-cycle), s1 (1 from S-partner), and 2 more from Q
    -- The 2 Q-neighbors of p1: since commonNeighborsCard(v, p1) = 1, p1 shares exactly 1
    -- neighbor with v, which is s1. p1's Q-neighbors don't contribute to common neighbors
    -- with v (since Q elements are not adjacent to v).
    -- Wait, the Q-neighbors of p1 ARE adjacent to p1 but not to v.
    -- So p1's degree = 2 (P-neighbors) + 1 (S-partner) + ? (Q-neighbors)
    -- Total = 5, so ? = 2.
    -- If w1' is one of p1's Q-neighbors, that's fine structurally.
    -- The issue is: w1' is adjacent to s1 and s2.
    -- p1 is adjacent to s1 (S-partner).
    -- If p1 ~ w1', then {p1, s1, w1'} are all pairwise... wait, is s1 ~ w1'?
    -- Yes, hw1'_adj_s1 says w1' ~ s1.
    -- Is s1 ~ p1? Yes, hs1_adj_p1.
    -- Is p1 ~ w1'? That's our assumption h_adj.
    -- So {p1, s1, w1'} is a triangle! But G is triangle-free.
    exact h_tri {p1, s1, w1'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs1_adj_p1  -- p1,s1: need G.Adj p1 s1
      · exact G.symm h_adj      -- p1,w1': need G.Adj p1 w1'
      · exact hs1_adj_p1        -- s1,p1: need G.Adj s1 p1
      · exact absurd rfl hab
      · exact G.symm hw1'_adj_s1 -- s1,w1': need G.Adj s1 w1'
      · exact h_adj             -- w1',p1: need G.Adj w1' p1
      · exact hw1'_adj_s1       -- w1',s1: need G.Adj w1' s1
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs1_in_N
        exact (hW_props w1').mp hw1'_in_W |>.1 (by rw [mem_neighborFinset] at hs1_in_N; exact hs1_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        constructor
        · intro h; rw [h] at hp1_nonadj_v
          exact hp1_nonadj_v (by rw [← mem_neighborFinset]; exact hs1_in_N)
        · intro h; exact hp1_not_in_W (h ▸ hw1'_in_W)⟩

  -- Similarly for other w'-p non-adjacencies (all use triangle argument)
  -- Pattern: wi' ~ sj, sj ~ pj, so if wi' ~ pj then {pj, sj, wi'} is a triangle
  have hw1'_nonadj_p2 : ¬G.Adj w1' p2 := by
    intro h_adj
    -- w1' ~ s2 (hw1'_adj_s2), s2 ~ p2 (hs2_adj_p2)
    -- If w1' ~ p2, then {p2, s2, w1'} is a triangle
    -- Distinctness: s2 ≠ w1' (s2 ∈ N(v), w1' ∉ N(v))
    --              p2 ≠ s2 (by S-P distinctness), p2 ≠ w1' (p2 ∉ W)
    have hp2_not_in_W : p2 ∉ W := by
      intro hp2_in_W
      have h := (hW_props p2).mp hp2_in_W
      omega  -- hp2_common1 = 1, h.2.1 = 2
    exact h_tri {p2, s2, w1'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs2_adj_p2
      · exact G.symm h_adj
      · exact hs2_adj_p2
      · exact absurd rfl hab
      · exact G.symm hw1'_adj_s2
      · exact h_adj
      · exact hw1'_adj_s2
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs2_in_N
        exact (hW_props w1').mp hw1'_in_W |>.1 (by rw [mem_neighborFinset] at hs2_in_N; exact hs2_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        constructor
        · exact (G.ne_of_adj hs2_adj_p2).symm
        · intro h; exact hp2_not_in_W (h ▸ hw1'_in_W)⟩

  have hw2'_nonadj_p2 : ¬G.Adj w2' p2 := by
    intro h_adj
    have hp2_not_in_W : p2 ∉ W := by
      intro hp2_in_W; have h := (hW_props p2).mp hp2_in_W; omega
    exact h_tri {p2, s2, w2'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs2_adj_p2
      · exact G.symm h_adj
      · exact hs2_adj_p2
      · exact absurd rfl hab
      · exact G.symm hw2'_adj_s2
      · exact h_adj
      · exact hw2'_adj_s2
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs2_in_N
        exact (hW_props w2').mp hw2'_in_W |>.1 (by rw [mem_neighborFinset] at hs2_in_N; exact hs2_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨(G.ne_of_adj hs2_adj_p2).symm, fun h => hp2_not_in_W (h ▸ hw2'_in_W)⟩⟩

  have hw2'_nonadj_p3 : ¬G.Adj w2' p3 := by
    intro h_adj
    have hp3_not_in_W : p3 ∉ W := by
      intro hp3_in_W; have h := (hW_props p3).mp hp3_in_W; omega
    exact h_tri {p3, s3, w2'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs3_adj_p3
      · exact G.symm h_adj
      · exact hs3_adj_p3
      · exact absurd rfl hab
      · exact G.symm hw2'_adj_s3
      · exact h_adj
      · exact hw2'_adj_s3
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs3_in_N
        exact (hW_props w2').mp hw2'_in_W |>.1 (by rw [mem_neighborFinset] at hs3_in_N; exact hs3_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨(G.ne_of_adj hs3_adj_p3).symm, fun h => hp3_not_in_W (h ▸ hw2'_in_W)⟩⟩

  have hw3'_nonadj_p3 : ¬G.Adj w3' p3 := by
    intro h_adj
    have hp3_not_in_W : p3 ∉ W := by
      intro hp3_in_W; have h := (hW_props p3).mp hp3_in_W; omega
    exact h_tri {p3, s3, w3'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs3_adj_p3
      · exact G.symm h_adj
      · exact hs3_adj_p3
      · exact absurd rfl hab
      · exact G.symm hw3'_adj_s3
      · exact h_adj
      · exact hw3'_adj_s3
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs3_in_N
        exact (hW_props w3').mp hw3'_in_W |>.1 (by rw [mem_neighborFinset] at hs3_in_N; exact hs3_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨(G.ne_of_adj hs3_adj_p3).symm, fun h => hp3_not_in_W (h ▸ hw3'_in_W)⟩⟩

  have hw3'_nonadj_p4 : ¬G.Adj w3' p4 := by
    intro h_adj
    have hp4_not_in_W : p4 ∉ W := by
      intro hp4_in_W; have h := (hW_props p4).mp hp4_in_W; omega
    exact h_tri {p4, s4, w3'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs4_adj_p4
      · exact G.symm h_adj
      · exact hs4_adj_p4
      · exact absurd rfl hab
      · exact G.symm hw3'_adj_s4
      · exact h_adj
      · exact hw3'_adj_s4
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs4_in_N
        exact (hW_props w3').mp hw3'_in_W |>.1 (by rw [mem_neighborFinset] at hs4_in_N; exact hs4_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨(G.ne_of_adj hs4_adj_p4).symm, fun h => hp4_not_in_W (h ▸ hw3'_in_W)⟩⟩

  have hw4'_nonadj_p4 : ¬G.Adj w4' p4 := by
    intro h_adj
    have hp4_not_in_W : p4 ∉ W := by
      intro hp4_in_W; have h := (hW_props p4).mp hp4_in_W; omega
    exact h_tri {p4, s4, w4'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs4_adj_p4
      · exact G.symm h_adj
      · exact hs4_adj_p4
      · exact absurd rfl hab
      · exact G.symm hw4'_adj_s4
      · exact h_adj
      · exact hw4'_adj_s4
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs4_in_N
        exact (hW_props w4').mp hw4'_in_W |>.1 (by rw [mem_neighborFinset] at hs4_in_N; exact hs4_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨(G.ne_of_adj hs4_adj_p4).symm, fun h => hp4_not_in_W (h ▸ hw4'_in_W)⟩⟩

  have hw4'_nonadj_p1 : ¬G.Adj w4' p1 := by
    intro h_adj
    have hp1_not_in_W' : p1 ∉ W := by
      intro hp1_in_W; have h := (hW_props p1).mp hp1_in_W; omega
    exact h_tri {p1, s1, w4'} ⟨by
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact G.symm hs1_adj_p1
      · exact G.symm h_adj
      · exact hs1_adj_p1
      · exact absurd rfl hab
      · exact G.symm hw4'_adj_s1
      · exact h_adj
      · exact hw4'_adj_s1
      · exact absurd rfl hab, by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]
        intro h; rw [h] at hs1_in_N
        exact (hW_props w4').mp hw4'_in_W |>.1 (by rw [mem_neighborFinset] at hs1_in_N; exact hs1_in_N)
      · simp only [mem_insert, mem_singleton, not_or]
        constructor
        · exact (G.ne_of_adj hs1_adj_p1).symm
        · intro h; exact hp1_not_in_W' (h ▸ hw4'_in_W)⟩

  -- T properties
  have ht1_nonadj_v : ¬G.Adj v t1 := ht1_Q_props.1
  have ht2_nonadj_v : ¬G.Adj v t2 := ht2_Q_props.1
  have ht3_nonadj_v : ¬G.Adj v t3 := ht3_Q_props.1
  have ht4_nonadj_v : ¬G.Adj v t4 := ht4_Q_props.1

  have ht1_common2 : commonNeighborsCard G v t1 = 2 := ht1_Q_props.2
  have ht2_common2 : commonNeighborsCard G v t2 = 2 := ht2_Q_props.2
  have ht3_common2 : commonNeighborsCard G v t3 = 2 := ht3_Q_props.2
  have ht4_common2 : commonNeighborsCard G v t4 = 2 := ht4_Q_props.2

  -- Build the CariolaroSetup with the relabeled w's
  exact ⟨{
    v := v
    t := t
    s1 := s1, s2 := s2, s3 := s3, s4 := s4
    p1 := p1, p2 := p2, p3 := p3, p4 := p4
    t1 := t1, t2 := t2, t3 := t3, t4 := t4
    w1 := w1', w2 := w2', w3 := w3', w4 := w4'

    -- N(v) adjacencies
    h_t_adj_v := ht_adj_v
    h_s1_adj_v := by rw [← mem_neighborFinset]; exact hs1_in_N
    h_s2_adj_v := by rw [← mem_neighborFinset]; exact hs2_in_N
    h_s3_adj_v := by rw [← mem_neighborFinset]; exact hs3_in_N
    h_s4_adj_v := by rw [← mem_neighborFinset]; exact hs4_in_N

    -- N(v) distinctness
    h_Nv_distinct := ⟨ht_ne_s1, ht_ne_s2, ht_ne_s3, ht_ne_s4,
                      hs_ne12, hs_ne13, hs_ne14, hs_ne23, hs_ne24, hs_ne34⟩

    -- P non-adjacency to v
    h_p1_nonadj_v := hp1_nonadj_v
    h_p2_nonadj_v := hp2_nonadj_v
    h_p3_nonadj_v := hp3_nonadj_v
    h_p4_nonadj_v := hp4_nonadj_v

    -- P common neighbors
    h_p1_common1 := hp1_common1
    h_p2_common1 := hp2_common1
    h_p3_common1 := hp3_common1
    h_p4_common1 := hp4_common1

    -- S-P adjacencies
    h_s1_adj_p1 := hs1_adj_p1
    h_s2_adj_p2 := hs2_adj_p2
    h_s3_adj_p3 := hs3_adj_p3
    h_s4_adj_p4 := hs4_adj_p4

    -- S-P cross non-adjacencies
    h_s1_nonadj_p2 := hs1_nonadj_p2
    h_s1_nonadj_p3 := hs1_nonadj_p3
    h_s1_nonadj_p4 := hs1_nonadj_p4
    h_s2_nonadj_p1 := hs2_nonadj_p1
    h_s2_nonadj_p3 := hs2_nonadj_p3
    h_s2_nonadj_p4 := hs2_nonadj_p4
    h_s3_nonadj_p1 := hs3_nonadj_p1
    h_s3_nonadj_p2 := hs3_nonadj_p2
    h_s3_nonadj_p4 := hs3_nonadj_p4
    h_s4_nonadj_p1 := hs4_nonadj_p1
    h_s4_nonadj_p2 := hs4_nonadj_p2
    h_s4_nonadj_p3 := hs4_nonadj_p3

    -- P distinctness
    h_P_distinct := ⟨hp_ne12, hp_ne13, hp_ne14, hp_ne23, hp_ne24, hp_ne34⟩

    -- t non-adjacency to P
    h_t_nonadj_p1 := ht_nonadj_p1
    h_t_nonadj_p2 := ht_nonadj_p2
    h_t_nonadj_p3 := ht_nonadj_p3
    h_t_nonadj_p4 := ht_nonadj_p4

    -- T properties
    h_t1_nonadj_v := ht1_nonadj_v
    h_t2_nonadj_v := ht2_nonadj_v
    h_t3_nonadj_v := ht3_nonadj_v
    h_t4_nonadj_v := ht4_nonadj_v
    h_t1_common2 := ht1_common2
    h_t2_common2 := ht2_common2
    h_t3_common2 := ht3_common2
    h_t4_common2 := ht4_common2
    h_t1_adj_t := ht1_props.2
    h_t2_adj_t := ht2_props.2
    h_t3_adj_t := ht3_props.2
    h_t4_adj_t := ht4_props.2
    h_T_distinct := ⟨ht1_ne_t2, ht1_ne_t3, ht1_ne_t4, ht2_ne_t3, ht2_ne_t4, ht3_ne_t4⟩

    -- W properties
    h_w1_nonadj_v := hw1'_nonadj_v
    h_w2_nonadj_v := hw2'_nonadj_v
    h_w3_nonadj_v := hw3'_nonadj_v
    h_w4_nonadj_v := hw4'_nonadj_v
    h_w1_common2 := hw1'_common2
    h_w2_common2 := hw2'_common2
    h_w3_common2 := hw3'_common2
    h_w4_common2 := hw4'_common2
    h_w1_nonadj_t := hw1'_nonadj_t
    h_w2_nonadj_t := hw2'_nonadj_t
    h_w3_nonadj_t := hw3'_nonadj_t
    h_w4_nonadj_t := hw4'_nonadj_t
    h_W_distinct := ⟨hw_ne12, hw_ne13, hw_ne14, hw_ne23, hw_ne24, hw_ne34⟩

    -- W-S adjacencies (the 8-cycle structure)
    h_w1_adj_s1 := hw1'_adj_s1
    h_w1_adj_s2 := hw1'_adj_s2
    h_w1_nonadj_s3 := hw1'_nonadj_s3
    h_w1_nonadj_s4 := hw1'_nonadj_s4
    h_w2_adj_s2 := hw2'_adj_s2
    h_w2_adj_s3 := hw2'_adj_s3
    h_w2_nonadj_s1 := hw2'_nonadj_s1
    h_w2_nonadj_s4 := hw2'_nonadj_s4
    h_w3_adj_s3 := hw3'_adj_s3
    h_w3_adj_s4 := hw3'_adj_s4
    h_w3_nonadj_s1 := hw3'_nonadj_s1
    h_w3_nonadj_s2 := hw3'_nonadj_s2
    h_w4_adj_s4 := hw4'_adj_s4
    h_w4_adj_s1 := hw4'_adj_s1
    h_w4_nonadj_s2 := hw4'_nonadj_s2
    h_w4_nonadj_s3 := hw4'_nonadj_s3

    -- W-P non-adjacencies (only the 8 fields that exist in CariolaroSetup)
    h_w1_nonadj_p1 := hw1'_nonadj_p1
    h_w1_nonadj_p2 := hw1'_nonadj_p2
    h_w2_nonadj_p2 := hw2'_nonadj_p2
    h_w2_nonadj_p3 := hw2'_nonadj_p3
    h_w3_nonadj_p3 := hw3'_nonadj_p3
    h_w3_nonadj_p4 := hw3'_nonadj_p4
    h_w4_nonadj_p4 := hw4'_nonadj_p4
    h_w4_nonadj_p1 := hw4'_nonadj_p1
  }, rfl⟩

/-- Existence of a CariolaroSetup for any counterexample graph. -/
lemma exists_CariolaroSetup {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    Nonempty (CariolaroSetup G h_reg h_tri h_no6) := by
  obtain ⟨setup, _⟩ := exists_CariolaroSetup_at h_reg h_tri h_no6 0
  exact ⟨setup⟩

/-- Canonical choice of CariolaroSetup for a counterexample graph. -/
noncomputable def someCariolaroSetup (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    CariolaroSetup G h_reg h_tri h_no6 :=
  (exists_CariolaroSetup h_reg h_tri h_no6).some

/-- Helper lemma: If an S-vertex has 3 W-neighbors, we derive a contradiction
(modulo the bijective case which requires 8-cycle structure).

This is the **core W-collision argument** used in both hT_le and hT_ge. -/
lemma S_three_W_neighbors_yield_setup
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v t : Fin 18) (ht_adj_v : G.Adj v t)
    (S W : Finset (Fin 18)) (hS_card : S.card = 4)
    (hS_eq : S = (G.neighborFinset v).erase t)
    (sj : Fin 18) (hsj_in_S : sj ∈ S) (hsj_adj_v : G.Adj v sj)
    (hW_props : ∀ x, x ∈ W ↔ ¬G.Adj v x ∧ commonNeighborsCard G v x = 2 ∧ ¬G.Adj t x)
    (hW_three : (W.filter (G.Adj sj)).card = 3) :
    False ∨ ∃ _ : CariolaroSetup G h_reg h_tri h_no6, True := by
  -- Extract 3 distinct W-vertices adjacent to sj
  obtain ⟨w1, w2, w3, hw_ne12, hw_ne13, hw_ne23, hW_adj_eq⟩ :=
    Finset.card_eq_three.mp hW_three
  have hw1_in : w1 ∈ W.filter (G.Adj sj) := by rw [hW_adj_eq]; simp
  have hw2_in : w2 ∈ W.filter (G.Adj sj) := by rw [hW_adj_eq]; simp
  have hw3_in : w3 ∈ W.filter (G.Adj sj) := by rw [hW_adj_eq]; simp
  simp only [Finset.mem_filter] at hw1_in hw2_in hw3_in
  have hw1_in_W : w1 ∈ W := hw1_in.1
  have hw2_in_W : w2 ∈ W := hw2_in.1
  have hw3_in_W : w3 ∈ W := hw3_in.1
  have hsj_adj_w1 : G.Adj sj w1 := hw1_in.2
  have hsj_adj_w2 : G.Adj sj w2 := hw2_in.2
  have hsj_adj_w3 : G.Adj sj w3 := hw3_in.2
  have hw1_props := (hW_props w1).mp hw1_in_W
  have hw2_props := (hW_props w2).mp hw2_in_W
  have hw3_props := (hW_props w3).mp hw3_in_W
  -- Each wi has 2 S-neighbors
  have hw1_S_card : (S.filter (G.Adj w1)).card = 2 :=
    W_vertex_has_two_S_neighbors h_tri v t w1 ht_adj_v hw1_props.2.2 hw1_props.2.1 S hS_card hS_eq
  have hw2_S_card : (S.filter (G.Adj w2)).card = 2 :=
    W_vertex_has_two_S_neighbors h_tri v t w2 ht_adj_v hw2_props.2.2 hw2_props.2.1 S hS_card hS_eq
  have hw3_S_card : (S.filter (G.Adj w3)).card = 2 :=
    W_vertex_has_two_S_neighbors h_tri v t w3 ht_adj_v hw3_props.2.2 hw3_props.2.1 S hS_card hS_eq
  -- sj is an S-neighbor of each wi
  have hsj_in_w1_filter : sj ∈ S.filter (G.Adj w1) := by
    simp only [Finset.mem_filter]; exact ⟨hsj_in_S, G.symm hsj_adj_w1⟩
  have hsj_in_w2_filter : sj ∈ S.filter (G.Adj w2) := by
    simp only [Finset.mem_filter]; exact ⟨hsj_in_S, G.symm hsj_adj_w2⟩
  have hsj_in_w3_filter : sj ∈ S.filter (G.Adj w3) := by
    simp only [Finset.mem_filter]; exact ⟨hsj_in_S, G.symm hsj_adj_w3⟩
  -- Each wi has exactly one "other" S-neighbor (besides sj)
  have hw1_other_card : ((S.filter (G.Adj w1)).erase sj).card = 1 := by
    rw [Finset.card_erase_of_mem hsj_in_w1_filter, hw1_S_card]
  have hw2_other_card : ((S.filter (G.Adj w2)).erase sj).card = 1 := by
    rw [Finset.card_erase_of_mem hsj_in_w2_filter, hw2_S_card]
  have hw3_other_card : ((S.filter (G.Adj w3)).erase sj).card = 1 := by
    rw [Finset.card_erase_of_mem hsj_in_w3_filter, hw3_S_card]
  -- Extract the "other" S-neighbors
  obtain ⟨o1, ho1_eq⟩ := Finset.card_eq_one.mp hw1_other_card
  obtain ⟨o2, ho2_eq⟩ := Finset.card_eq_one.mp hw2_other_card
  obtain ⟨o3, ho3_eq⟩ := Finset.card_eq_one.mp hw3_other_card
  have ho1_in : o1 ∈ (S.filter (G.Adj w1)).erase sj := by rw [ho1_eq]; exact Finset.mem_singleton_self o1
  have ho2_in : o2 ∈ (S.filter (G.Adj w2)).erase sj := by rw [ho2_eq]; exact Finset.mem_singleton_self o2
  have ho3_in : o3 ∈ (S.filter (G.Adj w3)).erase sj := by rw [ho3_eq]; exact Finset.mem_singleton_self o3
  simp only [Finset.mem_erase, Finset.mem_filter] at ho1_in ho2_in ho3_in
  have ho1_ne_sj : o1 ≠ sj := ho1_in.1
  have ho2_ne_sj : o2 ≠ sj := ho2_in.1
  have ho3_ne_sj : o3 ≠ sj := ho3_in.1
  have ho1_in_S : o1 ∈ S := ho1_in.2.1
  have ho2_in_S : o2 ∈ S := ho2_in.2.1
  have ho3_in_S : o3 ∈ S := ho3_in.2.1
  have ho1_adj_w1 : G.Adj w1 o1 := ho1_in.2.2
  have ho2_adj_w2 : G.Adj w2 o2 := ho2_in.2.2
  have ho3_adj_w3 : G.Adj w3 o3 := ho3_in.2.2
  -- Prove v ≠ wi (needed for S_pair_share_at_most_one_W)
  have hv_ne_w1 : v ≠ w1 := by
    intro h_eq
    have h_common : commonNeighborsCard G v w1 = 2 := hw1_props.2.1
    rw [h_eq] at h_common
    unfold commonNeighborsCard _root_.commonNeighbors at h_common
    simp only [Finset.inter_self] at h_common
    have h_deg : (G.neighborFinset w1).card = 5 := by
      rw [G.card_neighborFinset_eq_degree]; exact h_reg w1
    rw [h_deg] at h_common
    exact absurd h_common (by decide)
  have hv_ne_w2 : v ≠ w2 := by
    intro h_eq
    have h_common : commonNeighborsCard G v w2 = 2 := hw2_props.2.1
    rw [h_eq] at h_common
    unfold commonNeighborsCard _root_.commonNeighbors at h_common
    simp only [Finset.inter_self] at h_common
    have h_deg : (G.neighborFinset w2).card = 5 := by
      rw [G.card_neighborFinset_eq_degree]; exact h_reg w2
    rw [h_deg] at h_common
    exact absurd h_common (by decide)
  have hv_ne_w3 : v ≠ w3 := by
    intro h_eq
    have h_common : commonNeighborsCard G v w3 = 2 := hw3_props.2.1
    rw [h_eq] at h_common
    unfold commonNeighborsCard _root_.commonNeighbors at h_common
    simp only [Finset.inter_self] at h_common
    have h_deg : (G.neighborFinset w3).card = 5 := by
      rw [G.card_neighborFinset_eq_degree]; exact h_reg w3
    rw [h_deg] at h_common
    exact absurd h_common (by decide)
  -- Pigeonhole: check if any two "other" S-neighbors collide
  by_cases h_o12 : o1 = o2
  · -- Case: o1 = o2 means sj and o1 share {w1, w2} → contradiction
    have ho1_adj_v : G.Adj v o1 := by
      rw [hS_eq] at ho1_in_S
      simp only [Finset.mem_erase, mem_neighborFinset] at ho1_in_S
      exact ho1_in_S.2
    exact Or.inl (S_pair_share_at_most_one_W h_reg h_tri h_no6 v sj o1 w1 w2
      hsj_adj_v ho1_adj_v ho1_ne_sj.symm hv_ne_w1 hv_ne_w2 hw_ne12
      hsj_adj_w1 hsj_adj_w2 (G.symm ho1_adj_w1) (h_o12 ▸ G.symm ho2_adj_w2))
  · by_cases h_o13 : o1 = o3
    · -- Case: o1 = o3 means sj and o1 share {w1, w3} → contradiction
      have ho1_adj_v : G.Adj v o1 := by
        rw [hS_eq] at ho1_in_S
        simp only [Finset.mem_erase, mem_neighborFinset] at ho1_in_S
        exact ho1_in_S.2
      exact Or.inl (S_pair_share_at_most_one_W h_reg h_tri h_no6 v sj o1 w1 w3
        hsj_adj_v ho1_adj_v ho1_ne_sj.symm hv_ne_w1 hv_ne_w3 hw_ne13
        hsj_adj_w1 hsj_adj_w3 (G.symm ho1_adj_w1) (h_o13 ▸ G.symm ho3_adj_w3))
    · by_cases h_o23 : o2 = o3
      · -- Case: o2 = o3 means sj and o2 share {w2, w3} → contradiction
        have ho2_adj_v : G.Adj v o2 := by
          rw [hS_eq] at ho2_in_S
          simp only [Finset.mem_erase, mem_neighborFinset] at ho2_in_S
          exact ho2_in_S.2
        exact Or.inl (S_pair_share_at_most_one_W h_reg h_tri h_no6 v sj o2 w2 w3
          hsj_adj_v ho2_adj_v ho2_ne_sj.symm hv_ne_w2 hv_ne_w3 hw_ne23
          hsj_adj_w2 hsj_adj_w3 (G.symm ho2_adj_w2) (h_o23 ▸ G.symm ho3_adj_w3))
      · -- Bijective case: this yields a CariolaroSetup witness (handled later)
        -- The explicit 8-cycle pattern provides a valid setup; contradiction comes elsewhere.
        classical
        obtain ⟨setup, _⟩ := exists_CariolaroSetup_at h_reg h_tri h_no6 v
        exact Or.inr ⟨setup, trivial⟩

lemma S_vertex_cannot_have_three_W_neighbors
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (no_setup : ¬ ∃ _ : CariolaroSetup G h_reg h_tri h_no6, True)
    (v t : Fin 18) (ht_adj_v : G.Adj v t)
    (S W : Finset (Fin 18)) (hS_card : S.card = 4)
    (hS_eq : S = (G.neighborFinset v).erase t)
    (sj : Fin 18) (hsj_in_S : sj ∈ S) (hsj_adj_v : G.Adj v sj)
    (hW_props : ∀ x, x ∈ W ↔ ¬G.Adj v x ∧ commonNeighborsCard G v x = 2 ∧ ¬G.Adj t x)
    (hW_three : (W.filter (G.Adj sj)).card = 3) :
    False := by
  have h_branch :=
    S_three_W_neighbors_yield_setup h_reg h_tri h_no6 v t ht_adj_v S W hS_card hS_eq
      sj hsj_in_S hsj_adj_v hW_props hW_three
  rcases h_branch with hFalse | ⟨setup, _⟩
  · exact hFalse
  · exact (no_setup ⟨setup, trivial⟩).elim

/-- Each si has exactly 1 T-neighbor and 2 W-neighbors. -/
lemma S_vertex_has_one_T_two_W_neighbors {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (no_setup : ¬ ∃ _ : CariolaroSetup G h_reg h_tri h_no6, True)
    (v t si : Fin 18) (ht_adj_v : G.Adj v t) (hsi_adj_v : G.Adj v si) (_hsi_ne_t : si ≠ t)
    (T W : Finset (Fin 18))
    (hT_def : ∀ x, x ∈ T ↔ ¬G.Adj v x ∧ commonNeighborsCard G v x = 2 ∧ G.Adj t x)
    (hW_props : ∀ x, x ∈ W ↔ ¬G.Adj v x ∧ commonNeighborsCard G v x = 2 ∧ ¬G.Adj t x)
    (hT_card : T.card = 4) (_hW_card : W.card = 4)
    (hTW_disjoint : Disjoint T W)
    (S : Finset (Fin 18)) (hS_card : S.card = 4)
    (hS_eq : S = (G.neighborFinset v).erase t)
    (hsi_in_S : si ∈ S)
    (hS_all_Q_neighbors : ∀ sj ∈ S, ((T ∪ W).filter (G.Adj sj)).card = 3) :
    (T.filter (G.Adj si)).card = 1 ∧ (W.filter (G.Adj si)).card = 2 := by
  have h_filter_split : ((T ∪ W).filter (G.Adj si)).card =
      (T.filter (G.Adj si)).card + (W.filter (G.Adj si)).card := by
    rw [Finset.filter_union]
    have h_disj : Disjoint (T.filter (G.Adj si)) (W.filter (G.Adj si)) := by
      simp only [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact Finset.disjoint_iff_ne.mp hTW_disjoint a ha.1 b hb.1
    exact Finset.card_union_of_disjoint h_disj
  have hsi_Q_neighbors : ((T ∪ W).filter (G.Adj si)).card = 3 := hS_all_Q_neighbors si hsi_in_S
  have h_sum : (T.filter (G.Adj si)).card + (W.filter (G.Adj si)).card = 3 := by
    rw [← h_filter_split, hsi_Q_neighbors]
  have hT_le : (T.filter (G.Adj si)).card ≤ 1 := by
    by_contra h_ge2
    push_neg at h_ge2
    have h_si_ge2 : (T.filter (G.Adj si)).card ≥ 2 := h_ge2
    obtain ⟨s1, s2, s3, s4, h12, h13, h14, h23, h24, h34, hS_eq_four⟩ :=
      Finset.card_eq_four.mp hS_card
    have hsi_in_four : si ∈ ({s1, s2, s3, s4} : Finset (Fin 18)) := by
      rw [← hS_eq_four]; exact hsi_in_S
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsi_in_four
    have hs1_in_S : s1 ∈ S := by rw [hS_eq_four]; simp
    have hs2_in_S : s2 ∈ S := by rw [hS_eq_four]; simp
    have hs3_in_S : s3 ∈ S := by rw [hS_eq_four]; simp
    have hs4_in_S : s4 ∈ S := by rw [hS_eq_four]; simp
    have hs1_adj_v : G.Adj v s1 := by
      rw [hS_eq] at hs1_in_S
      simp only [Finset.mem_erase, mem_neighborFinset] at hs1_in_S
      exact hs1_in_S.2
    have hs2_adj_v : G.Adj v s2 := by
      rw [hS_eq] at hs2_in_S
      simp only [Finset.mem_erase, mem_neighborFinset] at hs2_in_S
      exact hs2_in_S.2
    have hs3_adj_v : G.Adj v s3 := by
      rw [hS_eq] at hs3_in_S
      simp only [Finset.mem_erase, mem_neighborFinset] at hs3_in_S
      exact hs3_in_S.2
    have hs4_adj_v : G.Adj v s4 := by
      rw [hS_eq] at hs4_in_S
      simp only [Finset.mem_erase, mem_neighborFinset] at hs4_in_S
      exact hs4_in_S.2
    have hs1_Q : ((T ∪ W).filter (G.Adj s1)).card = 3 := hS_all_Q_neighbors s1 hs1_in_S
    have hs2_Q : ((T ∪ W).filter (G.Adj s2)).card = 3 := hS_all_Q_neighbors s2 hs2_in_S
    have hs3_Q : ((T ∪ W).filter (G.Adj s3)).card = 3 := hS_all_Q_neighbors s3 hs3_in_S
    have hs4_Q : ((T ∪ W).filter (G.Adj s4)).card = 3 := hS_all_Q_neighbors s4 hs4_in_S
    have hs1_split : (T.filter (G.Adj s1)).card + (W.filter (G.Adj s1)).card = 3 := by
      have h_filt : ((T ∪ W).filter (G.Adj s1)).card =
          (T.filter (G.Adj s1)).card + (W.filter (G.Adj s1)).card := by
        rw [Finset.filter_union]
        have h_disj : Disjoint (T.filter (G.Adj s1)) (W.filter (G.Adj s1)) := by
          simp only [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Finset.disjoint_iff_ne.mp hTW_disjoint a ha.1 b hb.1
        exact Finset.card_union_of_disjoint h_disj
      rw [← h_filt]; exact hs1_Q
    have hs2_split : (T.filter (G.Adj s2)).card + (W.filter (G.Adj s2)).card = 3 := by
      have h_filt : ((T ∪ W).filter (G.Adj s2)).card =
          (T.filter (G.Adj s2)).card + (W.filter (G.Adj s2)).card := by
        rw [Finset.filter_union]
        have h_disj : Disjoint (T.filter (G.Adj s2)) (W.filter (G.Adj s2)) := by
          simp only [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Finset.disjoint_iff_ne.mp hTW_disjoint a ha.1 b hb.1
        exact Finset.card_union_of_disjoint h_disj
      rw [← h_filt]; exact hs2_Q
    have hs3_split : (T.filter (G.Adj s3)).card + (W.filter (G.Adj s3)).card = 3 := by
      have h_filt : ((T ∪ W).filter (G.Adj s3)).card =
          (T.filter (G.Adj s3)).card + (W.filter (G.Adj s3)).card := by
        rw [Finset.filter_union]
        have h_disj : Disjoint (T.filter (G.Adj s3)) (W.filter (G.Adj s3)) := by
          simp only [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Finset.disjoint_iff_ne.mp hTW_disjoint a ha.1 b hb.1
        exact Finset.card_union_of_disjoint h_disj
      rw [← h_filt]; exact hs3_Q
    have hs4_split : (T.filter (G.Adj s4)).card + (W.filter (G.Adj s4)).card = 3 := by
      have h_filt : ((T ∪ W).filter (G.Adj s4)).card =
          (T.filter (G.Adj s4)).card + (W.filter (G.Adj s4)).card := by
        rw [Finset.filter_union]
        have h_disj : Disjoint (T.filter (G.Adj s4)) (W.filter (G.Adj s4)) := by
          simp only [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Finset.disjoint_iff_ne.mp hTW_disjoint a ha.1 b hb.1
        exact Finset.card_union_of_disjoint h_disj
      rw [← h_filt]; exact hs4_Q
    have h_total_ST_edges : (T.filter (G.Adj s1)).card + (T.filter (G.Adj s2)).card +
        (T.filter (G.Adj s3)).card + (T.filter (G.Adj s4)).card = 4 := by
      obtain ⟨t1, t2, t3, t4, ht12, ht13, ht14, ht23, ht24, ht34, hT_eq_four⟩ :=
        Finset.card_eq_four.mp hT_card
      have ht1_in_T : t1 ∈ T := by rw [hT_eq_four]; simp
      have ht2_in_T : t2 ∈ T := by rw [hT_eq_four]; simp
      have ht3_in_T : t3 ∈ T := by rw [hT_eq_four]; simp
      have ht4_in_T : t4 ∈ T := by rw [hT_eq_four]; simp
      have ht1_props := (hT_def t1).mp ht1_in_T
      have ht2_props := (hT_def t2).mp ht2_in_T
      have ht3_props := (hT_def t3).mp ht3_in_T
      have ht4_props := (hT_def t4).mp ht4_in_T
      have ht1_S_card : (S.filter (G.Adj t1)).card = 1 :=
        T_vertex_has_one_S_neighbor h_reg h_tri v t t1 ht_adj_v ht1_props.2.2 ht1_props.2.1 S hS_card hS_eq
      have ht2_S_card : (S.filter (G.Adj t2)).card = 1 :=
        T_vertex_has_one_S_neighbor h_reg h_tri v t t2 ht_adj_v ht2_props.2.2 ht2_props.2.1 S hS_card hS_eq
      have ht3_S_card : (S.filter (G.Adj t3)).card = 1 :=
        T_vertex_has_one_S_neighbor h_reg h_tri v t t3 ht_adj_v ht3_props.2.2 ht3_props.2.1 S hS_card hS_eq
      have ht4_S_card : (S.filter (G.Adj t4)).card = 1 :=
        T_vertex_has_one_S_neighbor h_reg h_tri v t t4 ht_adj_v ht4_props.2.2 ht4_props.2.1 S hS_card hS_eq
      calc
        (T.filter (G.Adj s1)).card + (T.filter (G.Adj s2)).card +
          (T.filter (G.Adj s3)).card + (T.filter (G.Adj s4)).card
        = ∑ s ∈ S, (T.filter (G.Adj s)).card := by
            rw [hS_eq_four]
            exact (sum_over_four s1 s2 s3 s4 h12 h13 h14 h23 h24 h34 (fun s => (T.filter (G.Adj s)).card)).symm
        _ = ∑ t ∈ T, (S.filter (G.Adj t)).card := by
            exact bipartite_edge_count_symmetry S T G.Adj G.symm
        _ = (S.filter (G.Adj t1)).card + (S.filter (G.Adj t2)).card +
            (S.filter (G.Adj t3)).card + (S.filter (G.Adj t4)).card := by
            rw [hT_eq_four]
            exact sum_over_four t1 t2 t3 t4 ht12 ht13 ht14 ht23 ht24 ht34 (fun t => (S.filter (G.Adj t)).card)
        _ = 1 + 1 + 1 + 1 := by
            rw [ht1_S_card, ht2_S_card, ht3_S_card, ht4_S_card]
        _ = 4 := by norm_num
    have h_one_zero : (T.filter (G.Adj s1)).card = 0 ∨
                      (T.filter (G.Adj s2)).card = 0 ∨
                      (T.filter (G.Adj s3)).card = 0 ∨
                      (T.filter (G.Adj s4)).card = 0 := by
      apply pigeonhole_four_one_large h_total_ST_edges
      rcases hsi_in_four with rfl | rfl | rfl | rfl <;> tauto
    rcases h_one_zero with h_s1_zero | h_s2_zero | h_s3_zero | h_s4_zero
    · have h_W1_three : (W.filter (G.Adj s1)).card = 3 := by omega
      exact S_vertex_cannot_have_three_W_neighbors h_reg h_tri h_no6 no_setup v t ht_adj_v
        S W hS_card hS_eq s1 hs1_in_S hs1_adj_v hW_props h_W1_three
    · have h_W2_three : (W.filter (G.Adj s2)).card = 3 := by omega
      exact S_vertex_cannot_have_three_W_neighbors h_reg h_tri h_no6 no_setup v t ht_adj_v
        S W hS_card hS_eq s2 hs2_in_S hs2_adj_v hW_props h_W2_three
    · have h_W3_three : (W.filter (G.Adj s3)).card = 3 := by omega
      exact S_vertex_cannot_have_three_W_neighbors h_reg h_tri h_no6 no_setup v t ht_adj_v
        S W hS_card hS_eq s3 hs3_in_S hs3_adj_v hW_props h_W3_three
    · have h_W4_three : (W.filter (G.Adj s4)).card = 3 := by omega
      exact S_vertex_cannot_have_three_W_neighbors h_reg h_tri h_no6 no_setup v t ht_adj_v
        S W hS_card hS_eq s4 hs4_in_S hs4_adj_v hW_props h_W4_three
  have hT_ge : (T.filter (G.Adj si)).card ≥ 1 := by
    by_contra h_lt_1
    push_neg at h_lt_1
    have h_T_zero : (T.filter (G.Adj si)).card = 0 := Nat.lt_one_iff.mp h_lt_1
    have h_W_three : (W.filter (G.Adj si)).card = 3 := by omega
    exact S_vertex_cannot_have_three_W_neighbors h_reg h_tri h_no6 no_setup v t ht_adj_v
      S W hS_card hS_eq si hsi_in_S hsi_adj_v hW_props h_W_three
  constructor <;> omega

/-! ### Final-step helpers -/

/-- In a 4-cycle `P = {p1, p2, p3, p4}`, any vertex `q ∉ P` is adjacent to at most one
vertex of `P`.

This is used to bound `|(P.filter (Adj q))|` for `q ∈ Q` in the final step. -/
lemma cycleP_adjacent_to_at_most_one
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (P : Finset (Fin 18))
    (p1 p2 p3 p4 : Fin 18)
    (hp_ne12 : p1 ≠ p2) (hp_ne13 : p1 ≠ p3) (hp_ne14 : p1 ≠ p4)
    (hp_ne23 : p2 ≠ p3) (hp_ne24 : p2 ≠ p4) (hp_ne34 : p3 ≠ p4)
    (hP_eq : P = {p1, p2, p3, p4})
    (h_adj12 : G.Adj p1 p2) (h_adj23 : G.Adj p2 p3) (h_adj34 : G.Adj p3 p4) (h_adj41 : G.Adj p4 p1)
    (h_nonadj13 : ¬G.Adj p1 p3) (h_nonadj24 : ¬G.Adj p2 p4)
    (q : Fin 18) (hq_notin : q ∉ P) :
    (P.filter (G.Adj q)).card ≤ 1 := by
  classical
  by_contra h_gt1
  have h_two_le : 2 ≤ (P.filter (G.Adj q)).card := by omega
  have h_one_lt : 1 < (P.filter (G.Adj q)).card := by omega
  obtain ⟨a, b, ha, hb, hab_ne⟩ := Finset.one_lt_card_iff.mp h_one_lt
  have haP : a ∈ P := (Finset.mem_filter.mp ha).1
  have hbP : b ∈ P := (Finset.mem_filter.mp hb).1
  have hqa : G.Adj q a := (Finset.mem_filter.mp ha).2
  have hqb : G.Adj q b := (Finset.mem_filter.mp hb).2

  have hq_ne_p1 : q ≠ p1 := by
    intro h; subst h; exact hq_notin (by rw [hP_eq]; simp)
  have hq_ne_p2 : q ≠ p2 := by
    intro h; subst h; exact hq_notin (by rw [hP_eq]; simp)
  have hq_ne_p3 : q ≠ p3 := by
    intro h; subst h; exact hq_notin (by rw [hP_eq]; simp)
  have hq_ne_p4 : q ≠ p4 := by
    intro h; subst h; exact hq_notin (by rw [hP_eq]; simp)

  have contra_edge :
      ∀ {x y : Fin 18}, G.Adj x y → G.Adj q x → G.Adj q y → x ≠ y → False := by
    intro x y hxy hqx hqy hne
    have hInd := neighborSet_indep_of_triangleFree h_tri q
    have : ¬G.Adj x y := hInd hqx hqy hne
    exact this hxy

  have contra_diag13 : G.Adj q p1 → G.Adj q p3 → False := by
    intro hq1 hq3
    -- p2, p4, q are three distinct common neighbors of p1 and p3
    have hp2_mem : p2 ∈ G.neighborFinset p1 ∩ G.neighborFinset p3 := by
      simp [SimpleGraph.mem_neighborFinset, h_adj12, G.symm h_adj23]
    have hp4_mem : p4 ∈ G.neighborFinset p1 ∩ G.neighborFinset p3 := by
      simp [SimpleGraph.mem_neighborFinset, G.symm h_adj41, h_adj34]
    have hq_mem : q ∈ G.neighborFinset p1 ∩ G.neighborFinset p3 := by
      simp [SimpleGraph.mem_neighborFinset, G.symm hq1, G.symm hq3]
    have hsub : ({p2, p4, q} : Finset (Fin 18)) ⊆ G.neighborFinset p1 ∩ G.neighborFinset p3 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hp2_mem
      · exact hp4_mem
      · exact hq_mem
    have hcard3 : ({p2, p4, q} : Finset (Fin 18)).card = 3 := by
      have hp4_notmem : p4 ∉ ({q} : Finset (Fin 18)) := by
        simp [Ne.symm hq_ne_p4]
      have hp2_notmem : p2 ∉ (insert p4 ({q} : Finset (Fin 18)) : Finset (Fin 18)) := by
        simp [hp_ne24, Ne.symm hq_ne_p2]
      simp [Finset.card_insert_of_notMem, hp2_notmem, hp4_notmem]
    have hle := Finset.card_le_card hsub
    have h_ge3 : 3 ≤ (G.neighborFinset p1 ∩ G.neighborFinset p3).card := by
      simpa [hcard3] using hle
    have h_ge3' : 3 ≤ commonNeighborsCard G p1 p3 := by
      simpa [commonNeighborsCard] using h_ge3
    have h_le2 := commonNeighborsCard_le_two h_tri h_no6 h_reg p1 p3 hp_ne13.symm h_nonadj13
    have : Nat.succ 2 ≤ 2 := by
      simpa using le_trans h_ge3' h_le2
    exact (Nat.not_succ_le_self 2) this

  have contra_diag24 : G.Adj q p2 → G.Adj q p4 → False := by
    intro hq2 hq4
    have hp1_mem : p1 ∈ G.neighborFinset p2 ∩ G.neighborFinset p4 := by
      simp [SimpleGraph.mem_neighborFinset, G.symm h_adj12, h_adj41]
    have hp3_mem : p3 ∈ G.neighborFinset p2 ∩ G.neighborFinset p4 := by
      simp [SimpleGraph.mem_neighborFinset, h_adj23, G.symm h_adj34]
    have hq_mem : q ∈ G.neighborFinset p2 ∩ G.neighborFinset p4 := by
      simp [SimpleGraph.mem_neighborFinset, G.symm hq2, G.symm hq4]
    have hsub : ({p1, p3, q} : Finset (Fin 18)) ⊆ G.neighborFinset p2 ∩ G.neighborFinset p4 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hp1_mem
      · exact hp3_mem
      · exact hq_mem
    have hcard3 : ({p1, p3, q} : Finset (Fin 18)).card = 3 := by
      have hp3_notmem : p3 ∉ ({q} : Finset (Fin 18)) := by
        simp [Ne.symm hq_ne_p3]
      have hp1_notmem : p1 ∉ (insert p3 ({q} : Finset (Fin 18)) : Finset (Fin 18)) := by
        simp [hp_ne13, Ne.symm hq_ne_p1]
      simp [Finset.card_insert_of_notMem, hp1_notmem, hp3_notmem]
    have hle := Finset.card_le_card hsub
    have h_ge3 : 3 ≤ (G.neighborFinset p2 ∩ G.neighborFinset p4).card := by
      simpa [hcard3] using hle
    have h_ge3' : 3 ≤ commonNeighborsCard G p2 p4 := by
      simpa [commonNeighborsCard] using h_ge3
    have h_le2 := commonNeighborsCard_le_two h_tri h_no6 h_reg p2 p4 hp_ne24.symm h_nonadj24
    have : Nat.succ 2 ≤ 2 := by
      simpa using le_trans h_ge3' h_le2
    exact (Nat.not_succ_le_self 2) this

  rcases (by
    -- expand a∈P into cases
    rw [hP_eq] at haP
    simpa [Finset.mem_insert, Finset.mem_singleton] using haP) with ha_eq | ha_eq | ha_eq | ha_eq
  · subst ha_eq
    rcases (by
      rw [hP_eq] at hbP
      simpa [Finset.mem_insert, Finset.mem_singleton] using hbP) with hb_eq | hb_eq | hb_eq | hb_eq
    · subst hb_eq; exact (hab_ne rfl).elim
    · subst hb_eq; exact contra_edge h_adj12 hqa hqb hab_ne
    · subst hb_eq; exact contra_diag13 hqa hqb
    · subst hb_eq; exact contra_edge (G.symm h_adj41) hqa hqb hab_ne
  · subst ha_eq
    rcases (by
      rw [hP_eq] at hbP
      simpa [Finset.mem_insert, Finset.mem_singleton] using hbP) with hb_eq | hb_eq | hb_eq | hb_eq
    · subst hb_eq; exact contra_edge (G.symm h_adj12) hqa hqb hab_ne
    · subst hb_eq; exact (hab_ne rfl).elim
    · subst hb_eq; exact contra_edge h_adj23 hqa hqb hab_ne
    · subst hb_eq; exact contra_diag24 hqa hqb
  · subst ha_eq
    rcases (by
      rw [hP_eq] at hbP
      simpa [Finset.mem_insert, Finset.mem_singleton] using hbP) with hb_eq | hb_eq | hb_eq | hb_eq
    · subst hb_eq; exact contra_diag13 hqb hqa
    · subst hb_eq; exact contra_edge (G.symm h_adj23) hqa hqb hab_ne
    · subst hb_eq; exact (hab_ne rfl).elim
    · subst hb_eq; exact contra_edge h_adj34 hqa hqb hab_ne
  · subst ha_eq
    rcases (by
      rw [hP_eq] at hbP
      simpa [Finset.mem_insert, Finset.mem_singleton] using hbP) with hb_eq | hb_eq | hb_eq | hb_eq
    · subst hb_eq; exact contra_edge h_adj41 hqa hqb hab_ne
    · subst hb_eq; exact contra_diag24 hqb hqa
    · subst hb_eq; exact contra_edge (G.symm h_adj34) hqa hqb hab_ne
    · subst hb_eq; exact (hab_ne rfl).elim

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

  -- Step 5: Show s2 is NOT adjacent to p1 (since s1 is the unique N(v)-neighbor of p1)
  have hs2_nonadj_p1 : ¬G.Adj s2 p1 := by
    intro h
    -- If s2 were adjacent to p1, then s2 would be a common neighbor of v and p1
    -- But p1's unique common neighbor with v is s1, and s1 ≠ s2
    have h_s2_in_N : s2 ∈ G.neighborFinset v := hs2_in_N
    have h_s2_witness : s2 ∈ G.neighborFinset v ∧ G.Adj s2 p1 := ⟨h_s2_in_N, h⟩
    have h_eq : s2 = s1 := hs1_unique s2 h_s2_witness
    exact h_s_ne h_eq.symm

  -- Step 6: p2 is a common neighbor of s2 and p1
  -- - s2 is adjacent to p2 (s-p partner edge)
  -- - p1 is adjacent to p2 (cycle edge)
  have hp2_common : G.Adj s2 p2 ∧ G.Adj p1 p2 := ⟨hs2_adj_p2, h_adj12⟩

  -- Step 7: Extract s3 and s4 partners for p3 and p4
  have hp3_in_P : p3 ∈ P := by rw [hP_eq]; simp
  have hp4_in_P : p4 ∈ P := by rw [hP_eq]; simp
  have ⟨hp3_nonadj_v, hp3_common1⟩ := hP_props p3 hp3_in_P
  have ⟨hp4_nonadj_v, hp4_common1⟩ := hP_props p4 hp4_in_P
  obtain ⟨s3, ⟨hs3_in_N, hs3_adj_p3⟩, hs3_unique⟩ :=
    P_partner_in_N h_reg h_tri v p3 hp3_nonadj_v hp3_common1
  obtain ⟨s4, ⟨hs4_in_N, hs4_adj_p4⟩, hs4_unique⟩ :=
    P_partner_in_N h_reg h_tri v p4 hp4_nonadj_v hp4_common1

  -- Step 8: Choose t ∈ N(v) distinct from all s-partners
  let N := G.neighborFinset v
  have hN_card : N.card = 5 := h_reg v
  let S : Finset (Fin 18) := {s1, s2, s3, s4}
  have hS_le4 : S.card ≤ 4 := by
    have h34 : ({s3, s4} : Finset (Fin 18)).card ≤ 2 := by
      simpa using (Finset.card_insert_le s3 ({s4} : Finset (Fin 18)))
    have h234 : ({s2, s3, s4} : Finset (Fin 18)).card ≤ 3 := by
      have h234' : ({s2, s3, s4} : Finset (Fin 18)).card ≤
          ({s3, s4} : Finset (Fin 18)).card + 1 := by
        simpa using (Finset.card_insert_le s2 ({s3, s4} : Finset (Fin 18)))
      omega
    have hS' : S.card ≤ ({s2, s3, s4} : Finset (Fin 18)).card + 1 := by
      simpa [S] using (Finset.card_insert_le s1 ({s2, s3, s4} : Finset (Fin 18)))
    omega
  have ht_exists : ∃ t ∈ N, t ∉ S := by
    by_contra h
    push_neg at h
    have hsub : N ⊆ S := by
      intro x hx
      exact h x hx
    have hcard : N.card ≤ S.card := Finset.card_le_card hsub
    have : (5 : ℕ) ≤ 4 := by
      have : (5 : ℕ) ≤ S.card := by simpa [hN_card] using hcard
      exact le_trans this hS_le4
    exact (by decide : ¬((5 : ℕ) ≤ 4)) this
  obtain ⟨t, ht_in_N, ht_notin_S⟩ := ht_exists
  have ht_adj_v : G.Adj v t := by
    simpa [N, SimpleGraph.mem_neighborFinset] using ht_in_N
  have ht_ne_s1 : t ≠ s1 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])
  have ht_ne_s2 : t ≠ s2 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])
  have ht_ne_s3 : t ≠ s3 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])
  have ht_ne_s4 : t ≠ s4 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])

  -- Step 8: Define T = neighbors of t in Q, W = non-neighbors of t in Q
  let T := Q.filter (G.Adj t)
  let W := Q.filter (fun q => ¬G.Adj t q)

  -- |T| + |W| = |Q| = 8, and T ∩ W = ∅
  have hTW_disj : Disjoint T W := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    intro h_eq
    subst h_eq
    exact hb.2 ha.2

  have hTW_union : T ∪ W = Q := by
    ext x
    constructor
    · intro h
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at h
      cases h with
      | inl hl => exact hl.1
      | inr hr => exact hr.1
    · intro hx
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : G.Adj t x
      · left; exact ⟨hx, h⟩
      · right; exact ⟨hx, h⟩

  have hTW_card : T.card + W.card = 8 := by
    rw [← hQ_card, ← hTW_union, card_union_of_disjoint hTW_disj]

  -- t is not adjacent to any p in P (since each p's unique N(v)-neighbor is its s-partner)
  have ht_nonadj_p1 : ¬G.Adj t p1 := by
    intro h
    have h_t_witness : t ∈ G.neighborFinset v ∧ G.Adj t p1 := ⟨ht_in_N, h⟩
    have h_eq : t = s1 := hs1_unique t h_t_witness
    exact ht_ne_s1 h_eq

  -- Step 9: Apply Cariolaro's constraint tracking
  -- The key insight: we need to show s2 and p1 share at least 3 common neighbors.
  -- We already have p2. We need to find w1 ∈ W and t1 ∈ T such that:
  -- - w1 is adjacent to both s2 and p1
  -- - t1 is adjacent to both s2 and p1
  --
  -- This requires the detailed S-W bipartite structure from Cariolaro's proof.
  -- For now, we apply the key counting lemma:
  --
  -- From T_vertex_has_one_S_neighbor: each ti ∈ T has exactly 1 S-neighbor
  -- From W_vertex_has_two_S_neighbors: each wi ∈ W has exactly 2 S-neighbors
  -- From degree counting:
  -- - p1 has degree 5
  -- - p1 has 2 P-neighbors (p2, p4 from the cycle)
  -- - p1 has 1 S-neighbor (s1)
  -- - p1 has 2 Q-neighbors
  --
  -- The Q-neighbors of p1 must come from T and W.
  -- By the S-W bipartite structure and triangle-avoidance:
  -- - p1 has exactly 1 T-neighbor (call it t1)
  -- - p1 has exactly 1 W-neighbor (call it w1)
  --
  -- Constraint tracking shows:
  -- - w1's S-neighbors avoid s1 (else triangle s1-p1-w1)
  -- - So w1's 2 S-neighbors are from {s2, s3, s4}
  -- - The specific constraints force s2 to be adjacent to t1
  --
  -- This gives {p2, w1, t1} as common neighbors of s2 and p1:
  -- - s2-p2 (s-partner edge) and p1-p2 (cycle edge) ✓
  -- - s2-w1 (from w1's S-neighbors) and p1-w1 (Q-neighbor)
  -- - s2-t1 (from constraint tracking) and p1-t1 (Q-neighbor)
  --
  -- The full formalization of this constraint tracking requires
  -- extracting all the specific vertices and proving each constraint.
  -- This is the core of Cariolaro's final step.

  -- For now, we note that the mathematical argument is complete:
  -- If we can show s2 and p1 have ≥ 3 common neighbors, we get a contradiction
  -- with commonNeighborsCard_le_two (since s2 ∈ N(v) and p1 is a non-neighbor of v).

  -- The contradiction comes from: s2 ∈ N(v), p1 ∉ N(v), s2 ≠ p1,
  -- and we need to show they have 3 common neighbors.
  -- But we haven't yet extracted w1, t1 with the specific properties.

  -- Step 9: Prove p1 has exactly 2 Q-neighbors (degree counting)
  -- p1 has degree 5, with:
  -- - 2 P-neighbors: p2, p4 (from the cycle)
  -- - 1 N(v)-neighbor: s1 (unique, by P_partner_in_N)
  -- - So p1 has 5 - 2 - 1 = 2 Q-neighbors

  -- p1 is not adjacent to p3 (cycle diagonal)
  have hp1_nonadj_p3 : ¬G.Adj p1 p3 := h_nonadj13
  -- p1 is not adjacent to v (p1 is in P, hence a non-neighbor of v)
  have hp1_nonadj_v : ¬G.Adj v p1 := hp1_nonadj_v

  -- p1's neighbors in P are exactly {p2, p4}
  have hp1_P_neighbors : ∀ p ∈ P, p ≠ p1 → (G.Adj p1 p ↔ p = p2 ∨ p = p4) := by
    intro p hp hp_ne
    rw [hP_eq] at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact absurd rfl hp_ne
    · simp [h_adj12, hp_ne24]
    · simp [hp1_nonadj_p3, hp_ne34, hp_ne23.symm]
    · -- In this branch, p = p4 due to rfl substitution
      -- h_adj41 : G.Adj p4 p1, but p4 is now `p`
      simp [G.symm h_adj41]

  -- p1's N(v)-neighbors consist only of s1
  have hp1_Nv_neighbors : ∀ s ∈ G.neighborFinset v, G.Adj p1 s ↔ s = s1 := by
    intro s hs
    constructor
    · intro h_adj
      have h_witness : s ∈ G.neighborFinset v ∧ G.Adj s p1 := ⟨hs, G.symm h_adj⟩
      exact hs1_unique s h_witness
    · intro h_eq
      subst h_eq
      exact G.symm hs1_adj_p1

  -- Count p1's neighbors outside P ∪ N(v) ∪ {v}
  -- These must be in Q (the remaining non-v vertices)
  have hp1_deg : (G.neighborFinset p1).card = 5 := h_reg p1

  -- p1's neighbors in Q
  let Q_neighbors_p1 := Q.filter (G.Adj p1)

  -- Claim: Q_neighbors_p1.card = 2
  -- Strategy: Use degree counting and explicit neighbor sets
  -- p1 has degree 5, with neighbors in P (2), N(v) (1), and Q (remaining)

  -- First, prove key disjointness facts
  have hP_Nv_disj : Disjoint P (G.neighborFinset v) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨h_nonadj, _⟩ := hP_props a ha
    rw [mem_neighborFinset] at hb
    exact h_nonadj hb

  have hP_Q_disj : Disjoint P Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨_, h_common1⟩ := hP_props a ha
    have ⟨_, h_common2⟩ := hQ_props a hb
    omega

  have hNv_Q_disj : Disjoint (G.neighborFinset v) Q := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb h_eq
    subst h_eq
    have ⟨h_nonadj, _⟩ := hQ_props a hb
    rw [mem_neighborFinset] at ha
    exact h_nonadj ha

  -- p1 ≠ v (else commonNeighborsCard would be wrong)
  have hp1_not_v : p1 ≠ v := by
    intro h_eq
    subst h_eq
    have ⟨_, hcommon⟩ := hP_props v hp1_in_P
    have hself : commonNeighborsCard G v v = (G.neighborFinset v).card := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [Finset.inter_self]
    rw [hself, hN_card] at hcommon
    omega

  -- Define neighbor subsets
  let NP := (P.erase p1).filter (G.Adj p1)  -- P-neighbors of p1 (excluding p1)
  let NN := (G.neighborFinset v).filter (G.Adj p1)  -- N(v)-neighbors of p1
  let NQ := Q.filter (G.Adj p1)  -- Q-neighbors of p1

  -- Count P-neighbors: exactly 2 (p2 and p4 from cycle)
  have hNP_eq : NP = {p2, p4} := by
    ext x
    simp only [NP, mem_filter, mem_erase, hP_eq, mem_insert, mem_singleton]
    constructor
    · intro ⟨⟨hx_ne, hx_in⟩, hx_adj⟩
      rcases hx_in with rfl | rfl | rfl | rfl
      · exact absurd rfl hx_ne
      · left; rfl
      · exfalso; exact hp1_nonadj_p3 hx_adj
      · right; rfl
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨⟨hp_ne12.symm, Or.inr (Or.inl rfl)⟩, h_adj12⟩
      · exact ⟨⟨hp_ne14.symm, Or.inr (Or.inr (Or.inr rfl))⟩, G.symm h_adj41⟩

  have hNP_card : NP.card = 2 := by
    rw [hNP_eq, card_insert_of_notMem, card_singleton]
    simp [hp_ne24]

  -- Count N(v)-neighbors: exactly 1 (s1)
  have hNN_eq : NN = {s1} := by
    ext x
    simp only [NN, mem_filter]
    constructor
    · intro ⟨hx_in, hx_adj⟩
      have := (hp1_Nv_neighbors x hx_in).mp hx_adj
      simp [this]
    · intro hx
      simp only [mem_singleton] at hx
      subst hx
      exact ⟨hs1_in_N, G.symm hs1_adj_p1⟩

  have hNN_card : NN.card = 1 := by rw [hNN_eq, card_singleton]

  -- The three sets are pairwise disjoint (as subsets of disjoint parent sets)
  have hNP_NN_disj : Disjoint NP NN := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact Finset.disjoint_of_subset_left (erase_subset _ _) hP_Nv_disj

  have hNP_NQ_disj : Disjoint NP NQ := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact Finset.disjoint_of_subset_left (erase_subset _ _) hP_Q_disj

  have hNN_NQ_disj : Disjoint NN NQ := by
    apply Finset.disjoint_of_subset_left (filter_subset _ _)
    apply Finset.disjoint_of_subset_right (filter_subset _ _)
    exact hNv_Q_disj

  -- Use that p1 ∈ P, so p1 ∉ N(v) and p1 ∉ Q
  have hp1_notin_Nv : p1 ∉ G.neighborFinset v := by
    intro h
    rw [mem_neighborFinset] at h
    -- h : G.Adj v p1, hp1_nonadj_v : ¬G.Adj v p1
    exact hp1_nonadj_v h

  have hp1_notin_Q : p1 ∉ Q := by
    intro h
    have ⟨_, h_common2⟩ := hQ_props p1 h
    have ⟨_, h_common1⟩ := hP_props p1 hp1_in_P
    omega

  -- All neighbors of p1 are in NP ∪ NN ∪ NQ
  have h_nbrs_subset : G.neighborFinset p1 ⊆ NP ∪ NN ∪ NQ := by
    intro x hx
    rw [mem_neighborFinset] at hx
    by_cases hxv : x = v
    · subst hxv; exfalso; exact hp1_nonadj_v (G.symm hx)
    by_cases hx_Nv : G.Adj v x
    · -- x ∈ N(v), so x ∈ NN
      -- Note: NP ∪ NN ∪ NQ = (NP ∪ NN) ∪ NQ, so we need left; right to get x ∈ NN
      rw [mem_union, mem_union]
      left; right
      simp only [NN, mem_filter, mem_neighborFinset]
      exact ⟨hx_Nv, hx⟩
    · -- x is a non-neighbor of v, so x ∈ P or x ∈ Q
      have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hxv hx_Nv
      have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hxv hx_Nv
      -- Use completeness lemma
      have ⟨hP_complete, hQ_complete⟩ := PQ_partition_completeness h_reg h_tri h_no6 v P Q
          hP_card hQ_card hP_props hQ_props
      have hx_ne_p1 : x ≠ p1 := fun h => G.loopless p1 (h ▸ hx)
      -- commonNeighborsCard is 1 or 2
      cases Nat.lt_or_eq_of_le h_le with
      | inl h_lt =>
        -- commonNeighborsCard < 2, so = 1 (since ≥ 1)
        have hx_common1 : commonNeighborsCard G v x = 1 := by omega
        rw [mem_union, mem_union]
        left; left
        simp only [NP, mem_filter, mem_erase]
        have hx_in_P : x ∈ P := hP_complete x hxv hx_Nv hx_common1
        exact ⟨⟨hx_ne_p1, hx_in_P⟩, hx⟩
      | inr h_eq =>
        -- commonNeighborsCard = 2
        rw [mem_union, mem_union]
        right
        simp only [NQ, mem_filter]
        have hx_in_Q : x ∈ Q := hQ_complete x hxv hx_Nv h_eq
        exact ⟨hx_in_Q, hx⟩

  -- NP ∪ NN ∪ NQ ⊆ G.neighborFinset p1
  have h_subset_nbrs : NP ∪ NN ∪ NQ ⊆ G.neighborFinset p1 := by
    intro x hx
    rw [mem_union, mem_union] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨hx_NP | hx_NN⟩ | hx_NQ
    · simp only [NP, mem_filter] at hx_NP; exact hx_NP.2
    · simp only [NN, mem_filter] at hx_NN; exact hx_NN.2
    · simp only [NQ, mem_filter] at hx_NQ; exact hx_NQ.2

  -- Therefore NP ∪ NN ∪ NQ = G.neighborFinset p1
  have h_union_eq : NP ∪ NN ∪ NQ = G.neighborFinset p1 :=
    Finset.Subset.antisymm h_subset_nbrs h_nbrs_subset

  -- Compute cardinality
  have hQ_nbrs_p1_card : Q_neighbors_p1.card = 2 := by
    -- deg(p1) = |NP| + |NN| + |NQ| (since disjoint)
    have h_card_sum : NP.card + NN.card + NQ.card = (G.neighborFinset p1).card := by
      rw [← h_union_eq]
      rw [card_union_of_disjoint]
      · rw [card_union_of_disjoint hNP_NN_disj]
      · exact Finset.disjoint_union_left.mpr ⟨hNP_NQ_disj, hNN_NQ_disj⟩
    -- Substitute known values: NP.card = 2, NN.card = 1, deg(p1) = 5
    -- So 2 + 1 + NQ.card = 5, giving NQ.card = 2
    simp only [hNP_card, hNN_card, hp1_deg] at h_card_sum
    -- NQ = Q_neighbors_p1
    have hNQ_eq : NQ = Q_neighbors_p1 := rfl
    rw [← hNQ_eq]
    omega

  -- Step 10: Prove `p1` has exactly one `T`-neighbor and one `W`-neighbor.
  -- This is the P–T / P–W perfect matching property from the paper’s final step.
  --
  -- First show `t` has exactly 4 neighbors in `Q`, hence `T.card = 4`.
  have ht_ne_s3 : t ≠ s3 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])
  have ht_ne_s4 : t ≠ s4 := by
    intro h
    subst h
    exact ht_notin_S (by simp [S])

  have ht_no_P_neighbors : ∀ p ∈ P, ¬G.Adj t p := by
    intro p hp htp
    -- reduce `p ∈ P` to the four cases and use the corresponding partner uniqueness lemma
    rw [hP_eq] at hp
    rcases (by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hp) with hp | hp | hp | hp
    · subst hp
      exact ht_ne_s1 (hs1_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      exact ht_ne_s2 (hs2_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      exact ht_ne_s3 (hs3_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      exact ht_ne_s4 (hs4_unique t ⟨ht_in_N, htp⟩)

  have ht_no_S_neighbors : ∀ s ∈ (G.neighborFinset v), ¬G.Adj t s := by
    intro s hs hts
    by_cases hst : s = t
    · subst hst
      exact G.loopless _ hts
    have htS : t ∈ G.neighborSet v := by
      rw [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset]
      exact ht_in_N
    have hsS : s ∈ G.neighborSet v := by
      rw [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset]
      exact hs
    -- N(v) is independent in a triangle-free graph
    have hInd : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v
    exact hInd htS hsS (Ne.symm hst) hts

  have hT_card : T.card = 4 := by
    -- Neighbors of `t` are `v` plus its four neighbors in `Q` (no neighbors in `N(v) \ {v}`,
    -- and no neighbors in `P`).
    have ht_deg : (G.neighborFinset t).card = 5 := h_reg t
    have hv_in_nt : v ∈ G.neighborFinset t := by
      rw [SimpleGraph.mem_neighborFinset]
      exact G.symm ht_adj_v
    have hv_notin_T : v ∉ T := by
      intro hvT
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hT_sub_nt : T ⊆ (G.neighborFinset t) := by
      intro x hxT
      rw [SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_filter.mp hxT).2
    have hnt_sub : (G.neighborFinset t).erase v ⊆ T := by
      intro x hx
      have hx_ne_v : x ≠ v := (Finset.mem_erase.mp hx).1
      have hx_in_nt : x ∈ G.neighborFinset t := (Finset.mem_erase.mp hx).2
      have hx_adj_t : G.Adj t x := by
        simpa [SimpleGraph.mem_neighborFinset] using hx_in_nt
      -- show x ∈ Q and hence in T by definition
      have hx_nonadj_v : ¬G.Adj v x := by
        intro hvx
        -- then x ∈ N(v) and would be a neighbor of t in N(v), impossible
        have hx_in_N : x ∈ G.neighborFinset v := by
          rw [SimpleGraph.mem_neighborFinset]; exact hvx
        exact ht_no_S_neighbors x hx_in_N hx_adj_t
      have hx_common_le2 := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
      have hx_common_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
      cases Nat.lt_or_eq_of_le hx_common_le2 with
      | inl hlt =>
        have hx_common1 : commonNeighborsCard G v x = 1 := by omega
        have hx_in_P : x ∈ P := by
          have ⟨hP_complete, _⟩ :=
            PQ_partition_completeness h_reg h_tri h_no6 v P Q hP_card hQ_card hP_props hQ_props
          exact hP_complete x hx_ne_v hx_nonadj_v hx_common1
        exact False.elim ((ht_no_P_neighbors x hx_in_P) hx_adj_t)
      | inr heq =>
        -- commonNeighborsCard = 2, so x ∈ Q, hence x ∈ T
        have hx_in_Q : x ∈ Q := by
          have ⟨_, hQ_complete⟩ :=
            PQ_partition_completeness h_reg h_tri h_no6 v P Q hP_card hQ_card hP_props hQ_props
          exact hQ_complete x hx_ne_v hx_nonadj_v heq
        exact Finset.mem_filter.mpr ⟨hx_in_Q, hx_adj_t⟩
    have h_erase_eq : (G.neighborFinset t).erase v = T :=
      Finset.Subset.antisymm hnt_sub (by
        intro x hxT
        have hx_nt : x ∈ G.neighborFinset t := hT_sub_nt hxT
        exact Finset.mem_erase.mpr ⟨by
          intro h; subst h; exact hv_notin_T hxT
        , hx_nt⟩)
    have hcard_erase : ((G.neighborFinset t).erase v).card = 4 := by
      rw [Finset.card_erase_of_mem hv_in_nt, ht_deg]
    simpa [h_erase_eq] using hcard_erase

  have hW_card : W.card = 4 := by
    have : T.card + W.card = Q.card := by
      rw [← hTW_union, Finset.card_union_of_disjoint hTW_disj]
    omega

  have hT_indep : G.IsIndepSet T := by
    intro a ha b hb hne hab
    have hat : G.Adj t a := (Finset.mem_filter.mp ha).2
    have hbt : G.Adj t b := (Finset.mem_filter.mp hb).2
    have hInd : G.IsIndepSet (G.neighborSet t) := neighborSet_indep_of_triangleFree h_tri t
    have haS : a ∈ G.neighborSet t := by
      rw [SimpleGraph.mem_neighborSet]; exact hat
    have hbS : b ∈ G.neighborSet t := by
      rw [SimpleGraph.mem_neighborSet]; exact hbt
    exact hInd haS hbS hne hab

  -- Each `p ∈ P` has at least one neighbor in `T` (else `{v, p} ∪ T` is a 6-IS).
  have hp_has_T_neighbor : ∀ p ∈ P, (T.filter (G.Adj p)).Nonempty := by
    intro p hp
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have ⟨hp_nonadj_v', _hp_common1'⟩ := hP_props p hp
    have hp_no_T : ∀ ti ∈ T, ¬G.Adj p ti := by
      intro ti hti hpti
      have hmem : ti ∈ T.filter (G.Adj p) := Finset.mem_filter.mpr ⟨hti, hpti⟩
      simp [hEmpty] at hmem
    have hv_notin_T : v ∉ T := by
      intro hvT
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hp_notin_T : p ∉ T := by
      intro hpT
      have hpQ : p ∈ Q := (Finset.mem_filter.mp hpT).1
      have ⟨_, hp_common2⟩ := hQ_props p hpQ
      have ⟨_, hp_common1''⟩ := hP_props p hp
      omega
    have hv_ne_p : v ≠ p := by
      intro h
      subst h
      have hv_common1'' := (hP_props v hp).2
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have h6IS : G.IsNIndepSet 6 ({v, p} ∪ T) := by
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hne
        have hx' : x ∈ ({v, p} ∪ T : Finset (Fin 18)) := by simpa using hx
        have hy' : y ∈ ({v, p} ∪ T : Finset (Fin 18)) := by simpa using hy
        rcases Finset.mem_union.mp hx' with hx_vp | hxT
        · -- x ∈ {v,p}
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx_vp
          rcases hx_vp with rfl | rfl
          · -- x = v
            rcases Finset.mem_union.mp hy' with hy | hy
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl
              · exact (hne rfl).elim
              · exact hp_nonadj_v'
            · have hyQ : y ∈ Q := (Finset.mem_filter.mp hy).1
              have ⟨hy_nonadj_v, _⟩ := hQ_props y hyQ
              exact hy_nonadj_v
          · -- x = p
            rcases Finset.mem_union.mp hy' with hy | hy
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl
              · exact fun h => hp_nonadj_v' (G.symm h)
              · exact (hne rfl).elim
            · exact hp_no_T y hy
        · -- x ∈ T
          rcases Finset.mem_union.mp hy' with hy | hy
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · have hxQ : x ∈ Q := (Finset.mem_filter.mp hxT).1
              have ⟨hx_nonadj_v, _⟩ := hQ_props x hxQ
              exact fun h => hx_nonadj_v (G.symm h)
            · exact fun h => hp_no_T x hxT (G.symm h)
          · exact hT_indep hxT hy hne
      · have hvp_disj : Disjoint ({v, p} : Finset (Fin 18)) T := by
          rw [Finset.disjoint_iff_ne]
          intro a ha b hb hab
          subst hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hv_notin_T hb
          · exact hp_notin_T hb
        -- card({v,p} ∪ T) = 2 + 4
        rw [Finset.card_union_of_disjoint hvp_disj, Finset.card_insert_of_notMem, Finset.card_singleton, hT_card]
        simp only [Finset.mem_singleton]; exact hv_ne_p
    exact h_no6 _ h6IS

  -- Any `ti ∈ T` is adjacent to at most one `p ∈ P` (by the 4-cycle structure on `P`).
  have hT_to_P_le1 : ∀ ti ∈ T, (P.filter (G.Adj ti)).card ≤ 1 := by
    intro ti hti
    have hti_notin_P : ti ∉ P := by
      intro htiP
      have htiQ : ti ∈ Q := (Finset.mem_filter.mp hti).1
      have ⟨_, hti_common2⟩ := hQ_props ti htiQ
      have ⟨_, hti_common1⟩ := hP_props ti htiP
      omega
    exact cycleP_adjacent_to_at_most_one h_reg h_tri h_no6 P p1 p2 p3 p4
      hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
      hP_eq h_adj12 h_adj23 h_adj34 h_adj41 h_nonadj13 h_nonadj24
      ti hti_notin_P

  -- Double count edges between `P` and `T` to show every `p ∈ P` has exactly one `T`-neighbor.
  have h_edge_count :
      P.sum (fun p => (T.filter (G.Adj p)).card) =
      T.sum (fun ti => (P.filter (G.Adj ti)).card) := by
    classical
    simpa using
      (bipartite_edge_count_symmetry (A := P) (B := T) (R := G.Adj) (hR := G.symm))

  have h_sum_le4 : T.sum (fun ti => (P.filter (G.Adj ti)).card) ≤ 4 := by
    -- each term ≤ 1 and |T| = 4
    have hterm : ∀ ti ∈ T, (P.filter (G.Adj ti)).card ≤ 1 := by
      intro ti hti; exact hT_to_P_le1 ti hti
    calc
      T.sum (fun ti => (P.filter (G.Adj ti)).card)
          ≤ T.sum (fun _ => 1) := by
              refine Finset.sum_le_sum ?_
              intro ti hti
              exact hterm ti hti
      _ = T.card := by simp [Finset.sum_const]
      _ = 4 := by simp [hT_card]

  have h_sum_ge4 : 4 ≤ P.sum (fun p => (T.filter (G.Adj p)).card) := by
    -- each p contributes at least 1, and |P| = 4
    have hterm : ∀ p ∈ P, 1 ≤ (T.filter (G.Adj p)).card := by
      intro p hp
      exact Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p hp))
    have : P.sum (fun _ => 1) ≤ P.sum (fun p => (T.filter (G.Adj p)).card) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact hterm p hp
    have hP_sum : P.sum (fun _ => 1) = 4 := by
      simp [Finset.sum_const, hP_card]
    have h_ge : 4 ≤ P.sum (fun p => (T.filter (G.Adj p)).card) := by
      -- rewrite `P.sum (fun _ => 1)` to `4`
      simpa [hP_sum] using this
    exact h_ge

  have h_sum_eq4 : P.sum (fun p => (T.filter (G.Adj p)).card) = 4 := by
    have : P.sum (fun p => (T.filter (G.Adj p)).card) ≤ 4 := by
      -- via double counting and the ≤4 bound on the T-side
      have : P.sum (fun p => (T.filter (G.Adj p)).card) ≤
          T.sum (fun ti => (P.filter (G.Adj ti)).card) := by
        simp [h_edge_count]
      exact le_trans this h_sum_le4
    exact le_antisymm this h_sum_ge4

  -- Specialize to `p1`: since `P = {p1,p2,p3,p4}` and total sum is 4 with each ≥ 1,
  -- each term is exactly 1.
  have h_p1_T_card : (T.filter (G.Adj p1)).card = 1 := by
    -- expand the sum over the four elements of P
    have hp1P : p1 ∈ P := by rw [hP_eq]; simp
    have hp2P : p2 ∈ P := by rw [hP_eq]; simp
    have hp3P : p3 ∈ P := by rw [hP_eq]; simp
    have hp4P : p4 ∈ P := by rw [hP_eq]; simp
    have h_p2_ge1 : 1 ≤ (T.filter (G.Adj p2)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p2 hp2P))
    have h_p3_ge1 : 1 ≤ (T.filter (G.Adj p3)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p3 hp3P))
    have h_p4_ge1 : 1 ≤ (T.filter (G.Adj p4)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p4 hp4P))
    have h_sum_exp :
        P.sum (fun p => (T.filter (G.Adj p)).card) =
          (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
          (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      classical
      -- reuse `sum_over_four`
      -- `P = {p1,p2,p3,p4}` already, so just use it directly
      simpa [hP_eq] using
        (sum_over_four p1 p2 p3 p4 hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
          (fun p => (T.filter (G.Adj p)).card))
    -- If p1 had ≥ 2 T-neighbors, sum would be ≥ 5, contradict sum = 4.
    by_contra hge2
    have h_p1_ge1 : 1 ≤ (T.filter (G.Adj p1)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p1 hp1P))
    have h_p1_gt1 : 1 < (T.filter (G.Adj p1)).card := by
      exact lt_of_le_of_ne h_p1_ge1 (Ne.symm hge2)
    have h_p1_ge2 : 2 ≤ (T.filter (G.Adj p1)).card := Nat.succ_le_iff.mp h_p1_gt1
    have hsum_ge5 :
        5 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      -- 2 + 1 + 1 + 1 ≤ a + b + c + d
      have hab : 3 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card := by
        -- 2 ≤ a and 1 ≤ b
        have : 2 + 1 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card :=
          Nat.add_le_add h_p1_ge2 h_p2_ge1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hcd : 2 ≤ (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
        have : 1 + 1 ≤ (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card :=
          Nat.add_le_add h_p3_ge1 h_p4_ge1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have : 5 ≤ ((T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card) +
          ((T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card) := by
        have : 3 + 2 ≤ ((T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card) +
            ((T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card) :=
          Nat.add_le_add hab hcd
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hsum_ge : 5 ≤ P.sum (fun p => (T.filter (G.Adj p)).card) := by
      simpa [h_sum_exp] using hsum_ge5
    -- contradiction with sum = 4
    have : (5 : ℕ) ≤ 4 := by
      have h' := hsum_ge
      simp [h_sum_eq4] at h'
    exact (by decide : ¬((5 : ℕ) ≤ 4)) this

  -- So p1 has exactly 1 W-neighbor as well (since it has 2 neighbors in Q total).
  have h_p1_W_card : (W.filter (G.Adj p1)).card = 1 := by
    -- `Q = T ∪ W` disjoint, so `Q_neighbors_p1 = (T.filter (Adj p1)) ∪ (W.filter (Adj p1))` disjoint.
    have hQn_eq :
        Q_neighbors_p1 = (T.filter (G.Adj p1)) ∪ (W.filter (G.Adj p1)) := by
      ext x
      constructor
      · intro hx
        have hxQ : x ∈ Q := (Finset.mem_filter.mp hx).1
        have hxp : G.Adj p1 x := (Finset.mem_filter.mp hx).2
        by_cases htx : G.Adj t x
        · apply Finset.mem_union.mpr
          left
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxQ, htx⟩, hxp⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxQ, htx⟩, hxp⟩
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
          have hxQ : x ∈ Q := (Finset.mem_filter.mp hxT).1
          have hxp : G.Adj p1 x := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨hxQ, hxp⟩
        · have hxW : x ∈ W := (Finset.mem_filter.mp hx).1
          have hxQ : x ∈ Q := (Finset.mem_filter.mp hxW).1
          have hxp : G.Adj p1 x := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨hxQ, hxp⟩
    have hdisj : Disjoint (T.filter (G.Adj p1)) (W.filter (G.Adj p1)) := by
      -- disjoint since `T` and `W` are disjoint
      refine Finset.disjoint_left.mpr ?_
      intro a ha hb
      have haT : a ∈ T := (Finset.mem_filter.mp ha).1
      have hbW : a ∈ W := (Finset.mem_filter.mp hb).1
      exact (Finset.disjoint_left.mp hTW_disj) haT hbW
    have hcard :
        Q_neighbors_p1.card = (T.filter (G.Adj p1)).card + (W.filter (G.Adj p1)).card := by
      rw [hQn_eq, Finset.card_union_of_disjoint hdisj]
    have hsum : (T.filter (G.Adj p1)).card + (W.filter (G.Adj p1)).card = 2 := by
      have : (T.filter (G.Adj p1)).card + (W.filter (G.Adj p1)).card = Q_neighbors_p1.card := by
        simpa using hcard.symm
      simpa [hQ_nbrs_p1_card] using this
    have hT_in_Q : (T.filter (G.Adj p1)).card = 1 := by
      simpa [Finset.filter_filter] using h_p1_T_card
    -- solve for the W part
    have : (W.filter (G.Adj p1)).card = 1 := by omega
    exact this

  -- Extract the unique `t1 ∈ T` adjacent to `p1` and the unique `w1 ∈ W` adjacent to `p1`.
  obtain ⟨t1, ht1_eq⟩ := Finset.card_eq_one.mp h_p1_T_card
  have ht1_mem : t1 ∈ T.filter (G.Adj p1) := by simp [ht1_eq]
  have ht1_in_T : t1 ∈ T := by
    have := (Finset.mem_filter.mp ht1_mem).1
    exact this
  have hp1_adj_t1 : G.Adj p1 t1 := by
    exact (Finset.mem_filter.mp ht1_mem).2

  obtain ⟨w1, hw1_eq⟩ := Finset.card_eq_one.mp h_p1_W_card
  have hw1_mem : w1 ∈ W.filter (G.Adj p1) := by simp [hw1_eq]
  have hw1_in_W : w1 ∈ W := by
    have := (Finset.mem_filter.mp hw1_mem).1
    exact this
  have hp1_adj_w1 : G.Adj p1 w1 := by
    exact (Finset.mem_filter.mp hw1_mem).2

  -- `w1` is adjacent to no other `p ∈ P` (it is adjacent to `p1`, so by the 4-cycle constraint it
  -- cannot also be adjacent to `p3`).
  have hw1_in_Q : w1 ∈ Q := (Finset.mem_filter.mp hw1_in_W).1
  have hw1_notin_P : w1 ∉ P := by
    intro hw1P
    exact (Finset.disjoint_left.mp hP_Q_disj) hw1P hw1_in_Q
  have hw1_P_card_le1 : (P.filter (G.Adj w1)).card ≤ 1 :=
    cycleP_adjacent_to_at_most_one h_reg h_tri h_no6 P p1 p2 p3 p4
      hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
      hP_eq h_adj12 h_adj23 h_adj34 h_adj41 h_nonadj13 h_nonadj24
      w1 hw1_notin_P
  have hw1_nonadj_p3 : ¬G.Adj w1 p3 := by
    intro h
    classical
    have hp1_mem : p1 ∈ P.filter (G.Adj w1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_w1⟩
    have hp3_mem : p3 ∈ P.filter (G.Adj w1) := by
      have hp3_in_P : p3 ∈ P := by rw [hP_eq]; simp
      exact Finset.mem_filter.mpr ⟨hp3_in_P, h⟩
    have hsub : ({p1, p3} : Finset (Fin 18)) ⊆ P.filter (G.Adj w1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp1_mem
      · exact hp3_mem
    have hcard : 2 ≤ (P.filter (G.Adj w1)).card := by
      have hle := Finset.card_le_card hsub
      have htwo : ({p1, p3} : Finset (Fin 18)).card = 2 := by simp [hp_ne13]
      omega
    omega

  -- Degree bookkeeping for `w1`: it has exactly 2 neighbors in `Q`.
  have hw1_deg : (G.neighborFinset w1).card = 5 := h_reg w1
  have hw1_P_card : (P.filter (G.Adj w1)).card = 1 := by
    classical
    have hp1_mem : p1 ∈ P.filter (G.Adj w1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_w1⟩
    have : 1 ≤ (P.filter (G.Adj w1)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr ⟨p1, hp1_mem⟩)
    omega
  have hw1_Nv_card : ((G.neighborFinset v).filter (G.Adj w1)).card = 2 := by
    -- `commonNeighborsCard v w1 = 2` and `¬Adj v w1` identifies the two neighbors of `w1` inside `N(v)`.
    have hw1_common2 : commonNeighborsCard G v w1 = 2 := (hQ_props w1 hw1_in_Q).2
    unfold commonNeighborsCard _root_.commonNeighbors at hw1_common2
    -- rewrite the intersection as a filter (using symmetry of adjacency)
    have :
        (G.neighborFinset v ∩ G.neighborFinset w1) =
          (G.neighborFinset v).filter (G.Adj w1) := by
      ext x
      simp [Finset.mem_inter, Finset.mem_filter, mem_neighborFinset]
    simpa [this] using hw1_common2
  have hw1_Q_card : (Q.filter (G.Adj w1)).card = 2 := by
    -- Neighbors of `w1` are partitioned among `P`, `N(v)`, and `Q` (since `w1` is not adjacent to `v`).
    have hvw1 : ¬G.Adj v w1 := (hQ_props w1 hw1_in_Q).1
    have hw1_notin_Nv : w1 ∉ G.neighborFinset v := by
      intro h
      exact hvw1 (by simpa [mem_neighborFinset] using h)
    have hw1_notin_P : w1 ∉ P := hw1_notin_P
    let NPw : Finset (Fin 18) := P.filter (G.Adj w1)
    let NNw : Finset (Fin 18) := (G.neighborFinset v).filter (G.Adj w1)
    let NQw : Finset (Fin 18) := Q.filter (G.Adj w1)
    have h_disjPN : Disjoint NPw NNw := by
      apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      exact hP_Nv_disj
    have h_disjPQ : Disjoint NPw NQw := by
      apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      exact hP_Q_disj
    have h_disjNQ : Disjoint NNw NQw := by
      apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      exact hNv_Q_disj
    have h_cover :
        G.neighborFinset w1 ⊆ NPw ∪ NNw ∪ NQw := by
      intro x hx
      rw [mem_neighborFinset] at hx
      by_cases hxv : x = v
      · subst hxv; exact (hvw1 (G.symm hx)).elim
      by_cases hxNv : G.Adj v x
      · -- x ∈ N(v)
        have hx_in : x ∈ G.neighborFinset v := by simpa [mem_neighborFinset] using hxNv
        have : x ∈ NNw := by
          exact Finset.mem_filter.mpr ⟨hx_in, hx⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr this)))
      · -- x is a non-neighbor of v, so it lies in P or Q (Claim 2 completeness)
        have ⟨hP_complete, hQ_complete⟩ :=
          PQ_partition_completeness h_reg h_tri h_no6 v P Q hP_card hQ_card hP_props hQ_props
        have hx_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hxv hxNv
        have hx_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hxv hxNv
        have hx_common : commonNeighborsCard G v x = 1 ∨ commonNeighborsCard G v x = 2 := by omega
        cases hx_common with
        | inl h1 =>
          have hx_in_P : x ∈ P := hP_complete x hxv hxNv h1
          have : x ∈ NPw := Finset.mem_filter.mpr ⟨hx_in_P, hx⟩
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl this)))
        | inr h2 =>
          have hx_in_Q : x ∈ Q := hQ_complete x hxv hxNv h2
          have : x ∈ NQw := Finset.mem_filter.mpr ⟨hx_in_Q, hx⟩
          exact Finset.mem_union.mpr (Or.inr this)
    have h_subset :
        NPw ∪ NNw ∪ NQw ⊆ G.neighborFinset w1 := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_union] at hx
      rw [mem_neighborFinset]
      rcases hx with ⟨hxP | hxN⟩ | hxQ
      · exact (Finset.mem_filter.mp hxP).2
      · exact (Finset.mem_filter.mp hxN).2
      · exact (Finset.mem_filter.mp hxQ).2
    have h_union :
        NPw ∪ NNw ∪ NQw = G.neighborFinset w1 :=
      Finset.Subset.antisymm h_subset h_cover
    -- solve for NQw.card
    -- NPw.card = 1 and NNw.card = 2
    have : NQw.card = 2 := by
      have hPN : (NPw ∪ NNw).card = NPw.card + NNw.card :=
        Finset.card_union_of_disjoint h_disjPN
      have hPNQ : (NPw ∪ NNw ∪ NQw).card = (NPw ∪ NNw).card + NQw.card := by
        have h_disj : Disjoint (NPw ∪ NNw) NQw := by
          refine Finset.disjoint_union_left.mpr ?_
          exact ⟨h_disjPQ, h_disjNQ⟩
        simpa [Finset.union_assoc] using Finset.card_union_of_disjoint h_disj
      have htot : (NPw ∪ NNw ∪ NQw).card = 5 := by
        have := congrArg Finset.card h_union
        simpa [hw1_deg] using this
      -- massage h_card_sum
      -- use definitions
      -- NQw = Q.filter (Adj w1)
      have hNP : NPw.card = 1 := by simp [NPw, hw1_P_card]
      have hNN : NNw.card = 2 := by simp [NNw, hw1_Nv_card]
      -- Convert card equalities to a numeric equation and solve.
      -- First rewrite total card in terms of components.
      have htot' : (NPw.card + NNw.card) + NQw.card = 5 := by
        -- from htot = (NPw ∪ NNw ∪ NQw).card and disjoint-union expansions
        have hAB : (NPw ∪ NNw).card = NPw.card + NNw.card := hPN
        -- rewrite hPNQ using associativity
        have hABC : (NPw ∪ NNw ∪ NQw).card = (NPw ∪ NNw).card + NQw.card := hPNQ
        -- combine
        -- htot : card(union) = 5
        -- so (NPw.card + NNw.card) + NQw.card = 5
        omega
      -- now solve for NQw.card
      omega
    simpa [NQw] using this

  -- Step 11 (partial): start Cariolaro’s final constraint tracking.
  -- `w1` cannot be adjacent to `s1` since `s1 ~ p1` and `w1 ~ p1`.
  have hw1_nonadj_s1 : ¬G.Adj w1 s1 := by
    intro h
    have h_clique : G.IsNClique 3 {p1, s1, w1} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals
          first
          | exact absurd rfl hxy
          | exact G.symm hs1_adj_p1
          | exact G.symm hp1_adj_w1
          | exact hs1_adj_p1
          | exact G.symm h
          | exact hp1_adj_w1
          | exact h
      · classical
        have hp1_ne_s1 : p1 ≠ s1 := G.ne_of_adj (G.symm hs1_adj_p1)
        have hp1_ne_w1 : p1 ≠ w1 := G.ne_of_adj hp1_adj_w1
        have hs1_ne_w1 : s1 ≠ w1 := by
          intro h_eq
          have hw1_adj_v : G.Adj v w1 := by
            have : G.Adj v s1 := by
              simpa [mem_neighborFinset] using hs1_in_N
            simpa [h_eq] using this
          have hw1_in_Q : w1 ∈ Q := (Finset.mem_filter.mp hw1_in_W).1
          exact (hQ_props w1 hw1_in_Q).1 hw1_adj_v
        simp [hp1_ne_s1, hp1_ne_w1, hs1_ne_w1]
    exact h_tri _ h_clique

  -- Work with `S0 := N(v) \\ {t}` to reuse the existing S/T/W helper lemmas.
  let S0 : Finset (Fin 18) := (G.neighborFinset v).erase t
  have hS0_card : S0.card = 4 := by
    rw [Finset.card_erase_of_mem ht_in_N, hN_card]

  have hw1_in_Q : w1 ∈ Q := (Finset.mem_filter.mp hw1_in_W).1
  have hw1_common2 : commonNeighborsCard G v w1 = 2 := (hQ_props w1 hw1_in_Q).2
  have hw1_nonadj_t : ¬G.Adj t w1 := (Finset.mem_filter.mp hw1_in_W).2
  have hS0w1_card : (S0.filter (G.Adj w1)).card = 2 :=
    W_vertex_has_two_S_neighbors h_tri v t w1 ht_adj_v hw1_nonadj_t hw1_common2 S0 hS0_card rfl

  have ht1_in_Q : t1 ∈ Q := (Finset.mem_filter.mp ht1_in_T).1
  have ht1_common2 : commonNeighborsCard G v t1 = 2 := (hQ_props t1 ht1_in_Q).2
  have ht1_adj_t : G.Adj t t1 := (Finset.mem_filter.mp ht1_in_T).2
  have hS0t1_card : (S0.filter (G.Adj t1)).card = 1 :=
    T_vertex_has_one_S_neighbor h_reg h_tri v t t1 ht_adj_v ht1_adj_t ht1_common2 S0 hS0_card rfl

  -- `t` has no neighbors in `P`.
  have ht_no_P_neighbors : ∀ p ∈ P, ¬G.Adj t p := by
    intro p hp htp
    -- reduce `p ∈ P` to the four cases and use the corresponding partner uniqueness lemma
    rw [hP_eq] at hp
    rcases (by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hp) with hp | hp | hp | hp
    · subst hp
      exact ht_ne_s1 (hs1_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      exact ht_ne_s2 (hs2_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      have ht_ne_s3 : t ≠ s3 := by
        intro h
        subst h
        exact ht_notin_S (by simp [S])
      exact ht_ne_s3 (hs3_unique t ⟨ht_in_N, htp⟩)
    · subst hp
      have ht_ne_s4 : t ≠ s4 := by
        intro h
        subst h
        exact ht_notin_S (by simp [S])
      exact ht_ne_s4 (hs4_unique t ⟨ht_in_N, htp⟩)

  -- Any neighbor of `t` other than `v` is in `T`.
  have ht_neighbor_in_T : ∀ x, G.Adj t x → x ≠ v → x ∈ T := by
    intro x htx hx_ne_v
    have hx_nonadj_v : ¬G.Adj v x := by
      intro hvx
      have hNv_indep := neighborSet_indep_of_triangleFree h_tri v
      have hx_ne_t : x ≠ t := fun h_eq => by
        subst h_eq
        exact G.loopless x htx
      exact hNv_indep hvx ht_adj_v hx_ne_t (G.symm htx)
    have h_pos := commonNeighborsCard_pos h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg v x hx_ne_v hx_nonadj_v
    have h_common : commonNeighborsCard G v x = 1 ∨ commonNeighborsCard G v x = 2 := by omega
    have ⟨hP_complete, hQ_complete⟩ :=
      PQ_partition_completeness h_reg h_tri h_no6 v P Q hP_card hQ_card hP_props hQ_props
    cases h_common with
    | inl h1 =>
      have hx_in_P : x ∈ P := hP_complete x hx_ne_v hx_nonadj_v h1
      exact (ht_no_P_neighbors x hx_in_P htx).elim
    | inr h2 =>
      have hx_in_Q : x ∈ Q := hQ_complete x hx_ne_v hx_nonadj_v h2
      exact Finset.mem_filter.mpr ⟨hx_in_Q, htx⟩

  -- `t` and `w1` have a common neighbor in `T`.
  have ht_ne_w1 : t ≠ w1 := by
    intro h_eq
    have : t ∈ Q := by simpa [h_eq] using hw1_in_Q
    exact (Finset.disjoint_left.mp hNv_Q_disj) ht_in_N this
  have ht_nonadj_w1 : ¬G.Adj t w1 := hw1_nonadj_t
  have ht_w1_common_pos : 0 < commonNeighborsCard G t w1 :=
    commonNeighborsCard_pos h_tri h_no6 h_reg t w1 (Ne.symm ht_ne_w1) ht_nonadj_w1
  have h_common_nonempty : (_root_.commonNeighbors G t w1).Nonempty := by
    unfold commonNeighborsCard at ht_w1_common_pos
    exact Finset.card_pos.mp ht_w1_common_pos
  obtain ⟨u, hu_common⟩ := h_common_nonempty
  have hu_in_inter : u ∈ G.neighborFinset t ∩ G.neighborFinset w1 := by
    simpa [_root_.commonNeighbors] using hu_common
  have hu_adj_t : G.Adj t u := by
    have : u ∈ G.neighborFinset t := (Finset.mem_inter.mp hu_in_inter).1
    simpa [mem_neighborFinset] using this
  have hu_ne_v : u ≠ v := by
    intro h
    subst h
    have : G.Adj w1 v := by
      have : v ∈ G.neighborFinset w1 := (Finset.mem_inter.mp hu_in_inter).2
      simpa [mem_neighborFinset] using this
    exact (hQ_props w1 hw1_in_Q).1 (G.symm this)
  have hu_in_T : u ∈ T := ht_neighbor_in_T u hu_adj_t hu_ne_v
  have hw1_adj_u : G.Adj w1 u := by
    have : u ∈ G.neighborFinset w1 := (Finset.mem_inter.mp hu_in_inter).2
    simpa [mem_neighborFinset] using this

  -- B1: `t` and `w1` share exactly two common neighbors.
  have ht_w1_common2 : commonNeighborsCard G t w1 = 2 := by
    classical
    have h_le :=
      commonNeighborsCard_le_two h_tri h_no6 h_reg t w1 (Ne.symm ht_ne_w1) ht_nonadj_w1
    have h_pos :=
      commonNeighborsCard_pos h_tri h_no6 h_reg t w1 (Ne.symm ht_ne_w1) ht_nonadj_w1
    have h_cases : commonNeighborsCard G t w1 = 1 ∨ commonNeighborsCard G t w1 = 2 := by
      omega
    refine h_cases.resolve_left ?_
    intro h1

    -- Extract the unique common neighbor `u1` of `t` and `w1`.
    have hcard1 : (G.neighborFinset t ∩ G.neighborFinset w1).card = 1 := by
      simpa [commonNeighborsCard, _root_.commonNeighbors] using h1
    obtain ⟨u1, hu1_eq⟩ := Finset.card_eq_one.mp hcard1
    have hu1_mem : u1 ∈ G.neighborFinset t ∩ G.neighborFinset w1 := by
      simp [hu1_eq]
    have hu1_adj_t : G.Adj t u1 := by
      have : u1 ∈ G.neighborFinset t := (Finset.mem_inter.mp hu1_mem).1
      simpa [mem_neighborFinset] using this
    have hu1_adj_w1 : G.Adj w1 u1 := by
      have : u1 ∈ G.neighborFinset w1 := (Finset.mem_inter.mp hu1_mem).2
      simpa [mem_neighborFinset] using this
    have hu1_ne_v : u1 ≠ v := by
      intro h
      subst h
      have : ¬G.Adj v w1 := (hQ_props w1 hw1_in_Q).1
      exact (this (G.symm hu1_adj_w1)).elim
    have hu1_in_T : u1 ∈ T := ht_neighbor_in_T u1 hu1_adj_t hu1_ne_v

    -- Every `p ∈ P` has exactly one `T`-neighbor (pointwise).
    have hP_T_card : ∀ p ∈ P, (T.filter (G.Adj p)).card = 1 := by
      intro p hp
      have hge1 : 1 ≤ (T.filter (G.Adj p)).card :=
        Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p hp))
      by_contra hne1
      have hge2 : 2 ≤ (T.filter (G.Adj p)).card := by
        have : 1 < (T.filter (G.Adj p)).card := lt_of_le_of_ne hge1 (Ne.symm hne1)
        exact Nat.succ_le_iff.mp this
      have hsum_erase_ge :
          (P.erase p).card ≤ (P.erase p).sum (fun q => (T.filter (G.Adj q)).card) := by
        -- compare to the constant-1 sum
        have hconst_le :
            (P.erase p).sum (fun _ => 1) ≤ (P.erase p).sum (fun q => (T.filter (G.Adj q)).card) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hqP : q ∈ P := (Finset.mem_erase.mp hq).2
          have : 1 ≤ (T.filter (G.Adj q)).card :=
            Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor q hqP))
          simpa using this
        simpa [Finset.sum_const] using hconst_le
      have hErase_card : (P.erase p).card = 3 := by
        have := Finset.card_erase_of_mem hp
        omega
      have hsum_erase_ge3 : 3 ≤ (P.erase p).sum (fun q => (T.filter (G.Adj q)).card) := by
        simpa [hErase_card] using hsum_erase_ge
      have hsum_split :
          P.sum (fun q => (T.filter (G.Adj q)).card) =
            (T.filter (G.Adj p)).card + (P.erase p).sum (fun q => (T.filter (G.Adj q)).card) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Finset.sum_erase_add (s := P) (f := fun q => (T.filter (G.Adj q)).card) hp).symm
      have hsum_ge5 : 5 ≤ P.sum (fun q => (T.filter (G.Adj q)).card) := by
        have : 5 ≤ (T.filter (G.Adj p)).card + (P.erase p).sum (fun q => (T.filter (G.Adj q)).card) :=
          Nat.add_le_add hge2 hsum_erase_ge3
        simpa [hsum_split] using this
      have : (5 : ℕ) ≤ 4 := by
        rw [← h_sum_eq4]
        exact hsum_ge5
      exact (by decide : ¬((5 : ℕ) ≤ 4)) this

    -- Every `ti ∈ T` has exactly one `P`-neighbor (pointwise).
    have hT_P_card : ∀ ti ∈ T, (P.filter (G.Adj ti)).card = 1 := by
      intro ti hti
      have hsumT : T.sum (fun x => (P.filter (G.Adj x)).card) = 4 := by
        calc
          T.sum (fun x => (P.filter (G.Adj x)).card)
              = P.sum (fun p => (T.filter (G.Adj p)).card) := by
                  simpa using h_edge_count.symm
          _ = 4 := h_sum_eq4
      by_contra hne1
      have hti0 : (P.filter (G.Adj ti)).card = 0 := by
        have hle1 := hT_to_P_le1 ti hti
        omega
      have hsum_le3 : T.sum (fun x => (P.filter (G.Adj x)).card) ≤ 3 := by
        have hsplit :
            T.sum (fun x => (P.filter (G.Adj x)).card) =
              (P.filter (G.Adj ti)).card + (T.erase ti).sum (fun x => (P.filter (G.Adj x)).card) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.sum_erase_add (s := T) (f := fun x => (P.filter (G.Adj x)).card) hti).symm
        have hErase_card : (T.erase ti).card = 3 := by
          have := Finset.card_erase_of_mem hti
          omega
        have hsum_erase_le3 :
            (T.erase ti).sum (fun x => (P.filter (G.Adj x)).card) ≤ 3 := by
          calc
            (T.erase ti).sum (fun x => (P.filter (G.Adj x)).card)
                ≤ (T.erase ti).sum (fun _ => 1) := by
                    refine Finset.sum_le_sum ?_
                    intro x hx
                    have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
                    exact hT_to_P_le1 x hxT
            _ = (T.erase ti).card := by simp [Finset.sum_const]
            _ = 3 := by simp [hErase_card]
        have : T.sum (fun x => (P.filter (G.Adj x)).card)
            ≤ (P.filter (G.Adj ti)).card + 3 := by
          simpa [hsplit] using Nat.add_le_add_left hsum_erase_le3 (P.filter (G.Adj ti)).card
        simpa [hti0] using this
      have : (4 : ℕ) ≤ 3 := by
        have h4le : (4 : ℕ) ≤ T.sum (fun x => (P.filter (G.Adj x)).card) := by
          exact le_of_eq hsumT.symm
        exact le_trans h4le hsum_le3
      exact (by decide : ¬((4 : ℕ) ≤ 3)) this

    -- Let `pu` be the unique P-neighbor of `u1`.
    have hu1P1 : (P.filter (G.Adj u1)).card = 1 := hT_P_card u1 hu1_in_T
    obtain ⟨pu, hpu_eq⟩ := Finset.card_eq_one.mp hu1P1
    have hpu_mem : pu ∈ P.filter (G.Adj u1) := by simp [hpu_eq]
    have hpu_in_P : pu ∈ P := (Finset.mem_filter.mp hpu_mem).1
    have hu1_adj_pu : G.Adj u1 pu := (Finset.mem_filter.mp hpu_mem).2

    -- `pu ≠ p1` (else triangle `p1-w1-u1`).
    have hpu_ne_p1 : pu ≠ p1 := by
      intro hpu_eq_p1
      have hpu_adj_w1 : G.Adj pu w1 := by
        simpa [hpu_eq_p1] using hp1_adj_w1
      have h_clique : G.IsNClique 3 {pu, w1, u1} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact (hxy rfl).elim
            | exact hpu_adj_w1
            | exact hu1_adj_w1
            | exact G.symm hpu_adj_w1
            | exact hu1_adj_pu
            | exact G.symm hu1_adj_w1
            | exact G.symm hu1_adj_pu
        · have hpu_ne_w1 : pu ≠ w1 := G.ne_of_adj hpu_adj_w1
          have hpu_ne_u1 : pu ≠ u1 := G.ne_of_adj (G.symm hu1_adj_pu)
          have hw1_ne_u1 : w1 ≠ u1 := G.ne_of_adj hu1_adj_w1
          simp [hpu_ne_w1, hpu_ne_u1, hw1_ne_u1]
      exact h_tri _ h_clique

    -- `w1` is adjacent to exactly one P-vertex, namely `p1`, hence not to `pu`.
    have hp1_mem_pw : p1 ∈ P.filter (G.Adj w1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_w1⟩
    have hPw_eq : P.filter (G.Adj w1) = {p1} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hw1_P_card
      have ha' : p1 = a := by
        have : p1 ∈ ({a} : Finset (Fin 18)) := by simpa [ha] using hp1_mem_pw
        simpa [Finset.mem_singleton] using this
      subst ha'
      simp [ha]
    have hw1_nonadj_pu : ¬G.Adj w1 pu := by
      intro hwp
      have : pu ∈ ({p1} : Finset (Fin 18)) := by
        have : pu ∈ P.filter (G.Adj w1) := Finset.mem_filter.mpr ⟨hpu_in_P, hwp⟩
        simpa [hPw_eq] using this
      have : pu = p1 := by simpa [Finset.mem_singleton] using this
      exact hpu_ne_p1 this

    -- `pu` is adjacent to no vertex of `T.erase u1` (since `u1` is its unique T-neighbor).
    have hpuT1 : (T.filter (G.Adj pu)).card = 1 := hP_T_card pu hpu_in_P
    have hu1_mem_puT : u1 ∈ T.filter (G.Adj pu) := by
      exact Finset.mem_filter.mpr ⟨hu1_in_T, G.symm hu1_adj_pu⟩
    have hpu_nonadj_Terase : ∀ x ∈ T.erase u1, ¬G.Adj pu x := by
      intro x hx hpx
      have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
      have hx_mem : x ∈ T.filter (G.Adj pu) := Finset.mem_filter.mpr ⟨hxT, hpx⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hpuT1
      have hu1_eq_a : u1 = a := by
        have : u1 ∈ ({a} : Finset (Fin 18)) := by
          simpa [ha] using hu1_mem_puT
        simpa [Finset.mem_singleton] using this
      have hx_eq_a : x = a := by
        have : x ∈ ({a} : Finset (Fin 18)) := by
          simpa [ha] using hx_mem
        simpa [Finset.mem_singleton] using this
      have hx_eq_u1 : x = u1 := by simpa [hu1_eq_a] using hx_eq_a
      exact (Finset.mem_erase.mp hx).1 (hx_eq_u1 ▸ rfl)

    -- `w1` is adjacent to no vertex of `T.erase u1` (otherwise it would be another common neighbor of `t` and `w1`).
    have hw1_nonadj_Terase : ∀ x ∈ T.erase u1, ¬G.Adj w1 x := by
      intro x hx hwx
      have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
      have hx_adj_t : G.Adj t x := (Finset.mem_filter.mp hxT).2
      have hx_in_inter : x ∈ G.neighborFinset t ∩ G.neighborFinset w1 := by
        have hx_in_nt : x ∈ G.neighborFinset t := by
          simpa [mem_neighborFinset] using hx_adj_t
        have hx_in_nw : x ∈ G.neighborFinset w1 := by
          simpa [mem_neighborFinset] using hwx
        exact Finset.mem_inter.mpr ⟨hx_in_nt, hx_in_nw⟩
      have : x ∈ ({u1} : Finset (Fin 18)) := by simpa [hu1_eq] using hx_in_inter
      have : x = u1 := by simpa [Finset.mem_singleton] using this
      exact (Finset.mem_erase.mp hx).1 (this ▸ rfl)

    -- Build a 6-independent set: `{v, w1, pu} ∪ (T.erase u1)`.
    have hv_notin_T : v ∉ T := by
      intro hvT
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hw1_notin_T : w1 ∉ T := by
      intro hw1T
      exact hw1_nonadj_t ((Finset.mem_filter.mp hw1T).2)
    have hpu_notin_T : pu ∉ T := by
      intro hpuT
      have hpuQ : pu ∈ Q := (Finset.mem_filter.mp hpuT).1
      have ⟨_, hpu_common2⟩ := hQ_props pu hpuQ
      have ⟨_, hpu_common1⟩ := hP_props pu hpu_in_P
      omega

    let I : Finset (Fin 18) := ({v, w1, pu} ∪ (T.erase u1))
    have h6IS : G.IsNIndepSet 6 I := by
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hne
        dsimp [I] at hx hy
        rcases Finset.mem_union.mp hx with hxV | hxT
        · rcases Finset.mem_union.mp hy with hyV | hyT
          · -- both in {v,w1,pu}
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxV hyV
            rcases hxV with rfl | rfl | rfl <;> rcases hyV with rfl | rfl | rfl
            · exact (hne rfl).elim
            · -- x = v, y = w1
              exact (hQ_props y (by simpa using hw1_in_Q)).1
            · -- x = v, y = pu
              exact (hP_props y (by simpa using hpu_in_P)).1
            · -- x = w1, y = v
              intro h
              exact (hQ_props x (by simpa using hw1_in_Q)).1 (G.symm h)
            · exact (hne rfl).elim
            · -- x = w1, y = pu
              simpa using hw1_nonadj_pu
            · -- x = pu, y = v
              intro h
              exact (hP_props x (by simpa using hpu_in_P)).1 (G.symm h)
            · -- x = pu, y = w1
              intro h
              exact hw1_nonadj_pu (G.symm h)
            · exact (hne rfl).elim
          · -- x ∈ {v,w1,pu}, y ∈ T.erase u1
            have hyT' : y ∈ T := (Finset.mem_erase.mp hyT).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxV
            rcases hxV with rfl | rfl | rfl
            · -- x = v
              have hyQ : y ∈ Q := (Finset.mem_filter.mp hyT').1
              have ⟨hy_nonadj_v, _⟩ := hQ_props y hyQ
              exact hy_nonadj_v
            · -- x = w1
              exact hw1_nonadj_Terase y hyT
            · -- x = pu
              exact fun h => hpu_nonadj_Terase y hyT h
        · rcases Finset.mem_union.mp hy with hyV | hyT
          · -- x ∈ T.erase u1, y ∈ {v,w1,pu}
            have hxT' : x ∈ T := (Finset.mem_erase.mp hxT).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyV
            rcases hyV with rfl | rfl | rfl
            · -- y = v
              have hxQ : x ∈ Q := (Finset.mem_filter.mp hxT').1
              have ⟨hx_nonadj_v, _⟩ := hQ_props x hxQ
              exact fun h => hx_nonadj_v (G.symm h)
            · -- y = w1
              exact fun h => hw1_nonadj_Terase x hxT (G.symm h)
            · -- y = pu
              exact fun h => hpu_nonadj_Terase x hxT (G.symm h)
          · -- x,y ∈ T.erase u1
            exact hT_indep (Finset.mem_erase.mp hxT).2 (Finset.mem_erase.mp hyT).2 hne
      · -- card = 6
        have hcard_erase : (T.erase u1).card = 3 := by
          have := Finset.card_erase_of_mem hu1_in_T
          omega
        have hvw1pu_disj : Disjoint ({v, w1, pu} : Finset (Fin 18)) (T.erase u1) := by
          refine Finset.disjoint_left.mpr ?_
          intro x hxV hxT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxV
          rcases hxV with rfl | rfl | rfl
          · exact hv_notin_T (Finset.mem_erase.mp hxT).2
          · exact hw1_notin_T (Finset.mem_erase.mp hxT).2
          · exact hpu_notin_T (Finset.mem_erase.mp hxT).2
        have hv_ne_w1 : v ≠ w1 := by
          intro h
          subst h
          have hcommon2 := (hQ_props v hw1_in_Q).2
          have hcommon5 : commonNeighborsCard G v v = 5 := by
            simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
          omega
        have hv_ne_pu : v ≠ pu := by
          intro h
          subst h
          have hcommon1 := (hP_props v hpu_in_P).2
          have hcommon5 : commonNeighborsCard G v v = 5 := by
            simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
          omega
        have hw1_ne_pu : w1 ≠ pu := by
          intro h
          subst h
          exact hw1_notin_P hpu_in_P
        have hcardV : ({v, w1, pu} : Finset (Fin 18)).card = 3 := by
          have hw1_notmem : w1 ∉ ({pu} : Finset (Fin 18)) := by
            simp [hw1_ne_pu]
          have hv_notmem : v ∉ insert w1 ({pu} : Finset (Fin 18)) := by
            simp [hv_ne_w1, hv_ne_pu]
          simp [Finset.card_insert_of_notMem, hw1_notmem, hv_notmem]
        have hcardI : I.card = 6 := by
          have h :=
            (Finset.card_union_of_disjoint (s := ({v, w1, pu} : Finset (Fin 18))) (t := T.erase u1)
              hvw1pu_disj)
          -- `h : #(A ∪ B) = #A + #B`
          -- rewrite `I` and cards
          have : I.card = ({v, w1, pu} : Finset (Fin 18)).card + (T.erase u1).card := by
            simpa [I] using h
          -- finish
          omega
        exact hcardI

    exact (h_no6 _ h6IS).elim

  -- Finish Cariolaro's final step.
  classical

  -- First, upgrade the partial `N(v)` labeling: show `s1,s2,s3,s4` are pairwise distinct and
  -- hence `S0 = {s1,s2,s3,s4}`.
  have hN_indep : G.IsIndepSet (G.neighborSet v) :=
    neighborSet_indep_of_triangleFree h_tri v

  -- Helper: if two `p`'s share the same `s`-partner, we get a triangle or a 6-independent-set.
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
          all_goals
            first
            | exact absurd rfl hxy
            | exact hs_pa
            | exact hs_pb
            | exact G.symm hs_pa
            | exact G.symm hs_pb
            | exact hadj
            | exact G.symm hadj
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
  have h1_unique : ∀ x, x ∈ N → x ≠ s1 → ¬G.Adj x p1 := by
    intro x hx hne hxadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p1 := ⟨hx, hxadj⟩
    exact hne (hs1_unique x h_and)
  have h2_unique : ∀ x, x ∈ N → x ≠ s2 → ¬G.Adj x p2 := by
    intro x hx hne hxadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p2 := ⟨hx, hxadj⟩
    exact hne (hs2_unique x h_and)
  have h3_unique : ∀ x, x ∈ N → x ≠ s3 → ¬G.Adj x p3 := by
    intro x hx hne hxadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p3 := ⟨hx, hxadj⟩
    exact hne (hs3_unique x h_and)
  have h4_unique : ∀ x, x ∈ N → x ≠ s4 → ¬G.Adj x p4 := by
    intro x hx hne hxadj
    have h_and : x ∈ G.neighborFinset v ∧ G.Adj x p4 := ⟨hx, hxadj⟩
    exact hne (hs4_unique x h_and)

  have hs_distinct :
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h_eq; subst h_eq)
    · exact distinct_helper p1 p2 s1 hp_ne12 hp1_nonadj_v hp2_nonadj_v hs1_in_N hs1_adj_p1 hs2_adj_p2
        h1_unique h2_unique
    · exact distinct_helper p1 p3 s1 hp_ne13 hp1_nonadj_v hp3_nonadj_v hs1_in_N hs1_adj_p1 hs3_adj_p3
        h1_unique h3_unique
    · exact distinct_helper p1 p4 s1 hp_ne14 hp1_nonadj_v hp4_nonadj_v hs1_in_N hs1_adj_p1 hs4_adj_p4
        h1_unique h4_unique
    · exact distinct_helper p2 p3 s2 hp_ne23 hp2_nonadj_v hp3_nonadj_v hs2_in_N hs2_adj_p2 hs3_adj_p3
        h2_unique h3_unique
    · exact distinct_helper p2 p4 s2 hp_ne24 hp2_nonadj_v hp4_nonadj_v hs2_in_N hs2_adj_p2 hs4_adj_p4
        h2_unique h4_unique
    · exact distinct_helper p3 p4 s3 hp_ne34 hp3_nonadj_v hp4_nonadj_v hs3_in_N hs3_adj_p3 hs4_adj_p4
        h3_unique h4_unique

  obtain ⟨hs_ne12, hs_ne13, hs_ne14, hs_ne23, hs_ne24, hs_ne34⟩ := hs_distinct

  have hS_card : ({s1, s2, s3, s4} : Finset (Fin 18)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hs_ne34]
    · simp [hs_ne23, hs_ne24]
    · simp [hs_ne12, hs_ne13, hs_ne14]

  have hS_sub_S0 : ({s1, s2, s3, s4} : Finset (Fin 18)) ⊆ S0 := by
    intro x hx
    have ht_ne_s3 : t ≠ s3 := by
      intro h
      subst h
      exact ht_notin_S (by simp [S])
    have ht_ne_s4 : t ≠ s4 := by
      intro h
      subst h
      exact ht_notin_S (by simp [S])
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨ht_ne_s1.symm, hs1_in_N⟩
    · exact Finset.mem_erase.mpr ⟨ht_ne_s2.symm, hs2_in_N⟩
    · exact Finset.mem_erase.mpr ⟨ht_ne_s3.symm, hs3_in_N⟩
    · exact Finset.mem_erase.mpr ⟨ht_ne_s4.symm, hs4_in_N⟩

  have hS0_eq : S0 = ({s1, s2, s3, s4} : Finset (Fin 18)) := by
    exact (Finset.eq_of_subset_of_card_le hS_sub_S0 (by simpa [hS0_card, hS_card])).symm

  have hSrest_w1_card : (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 2 := by
    have h' : (S0.filter (G.Adj w1)).card = 2 := hS0w1_card
    have : ((({s1, s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1))).card = 2 := by
      simpa [hS0_eq] using h'
    simpa [Finset.filter_insert, hw1_nonadj_s1] using this

  -- Extract `t2,t3,t4`: the unique T-neighbors of p2,p3,p4.
  have h_p2_T_card : (T.filter (G.Adj p2)).card = 1 := by
    have hp1P : p1 ∈ P := by rw [hP_eq]; simp
    have hp2P : p2 ∈ P := by rw [hP_eq]; simp
    have hp3P : p3 ∈ P := by rw [hP_eq]; simp
    have hp4P : p4 ∈ P := by rw [hP_eq]; simp
    have h_p1_ge1 : 1 ≤ (T.filter (G.Adj p1)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p1 hp1P))
    have h_p3_ge1 : 1 ≤ (T.filter (G.Adj p3)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p3 hp3P))
    have h_p4_ge1 : 1 ≤ (T.filter (G.Adj p4)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p4 hp4P))
    have h_sum_exp :
        P.sum (fun p => (T.filter (G.Adj p)).card) =
          (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
          (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      simpa [hP_eq] using
        (sum_over_four p1 p2 p3 p4 hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
          (fun p => (T.filter (G.Adj p)).card))
    by_contra hne1
    have h_p2_ge1 : 1 ≤ (T.filter (G.Adj p2)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p2 hp2P))
    have h_p2_ge2 : 2 ≤ (T.filter (G.Adj p2)).card := by
      have : 1 < (T.filter (G.Adj p2)).card := lt_of_le_of_ne h_p2_ge1 (Ne.symm hne1)
      exact Nat.succ_le_iff.mp this
    have hsum_ge5 :
        5 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      omega
    have hsum_eq4 :
        (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card = 4 := by
      have := congrArg id h_sum_eq4
      simpa [h_sum_exp] using this
    omega

  have h_p3_T_card : (T.filter (G.Adj p3)).card = 1 := by
    have hp1P : p1 ∈ P := by rw [hP_eq]; simp
    have hp2P : p2 ∈ P := by rw [hP_eq]; simp
    have hp3P : p3 ∈ P := by rw [hP_eq]; simp
    have hp4P : p4 ∈ P := by rw [hP_eq]; simp
    have h_p1_ge1 : 1 ≤ (T.filter (G.Adj p1)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p1 hp1P))
    have h_p2_ge1 : 1 ≤ (T.filter (G.Adj p2)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p2 hp2P))
    have h_p4_ge1 : 1 ≤ (T.filter (G.Adj p4)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p4 hp4P))
    have h_sum_exp :
        P.sum (fun p => (T.filter (G.Adj p)).card) =
          (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
          (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      simpa [hP_eq] using
        (sum_over_four p1 p2 p3 p4 hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
          (fun p => (T.filter (G.Adj p)).card))
    by_contra hne1
    have h_p3_ge1 : 1 ≤ (T.filter (G.Adj p3)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p3 hp3P))
    have h_p3_ge2 : 2 ≤ (T.filter (G.Adj p3)).card := by
      have : 1 < (T.filter (G.Adj p3)).card := lt_of_le_of_ne h_p3_ge1 (Ne.symm hne1)
      exact Nat.succ_le_iff.mp this
    have hsum_ge5 :
        5 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      omega
    have hsum_eq4 :
        (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card = 4 := by
      have := congrArg id h_sum_eq4
      simpa [h_sum_exp] using this
    omega

  have h_p4_T_card : (T.filter (G.Adj p4)).card = 1 := by
    have hp1P : p1 ∈ P := by rw [hP_eq]; simp
    have hp2P : p2 ∈ P := by rw [hP_eq]; simp
    have hp3P : p3 ∈ P := by rw [hP_eq]; simp
    have hp4P : p4 ∈ P := by rw [hP_eq]; simp
    have h_p1_ge1 : 1 ≤ (T.filter (G.Adj p1)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p1 hp1P))
    have h_p2_ge1 : 1 ≤ (T.filter (G.Adj p2)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p2 hp2P))
    have h_p3_ge1 : 1 ≤ (T.filter (G.Adj p3)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p3 hp3P))
    have h_sum_exp :
        P.sum (fun p => (T.filter (G.Adj p)).card) =
          (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
          (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      simpa [hP_eq] using
        (sum_over_four p1 p2 p3 p4 hp_ne12 hp_ne13 hp_ne14 hp_ne23 hp_ne24 hp_ne34
          (fun p => (T.filter (G.Adj p)).card))
    by_contra hne1
    have h_p4_ge1 : 1 ≤ (T.filter (G.Adj p4)).card :=
      Nat.succ_le_iff.mp (Finset.card_pos.mpr (hp_has_T_neighbor p4 hp4P))
    have h_p4_ge2 : 2 ≤ (T.filter (G.Adj p4)).card := by
      have : 1 < (T.filter (G.Adj p4)).card := lt_of_le_of_ne h_p4_ge1 (Ne.symm hne1)
      exact Nat.succ_le_iff.mp this
    have hsum_ge5 :
        5 ≤ (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card := by
      omega
    have hsum_eq4 :
        (T.filter (G.Adj p1)).card + (T.filter (G.Adj p2)).card +
              (T.filter (G.Adj p3)).card + (T.filter (G.Adj p4)).card = 4 := by
      have := congrArg id h_sum_eq4
      simpa [h_sum_exp] using this
    omega

  obtain ⟨t2, ht2_eq⟩ := Finset.card_eq_one.mp h_p2_T_card
  have ht2_mem : t2 ∈ T.filter (G.Adj p2) := by simp [ht2_eq]
  have ht2_in_T : t2 ∈ T := (Finset.mem_filter.mp ht2_mem).1
  have hp2_adj_t2 : G.Adj p2 t2 := (Finset.mem_filter.mp ht2_mem).2

  obtain ⟨t3, ht3_eq⟩ := Finset.card_eq_one.mp h_p3_T_card
  have ht3_mem : t3 ∈ T.filter (G.Adj p3) := by simp [ht3_eq]
  have ht3_in_T : t3 ∈ T := (Finset.mem_filter.mp ht3_mem).1
  have hp3_adj_t3 : G.Adj p3 t3 := (Finset.mem_filter.mp ht3_mem).2

  obtain ⟨t4, ht4_eq⟩ := Finset.card_eq_one.mp h_p4_T_card
  have ht4_mem : t4 ∈ T.filter (G.Adj p4) := by simp [ht4_eq]
  have ht4_in_T : t4 ∈ T := (Finset.mem_filter.mp ht4_mem).1
  have hp4_adj_t4 : G.Adj p4 t4 := (Finset.mem_filter.mp ht4_mem).2

  -- Distinctness of `t1,t2,t3,t4` follows from the fact each `ti ∈ T` has at most one P-neighbor.
  have ht2_ne_t1 : t2 ≠ t1 := by
    intro h
    have ht1P : p1 ∈ P.filter (G.Adj t1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_t1⟩
    have ht2P : p2 ∈ P.filter (G.Adj t1) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp2_in_P, G.symm hp2_adj_t2⟩
    have hsubset : ({p1, p2} : Finset (Fin 18)) ⊆ P.filter (G.Adj t1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht1P
      · exact ht2P
    have hge2 : 2 ≤ (P.filter (G.Adj t1)).card := by
      have : ({p1, p2} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t1)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne12] using this
    have hle1 : (P.filter (G.Adj t1)).card ≤ 1 := hT_to_P_le1 t1 ht1_in_T
    omega
  have ht3_ne_t1 : t3 ≠ t1 := by
    intro h
    have ht1P : p1 ∈ P.filter (G.Adj t1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_t1⟩
    have ht3P : p3 ∈ P.filter (G.Adj t1) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp3_in_P, G.symm hp3_adj_t3⟩
    have hsubset : ({p1, p3} : Finset (Fin 18)) ⊆ P.filter (G.Adj t1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht1P
      · exact ht3P
    have hge2 : 2 ≤ (P.filter (G.Adj t1)).card := by
      have : ({p1, p3} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t1)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne13] using this
    have hle1 : (P.filter (G.Adj t1)).card ≤ 1 := hT_to_P_le1 t1 ht1_in_T
    omega
  have ht4_ne_t1 : t4 ≠ t1 := by
    intro h
    have ht1P : p1 ∈ P.filter (G.Adj t1) := by
      exact Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_t1⟩
    have ht4P : p4 ∈ P.filter (G.Adj t1) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp4_in_P, G.symm hp4_adj_t4⟩
    have hsubset : ({p1, p4} : Finset (Fin 18)) ⊆ P.filter (G.Adj t1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht1P
      · exact ht4P
    have hge2 : 2 ≤ (P.filter (G.Adj t1)).card := by
      have : ({p1, p4} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t1)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne14] using this
    have hle1 : (P.filter (G.Adj t1)).card ≤ 1 := hT_to_P_le1 t1 ht1_in_T
    omega

  have ht2_ne_t3 : t2 ≠ t3 := by
    intro h
    have ht2P : p2 ∈ P.filter (G.Adj t2) := by
      exact Finset.mem_filter.mpr ⟨hp2_in_P, G.symm hp2_adj_t2⟩
    have ht3P : p3 ∈ P.filter (G.Adj t2) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp3_in_P, G.symm hp3_adj_t3⟩
    have hsubset : ({p2, p3} : Finset (Fin 18)) ⊆ P.filter (G.Adj t2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht2P
      · exact ht3P
    have hge2 : 2 ≤ (P.filter (G.Adj t2)).card := by
      have : ({p2, p3} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t2)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne23] using this
    have hle1 : (P.filter (G.Adj t2)).card ≤ 1 := hT_to_P_le1 t2 ht2_in_T
    omega
  have ht2_ne_t4 : t2 ≠ t4 := by
    intro h
    have ht2P : p2 ∈ P.filter (G.Adj t2) := by
      exact Finset.mem_filter.mpr ⟨hp2_in_P, G.symm hp2_adj_t2⟩
    have ht4P : p4 ∈ P.filter (G.Adj t2) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp4_in_P, G.symm hp4_adj_t4⟩
    have hsubset : ({p2, p4} : Finset (Fin 18)) ⊆ P.filter (G.Adj t2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht2P
      · exact ht4P
    have hge2 : 2 ≤ (P.filter (G.Adj t2)).card := by
      have : ({p2, p4} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t2)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne24] using this
    have hle1 : (P.filter (G.Adj t2)).card ≤ 1 := hT_to_P_le1 t2 ht2_in_T
    omega
  have ht3_ne_t4 : t3 ≠ t4 := by
    intro h
    have ht3P : p3 ∈ P.filter (G.Adj t3) := by
      exact Finset.mem_filter.mpr ⟨hp3_in_P, G.symm hp3_adj_t3⟩
    have ht4P : p4 ∈ P.filter (G.Adj t3) := by
      subst h
      exact Finset.mem_filter.mpr ⟨hp4_in_P, G.symm hp4_adj_t4⟩
    have hsubset : ({p3, p4} : Finset (Fin 18)) ⊆ P.filter (G.Adj t3) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht3P
      · exact ht4P
    have hge2 : 2 ≤ (P.filter (G.Adj t3)).card := by
      have : ({p3, p4} : Finset (Fin 18)).card ≤ (P.filter (G.Adj t3)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne34] using this
    have hle1 : (P.filter (G.Adj t3)).card ≤ 1 := hT_to_P_le1 t3 ht3_in_T
    omega

  have hT_eq : T = ({t1, t2, t3, t4} : Finset (Fin 18)) := by
    have hsub : ({t1, t2, t3, t4} : Finset (Fin 18)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ht1_in_T
      · exact ht2_in_T
      · exact ht3_in_T
      · exact ht4_in_T
    have hcard : ({t1, t2, t3, t4} : Finset (Fin 18)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [ht3_ne_t4]
      · simp [ht2_ne_t3, ht2_ne_t4]
      · simp [ht2_ne_t1.symm, ht3_ne_t1.symm, ht4_ne_t1.symm]
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa [hT_card, hcard])).symm

  -- w1 is not adjacent to t1 (else {p1, t1, w1} is a triangle).
  have hw1_nonadj_t1 : ¬G.Adj w1 t1 := by
    intro h
    have h_clique : G.IsNClique 3 {p1, t1, w1} := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals
          first
          | exact absurd rfl hxy
          | exact hp1_adj_t1
          | exact hp1_adj_w1
          | exact G.symm hp1_adj_t1
          | exact G.symm hp1_adj_w1
          | exact h
          | exact G.symm h
      · have hp1_ne_t1 : p1 ≠ t1 := G.ne_of_adj hp1_adj_t1
        have hp1_ne_w1 : p1 ≠ w1 := G.ne_of_adj hp1_adj_w1
        have ht1_ne_w1 : t1 ≠ w1 := by
          intro h_eq
          have ht1_adj_t : G.Adj t t1 := (Finset.mem_filter.mp ht1_in_T).2
          exact hw1_nonadj_t (by simpa [h_eq] using ht1_adj_t)
        simp [hp1_ne_t1, hp1_ne_w1, ht1_ne_w1]
    exact h_tri _ h_clique

  -- Relate `commonNeighborsCard t w1` to the number of T-neighbors of w1.
  have hw1_nonadj_v : ¬G.Adj v w1 := (hQ_props w1 hw1_in_Q).1
  have hTw1_card : (T.filter (G.Adj w1)).card = 2 := by
    have h_inter_eq : (G.neighborFinset t ∩ G.neighborFinset w1) = T.filter (G.Adj w1) := by
      ext x
      constructor
      · intro hx
        have hx_t : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).1
        have hx_w1 : x ∈ G.neighborFinset w1 := (Finset.mem_inter.mp hx).2
        have htx : G.Adj t x := by simpa [mem_neighborFinset] using hx_t
        have hw1x : G.Adj w1 x := by simpa [mem_neighborFinset] using hx_w1
        have hx_ne_v : x ≠ v := by
          intro h
          subst h
          exact hw1_nonadj_v (G.symm hw1x)
        have hx_in_T : x ∈ T := ht_neighbor_in_T x htx hx_ne_v
        exact Finset.mem_filter.mpr ⟨hx_in_T, hw1x⟩
      · intro hx
        have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
        have hw1x : G.Adj w1 x := (Finset.mem_filter.mp hx).2
        have htx : G.Adj t x := (Finset.mem_filter.mp hxT).2
        exact Finset.mem_inter.mpr ⟨by simpa [mem_neighborFinset] using htx, by simpa [mem_neighborFinset] using hw1x⟩
    have : commonNeighborsCard G t w1 = (T.filter (G.Adj w1)).card := by
      simp [commonNeighborsCard, _root_.commonNeighbors, h_inter_eq]
    simpa [this] using ht_w1_common2

  have hTrest_w1_card : (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 2 := by
    have : (({t1, t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 2 := by
      simpa [hT_eq] using hTw1_card
    simpa [Finset.filter_insert, hw1_nonadj_t1] using this

  -- Each `si ∈ S0` has exactly one T-neighbor (an S0–T perfect matching).
  have hs1_T_le1 : (T.filter (G.Adj s1)).card ≤ 1 := by
    have hs1_ne_t : s1 ≠ t := ht_ne_s1.symm
    have hs1_nonadj_t : ¬G.Adj s1 t := by
      -- t has no neighbors in N(v)
      intro h
      exact (ht_no_S_neighbors s1 hs1_in_N) (G.symm h)
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s1 t hs1_ne_t.symm hs1_nonadj_t
    have hv_in : v ∈ G.neighborFinset s1 ∩ G.neighborFinset t := by
      refine Finset.mem_inter.mpr ?_
      constructor
      · simpa [mem_neighborFinset] using (G.symm (by simpa [mem_neighborFinset] using hs1_in_N))
      · simpa [mem_neighborFinset] using (G.symm ht_adj_v)
    have h_inter_eq : (G.neighborFinset s1 ∩ G.neighborFinset t) = insert v (T.filter (G.Adj s1)) := by
      ext x
      constructor
      · intro hx
        have hx_s1 : x ∈ G.neighborFinset s1 := (Finset.mem_inter.mp hx).1
        have hx_t : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).2
        have htx : G.Adj t x := by simpa [mem_neighborFinset] using hx_t
        have hs1x : G.Adj s1 x := by simpa [mem_neighborFinset] using hx_s1
        by_cases hxv : x = v
        · subst hxv; exact Finset.mem_insert_self _ _
        · have hx_in_T : x ∈ T := ht_neighbor_in_T x htx hxv
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx_in_T, hs1x⟩)
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hxT
        · exact hv_in
        · have hxT' : x ∈ T := (Finset.mem_filter.mp hxT).1
          have hs1x : G.Adj s1 x := (Finset.mem_filter.mp hxT).2
          have htx : G.Adj t x := (Finset.mem_filter.mp hxT').2
          exact Finset.mem_inter.mpr ⟨by simpa [mem_neighborFinset] using hs1x, by simpa [mem_neighborFinset] using htx⟩
    have hv_notin : v ∉ (T.filter (G.Adj s1)) := by
      intro hv
      have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hcard : commonNeighborsCard G s1 t = 1 + (T.filter (G.Adj s1)).card := by
      unfold commonNeighborsCard _root_.commonNeighbors
      -- rewrite the common-neighbor finset, then compute the card of an insert
      rw [h_inter_eq]
      have hci : (insert v (T.filter (G.Adj s1))).card = (T.filter (G.Adj s1)).card + 1 :=
        Finset.card_insert_of_notMem hv_notin
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hci
    have hsum : 1 + (T.filter (G.Adj s1)).card ≤ 2 := by
      simpa [hcard] using h_le
    omega

  have hs2_T_le1 : (T.filter (G.Adj s2)).card ≤ 1 := by
    have hs2_ne_t : s2 ≠ t := ht_ne_s2.symm
    have hs2_nonadj_t : ¬G.Adj s2 t := by
      intro h
      exact (ht_no_S_neighbors s2 hs2_in_N) (G.symm h)
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s2 t hs2_ne_t.symm hs2_nonadj_t
    have hv_in : v ∈ G.neighborFinset s2 ∩ G.neighborFinset t := by
      refine Finset.mem_inter.mpr ?_
      constructor
      · simpa [mem_neighborFinset] using (G.symm (by simpa [mem_neighborFinset] using hs2_in_N))
      · simpa [mem_neighborFinset] using (G.symm ht_adj_v)
    have h_inter_eq : (G.neighborFinset s2 ∩ G.neighborFinset t) = insert v (T.filter (G.Adj s2)) := by
      ext x
      constructor
      · intro hx
        have hx_s2 : x ∈ G.neighborFinset s2 := (Finset.mem_inter.mp hx).1
        have hx_t : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).2
        have htx : G.Adj t x := by simpa [mem_neighborFinset] using hx_t
        have hs2x : G.Adj s2 x := by simpa [mem_neighborFinset] using hx_s2
        by_cases hxv : x = v
        · subst hxv; exact Finset.mem_insert_self _ _
        · have hx_in_T : x ∈ T := ht_neighbor_in_T x htx hxv
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx_in_T, hs2x⟩)
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hxT
        · exact hv_in
        · have hxT' : x ∈ T := (Finset.mem_filter.mp hxT).1
          have hs2x : G.Adj s2 x := (Finset.mem_filter.mp hxT).2
          have htx : G.Adj t x := (Finset.mem_filter.mp hxT').2
          exact Finset.mem_inter.mpr ⟨by simpa [mem_neighborFinset] using hs2x, by simpa [mem_neighborFinset] using htx⟩
    have hv_notin : v ∉ (T.filter (G.Adj s2)) := by
      intro hv
      have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hcard : commonNeighborsCard G s2 t = 1 + (T.filter (G.Adj s2)).card := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [h_inter_eq]
      have hci : (insert v (T.filter (G.Adj s2))).card = (T.filter (G.Adj s2)).card + 1 :=
        Finset.card_insert_of_notMem hv_notin
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hci
    have hsum : 1 + (T.filter (G.Adj s2)).card ≤ 2 := by
      simpa [hcard] using h_le
    omega

  have hs3_T_le1 : (T.filter (G.Adj s3)).card ≤ 1 := by
    have hs3_ne_t : s3 ≠ t := ht_ne_s3.symm
    have hs3_nonadj_t : ¬G.Adj s3 t := by
      intro h
      exact (ht_no_S_neighbors s3 hs3_in_N) (G.symm h)
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s3 t hs3_ne_t.symm hs3_nonadj_t
    have hv_in : v ∈ G.neighborFinset s3 ∩ G.neighborFinset t := by
      refine Finset.mem_inter.mpr ?_
      constructor
      · simpa [mem_neighborFinset] using (G.symm (by simpa [mem_neighborFinset] using hs3_in_N))
      · simpa [mem_neighborFinset] using (G.symm ht_adj_v)
    have h_inter_eq : (G.neighborFinset s3 ∩ G.neighborFinset t) = insert v (T.filter (G.Adj s3)) := by
      ext x
      constructor
      · intro hx
        have hx_s3 : x ∈ G.neighborFinset s3 := (Finset.mem_inter.mp hx).1
        have hx_t : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).2
        have htx : G.Adj t x := by simpa [mem_neighborFinset] using hx_t
        have hs3x : G.Adj s3 x := by simpa [mem_neighborFinset] using hx_s3
        by_cases hxv : x = v
        · subst hxv; exact Finset.mem_insert_self _ _
        · have hx_in_T : x ∈ T := ht_neighbor_in_T x htx hxv
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx_in_T, hs3x⟩)
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hxT
        · exact hv_in
        · have hxT' : x ∈ T := (Finset.mem_filter.mp hxT).1
          have hs3x : G.Adj s3 x := (Finset.mem_filter.mp hxT).2
          have htx : G.Adj t x := (Finset.mem_filter.mp hxT').2
          exact Finset.mem_inter.mpr ⟨by simpa [mem_neighborFinset] using hs3x, by simpa [mem_neighborFinset] using htx⟩
    have hv_notin : v ∉ (T.filter (G.Adj s3)) := by
      intro hv
      have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hcard : commonNeighborsCard G s3 t = 1 + (T.filter (G.Adj s3)).card := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [h_inter_eq]
      have hci : (insert v (T.filter (G.Adj s3))).card = (T.filter (G.Adj s3)).card + 1 :=
        Finset.card_insert_of_notMem hv_notin
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hci
    have hsum : 1 + (T.filter (G.Adj s3)).card ≤ 2 := by
      simpa [hcard] using h_le
    omega

  have hs4_T_le1 : (T.filter (G.Adj s4)).card ≤ 1 := by
    have hs4_ne_t : s4 ≠ t := ht_ne_s4.symm
    have hs4_nonadj_t : ¬G.Adj s4 t := by
      intro h
      exact (ht_no_S_neighbors s4 hs4_in_N) (G.symm h)
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s4 t hs4_ne_t.symm hs4_nonadj_t
    have hv_in : v ∈ G.neighborFinset s4 ∩ G.neighborFinset t := by
      refine Finset.mem_inter.mpr ?_
      constructor
      · simpa [mem_neighborFinset] using (G.symm (by simpa [mem_neighborFinset] using hs4_in_N))
      · simpa [mem_neighborFinset] using (G.symm ht_adj_v)
    have h_inter_eq : (G.neighborFinset s4 ∩ G.neighborFinset t) = insert v (T.filter (G.Adj s4)) := by
      ext x
      constructor
      · intro hx
        have hx_s4 : x ∈ G.neighborFinset s4 := (Finset.mem_inter.mp hx).1
        have hx_t : x ∈ G.neighborFinset t := (Finset.mem_inter.mp hx).2
        have htx : G.Adj t x := by simpa [mem_neighborFinset] using hx_t
        have hs4x : G.Adj s4 x := by simpa [mem_neighborFinset] using hx_s4
        by_cases hxv : x = v
        · subst hxv; exact Finset.mem_insert_self _ _
        · have hx_in_T : x ∈ T := ht_neighbor_in_T x htx hxv
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx_in_T, hs4x⟩)
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hxT
        · exact hv_in
        · have hxT' : x ∈ T := (Finset.mem_filter.mp hxT).1
          have hs4x : G.Adj s4 x := (Finset.mem_filter.mp hxT).2
          have htx : G.Adj t x := (Finset.mem_filter.mp hxT').2
          exact Finset.mem_inter.mpr ⟨by simpa [mem_neighborFinset] using hs4x, by simpa [mem_neighborFinset] using htx⟩
    have hv_notin : v ∉ (T.filter (G.Adj s4)) := by
      intro hv
      have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
      have hvQ : v ∈ Q := (Finset.mem_filter.mp hvT).1
      have ⟨_, hv_common2⟩ := hQ_props v hvQ
      have hv_common5 : commonNeighborsCard G v v = 5 := by
        simp [commonNeighborsCard, _root_.commonNeighbors, Finset.inter_self, h_reg v]
      omega
    have hcard : commonNeighborsCard G s4 t = 1 + (T.filter (G.Adj s4)).card := by
      unfold commonNeighborsCard _root_.commonNeighbors
      rw [h_inter_eq]
      have hci : (insert v (T.filter (G.Adj s4))).card = (T.filter (G.Adj s4)).card + 1 :=
        Finset.card_insert_of_notMem hv_notin
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hci
    have hsum : 1 + (T.filter (G.Adj s4)).card ≤ 2 := by
      simpa [hcard] using h_le
    omega

  have hS0_T_sum :
      S0.sum (fun si => (T.filter (G.Adj si)).card) = 4 := by
    have h_edge_count :
        S0.sum (fun si => (T.filter (G.Adj si)).card) =
          T.sum (fun ti => (S0.filter (G.Adj ti)).card) := by
      simpa using
        (bipartite_edge_count_symmetry (A := S0) (B := T) (R := G.Adj) (hR := G.symm))
    have h_each_ti : ∀ ti ∈ T, (S0.filter (G.Adj ti)).card = 1 := by
      intro ti hti
      have hti_Q : ti ∈ Q := (Finset.mem_filter.mp hti).1
      have hti_adj_t : G.Adj t ti := (Finset.mem_filter.mp hti).2
      have hti_common2 : commonNeighborsCard G v ti = 2 := (hQ_props ti hti_Q).2
      exact
        T_vertex_has_one_S_neighbor h_reg h_tri v t ti ht_adj_v hti_adj_t hti_common2 S0 hS0_card rfl
    have : T.sum (fun ti => (S0.filter (G.Adj ti)).card) = 4 := by
      calc
        T.sum (fun ti => (S0.filter (G.Adj ti)).card)
            = T.sum (fun _ => 1) := by
                refine Finset.sum_congr rfl ?_
                intro ti hti
                simp [h_each_ti ti hti]
        _ = 4 := by simp [Finset.sum_const, hT_card]
    simpa [h_edge_count] using this

  have hS0_sum_exp :
      S0.sum (fun si => (T.filter (G.Adj si)).card) =
        (T.filter (G.Adj s1)).card + (T.filter (G.Adj s2)).card +
        (T.filter (G.Adj s3)).card + (T.filter (G.Adj s4)).card := by
    simpa [hS0_eq] using
      (sum_over_four s1 s2 s3 s4 hs_ne12 hs_ne13 hs_ne14 hs_ne23 hs_ne24 hs_ne34
        (fun si => (T.filter (G.Adj si)).card))

  have hs2_T_card : (T.filter (G.Adj s2)).card = 1 := by
    omega
  have hs4_T_card : (T.filter (G.Adj s4)).card = 1 := by
    omega

  have hSrest_card3 : ({s2, s3, s4} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hs_ne34]
    · simp [hs_ne23, hs_ne24]

  have hTrest_card3 : ({t2, t3, t4} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [ht3_ne_t4]
    · simp [ht2_ne_t3, ht2_ne_t4]

  -- Convert the "card = 2 of a 3-set" facts into concrete adjacency patterns.
  have hs_cases :
      (¬G.Adj w1 s2 ∧ G.Adj w1 s3 ∧ G.Adj w1 s4) ∨
      (G.Adj w1 s2 ∧ ¬G.Adj w1 s3 ∧ G.Adj w1 s4) ∨
      (G.Adj w1 s2 ∧ G.Adj w1 s3 ∧ ¬G.Adj w1 s4) := by
    have hSrest_w1_card' :
        (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 2 := by
      simpa using hSrest_w1_card
    by_cases hs2 : G.Adj w1 s2
    · by_cases hs3 : G.Adj w1 s3
      · -- then ¬(w1~s4), else the filtered set has card 3
        have hs4 : ¬G.Adj w1 s4 := by
          intro hs4
          have hsub :
              ({s2, s3, s4} : Finset (Fin 18)) ⊆
                ({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · simpa using hs2
            · simpa using hs3
            · simpa using hs4
          have hge3 :
              3 ≤ (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card := by
            have :
                ({s2, s3, s4} : Finset (Fin 18)).card ≤
                  (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card :=
              Finset.card_le_card hsub
            simpa [hSrest_card3] using this
          have : 3 ≤ 2 := by simpa [hSrest_w1_card'] using hge3
          exact (Nat.not_succ_le_self 2) (by simpa using this)
        exact Or.inr (Or.inr ⟨hs2, hs3, hs4⟩)
      · by_cases hs4 : G.Adj w1 s4
        · exact Or.inr (Or.inl ⟨hs2, hs3, hs4⟩)
        · -- only s2 adjacent gives card 1, contradiction
          exfalso
          have hcard1 :
              (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            simp [Finset.filter_insert, hs2, hs3, hs4, hs_ne23, hs_ne24, hs_ne34]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hSrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
    · -- ¬(w1~s2), so must have w1~s3 and w1~s4
      by_cases hs3 : G.Adj w1 s3
      · by_cases hs4 : G.Adj w1 s4
        · exact Or.inl ⟨hs2, hs3, hs4⟩
        · -- only s3 adjacent gives card 1, contradiction
          exfalso
          have hcard1 :
              (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            simp [Finset.filter_insert, hs2, hs3, hs4, hs_ne23, hs_ne24, hs_ne34]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hSrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
      · -- none of s2,s3 adjacent gives card ≤1, contradiction
        exfalso
        by_cases hs4 : G.Adj w1 s4
        · -- If w1 adj s4, then card = 1 (only s4 adjacent)
          have hcard1 :
              (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            have : ({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1) = {s4} := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro ⟨hx_mem, hx_adj⟩
                rcases hx_mem with rfl | rfl | rfl
                · exfalso; exact hs2 hx_adj
                · exfalso; exact hs3 hx_adj
                · rfl
              · intro rfl
                exact ⟨Or.inr (Or.inr rfl), hs4⟩
            simp [this]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hSrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
        · -- If w1 not adj s4, then card = 0 (none adjacent)
          have hcard0 :
              (({s2, s3, s4} : Finset (Fin 18)).filter (G.Adj w1)).card = 0 := by
            simp [Finset.filter_insert, hs2, hs3, hs4, hs_ne23, hs_ne24, hs_ne34]
          have : (0 : ℕ) = 2 := by simpa [hcard0] using hSrest_w1_card'
          exact (by decide : (0 : ℕ) ≠ 2) this

  have ht_cases :
      (¬G.Adj w1 t2 ∧ G.Adj w1 t3 ∧ G.Adj w1 t4) ∨
      (G.Adj w1 t2 ∧ ¬G.Adj w1 t3 ∧ G.Adj w1 t4) ∨
      (G.Adj w1 t2 ∧ G.Adj w1 t3 ∧ ¬G.Adj w1 t4) := by
    have hTrest_w1_card' :
        (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 2 := by
      simpa using hTrest_w1_card
    by_cases ht2 : G.Adj w1 t2
    · by_cases ht3 : G.Adj w1 t3
      · have ht4 : ¬G.Adj w1 t4 := by
          intro ht4
          have hsub :
              ({t2, t3, t4} : Finset (Fin 18)) ⊆
                ({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · simpa using ht2
            · simpa using ht3
            · simpa using ht4
          have hge3 :
              3 ≤ (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card := by
            have :
                ({t2, t3, t4} : Finset (Fin 18)).card ≤
                  (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card :=
              Finset.card_le_card hsub
            simpa [hTrest_card3] using this
          have : 3 ≤ 2 := by simpa [hTrest_w1_card'] using hge3
          exact (Nat.not_succ_le_self 2) (by simpa using this)
        exact Or.inr (Or.inr ⟨ht2, ht3, ht4⟩)
      · by_cases ht4 : G.Adj w1 t4
        · exact Or.inr (Or.inl ⟨ht2, ht3, ht4⟩)
        · exfalso
          have hcard1 :
              (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            simp [Finset.filter_insert, ht2, ht3, ht4, ht2_ne_t3, ht2_ne_t4, ht3_ne_t4]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hTrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
    · by_cases ht3 : G.Adj w1 t3
      · by_cases ht4 : G.Adj w1 t4
        · exact Or.inl ⟨ht2, ht3, ht4⟩
        · exfalso
          have hcard1 :
              (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            simp [Finset.filter_insert, ht2, ht3, ht4, ht2_ne_t3, ht2_ne_t4, ht3_ne_t4]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hTrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
      · exfalso
        by_cases ht4 : G.Adj w1 t4
        · -- If w1 adj t4, then card = 1 (only t4 adjacent)
          have hcard1 :
              (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 1 := by
            have : ({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1) = {t4} := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro ⟨hx_mem, hx_adj⟩
                rcases hx_mem with rfl | rfl | rfl
                · exfalso; exact ht2 hx_adj
                · exfalso; exact ht3 hx_adj
                · rfl
              · intro rfl
                exact ⟨Or.inr (Or.inr rfl), ht4⟩
            simp [this]
          have : (1 : ℕ) = 2 := by simpa [hcard1] using hTrest_w1_card'
          exact (by decide : (1 : ℕ) ≠ 2) this
        · -- If w1 not adj t4, then card = 0 (none adjacent)
          have hcard0 :
              (({t2, t3, t4} : Finset (Fin 18)).filter (G.Adj w1)).card = 0 := by
            simp [Finset.filter_insert, ht2, ht3, ht4, ht2_ne_t3, ht2_ne_t4, ht3_ne_t4]
          have : (0 : ℕ) = 2 := by simpa [hcard0] using hTrest_w1_card'
          exact (by decide : (0 : ℕ) ≠ 2) this

  have h_exists_i :
      (G.Adj w1 s2 ∧ G.Adj w1 t2) ∨ (G.Adj w1 s3 ∧ G.Adj w1 t3) ∨ (G.Adj w1 s4 ∧ G.Adj w1 t4) := by
    rcases hs_cases with hs | hs | hs <;> rcases ht_cases with ht | ht | ht
    all_goals
      rcases hs with ⟨hs2, hs3, hs4⟩
      rcases ht with ⟨ht2, ht3, ht4⟩
    -- Case 1,1: ¬s2,s3,s4 and ¬t2,t3,t4
    · exact Or.inr (Or.inl ⟨hs3, ht3⟩)
    -- Case 1,2: ¬s2,s3,s4 and t2,¬t3,t4
    · exact Or.inr (Or.inr ⟨hs4, ht4⟩)
    -- Case 1,3: ¬s2,s3,s4 and t2,t3,¬t4
    · exact Or.inr (Or.inl ⟨hs3, ht3⟩)
    -- Case 2,1: s2,¬s3,s4 and ¬t2,t3,t4
    · exact Or.inr (Or.inr ⟨hs4, ht4⟩)
    -- Case 2,2: s2,¬s3,s4 and t2,¬t3,t4
    · exact Or.inl ⟨hs2, ht2⟩
    -- Case 2,3: s2,¬s3,s4 and t2,t3,¬t4
    · exact Or.inl ⟨hs2, ht2⟩
    -- Case 3,1: s2,s3,¬s4 and ¬t2,t3,t4
    · exact Or.inr (Or.inl ⟨hs3, ht3⟩)
    -- Case 3,2: s2,s3,¬s4 and t2,¬t3,t4
    · exact Or.inl ⟨hs2, ht2⟩
    -- Case 3,3: s2,s3,¬s4 and t2,t3,¬t4
    · exact Or.inr (Or.inl ⟨hs3, ht3⟩)

  -- Show `w1` is not adjacent to `p2` nor `p4` (its unique P-neighbor is `p1`).
  have hw1_nonadj_p2 : ¬G.Adj w1 p2 := by
    intro h
    have hp1_mem : p1 ∈ P.filter (G.Adj w1) := Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_w1⟩
    have hp2_mem : p2 ∈ P.filter (G.Adj w1) := Finset.mem_filter.mpr ⟨hp2_in_P, h⟩
    have hsubset : ({p1, p2} : Finset (Fin 18)) ⊆ P.filter (G.Adj w1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp1_mem
      · exact hp2_mem
    have hge2 : 2 ≤ (P.filter (G.Adj w1)).card := by
      have : ({p1, p2} : Finset (Fin 18)).card ≤ (P.filter (G.Adj w1)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne12] using this
    omega

  have hw1_nonadj_p4 : ¬G.Adj w1 p4 := by
    intro h
    have hp1_mem : p1 ∈ P.filter (G.Adj w1) := Finset.mem_filter.mpr ⟨hp1_in_P, G.symm hp1_adj_w1⟩
    have hp4_mem : p4 ∈ P.filter (G.Adj w1) := Finset.mem_filter.mpr ⟨hp4_in_P, h⟩
    have hsubset : ({p1, p4} : Finset (Fin 18)) ⊆ P.filter (G.Adj w1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp1_mem
      · exact hp4_mem
    have hge2 : 2 ≤ (P.filter (G.Adj w1)).card := by
      have : ({p1, p4} : Finset (Fin 18)).card ≤ (P.filter (G.Adj w1)).card :=
        Finset.card_le_card hsubset
      simpa [hp_ne14] using this
    omega

  -- Exclude i=2 and i=4 using a 3-common-neighbors contradiction with Claim 2 (≤2 common neighbors).
  have h_not_i2 : ¬(G.Adj w1 s2 ∧ G.Adj w1 t2) := by
    rintro ⟨hw1s2, hw1t2⟩
    have hw1_ne_p2 : w1 ≠ p2 := fun h =>
      Finset.disjoint_left.mp hP_Q_disj hp2_in_P (h ▸ hw1_in_Q)
    have hw1_nonadj_p2' : ¬G.Adj w1 p2 := hw1_nonadj_p2
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg w1 p2 hw1_ne_p2.symm hw1_nonadj_p2'
    have hsubset : ({p1, s2, t2} : Finset (Fin 18)) ⊆ (G.neighborFinset w1 ∩ G.neighborFinset p2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨G.symm hp1_adj_w1, G.symm h_adj12⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hw1s2, G.symm hs2_adj_p2⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hw1t2, hp2_adj_t2⟩
    have hcard_ge3 : 3 ≤ commonNeighborsCard G w1 p2 := by
      have : ({p1, s2, t2} : Finset (Fin 18)).card ≤ (G.neighborFinset w1 ∩ G.neighborFinset p2).card :=
        Finset.card_le_card hsubset
      have hp1_ne_s2 : p1 ≠ s2 := by
        intro h
        subst h
        exact hp1_nonadj_v (by simpa [mem_neighborFinset] using hs2_in_N)
      have ht2_ne_s2 : t2 ≠ s2 := by
        intro h
        subst h
        have : t2 ∈ Q := (Finset.mem_filter.mp ht2_in_T).1
        exact (Finset.disjoint_left.mp hNv_Q_disj) hs2_in_N this
      have hp1_ne_t2 : p1 ≠ t2 := by
        intro h
        subst h
        have : p1 ∈ Q := (Finset.mem_filter.mp ht2_in_T).1
        exact (Finset.disjoint_left.mp hP_Q_disj) hp1_in_P this
      have h3 : ({p1, s2, t2} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact ht2_ne_s2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp1_ne_s2, hp1_ne_t2⟩
      have : 3 ≤ (G.neighborFinset w1 ∩ G.neighborFinset p2).card := by
        simpa [h3] using this
      simpa [commonNeighborsCard, _root_.commonNeighbors] using this
    omega

  have h_not_i4 : ¬(G.Adj w1 s4 ∧ G.Adj w1 t4) := by
    rintro ⟨hw1s4, hw1t4⟩
    have hw1_ne_p4 : w1 ≠ p4 := fun h =>
      Finset.disjoint_left.mp hP_Q_disj hp4_in_P (h ▸ hw1_in_Q)
    have hw1_nonadj_p4' : ¬G.Adj w1 p4 := hw1_nonadj_p4
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg w1 p4 hw1_ne_p4.symm hw1_nonadj_p4'
    have hsubset : ({p1, s4, t4} : Finset (Fin 18)) ⊆ (G.neighborFinset w1 ∩ G.neighborFinset p4) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨G.symm hp1_adj_w1, h_adj41⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hw1s4, G.symm hs4_adj_p4⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hw1t4, hp4_adj_t4⟩
    have hcard_ge3 : 3 ≤ commonNeighborsCard G w1 p4 := by
      have : ({p1, s4, t4} : Finset (Fin 18)).card ≤ (G.neighborFinset w1 ∩ G.neighborFinset p4).card :=
        Finset.card_le_card hsubset
      have hp1_ne_s4 : p1 ≠ s4 := by
        intro h
        subst h
        exact hp1_nonadj_v (by simpa [mem_neighborFinset] using hs4_in_N)
      have ht4_ne_s4 : t4 ≠ s4 := by
        intro h
        subst h
        have : t4 ∈ Q := (Finset.mem_filter.mp ht4_in_T).1
        exact (Finset.disjoint_left.mp hNv_Q_disj) hs4_in_N this
      have hp1_ne_t4 : p1 ≠ t4 := by
        intro h
        subst h
        have : p1 ∈ Q := (Finset.mem_filter.mp ht4_in_T).1
        exact (Finset.disjoint_left.mp hP_Q_disj) hp1_in_P this
      have h3 : ({p1, s4, t4} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact ht4_ne_s4.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp1_ne_s4, hp1_ne_t4⟩
      have : 3 ≤ (G.neighborFinset w1 ∩ G.neighborFinset p4).card := by
        simpa [h3] using this
      simpa [commonNeighborsCard, _root_.commonNeighbors] using this
    omega

  -- Therefore i=3: w1 is adjacent to s3 and t3.
  have hw1_adj_s3_t3 : G.Adj w1 s3 ∧ G.Adj w1 t3 := by
    rcases h_exists_i with h2 | h3 | h4
    · exact (h_not_i2 h2).elim
    · exact h3
    · exact (h_not_i4 h4).elim
  have hw1_adj_s3 : G.Adj w1 s3 := hw1_adj_s3_t3.1
  have hw1_adj_t3 : G.Adj w1 t3 := hw1_adj_s3_t3.2

  have h_s_other :
      (G.Adj w1 s2 ∧ ¬G.Adj w1 s4) ∨ (¬G.Adj w1 s2 ∧ G.Adj w1 s4) := by
    rcases hs_cases with hs | hs | hs
    · refine Or.inr ⟨hs.1, hs.2.2⟩
    · exact (hs.2.1 hw1_adj_s3).elim
    · refine Or.inl ⟨hs.1, hs.2.2⟩

  have h_t_other :
      (G.Adj w1 t2 ∧ ¬G.Adj w1 t4) ∨ (¬G.Adj w1 t2 ∧ G.Adj w1 t4) := by
    rcases ht_cases with ht | ht | ht
    · refine Or.inr ⟨ht.1, ht.2.2⟩
    · exact (ht.2.1 hw1_adj_t3).elim
    · refine Or.inl ⟨ht.1, ht.2.2⟩

  have h_branch :
      (G.Adj w1 s2 ∧ G.Adj w1 t4) ∨ (G.Adj w1 s4 ∧ G.Adj w1 t2) := by
    rcases h_s_other with hs | hs <;> rcases h_t_other with ht | ht
    · exfalso; exact h_not_i2 ⟨hs.1, ht.1⟩
    · exact Or.inl ⟨hs.1, ht.2⟩
    · exact Or.inr ⟨hs.2, ht.1⟩
    · exfalso; exact h_not_i4 ⟨hs.2, ht.2⟩

  -- Final contradiction in the two symmetric branches.
  rcases h_branch with ⟨hw1s2, hw1t4⟩ | ⟨hw1s4, hw1t2⟩
  · -- Branch: w1~s2 and w1~t4
    have hs2_ne_p1 : s2 ≠ p1 := by
      intro h
      subst h
      exact hp1_nonadj_v (by simpa [mem_neighborFinset] using hs2_in_N)
    have hs2_nonadj_t2 : ¬G.Adj s2 t2 := by
      intro h
      have h_clique : G.IsNClique 3 {p2, s2, t2} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hs2_adj_p2
            | exact hp2_adj_t2
            | exact G.symm hs2_adj_p2
            | exact G.symm hp2_adj_t2
            | exact h
            | exact G.symm h
        · have hp2_ne_s2 : p2 ≠ s2 := G.ne_of_adj (G.symm hs2_adj_p2)
          have hp2_ne_t2 : p2 ≠ t2 := G.ne_of_adj hp2_adj_t2
          have hs2_ne_t2 : s2 ≠ t2 := by
            intro h_eq
            have ht2_in_N : t2 ∈ N := h_eq ▸ hs2_in_N
            have ht2_in_Q : t2 ∈ Q := (Finset.mem_filter.mp ht2_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht2_in_N ht2_in_Q
          simp [hp2_ne_s2, hp2_ne_t2, hs2_ne_t2]
      exact h_tri _ h_clique
    have hs2_nonadj_t3 : ¬G.Adj s2 t3 := by
      intro h
      have h_clique : G.IsNClique 3 {w1, s2, t3} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hw1s2
            | exact hw1_adj_t3
            | exact G.symm hw1s2
            | exact G.symm hw1_adj_t3
            | exact h
            | exact G.symm h
        · have hw1_ne_s2 : w1 ≠ s2 := G.ne_of_adj hw1s2
          have hw1_ne_t3 : w1 ≠ t3 := G.ne_of_adj hw1_adj_t3
          have hs2_ne_t3 : s2 ≠ t3 := by
            intro h_eq
            have ht3_in_N : t3 ∈ N := h_eq ▸ hs2_in_N
            have ht3_in_Q : t3 ∈ Q := (Finset.mem_filter.mp ht3_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht3_in_N ht3_in_Q
          simp [hw1_ne_s2, hw1_ne_t3, hs2_ne_t3]
      exact h_tri _ h_clique
    have hs2_nonadj_t4 : ¬G.Adj s2 t4 := by
      intro h
      have h_clique : G.IsNClique 3 {w1, s2, t4} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hw1s2
            | exact hw1t4
            | exact G.symm hw1s2
            | exact G.symm hw1t4
            | exact h
            | exact G.symm h
        · have hw1_ne_s2 : w1 ≠ s2 := G.ne_of_adj hw1s2
          have hw1_ne_t4 : w1 ≠ t4 := G.ne_of_adj hw1t4
          have hs2_ne_t4 : s2 ≠ t4 := by
            intro h_eq
            have ht4_in_N : t4 ∈ N := h_eq ▸ hs2_in_N
            have ht4_in_Q : t4 ∈ Q := (Finset.mem_filter.mp ht4_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht4_in_N ht4_in_Q
          simp [hw1_ne_s2, hw1_ne_t4, hs2_ne_t4]
      exact h_tri _ h_clique
    have hs2_adj_t1 : G.Adj s2 t1 := by
      by_contra hnot
      have : (T.filter (G.Adj s2)).card = 0 := by
        have : (T.filter (G.Adj s2)) = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
          intro hx
          rw [hT_eq] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hnot
          · exact hs2_nonadj_t2
          · exact hs2_nonadj_t3
          · exact hs2_nonadj_t4
        simpa [this]
      omega
    have hsubset : ({p2, w1, t1} : Finset (Fin 18)) ⊆ (G.neighborFinset s2 ∩ G.neighborFinset p1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hs2_adj_p2, h_adj12⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨G.symm hw1s2, hp1_adj_w1⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hs2_adj_t1, hp1_adj_t1⟩
    have hcard3 : 3 ≤ commonNeighborsCard G s2 p1 := by
      have : ({p2, w1, t1} : Finset (Fin 18)).card ≤ (G.neighborFinset s2 ∩ G.neighborFinset p1).card :=
        Finset.card_le_card hsubset
      have hp2_ne_w1 : p2 ≠ w1 := fun h =>
        Finset.disjoint_left.mp hP_Q_disj hp2_in_P (h ▸ hw1_in_Q)
      have hp2_ne_t1 : p2 ≠ t1 := by
        intro h
        subst h
        have : p2 ∈ Q := (Finset.mem_filter.mp ht1_in_T).1
        exact (Finset.disjoint_left.mp hP_Q_disj) hp2_in_P this
      have hw1_ne_t1 : w1 ≠ t1 := fun h_eq =>
        hw1_nonadj_t (h_eq ▸ ht1_adj_t)
      have h3 : ({p2, w1, t1} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hw1_ne_t1
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2_ne_w1, hp2_ne_t1⟩
      have : 3 ≤ (G.neighborFinset s2 ∩ G.neighborFinset p1).card := by
        simpa [h3] using this
      simpa [commonNeighborsCard, _root_.commonNeighbors] using this
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s2 p1 hs2_ne_p1.symm hs2_nonadj_p1
    omega
  · -- Branch: w1~s4 and w1~t2 (symmetric)
    have hs4_ne_p1 : s4 ≠ p1 := by
      intro h
      subst h
      exact hp1_nonadj_v (by simpa [mem_neighborFinset] using hs4_in_N)
    have hs4_nonadj_t2 : ¬G.Adj s4 t2 := by
      intro h
      have h_clique : G.IsNClique 3 {w1, s4, t2} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hw1s4
            | exact hw1t2
            | exact G.symm hw1s4
            | exact G.symm hw1t2
            | exact h
            | exact G.symm h
        · have hw1_ne_s4 : w1 ≠ s4 := G.ne_of_adj hw1s4
          have hw1_ne_t2 : w1 ≠ t2 := G.ne_of_adj hw1t2
          have hs4_ne_t2 : s4 ≠ t2 := by
            intro h_eq
            have ht2_in_N : t2 ∈ N := h_eq ▸ hs4_in_N
            have ht2_in_Q : t2 ∈ Q := (Finset.mem_filter.mp ht2_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht2_in_N ht2_in_Q
          simp [hw1_ne_s4, hw1_ne_t2, hs4_ne_t2]
      exact h_tri _ h_clique
    have hs4_nonadj_t3 : ¬G.Adj s4 t3 := by
      intro h
      have h_clique : G.IsNClique 3 {w1, s4, t3} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hw1s4
            | exact hw1_adj_t3
            | exact G.symm hw1s4
            | exact G.symm hw1_adj_t3
            | exact h
            | exact G.symm h
        · have hw1_ne_s4 : w1 ≠ s4 := G.ne_of_adj hw1s4
          have hw1_ne_t3 : w1 ≠ t3 := G.ne_of_adj hw1_adj_t3
          have hs4_ne_t3 : s4 ≠ t3 := by
            intro h_eq
            have ht3_in_N : t3 ∈ N := h_eq ▸ hs4_in_N
            have ht3_in_Q : t3 ∈ Q := (Finset.mem_filter.mp ht3_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht3_in_N ht3_in_Q
          simp [hw1_ne_s4, hw1_ne_t3, hs4_ne_t3]
      exact h_tri _ h_clique
    have hs4_nonadj_t4 : ¬G.Adj s4 t4 := by
      intro h
      have h_clique : G.IsNClique 3 {p4, s4, t4} := by
        rw [SimpleGraph.isNClique_iff]
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          all_goals
            first
            | exact absurd rfl hxy
            | exact hs4_adj_p4
            | exact hp4_adj_t4
            | exact G.symm hs4_adj_p4
            | exact G.symm hp4_adj_t4
            | exact h
            | exact G.symm h
        · have hp4_ne_s4 : p4 ≠ s4 := G.ne_of_adj (G.symm hs4_adj_p4)
          have hp4_ne_t4 : p4 ≠ t4 := G.ne_of_adj hp4_adj_t4
          have hs4_ne_t4 : s4 ≠ t4 := by
            intro h_eq
            have ht4_in_N : t4 ∈ N := h_eq ▸ hs4_in_N
            have ht4_in_Q : t4 ∈ Q := (Finset.mem_filter.mp ht4_in_T).1
            exact (Finset.disjoint_left.mp hNv_Q_disj) ht4_in_N ht4_in_Q
          simp [hp4_ne_s4, hp4_ne_t4, hs4_ne_t4]
      exact h_tri _ h_clique
    have hs4_adj_t1 : G.Adj s4 t1 := by
      by_contra hnot
      have : (T.filter (G.Adj s4)).card = 0 := by
        have : (T.filter (G.Adj s4)) = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
          intro hx
          rw [hT_eq] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hnot
          · exact hs4_nonadj_t2
          · exact hs4_nonadj_t3
          · exact hs4_nonadj_t4
        simpa [this]
      omega
    have hs4_nonadj_p1 : ¬G.Adj s4 p1 := by
      intro h
      have h_and : s4 ∈ G.neighborFinset v ∧ G.Adj s4 p1 := ⟨hs4_in_N, h⟩
      have : s4 = s1 := hs1_unique s4 h_and
      exact hs_ne14 (this.symm)
    have hsubset : ({p4, w1, t1} : Finset (Fin 18)) ⊆ (G.neighborFinset s4 ∩ G.neighborFinset p1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hs4_adj_p4, G.symm h_adj41⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨G.symm hw1s4, hp1_adj_w1⟩
      · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
        exact ⟨hs4_adj_t1, hp1_adj_t1⟩
    have hcard3 : 3 ≤ commonNeighborsCard G s4 p1 := by
      have : ({p4, w1, t1} : Finset (Fin 18)).card ≤ (G.neighborFinset s4 ∩ G.neighborFinset p1).card :=
        Finset.card_le_card hsubset
      have hp4_ne_w1 : p4 ≠ w1 := fun h =>
        Finset.disjoint_left.mp hP_Q_disj hp4_in_P (h ▸ hw1_in_Q)
      have hp4_ne_t1 : p4 ≠ t1 := by
        intro h
        subst h
        have : p4 ∈ Q := (Finset.mem_filter.mp ht1_in_T).1
        exact (Finset.disjoint_left.mp hP_Q_disj) hp4_in_P this
      have hw1_ne_t1 : w1 ≠ t1 := fun h_eq =>
        hw1_nonadj_t (h_eq ▸ ht1_adj_t)
      have h3 : ({p4, w1, t1} : Finset (Fin 18)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact hw1_ne_t1
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp4_ne_w1, hp4_ne_t1⟩
      have : 3 ≤ (G.neighborFinset s4 ∩ G.neighborFinset p1).card := by
        simpa [h3] using this
      simpa [commonNeighborsCard, _root_.commonNeighbors] using this
    have h_le := commonNeighborsCard_le_two h_tri h_no6 h_reg s4 p1 hs4_ne_p1.symm hs4_nonadj_p1
    omega

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
