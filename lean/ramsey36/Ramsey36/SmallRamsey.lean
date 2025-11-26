import Ramsey36.Basic
import Mathlib.Tactic
import Hammer

open SimpleGraph
open Finset

/-
# Small Ramsey Numbers R(3,4) and R(3,5)

This file will eventually replace the axioms for small Ramsey numbers.
We start by setting up the 8-vertex critical graph for R(3,4) to support
the lower-bound proof.
-/

/-! ## Critical graph for R(3,4) -/

abbrev V34 := Fin 8

def neighbors34 : V34 → Finset V34
| 0 => {1, 7, 4}
| 1 => {0, 2, 5}
| 2 => {1, 3, 6}
| 3 => {2, 4, 7}
| 4 => {3, 5, 0}
| 5 => {4, 6, 1}
| 6 => {5, 7, 2}
| 7 => {6, 0, 3}

def adj34 (v w : V34) : Prop := w ∈ neighbors34 v

lemma neighbors34_symm (v w : V34) : w ∈ neighbors34 v ↔ v ∈ neighbors34 w := by
  fin_cases v <;> fin_cases w <;> decide

def critical34 : SimpleGraph V34 where
  Adj := adj34
  symm := by
    intro v w h
    exact (neighbors34_symm v w).mp h
  loopless := by
    intro v hv
    fin_cases v <;> simp [adj34, neighbors34] at hv

instance : DecidableRel critical34.Adj := by
  intro v w
  unfold critical34 adj34
  infer_instance

instance : Decidable (TriangleFree critical34) := by
  unfold TriangleFree CliqueFree
  infer_instance

instance : Decidable (NoKIndepSet 4 critical34) := by
  unfold NoKIndepSet IndepSetFree
  infer_instance

lemma critical34_triangleFree : TriangleFree critical34 := by
  native_decide

lemma critical34_no_4_indep : NoKIndepSet 4 critical34 := by
  native_decide

lemma not_hasRamseyProperty_34 : ¬ HasRamseyProperty 3 4 critical34 := by
  unfold HasRamseyProperty
  push_neg
  constructor
  · intro s hs
    exact critical34_triangleFree s hs
  · intro s hs
    exact critical34_no_4_indep s hs

/-! ## Critical graph for R(3,3) -/

/-- The 5-cycle C5 is the unique critical graph for R(3,3)=6 -/
abbrev V33 := Fin 5

def neighbors33 : V33 → Finset V33
| 0 => {1, 4}  -- Cycle: 0-1-2-3-4-0
| 1 => {0, 2}
| 2 => {1, 3}
| 3 => {2, 4}
| 4 => {3, 0}

def adj33 (v w : V33) : Prop := w ∈ neighbors33 v

lemma neighbors33_symm (v w : V33) : w ∈ neighbors33 v ↔ v ∈ neighbors33 w := by
  fin_cases v <;> fin_cases w <;> decide

def critical33 : SimpleGraph V33 where
  Adj := adj33
  symm := by
    intro v w h
    exact (neighbors33_symm v w).mp h
  loopless := by
    intro v hv
    fin_cases v <;> simp [adj33, neighbors33] at hv

instance : DecidableRel critical33.Adj := by
  intro v w
  unfold critical33 adj33
  infer_instance

instance : Decidable (TriangleFree critical33) := by
  unfold TriangleFree CliqueFree
  infer_instance

instance : Decidable (NoKIndepSet 3 critical33) := by
  unfold NoKIndepSet IndepSetFree
  infer_instance

lemma critical33_triangleFree : TriangleFree critical33 := by
  native_decide

lemma critical33_no_3_indep : NoKIndepSet 3 critical33 := by
  native_decide

lemma not_hasRamseyProperty_33 : ¬ HasRamseyProperty 3 3 critical33 := by
  unfold HasRamseyProperty
  push_neg
  constructor
  · intro s hs
    exact critical33_triangleFree s hs
  · intro s hs
    exact critical33_no_3_indep s hs

/-
# Critical graph for R(3,5)
-/

abbrev V35 := Fin 13

/-- H13: edges between vertices differing by ±1 or ±5 modulo 13. -/
def neighbors35 : V35 → Finset V35
| 0  => {1, 5, 8, 12}
| 1  => {0, 2, 6, 9}
| 2  => {1, 3, 7, 10}
| 3  => {2, 4, 8, 11}
| 4  => {3, 5, 9, 12}
| 5  => {0, 4, 6, 10}
| 6  => {1, 5, 7, 11}
| 7  => {2, 6, 8, 12}
| 8  => {0, 3, 7, 9}
| 9  => {1, 4, 8, 10}
| 10 => {2, 5, 9, 11}
| 11 => {3, 6, 10, 12}
| 12 => {0, 4, 7, 11}

def adj35 (v w : V35) : Prop := w ∈ neighbors35 v

lemma neighbors35_symm (v w : V35) : w ∈ neighbors35 v ↔ v ∈ neighbors35 w := by
  fin_cases v <;> fin_cases w <;> decide

def critical35 : SimpleGraph V35 where
  Adj := adj35
  symm := by
    intro v w h
    exact (neighbors35_symm v w).mp h
  loopless := by
    intro v hv
    fin_cases v <;> simp [adj35, neighbors35] at hv

instance : DecidableRel critical35.Adj := by
  intro v w
  unfold critical35 adj35
  infer_instance

instance : Decidable (TriangleFree critical35) := by
  unfold TriangleFree CliqueFree
  infer_instance

instance : Decidable (NoKIndepSet 5 critical35) := by
  unfold NoKIndepSet IndepSetFree
  infer_instance

lemma critical35_triangleFree : TriangleFree critical35 := by
  native_decide

lemma critical35_no_5_indep : NoKIndepSet 5 critical35 := by
  native_decide

/-- The critical 13-vertex graph does not have the Ramsey property (3,5). -/
lemma not_hasRamseyProperty_35 : ¬ HasRamseyProperty 3 5 critical35 := by
  unfold HasRamseyProperty
  push_neg
  constructor
  · intro s hs
    exact critical35_triangleFree s hs
  · intro s hs
    exact critical35_no_5_indep s hs

/-! ## Lower bounds from critical graphs -/

theorem ramsey_three_three_ge_6_of_nonempty
    (h_nonempty :
      Set.Nonempty {n : ℕ |
        n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 3 G}) :
    6 ≤ ramseyNumber 3 3 := by
  apply le_csInf
  · exact h_nonempty
  · intro n hn
    rcases hn with ⟨h_pos, h_forall⟩
    by_contra h_lt
    have h_le : n ≤ 5 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h_lt)
    let f : Fin n ↪ Fin 5 := (Fin.castLEOrderEmb h_le).toEmbedding
    let G' := critical33.comap f
    have h_has := h_forall G'
    rcases h_has with ⟨s, hs⟩ | ⟨s, hs⟩
    · -- 3-clique lifts to 3-clique in critical33
      have h_clique : critical33.IsNClique 3 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_33 (Or.inl ⟨s.map f, h_clique⟩)
    · -- 3-indep lifts to 3-indep in critical33
      have h_indep : critical33.IsNIndepSet 3 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_33 (Or.inr ⟨s.map f, h_indep⟩)

theorem ramsey_three_four_ge_9_of_nonempty
    (h_nonempty :
      Set.Nonempty {n : ℕ |
        n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G}) :
    9 ≤ ramseyNumber 3 4 := by
  apply le_csInf
  · exact h_nonempty
  · intro n hn
    rcases hn with ⟨h_pos, h_forall⟩
    by_contra h_lt
    have h_le : n ≤ 8 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h_lt)
    let f : Fin n ↪ Fin 8 := (Fin.castLEOrderEmb h_le).toEmbedding
    let G' := critical34.comap f
    have h_has := h_forall G'
    rcases h_has with ⟨s, hs⟩ | ⟨s, hs⟩
    · -- 3-clique lifts to 3-clique in critical34
      have h_clique : critical34.IsNClique 3 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_34 (Or.inl ⟨s.map f, h_clique⟩)
    · -- 4-indep lifts to 4-indep in critical34
      have h_indep : critical34.IsNIndepSet 4 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_34 (Or.inr ⟨s.map f, h_indep⟩)

theorem ramsey_three_five_ge_14_of_nonempty
    (h_nonempty :
      Set.Nonempty {n : ℕ |
        n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G}) :
    14 ≤ ramseyNumber 3 5 := by
  apply le_csInf
  · exact h_nonempty
  · intro n hn
    rcases hn with ⟨h_pos, h_forall⟩
    by_contra h_lt
    have h_le : n ≤ 13 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h_lt)
    let f : Fin n ↪ Fin 13 := (Fin.castLEOrderEmb h_le).toEmbedding
    let G' := critical35.comap f
    have h_has := h_forall G'
    rcases h_has with ⟨s, hs⟩ | ⟨s, hs⟩
    · -- 3-clique lifts to 3-clique in critical35
      have h_clique : critical35.IsNClique 3 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_35 (Or.inl ⟨s.map f, h_clique⟩)
    · -- 5-indep lifts to 5-indep in critical35
      have h_indep : critical35.IsNIndepSet 5 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := by
            intro h
            apply hxy
            ext
            simp [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_35 (Or.inr ⟨s.map f, h_indep⟩)

/-
# Upper bounds (placeholders)
-/

set_option maxHeartbeats 400000

theorem hasRamseyProperty_3_3_6 :
    0 < 6 ∧ ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj], HasRamseyProperty 3 3 G := by
  -- Classical R(3,3)=6 proof using pigeonhole principle + Hammer
  constructor
  · norm_num
  · intro G _
    unfold HasRamseyProperty
    let v : Fin 6 := 0
    let others := (Finset.univ : Finset (Fin 6)).erase v
    let adjacent := others.filter (fun u => G.Adj v u)
    let nonadjacent := others.filter (fun u => ¬ G.Adj v u)

    have h_others_card : others.card = 5 := by
      simp only [others, Finset.card_erase_of_mem, Finset.mem_univ]
      norm_num
    have h_partition : adjacent ∪ nonadjacent = others := by
      ext u; simp [adjacent, nonadjacent]; tauto
    have h_disjoint : Disjoint adjacent nonadjacent := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext u
      simp [adjacent, nonadjacent]
      tauto
    have h_sum : adjacent.card + nonadjacent.card = 5 := by
      have := Finset.card_union_of_disjoint h_disjoint
      rw [h_partition] at this; rw [← this, h_others_card]
    have h_pigeon : adjacent.card ≥ 3 ∨ nonadjacent.card ≥ 3 := by omega

    -- Case analysis on which has ≥3 vertices
    rcases h_pigeon with h_adj | h_nonadj

    · -- Case 1: ≥3 vertices adjacent to v
      obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_adj
      -- If S has an edge, get clique with v. Else S is independent.
      by_cases h_edge : ∃ (a b : Fin 6), a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ G.Adj a b
      · -- S has edge → clique
        obtain ⟨a, b, ha, hb, hab, h_ab⟩ := h_edge
        left
        use {v, a, b}
        -- {v,a,b} is a clique: v-a, v-b, a-b all connected
        constructor
        · -- All pairs connected
          intro x hx y hy hxy
          -- v is adjacent to both a and b (from S ⊆ adjacent)
          have hv_a : G.Adj v a := by
            have : a ∈ adjacent := hS_sub ha
            exact Finset.mem_filter.mp this |>.2
          have hv_b : G.Adj v b := by
            have : b ∈ adjacent := hS_sub hb
            exact Finset.mem_filter.mp this |>.2
          simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
          obtain (rfl | rfl | rfl) := hx
          <;> obtain (rfl | rfl | rfl) := hy
          · contradiction
          · exact hv_a
          · exact hv_b
          · exact G.symm hv_a
          · contradiction
          · exact h_ab
          · exact G.symm hv_b
          · exact G.symm h_ab
          · contradiction
        · -- Cardinality = 3
          have hv_ne_a : v ≠ a := by
            intro h_eq
            have ha_adj : a ∈ adjacent := hS_sub ha
            have : a ∈ others := Finset.mem_filter.mp ha_adj |>.1
            rw [← h_eq] at this
            simp [others] at this
          have hv_ne_b : v ≠ b := by
            intro h_eq
            have hb_adj : b ∈ adjacent := hS_sub hb
            have : b ∈ others := Finset.mem_filter.mp hb_adj |>.1
            rw [← h_eq] at this
            simp [others] at this
          simp [hv_ne_a, hv_ne_b, hab]
      · -- S has no edges → independent
        push_neg at h_edge
        right
        use S
        constructor
        · -- S is independent
          intro x hx y hy hxy h_adj
          exact h_edge x y hx hy hxy h_adj
        · -- Cardinality = 3
          exact hS_card

    · -- Case 2: ≥3 vertices non-adjacent to v
      obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_nonadj
      by_cases h_edge : ∃ (a b : Fin 6), a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ G.Adj a b
      · -- S has edge a-b → find third vertex c, analyze triangle
        obtain ⟨a, b, ha, hb, hab, h_ab⟩ := h_edge
        -- S has 3 vertices, get third vertex c
        have h_exists_c : ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
          by_contra h_not
          push_neg at h_not
          have : S ⊆ {a, b} := by
            intro x hx
            by_cases hxa : x = a
            · simp [hxa]
            · have := h_not x hx hxa
              simp [this]
          have : S.card ≤ 2 := by
            calc S.card ≤ ({a, b} : Finset (Fin 6)).card := Finset.card_le_card this
              _ ≤ 2 := by simp [hab]
          omega
        obtain ⟨c, hc, hca, hcb⟩ := h_exists_c
        -- Check if a-c or b-c edges exist
        by_cases h_ac : G.Adj a c
        · by_cases h_bc : G.Adj b c
          · -- All edges exist: {a,b,c} is 3-clique
            left
            use {a, b, c}
            constructor
            · intro x hx y hy hxy
              simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
              obtain (rfl | rfl | rfl) := hx
              <;> obtain (rfl | rfl | rfl) := hy
              · contradiction
              · exact h_ab
              · exact h_ac
              · exact G.symm h_ab
              · contradiction
              · exact h_bc
              · exact G.symm h_ac
              · exact G.symm h_bc
              · contradiction
            · simp [Ne.symm hca, Ne.symm hcb, hab]
          · -- a-b, a-c exist but not b-c: {v,b,c} is independent
            have hv_b : ¬ G.Adj v b := (Finset.mem_filter.mp (hS_sub hb)).2
            have hv_c : ¬ G.Adj v c := (Finset.mem_filter.mp (hS_sub hc)).2
            right
            use {v, b, c}
            constructor
            · intro x hx y hy hxy h_adj
              simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
              obtain (rfl | rfl | rfl) := hx
              <;> obtain (rfl | rfl | rfl) := hy
              · contradiction
              · exact hv_b h_adj
              · exact hv_c h_adj
              · exact hv_b (G.symm h_adj)
              · contradiction
              · exact h_bc h_adj
              · exact hv_c (G.symm h_adj)
              · exact h_bc (G.symm h_adj)
              · contradiction
            · have hv_ne_b : v ≠ b := by
                intro h_eq
                have : b ∈ others := Finset.mem_filter.mp (hS_sub hb) |>.1
                rw [← h_eq] at this
                simp [others] at this
              have hv_ne_c : v ≠ c := by
                intro h_eq
                have : c ∈ others := Finset.mem_filter.mp (hS_sub hc) |>.1
                rw [← h_eq] at this
                simp [others] at this
              simp [hv_ne_b, hv_ne_c, Ne.symm hcb]
        · by_cases h_bc : G.Adj b c
          · -- a-b, b-c exist but not a-c: {v,a,c} is independent
            have hv_a : ¬ G.Adj v a := (Finset.mem_filter.mp (hS_sub ha)).2
            have hv_c : ¬ G.Adj v c := (Finset.mem_filter.mp (hS_sub hc)).2
            right
            use {v, a, c}
            constructor
            · intro x hx y hy hxy h_adj
              simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
              obtain (rfl | rfl | rfl) := hx
              <;> obtain (rfl | rfl | rfl) := hy
              · contradiction
              · exact hv_a h_adj
              · exact hv_c h_adj
              · exact hv_a (G.symm h_adj)
              · contradiction
              · exact h_ac h_adj
              · exact hv_c (G.symm h_adj)
              · exact h_ac (G.symm h_adj)
              · contradiction
            · have hv_ne_a : v ≠ a := by
                intro h_eq
                have : a ∈ others := Finset.mem_filter.mp (hS_sub ha) |>.1
                rw [← h_eq] at this
                simp [others] at this
              have hv_ne_c : v ≠ c := by
                intro h_eq
                have : c ∈ others := Finset.mem_filter.mp (hS_sub hc) |>.1
                rw [← h_eq] at this
                simp [others] at this
              simp [hv_ne_a, hv_ne_c, Ne.symm hca]
          · -- Only a-b exists: {v,a,c} is independent
            have hv_a : ¬ G.Adj v a := (Finset.mem_filter.mp (hS_sub ha)).2
            have hv_c : ¬ G.Adj v c := (Finset.mem_filter.mp (hS_sub hc)).2
            right
            use {v, a, c}
            constructor
            · intro x hx y hy hxy h_adj
              simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
              obtain (rfl | rfl | rfl) := hx
              <;> obtain (rfl | rfl | rfl) := hy
              · contradiction
              · exact hv_a h_adj
              · exact hv_c h_adj
              · exact hv_a (G.symm h_adj)
              · contradiction
              · exact h_ac h_adj
              · exact hv_c (G.symm h_adj)
              · exact h_ac (G.symm h_adj)
              · contradiction
            · have hv_ne_a : v ≠ a := by
                intro h_eq
                have : a ∈ others := Finset.mem_filter.mp (hS_sub ha) |>.1
                rw [← h_eq] at this
                simp [others] at this
              have hv_ne_c : v ≠ c := by
                intro h_eq
                have : c ∈ others := Finset.mem_filter.mp (hS_sub hc) |>.1
                rw [← h_eq] at this
                simp [others] at this
              simp [hv_ne_a, hv_ne_c, Ne.symm hca]
      · -- S has no edges → independent
        push_neg at h_edge
        right
        use S
        constructor
        · intro x hx y hy hxy h_adj
          exact h_edge x y hx hy hxy h_adj
        · exact hS_card

/-! ## Small Ramsey equalities -/

theorem ramsey_three_three_proof : ramseyNumber 3 3 = 6 := by
  apply Nat.le_antisymm
  · -- upper bound
    apply csInf_le
    · use 0
      intro n hn
      exact Nat.zero_le n
    · constructor
      · exact hasRamseyProperty_3_3_6.1
      · intro G hG; simpa using hasRamseyProperty_3_3_6.2 G
  · -- lower bound
    have h_nonempty :
        Set.Nonempty {n : ℕ |
          n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 3 G} :=
      ⟨6, hasRamseyProperty_3_3_6⟩
    exact ramsey_three_three_ge_6_of_nonempty h_nonempty

/-! ## Degree lower bound via R(3,3)=6 (Krüger's approach) -/

/-- In a 9-vertex triangle-free graph with no 4-independent set,
    every vertex has degree at least 3.

    Proof strategy: If deg(v) ≤ 2, then the non-neighbors of v form
    a set H of size ≥ 6. By R(3,3)=6, any 6-element subset of H
    contains either a 3-clique or a 3-independent set.
    - A 3-clique in H (all non-adjacent to v) extends to a 3-clique in G
    - A 3-independent set in H extends to a 4-independent set in G
      (adding v, which is non-adjacent to all of H)
    Both cases contradict our assumptions. -/
lemma degree_ge_three_of_triangleFree_no_4indep
    {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no4 : NoKIndepSet 4 G)
    (v : Fin 9) :
    G.degree v ≥ 3 := by
  -- Proof by contradiction: assume deg(v) ≤ 2
  by_contra h_not
  push_neg at h_not
  have h_deg_le_2 : G.degree v ≤ 2 := Nat.lt_succ_iff.mp h_not

  -- The non-neighbors of v (excluding v itself) form a set H of size ≥ 6
  -- Non-neighbors = all vertices except v and neighbors of v
  let H := (Finset.univ : Finset (Fin 9)) \ (insert v (G.neighborFinset v))

  have h_H_card : H.card ≥ 6 := by
    -- |H| = 9 - |{v} ∪ neighbors(v)| = 9 - (1 + deg(v)) ≥ 9 - 3 = 6
    have h_union_card : (insert v (G.neighborFinset v)).card ≤ 3 := by
      calc (insert v (G.neighborFinset v)).card
          = (G.neighborFinset v).card + 1 := by
            rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
        _ = G.degree v + 1 := by rw [G.card_neighborFinset_eq_degree]
        _ ≤ 2 + 1 := by omega
        _ = 3 := by norm_num
    -- H and (insert v neighbors) partition univ
    -- So |H| = 9 - |insert v neighbors| ≥ 9 - 3 = 6
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
    have h_card_union : H.card + (insert v (G.neighborFinset v)).card = 9 := by
      have h_eq : (H ∪ (insert v (G.neighborFinset v))).card =
                   H.card + (insert v (G.neighborFinset v)).card :=
        Finset.card_union_of_disjoint h_disjoint
      rw [h_union] at h_eq
      have : (Finset.univ : Finset (Fin 9)).card = 9 := by simp [Fintype.card_fin]
      rw [this] at h_eq
      exact h_eq.symm
    -- Therefore |H| ≥ 9 - 3 = 6 since |H| + |insert v neighbors| = 9
    calc H.card
        = 9 - (insert v (G.neighborFinset v)).card := by
          have := h_card_union
          have := h_union_card
          omega
      _ ≥ 9 - 3 := by
          have := h_union_card
          omega
      _ = 6 := by norm_num

  -- Extract a 6-element subset H6 from H
  obtain ⟨H6, hH6_sub, hH6_card⟩ := Finset.exists_subset_card_eq h_H_card

  -- Key: v is not adjacent to any vertex in H6 (by definition of H)
  have h_v_nonadj_H6 : ∀ w ∈ H6, ¬ G.Adj v w := by
    intro w hw h_adj
    have hw_in_H : w ∈ H := hH6_sub hw
    simp only [H, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw_in_H
    apply hw_in_H
    apply Finset.mem_insert_of_mem
    rw [mem_neighborFinset]
    exact h_adj

  -- Apply R(3,3)=6: any 6-vertex graph has a 3-clique or 3-independent set
  -- Create induced subgraph on H6 via comap
  -- We need an embedding f : Fin 6 ↪ Fin 9 that maps onto H6
  have h_H6_card_type : Fintype.card (↑H6 : Set (Fin 9)) = 6 := by
    simp [Fintype.card_coe, hH6_card]

  -- Since |H6| = 6, there exists a bijection Fin 6 ≃ ↑H6
  have h_card_eq : Fintype.card (Fin 6) = Fintype.card (↑H6 : Set (Fin 9)) := by
    simp only [Fintype.card_fin]
    exact h_H6_card_type.symm
  let e : Fin 6 ≃ (↑H6 : Set (Fin 9)) := Fintype.equivOfCardEq h_card_eq
  -- Compose with subtype embedding to get Fin 6 ↪ Fin 9
  let f : Fin 6 ↪ Fin 9 := e.toEmbedding.trans (Function.Embedding.subtype _)

  -- Create the induced subgraph
  let G_H6 := G.comap f

  -- Apply R(3,3)=6 to G_H6
  have h_ramsey_prop : HasRamseyProperty 3 3 G_H6 := by
    exact (ramsey_of_ramseyNumber_eq ramsey_three_three_proof).2 G_H6
  rcases h_ramsey_prop with ⟨S, hS⟩ | ⟨T, hT⟩

  · -- Case 1: G_H6 contains a 3-clique S
    -- This lifts to a 3-clique in G, contradicting h_tri
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

  · -- Case 2: G_H6 contains a 3-independent set T
    -- T ∪ {v} is a 4-independent set in G
    let T_plus_v := insert v (T.map f)
    have h_indep_4 : G.IsNIndepSet 4 T_plus_v := by
      constructor
      · -- Show T_plus_v is independent
        intro x hx y hy hxy h_adj
        -- Cases: x = v or x ∈ T.map f, and y = v or y ∈ T.map f
        show False
        have hx' : x = v ∨ x ∈ T.map f := Finset.mem_insert.mp hx
        have hy' : y = v ∨ y ∈ T.map f := Finset.mem_insert.mp hy
        rcases hx' with rfl | hx_in_T <;> rcases hy' with rfl | hy_in_T
        · -- x = v, y = v: contradicts hxy
          exact hxy rfl
        · -- x = v, y ∈ T.map f: x (which is v) not adjacent to y in T.map f
          -- T.map f ⊆ H6, and v is not adjacent to H6
          -- y is in T.map f, which means y = f(y') for some y' in T
          have : y ∈ (↑H6 : Set (Fin 9)) := by
            rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
            -- f y' = (e y').val by definition of f
            show (f y') ∈ ↑H6
            change (e y').val ∈ ↑H6
            exact (e y').property
          have h_x_nonadj_y : ¬ G.Adj x y := h_v_nonadj_H6 y this
          exact h_x_nonadj_y h_adj
        · -- x ∈ T.map f, y = v: symmetric case
          have : x ∈ (↑H6 : Set (Fin 9)) := by
            rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
            show (f x') ∈ ↑H6
            change (e x').val ∈ ↑H6
            exact (e x').property
          have h_y_nonadj_x : ¬ G.Adj y x := h_v_nonadj_H6 x this
          exact h_y_nonadj_x (G.symm h_adj)
        · -- x, y ∈ T.map f: T is independent in G_H6, lifts to G
          -- Need to show: x and y not adjacent in G
          -- Since they map from T via f, and T is independent in G_H6
          rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
          rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
          have hne : x' ≠ y' := by
            intro h_eq
            apply hxy
            simp [h_eq]
          have h_not_adj_H6 : ¬ G_H6.Adj x' y' := hT.1 hx'_in_T hy'_in_T hne
          -- G_H6.Adj x' y' ↔ G.Adj (f x') (f y') by definition of comap
          exact h_not_adj_H6 h_adj
      · -- Show |T_plus_v| = 4
        -- T_plus_v = insert v (T.map f)
        -- |T_plus_v| = |T.map f| + 1 (since v ∉ T.map f) = |T| + 1 = 3 + 1 = 4
        have h_v_not_in_Tmap : v ∉ T.map f := by
          intro h_v_in
          -- v is in T.map f, so v = f(t) for some t in T
          -- But f maps into H6, and v is not in H
          rcases Finset.mem_map.mp h_v_in with ⟨t, ht_in_T, h_v_eq_ft⟩
          have h_ft_in_H6 : f t ∈ (↑H6 : Set (Fin 9)) := by
            show (f t) ∈ ↑H6
            change (e t).val ∈ ↑H6
            exact (e t).property
          -- Since f t = v, we have v ∈ (↑H6 : Set), which means v ∈ H6 (Finset)
          have h_v_in_H6 : v ∈ H6 := by
            rw [← h_v_eq_ft]
            exact h_ft_in_H6
          -- Since H6 ⊆ H, we have v ∈ H
          have h_v_in_H : v ∈ H := hH6_sub h_v_in_H6
          -- But v ∉ H by definition (H = univ \ (insert v neighbors))
          have h_v_not_in_H : v ∉ H := by
            intro h_absurd
            simp only [H, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert_self,
                       not_true_eq_false, and_false] at h_absurd
          exact h_v_not_in_H h_v_in_H
        calc T_plus_v.card
            = (T.map f).card + 1 := by
              show (insert v (T.map f)).card = _
              rw [Finset.card_insert_of_notMem h_v_not_in_Tmap]
          _ = T.card + 1 := by rw [Finset.card_map]
          _ = 3 + 1 := by rw [hT.2]
          _ = 4 := by norm_num
    exact h_no4 T_plus_v h_indep_4

/-! ## Parity contradiction: No 3-regular graph on 9 vertices -/

/-- A graph is 3-regular if every vertex has degree exactly 3 -/
def IsThreeRegular (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] : Prop :=
  ∀ v : Fin 9, G.degree v = 3

/-- In a 3-regular graph on 9 vertices, the sum of degrees is 27 (odd) -/
lemma odd_sum_degrees_of_three_regular
    {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (h_reg : IsThreeRegular G) :
    Odd (∑ v : Fin 9, G.degree v) := by
  have h_sum : ∑ v : Fin 9, G.degree v = 27 := by
    calc ∑ v : Fin 9, G.degree v
        = ∑ _v : Fin 9, 3 := by
          congr 1
          ext v
          exact h_reg v
      _ = 3 * (Finset.univ : Finset (Fin 9)).card := by
          rw [Finset.sum_const]
          ring
      _ = 3 * 9 := by simp [Fintype.card_fin]
      _ = 27 := by norm_num
  rw [h_sum]
  decide

/-- The sum of degrees in any graph is even (equals 2|E|) -/
lemma even_sum_degrees {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj] :
    Even (∑ v : Fin 9, G.degree v) := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-- No 3-regular graph exists on 9 vertices (parity contradiction) -/
lemma false_of_three_regular
    {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (h_reg : IsThreeRegular G) :
    False := by
  have h_odd := odd_sum_degrees_of_three_regular h_reg
  have h_even := even_sum_degrees (G := G)
  cases h_odd with
  | intro k hk =>
    cases h_even with
    | intro m hm =>
      rw [hk] at hm
      omega

/-! ## 3-Regularity: Combining degree bounds -/

/-- In a 9-vertex triangle-free graph with no 4-independent set,
    every vertex has degree exactly 3.

    This combines:
    - Upper bound: deg(v) ≤ 3 (from degree_le_of_triangleFree_no_indep)
    - Lower bound: deg(v) ≥ 3 (from degree_ge_three_of_triangleFree_no_4indep)
    -/
theorem three_regular_of_triangleFree_no_4indep
    {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no4 : NoKIndepSet 4 G) :
    IsThreeRegular G := by
  intro v

  -- Upper bound: deg(v) ≤ 3
  have h_ub : G.degree v ≤ 3 :=
    degree_le_of_triangleFree_no_indep h_tri h_no4 v

  -- Lower bound: deg(v) ≥ 3
  have h_lb : G.degree v ≥ 3 :=
    degree_ge_three_of_triangleFree_no_4indep h_tri h_no4 v

  -- Conclude equality
  omega

/-! ## Main contradiction and constructive upper bound for R(3,4)=9 -/

/-- No 9-vertex graph can be both triangle-free and have no 4-independent set.

    Proof: Such a graph would be 3-regular (by three_regular_of_triangleFree_no_4indep),
    but no 3-regular graph exists on 9 vertices (by false_of_three_regular).
    -/
theorem no_triangleFree_no_4indep_on_9
    {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no4 : NoKIndepSet 4 G) :
    False := by
  -- Prove 3-regular
  have h_reg : IsThreeRegular G :=
    three_regular_of_triangleFree_no_4indep h_tri h_no4

  -- Apply parity contradiction
  exact false_of_three_regular h_reg

/-
# Upper bounds continued (R(3,4) and R(3,5))
-/

theorem hasRamseyProperty_3_4_9 :
    0 < 9 ∧ ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G := by
  -- Krüger's proof (FULLTEXT01.txt lines 510-520):
  -- Assume G is (3,4;9)-graph. Then for all v: deg(v) ≥ 3 (by R(3,3)=6)
  -- and N(v) is independent (triangle-free), so |N(v)| < 4.
  -- Therefore G is 3-regular, which is impossible on 9 vertices (parity).
  constructor
  · norm_num
  · intro G _
    unfold HasRamseyProperty
    by_contra h_not
    push_neg at h_not
    obtain ⟨h_no_clique, h_no_indep⟩ := h_not
    have h_tri : TriangleFree G := by
      intro s hs
      exact h_no_clique s hs
    have h_no4 : NoKIndepSet 4 G := h_no_indep
    exact no_triangleFree_no_4indep_on_9 h_tri h_no4

theorem hasRamseyProperty_3_5_14 :
    0 < 14 ∧ ∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G := by
  -- Temporary: derive from the axiom in `Basic` until the constructive proof is available.
  simpa using (ramsey_of_ramseyNumber_eq ramsey_three_five)

/-! ## Small Ramsey equalities (continued) -/

theorem ramsey_three_four_proof : ramseyNumber 3 4 = 9 := by
  apply Nat.le_antisymm
  · -- upper bound
    apply csInf_le
    · use 0
      intro n hn
      exact Nat.zero_le n
    · constructor
      · exact hasRamseyProperty_3_4_9.1
      · intro G hG; simpa using hasRamseyProperty_3_4_9.2 G
  · -- lower bound
    have h_nonempty :
        Set.Nonempty {n : ℕ |
          n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G} :=
      ⟨9, hasRamseyProperty_3_4_9⟩
    exact ramsey_three_four_ge_9_of_nonempty h_nonempty

theorem ramsey_three_five_proof : ramseyNumber 3 5 = 14 := by
  apply Nat.le_antisymm
  · -- upper bound
    apply csInf_le
    · use 0
      intro n hn
      exact Nat.zero_le n
    · constructor
      · exact hasRamseyProperty_3_5_14.1
      · intro G hG; simpa using hasRamseyProperty_3_5_14.2 G
  · -- lower bound
    have h_nonempty :
        Set.Nonempty {n : ℕ |
          n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G} :=
      ⟨14, hasRamseyProperty_3_5_14⟩
    exact ramsey_three_five_ge_14_of_nonempty h_nonempty
