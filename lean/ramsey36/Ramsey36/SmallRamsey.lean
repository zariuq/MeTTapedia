import Ramsey36.Basic
import Mathlib.Tactic

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
            simpa [h]
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
            simpa [h]
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
            simpa [h]
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
            simpa [h]
          exact hs.1 hx' hy' hne
        · simpa using hs.2
      exact not_hasRamseyProperty_35 (Or.inr ⟨s.map f, h_indep⟩)

/-
# Upper bounds (placeholders)
-/

theorem hasRamseyProperty_3_4_9 :
    0 < 9 ∧ ∀ (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G := by
  -- Temporary: derive from the axiom in `Basic` until the constructive proof is available.
  simpa using (ramsey_of_ramseyNumber_eq ramsey_three_four)

theorem hasRamseyProperty_3_5_14 :
    0 < 14 ∧ ∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G := by
  -- Temporary: derive from the axiom in `Basic` until the constructive proof is available.
  simpa using (ramsey_of_ramseyNumber_eq ramsey_three_five)

/-! ## Small Ramsey equalities -/

theorem ramsey_three_four_proof : ramseyNumber 3 4 = 9 := by
  apply Nat.le_antisymm
  · -- upper bound
    have h_mem : 9 ∈ {n : ℕ |
        n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G} := by
      constructor
      · exact hasRamseyProperty_3_4_9.1
      · intro G hG; simpa using hasRamseyProperty_3_4_9.2 G
    apply csInf_le
    · refine ⟨9, ?_⟩
      exact h_mem
    · exact h_mem
  · -- lower bound
    have h_nonempty :
        Set.Nonempty {n : ℕ |
          n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 4 G} :=
      ⟨9, hasRamseyProperty_3_4_9⟩
    exact ramsey_three_four_ge_9_of_nonempty h_nonempty

theorem ramsey_three_five_proof : ramseyNumber 3 5 = 14 := by
  apply Nat.le_antisymm
  · -- upper bound
    have h_mem : 14 ∈ {n : ℕ |
        n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G} := by
      constructor
      · exact hasRamseyProperty_3_5_14.1
      · intro G hG; simpa using hasRamseyProperty_3_5_14.2 G
    apply csInf_le
    · refine ⟨14, ?_⟩
      exact h_mem
    · exact h_mem
  · -- lower bound
    have h_nonempty :
        Set.Nonempty {n : ℕ |
          n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 5 G} :=
      ⟨14, hasRamseyProperty_3_5_14⟩
    exact ramsey_three_five_ge_14_of_nonempty h_nonempty
