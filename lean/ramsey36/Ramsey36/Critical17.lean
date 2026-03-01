/-
# The 17-Vertex Critical Graph for R(3,6)

This file defines the Graver-Yackel graph: one of the 7 non-isomorphic
triangle-free graphs on 17 vertices with independence number α = 5.

## LLM Notes
- The full `decide` on `hasIndepSet 17 adj17Bool 6` causes kernel OOM.
- Fix: IndepSplit.lean splits into 12 sub-problems (~7.7s total).
- adj17Bool_spec uses `decide` on 289 pairs (fast: O(5) work each).
- adj17NotBool_spec similarly bridges the complement for triangle-free.
- IndepSetChecker.lean provides bridge theorems with explicit adj argument.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Ramsey36.Basic
import Ramsey36.IndepSetBridge
import Ramsey36.IndepSplit
import Ramsey36.IndepSmall

open SimpleGraph Finset

abbrev V := Fin 17

/-! ## Graph Definition -/

def neighbors17 (v : V) : Finset V :=
  if v = 0 then {9, 14, 15, 16}
  else if v = 1 then {7, 11, 13, 16}
  else if v = 2 then {8, 10, 12, 15}
  else if v = 3 then {6, 8, 13, 15, 16}
  else if v = 4 then {5, 7, 12, 14, 16}
  else if v = 5 then {4, 9, 10, 11, 13}
  else if v = 6 then {3, 10, 11, 12, 14}
  else if v = 7 then {1, 4, 9, 10, 15}
  else if v = 8 then {2, 3, 9, 11, 14}
  else if v = 9 then {0, 5, 7, 8, 12}
  else if v = 10 then {2, 5, 6, 7, 16}
  else if v = 11 then {1, 5, 6, 8, 15}
  else if v = 12 then {2, 4, 6, 9, 13}
  else if v = 13 then {1, 3, 5, 12, 14}
  else if v = 14 then {0, 4, 6, 8, 13}
  else if v = 15 then {0, 2, 3, 7, 11}
  else {0, 1, 3, 4, 10}  -- v = 16

def adj17 (v w : V) : Prop := w ∈ neighbors17 v

lemma neighbors17_symm (v w : V) : w ∈ neighbors17 v ↔ v ∈ neighbors17 w := by
  fin_cases v <;> fin_cases w <;> decide

def criticalGraph17 : SimpleGraph V where
  Adj := adj17
  symm := by
    intros v w h
    exact (neighbors17_symm v w).mp h
  loopless := by
    constructor; intro v h
    unfold adj17 neighbors17 at h
    fin_cases v <;> simp at h

/-! ## Decidability Instances -/

instance : DecidableRel criticalGraph17.Adj := by
  intro v w
  unfold criticalGraph17 adj17
  exact Finset.decidableMem w (neighbors17 v)

instance : Decidable (TriangleFree criticalGraph17) := by
  unfold TriangleFree CliqueFree
  infer_instance

instance : Decidable (NoKIndepSet 6 criticalGraph17) := by
  unfold NoKIndepSet IndepSetFree
  infer_instance

/-! ## Triangle-Free -/

/-- adj17Bool agrees with the Adj predicate of criticalGraph17 for all pairs. -/
private lemma adj17Bool_spec :
    ∀ v w : Fin 17, adj17Bool v w = decide (criticalGraph17.Adj v w) := by decide

/-- adj17NotBool agrees with the negated Adj predicate for all pairs. -/
private lemma adj17NotBool_spec :
    ∀ v w : Fin 17, adj17NotBool v w = !decide (criticalGraph17.Adj v w) := by decide

lemma criticalGraph17_triangleFree : TriangleFree criticalGraph17 :=
  triangleFree_of_adj_checker_false adj17NotBool_spec
    hasIndepSet_17_adj17NotBool_3_false

/-! ## No 6-Independent Set -/

/-- The Graver-Yackel graph has no 6-independent set. -/
lemma criticalGraph17_no_6_indep : NoKIndepSet 6 criticalGraph17 :=
  noKIndepSet_of_adj_checker_false adj17Bool_spec
    hasIndepSet_17_adj17Bool_6_false

/-! ## Ramsey Lower Bound -/

lemma not_hasRamseyProperty_17 : ¬ HasRamseyProperty 3 6 criticalGraph17 := by
  unfold HasRamseyProperty
  push_neg
  constructor
  · intro s h_clique
    exact criticalGraph17_triangleFree s h_clique
  · intro s h_indep
    exact criticalGraph17_no_6_indep s h_indep

theorem ramsey_three_six_ge_18_of_nonempty
    (h_nonempty : Set.Nonempty {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 6 G}) :
    18 ≤ ramseyNumber 3 6 := by
  apply le_csInf
  · exact h_nonempty
  · intro n hn
    rw [Set.mem_setOf_eq] at hn
    rcases hn with ⟨h_pos, h_forall⟩
    by_contra h_lt
    push_neg at h_lt
    have h_le : n ≤ 17 := Nat.le_of_lt_succ h_lt
    let f : Fin n ↪ Fin 17 := (Fin.castLEOrderEmb h_le).toEmbedding
    let G' := criticalGraph17.comap f
    have h_has := h_forall G'
    rcases h_has with ⟨s, h_clique⟩ | ⟨s, h_indep⟩
    · have h_clique' : criticalGraph17.IsNClique 3 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          simp at hx hy
          rcases hx with ⟨x', hx', rfl⟩
          rcases hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := fun h => hxy (congr_arg f h)
          exact h_clique.isClique hx' hy' hne
        · simp [h_clique.card_eq]
      exact not_hasRamseyProperty_17 (Or.inl ⟨s.map f, h_clique'⟩)
    · have h_indep' : criticalGraph17.IsNIndepSet 6 (s.map f) := by
        constructor
        · intro x hx y hy hxy
          simp at hx hy
          rcases hx with ⟨x', hx', rfl⟩
          rcases hy with ⟨y', hy', rfl⟩
          have hne : x' ≠ y' := fun h => hxy (congr_arg f h)
          exact h_indep.isIndepSet hx' hy' hne
        · simp [h_indep.card_eq]
      exact not_hasRamseyProperty_17 (Or.inr ⟨s.map f, h_indep'⟩)
