/-
# Ramsey Number Definitions

Core definitions for Ramsey theory, with NO axioms.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Ramsey Property -/

def HasRamseyProperty (k l : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∃ s : Finset V, G.IsNClique k s) ∨ (∃ s : Finset V, G.IsNIndepSet l s)

noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G}

/-! ## Graph Properties -/

abbrev TriangleFree (G : SimpleGraph V) : Prop := G.CliqueFree 3
abbrev NoKIndepSet (k : ℕ) (G : SimpleGraph V) : Prop := G.IndepSetFree k

abbrev IsKRegular (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  G.IsRegularOfDegree k

def commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) : Finset V :=
  G.neighborFinset v ∩ G.neighborFinset w

def commonNeighborsCard (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) : ℕ :=
  (_root_.commonNeighbors G v w).card

/-! ## Helper Lemmas -/

open Finset in
omit [Fintype V] in
lemma neighborSet_indep_of_triangleFree {G : SimpleGraph V} (h : TriangleFree G) (v : V) :
    G.IsIndepSet (G.neighborSet v) := by
  intros x hx y hy hne
  by_contra h_adj
  simp only [mem_neighborSet] at hx hy
  let s : Finset V := {v, x, y}
  have h_v_not_mem : v ∉ ({x, y} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨G.ne_of_adj hx, G.ne_of_adj hy⟩
  have h_x_not_mem : x ∉ ({y} : Finset V) := by
    simp only [mem_singleton]
    exact hne
  have h_s_card : s.card = 3 := by
    simp only [s]
    rw [card_insert_of_notMem h_v_not_mem, card_insert_of_notMem h_x_not_mem, card_singleton]
  have h_clique_prop : G.IsClique s := by
    rw [isClique_iff]
    intros a ha b hb hab
    simp only [mem_coe] at ha hb
    simp only [s, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals try contradiction
    · exact hx
    · exact hy
    · exact G.adj_symm hx
    · exact h_adj
    · exact G.adj_symm hy
    · exact G.adj_symm h_adj
  exact h s ⟨h_clique_prop, h_s_card⟩

open Finset in
lemma degree_le_of_triangleFree_no_indep {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no_indep : NoKIndepSet k G) (v : Fin n) :
    G.degree v ≤ k - 1 := by
  have hInd : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v
  by_contra! h_gt
  rw [← G.card_neighborFinset_eq_degree v] at h_gt
  cases k with
  | zero =>
    have h0 : G.IsNIndepSet 0 ∅ := by
      rw [isNIndepSet_iff]
      simp
    exact h_no_indep ∅ h0
  | succ k' =>
    simp only [Nat.add_one_sub_one] at h_gt
    have h_le : k' + 1 ≤ (G.neighborFinset v).card := Nat.succ_le_of_lt h_gt
    obtain ⟨s, hs_sub, hs_card⟩ := exists_subset_card_eq h_le
    have h_s_indep : G.IsIndepSet s := by
      intros x hx y hy hne
      apply hInd
      · rw [mem_neighborSet, ← mem_neighborFinset]; exact hs_sub hx
      · rw [mem_neighborSet, ← mem_neighborFinset]; exact hs_sub hy
      · exact hne
    have h_nindep : G.IsNIndepSet (k' + 1) s := by
      rw [isNIndepSet_iff]
      exact ⟨h_s_indep, hs_card⟩
    exact h_no_indep s h_nindep
