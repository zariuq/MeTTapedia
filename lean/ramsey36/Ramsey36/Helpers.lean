/-
# Helper Lemmas for Ramsey R(3,6) = 18 Proof

This file contains reusable abstractions that significantly reduce proof size
by factoring out common patterns.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Pattern 1: Filter cardinality implies disjunction

When filtering a 3-element set gives cardinality 2, exactly one element fails the predicate.
This replaces ~90 lines of explicit by_cases per use (used 2+ times).
-/

lemma filter_two_of_three {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : α → Prop) [DecidablePred p]
    (hcard : (({a, b, c} : Finset α).filter p).card = 2) :
    (¬p a ∧ p b ∧ p c) ∨ (p a ∧ ¬p b ∧ p c) ∨ (p a ∧ p b ∧ ¬p c) := by
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · exact fun h => hbc (mem_singleton.mp h)
    · simp [hab, hac]
  have h_removed : (({a, b, c} : Finset α) \ ({a, b, c} : Finset α).filter p).card = 1 := by
    have hsub : ({a, b, c} : Finset α).filter p ⊆ {a, b, c} := filter_subset p _
    simp only [card_sdiff_of_subset hsub, h3, hcard]
  obtain ⟨x, hx_eq⟩ := card_eq_one.mp h_removed
  have hx_in : x ∈ {a, b, c} \ ({a, b, c} : Finset α).filter p := by
    rw [hx_eq]; exact mem_singleton_self x
  rw [mem_sdiff, mem_filter, not_and] at hx_in
  have hx_mem := hx_in.1
  have hx_not_p : ¬p x := hx_in.2 hx_mem
  simp only [mem_insert, mem_singleton] at hx_mem
  have h_others : ∀ y ∈ ({a, b, c} : Finset α), y ≠ x → p y := by
    intro y hy hne
    by_contra h_not_p
    have hy_in_diff : y ∈ {a, b, c} \ ({a, b, c} : Finset α).filter p := by
      rw [mem_sdiff, mem_filter]
      exact ⟨hy, fun ⟨_, hp⟩ => h_not_p hp⟩
    rw [hx_eq, mem_singleton] at hy_in_diff
    exact hne hy_in_diff
  rcases hx_mem with rfl | rfl | rfl
  · left; exact ⟨hx_not_p, h_others b (by simp) hab.symm, h_others c (by simp) hac.symm⟩
  · right; left; exact ⟨h_others a (by simp) hab, hx_not_p, h_others c (by simp) hbc.symm⟩
  · right; right; exact ⟨h_others a (by simp) hac, h_others b (by simp) hbc, hx_not_p⟩

/-! ## Pattern 2: Membership in explicit 4-element set

Replaces repeated `rw [hP_eq]; simp` patterns for P = {p1, p2, p3, p4}.
-/

lemma mem_insert4_first {α : Type*} [DecidableEq α] (a b c d : α) :
    a ∈ ({a, b, c, d} : Finset α) := by simp

lemma mem_insert4_second {α : Type*} [DecidableEq α] (a b c d : α) :
    b ∈ ({a, b, c, d} : Finset α) := by simp

lemma mem_insert4_third {α : Type*} [DecidableEq α] (a b c d : α) :
    c ∈ ({a, b, c, d} : Finset α) := by simp

lemma mem_insert4_fourth {α : Type*} [DecidableEq α] (a b c d : α) :
    d ∈ ({a, b, c, d} : Finset α) := by simp

/-! ## Pattern 3: Cardinality of explicit small sets

These proofs appear 100+ times in the codebase.
-/

lemma card_insert4_of_ne {α : Type*} [DecidableEq α] (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [hcd]
  · simp [hbc, hbd]
  · simp [hab, hac, had]

lemma card_insert3_of_ne {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset α).card = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [hbc]
  · simp [hab, hac]

lemma card_insert2_of_ne {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    ({a, b} : Finset α).card = 2 := by
  rw [card_insert_of_notMem, card_singleton]
  simp [hab]

/-! ## Pattern 4: Disjoint sets imply element inequality

When P and Q are disjoint and x ∈ P and y ∈ Q, then x ≠ y.
This pattern appears 30+ times.
-/

lemma ne_of_mem_disjoint {α : Type*} [DecidableEq α] {A B : Finset α}
    (h_disj : Disjoint A B) {x y : α} (hx : x ∈ A) (hy : y ∈ B) : x ≠ y := by
  intro h_eq
  exact disjoint_left.mp h_disj hx (h_eq ▸ hy)

/-! ## Pattern 5: Triangle-free neighbor independence

The proof `neighborSet_indep_of_triangleFree` is used 34+ times. We provide
convenient corollaries for common use patterns.
-/

omit [Fintype V] in
lemma neighbors_nonadj_of_triangleFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_tri : G.CliqueFree 3) (v x y : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hne : x ≠ y) : ¬G.Adj x y := by
  intro hadj
  have h_clique : G.IsNClique 3 {v, x, y} := by
    rw [isNClique_iff]
    constructor
    · intro a ha b hb hab
      simp only [mem_coe, mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      all_goals first | exact absurd rfl hab | exact hx | exact hy | exact hadj
                      | exact G.symm hx | exact G.symm hy | exact G.symm hadj
    · have hv_ne_x := G.ne_of_adj hx
      have hv_ne_y := G.ne_of_adj hy
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [hne]
      · simp [hv_ne_x, hv_ne_y]
  exact h_tri _ h_clique

/-! ## Pattern 6: rcases 4-way membership (for P = {p1, p2, p3, p4})

This pattern appears 31+ times. Instead of explicit rcases, provide a
function that handles all cases uniformly.
-/

lemma forall_mem_insert4 {α : Type*} [DecidableEq α] {a b c d : α}
    (P : α → Prop) (ha : P a) (hb : P b) (hc : P c) (hd : P d) :
    ∀ x ∈ ({a, b, c, d} : Finset α), P x := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

lemma forall_mem_insert3 {α : Type*} [DecidableEq α] {a b c : α}
    (P : α → Prop) (ha : P a) (hb : P b) (hc : P c) :
    ∀ x ∈ ({a, b, c} : Finset α), P x := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-! ## Pattern 7: Subset equality from cardinality

If A ⊆ B and |A| = |B|, then A = B. Used implicitly many times.
-/

-- This is already in mathlib as `Finset.eq_of_subset_of_card_le`

/-! ## Pattern 8: Six-independent set contradiction

Given a triangle-free graph and certain conditions, construct a 6-IS contradiction.
This pattern appears in multiple variations.
-/

-- The specific 6-IS constructions are too varied to easily abstract,
-- but we can provide helpers for common subpatterns.

/-! ## Pattern 9: Common neighbor cardinality properties

commonNeighborsCard is already defined in RamseyDef.lean (appears 324 times).
-/

/-! ## Pattern 10: Filter on adjacency

Simplify filter expressions involving G.Adj.
-/

omit [Fintype V] in
lemma filter_adj_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v x : V} (hx : x ∈ S) (hadj : G.Adj v x)
    (hunique : ∀ y ∈ S, y ≠ x → ¬G.Adj v y) :
    S.filter (G.Adj v) = {x} := by
  ext y
  simp only [mem_filter, mem_singleton]
  constructor
  · intro ⟨hy, hadj_y⟩
    by_contra hne
    exact hunique y hy hne hadj_y
  · intro h_eq
    exact ⟨h_eq ▸ hx, h_eq ▸ hadj⟩

/-! ## Pattern 11: G.symm automation

G.symm appears 477 times. Provide convenient lemmas.
-/

omit [Fintype V] [DecidableEq V] in
lemma adj_symm_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    G.Adj x y ↔ G.Adj y x := ⟨fun h => G.symm h, fun h => G.symm h⟩

/-! ## Pattern 12: Finset membership cascades

Many proofs have chains like:
  have hx_in_erase : x ∈ S.erase y
  have hx_in_S : x ∈ S := mem_of_mem_erase hx_in_erase
This can be simplified.
-/

lemma mem_of_mem_erase' {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (h : a ∈ s.erase b) : a ∈ s ∧ a ≠ b :=
  ⟨mem_of_mem_erase h, ne_of_mem_erase h⟩
