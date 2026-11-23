/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Ramsey's theorem for graphs

Every graph on enough vertices has a clique of size `k` or an independent set of size `ℓ`
(Ramsey 1930; Diestel, *Graph Theory*, Theorem 9.1.1), and `C(k + ℓ - 2, k - 1)` vertices
suffice (Erdős–Szekeres). Mathlib has the Hales–Jewett and Hindman theorems but no graph
Ramsey theorem.

## Main results

* `SimpleGraph.RamseyProperty n k ℓ`: every graph on `n` vertices has a `k`-clique or an
  independent `ℓ`-set.
* `SimpleGraph.exists_ramseyProperty`: some `n` works.
* `SimpleGraph.ramseyProperty_choose`: `n = C(k + ℓ - 2, k - 1)` works.
-/

namespace SimpleGraph

open Finset

/-! ### Ramsey numbers

The **Ramsey number** R(k, ℓ) is the minimum n such that every 2-coloring
of the edges of K_n contains either a red K_k or a blue K_ℓ.
Equivalently, every graph on n vertices contains either a clique of size k
or an independent set of size ℓ.
-/

/-- The **Ramsey property** R(n, k, ℓ): every graph on n vertices
    contains a k-clique or an ℓ-independent set. -/
def RamseyProperty (n k ℓ : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)),
    (∃ S : Finset (Fin n), k ≤ S.card ∧ G.IsClique (↑S : Set _)) ∨
    (∃ S : Finset (Fin n), ℓ ≤ S.card ∧ Gᶜ.IsClique (↑S : Set _))

/-! ### Restriction lemma

Applying `RamseyProperty` on a subset of vertices via `SimpleGraph.comap`. -/

/-- Applying `RamseyProperty n k ℓ` to a subset `S` of `Fin N` with `n ≤ |S|`
    produces a k-clique or ℓ-independent set within `S`. -/
private lemma ramsey_apply_subset {n N k ℓ : ℕ}
    (h : RamseyProperty n k ℓ) (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (hS : n ≤ S.card) :
    (∃ T ⊆ S, k ≤ T.card ∧ G.IsClique (↑T : Set _)) ∨
    (∃ T ⊆ S, ℓ ≤ T.card ∧ Gᶜ.IsClique (↑T : Set _)) := by
  classical
  obtain ⟨S₀, hS₀sub, hS₀card⟩ := Finset.exists_subset_card_eq hS
  have hcard : Fintype.card ↑S₀ = n := by rw [Fintype.card_coe]; exact hS₀card
  let e := Fintype.equivFinOfCardEq hcard
  let f : Fin n → Fin N := Subtype.val ∘ e.symm
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hfS₀ : ∀ i, f i ∈ S₀ := fun i => (e.symm i).property
  obtain hcl | hind := h (G.comap f)
  · -- k-clique in G.comap f → k-clique in G within S
    left
    obtain ⟨T, hTk, hTcl⟩ := hcl
    refine ⟨T.map ⟨f, hf⟩, fun v hv => ?_, by rwa [Finset.card_map], ?_⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      exact hS₀sub (hfS₀ i)
    · intro u hu v hv huv
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hu hv
      obtain ⟨i, hi, rfl⟩ := hu
      obtain ⟨j, hj, rfl⟩ := hv
      have := hTcl hi hj (fun h => huv (congrArg f h))
      rwa [comap_adj] at this
  · -- ℓ-indep set in (G.comap f)ᶜ → ℓ-indep set in Gᶜ within S
    right
    obtain ⟨T, hTℓ, hTind⟩ := hind
    refine ⟨T.map ⟨f, hf⟩, fun v hv => ?_, by rwa [Finset.card_map], ?_⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      exact hS₀sub (hfS₀ i)
    · intro u hu v hv huv
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hu hv
      obtain ⟨i, hi, rfl⟩ := hu
      obtain ⟨j, hj, rfl⟩ := hv
      have hij : i ≠ j := fun h => huv (congrArg f h)
      have := hTind hi hj hij
      rw [compl_adj, comap_adj] at this
      exact ⟨hf.ne hij, this.2⟩

/-! ### Theorem 9.1.1 (Ramsey 1930)

> "For every k, ℓ ∈ ℕ there exists n ∈ ℕ such that every graph of
>  order ≥ n contains K_k as a subgraph or has an independent set of ℓ vertices."
-/

/-- **Theorem 9.1.1** (Ramsey 1930): R(k, ℓ) is finite.

    Proof by double induction using R(k+1, ℓ+1) ≤ R(k, ℓ+1) + R(k+1, ℓ) + 1.
    (Diestel §9.1, p. 212) -/
theorem exists_ramseyProperty (k ℓ : ℕ) :
    ∃ n, RamseyProperty n k ℓ := by
  revert ℓ
  induction k with
  | zero =>
    intro ℓ
    exact ⟨0, fun _ => Or.inl ⟨∅, by omega, by simp [IsClique, Set.Pairwise]⟩⟩
  | succ k ihk =>
    intro ℓ
    induction ℓ with
    | zero =>
      exact ⟨0, fun _ => Or.inr ⟨∅, by omega, by simp [IsClique, Set.Pairwise]⟩⟩
    | succ ℓ ihℓ =>
      -- IH: ihk gives ∀ ℓ', ∃ n, RamseyProperty n k ℓ'
      --     ihℓ gives ∃ n, RamseyProperty n (k+1) ℓ
      obtain ⟨n₁, h₁⟩ := ihk (ℓ + 1)  -- RamseyProperty n₁ k (ℓ + 1)
      obtain ⟨n₂, h₂⟩ := ihℓ            -- RamseyProperty n₂ (k + 1) ℓ
      refine ⟨n₁ + n₂ + 1, fun G => ?_⟩
      classical
      -- Step 1: pick vertex v₀ and partition remaining vertices
      let v₀ : Fin (n₁ + n₂ + 1) := ⟨0, by omega⟩
      let : DecidableRel G.Adj := Classical.decRel _
      let N := G.neighborFinset v₀
      let rest := Finset.univ.erase v₀
      let M := rest \ N
      -- Step 2: |N| + |M| = n₁ + n₂
      have hN_sub_rest : N ⊆ rest := by
        intro v hv
        rw [Finset.mem_erase]
        exact ⟨(G.ne_of_adj (mem_neighborFinset G v₀ v |>.mp hv)).symm, Finset.mem_univ _⟩
      have hNM : N.card + M.card = n₁ + n₂ := by
        have hrc : rest.card = n₁ + n₂ := by
          show (Finset.univ.erase v₀).card = _
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin]; omega
        have h_sdiff := Finset.card_sdiff_add_card_eq_card hN_sub_rest
        show N.card + (rest \ N).card = n₁ + n₂
        omega
      -- Step 3: pigeonhole — |N| ≥ n₁ or |M| ≥ n₂
      by_cases hN : n₁ ≤ N.card
      · -- Case 1: |N| ≥ n₁. Apply h₁ on N.
        obtain hcl | hind := ramsey_apply_subset h₁ G N hN
        · -- Found k-clique T ⊆ N. Extend with v₀ to get (k+1)-clique.
          obtain ⟨T, hTN, hTk, hTcl⟩ := hcl
          left
          have hv₀T : v₀ ∉ T := fun hv =>
            G.ne_of_adj (mem_neighborFinset G v₀ _ |>.mp (hTN hv)) rfl
          refine ⟨T ∪ {v₀}, ?_, ?_⟩
          · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv₀T),
                Finset.card_singleton]; omega
          · intro u hu v hv huv
            simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
              Set.mem_singleton_iff] at hu hv
            rcases hu with hu | rfl <;> rcases hv with hv | rfl
            · exact hTcl hu hv huv
            · exact (mem_neighborFinset G v₀ _ |>.mp (hTN (Finset.mem_coe.mp hu))).symm
            · exact mem_neighborFinset G v₀ _ |>.mp (hTN (Finset.mem_coe.mp hv))
            · exact absurd rfl huv
        · -- Found (ℓ+1)-indep set T ⊆ N. Done directly.
          obtain ⟨T, _, hTℓ, hTind⟩ := hind
          exact Or.inr ⟨T, hTℓ, hTind⟩
      · -- Case 2: |N| < n₁, so |M| ≥ n₂. Apply h₂ on M.
        push Not at hN
        have hM : n₂ ≤ M.card := by omega
        obtain hcl | hind := ramsey_apply_subset h₂ G M hM
        · -- Found (k+1)-clique T ⊆ M. Done directly.
          obtain ⟨T, _, hTk, hTcl⟩ := hcl
          exact Or.inl ⟨T, hTk, hTcl⟩
        · -- Found ℓ-indep set T ⊆ M. Extend with v₀ to get (ℓ+1)-indep set.
          obtain ⟨T, hTM, hTℓ, hTind⟩ := hind
          right
          have hv₀T : v₀ ∉ T := fun hv => by
            have hm := Finset.mem_sdiff.mp (hTM hv)
            exact absurd rfl (Finset.mem_erase.mp hm.1).1
          refine ⟨T ∪ {v₀}, ?_, ?_⟩
          · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv₀T),
                Finset.card_singleton]; omega
          · intro u hu v hv huv
            simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
              Set.mem_singleton_iff] at hu hv
            rcases hu with hu | rfl <;> rcases hv with hv | rfl
            · exact hTind hu hv huv
            · -- u ∈ T ⊆ M, v = v₀. Need Gᶜ.Adj u v₀.
              have hm := Finset.mem_sdiff.mp (hTM (Finset.mem_coe.mp hu))
              have hne : u ≠ v₀ := (Finset.mem_erase.mp hm.1).1
              have hnadj : ¬G.Adj v₀ u := fun h =>
                hm.2 (mem_neighborFinset G v₀ u |>.mpr h)
              rw [compl_adj]
              exact ⟨hne, fun h => hnadj h.symm⟩
            · -- u = v₀, v ∈ T ⊆ M. Need Gᶜ.Adj v₀ v.
              have hm := Finset.mem_sdiff.mp (hTM (Finset.mem_coe.mp hv))
              have hne : v ≠ v₀ := (Finset.mem_erase.mp hm.1).1
              have hnadj : ¬G.Adj v₀ v := fun h =>
                hm.2 (mem_neighborFinset G v₀ v |>.mpr h)
              rw [compl_adj]
              exact ⟨hne.symm, hnadj⟩
            · exact absurd rfl huv

/-- Core step: R(k+1, ℓ+1) ≤ R(k, ℓ+1) + R(k+1, ℓ), the recursive Ramsey bound. -/
private lemma ramsey_step {k ℓ n₁ n₂ : ℕ}
    (h₁ : RamseyProperty n₁ k (ℓ + 1))
    (h₂ : RamseyProperty n₂ (k + 1) ℓ)
    (hpos : 0 < n₁ + n₂) :
    RamseyProperty (n₁ + n₂) (k + 1) (ℓ + 1) := by
  intro G; classical
  let : DecidableRel G.Adj := Classical.decRel _
  let v₀ : Fin (n₁ + n₂) := ⟨0, hpos⟩
  let N := G.neighborFinset v₀
  let rest := Finset.univ.erase v₀
  let M := rest \ N
  have hN_sub : N ⊆ rest := by
    intro v hv; rw [Finset.mem_erase]
    exact ⟨(G.ne_of_adj (mem_neighborFinset G v₀ v |>.mp hv)).symm, Finset.mem_univ _⟩
  have hNM : N.card + M.card = n₁ + n₂ - 1 := by
    have hrc : rest.card = n₁ + n₂ - 1 := by
      show (Finset.univ.erase v₀).card = _
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := Finset.card_sdiff_add_card_eq_card hN_sub
    show N.card + (rest \ N).card = n₁ + n₂ - 1; omega
  by_cases hN : n₁ ≤ N.card
  · obtain hcl | hind := ramsey_apply_subset h₁ G N hN
    · obtain ⟨T, hTN, hTk, hTcl⟩ := hcl; left
      have hv₀T : v₀ ∉ T := fun hv =>
        G.ne_of_adj (mem_neighborFinset G v₀ _ |>.mp (hTN hv)) rfl
      refine ⟨T ∪ {v₀}, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv₀T),
            Finset.card_singleton]; omega
      · intro u hu v hv huv
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hu hv
        rcases hu with hu | rfl <;> rcases hv with hv | rfl
        · exact hTcl hu hv huv
        · exact (mem_neighborFinset G v₀ _ |>.mp (hTN (Finset.mem_coe.mp hu))).symm
        · exact mem_neighborFinset G v₀ _ |>.mp (hTN (Finset.mem_coe.mp hv))
        · exact absurd rfl huv
    · obtain ⟨T, _, hTℓ, hTind⟩ := hind
      exact Or.inr ⟨T, hTℓ, hTind⟩
  · push Not at hN
    have hM : n₂ ≤ M.card := by omega
    obtain hcl | hind := ramsey_apply_subset h₂ G M hM
    · obtain ⟨T, _, hTk, hTcl⟩ := hcl
      exact Or.inl ⟨T, hTk, hTcl⟩
    · obtain ⟨T, hTM, hTℓ, hTind⟩ := hind; right
      have hv₀T : v₀ ∉ T := fun hv => by
        have hm := Finset.mem_sdiff.mp (hTM hv)
        exact absurd rfl (Finset.mem_erase.mp hm.1).1
      refine ⟨T ∪ {v₀}, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv₀T),
            Finset.card_singleton]; omega
      · intro u hu v hv huv
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hu hv
        rcases hu with hu | rfl <;> rcases hv with hv | rfl
        · exact hTind hu hv huv
        · have hm := Finset.mem_sdiff.mp (hTM (Finset.mem_coe.mp hu))
          have hne := (Finset.mem_erase.mp hm.1).1
          have hnadj : ¬G.Adj v₀ u := fun h => hm.2 (mem_neighborFinset G v₀ u |>.mpr h)
          rw [compl_adj]; exact ⟨hne, fun h => hnadj h.symm⟩
        · have hm := Finset.mem_sdiff.mp (hTM (Finset.mem_coe.mp hv))
          have hne := (Finset.mem_erase.mp hm.1).1
          have hnadj : ¬G.Adj v₀ v := fun h => hm.2 (mem_neighborFinset G v₀ v |>.mpr h)
          rw [compl_adj]; exact ⟨hne.symm, hnadj⟩
        · exact absurd rfl huv

/-- **Upper bound**: R(k, ℓ) ≤ C(k+ℓ-2, k-1).
    (Diestel §9.1, Theorem 9.1.1) -/
theorem ramseyProperty_choose (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    RamseyProperty (Nat.choose (k + ℓ - 2) (k - 1)) k ℓ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  clear hk hℓ; revert ℓ
  induction k with
  | zero =>
    intro ℓ; simp
    -- C(ℓ, 0) = 1, need RamseyProperty 1 1 (ℓ+1)
    intro G; left
    exact ⟨{⟨0, by omega⟩}, by simp, by simp [IsClique, Set.Pairwise]⟩
  | succ k ihk =>
    intro ℓ; induction ℓ with
    | zero =>
      simp [Nat.choose_self]
      -- C(k+1, k+1) = 1, need RamseyProperty 1 (k+2) 1
      intro G; right
      exact ⟨{⟨0, by omega⟩}, by simp, by simp [IsClique, Set.Pairwise]⟩
    | succ ℓ ihℓ =>
      -- C((k+2)+(ℓ+2)-2, (k+2)-1) = C(k+ℓ+2, k+1)
      -- = C(k+ℓ+1, k) + C(k+ℓ+1, k+1)  by Pascal
      have hsimp1 : (k + 2) + (ℓ + 2) - 2 = k + ℓ + 2 := by omega
      have hsimp2 : (k + 2) - 1 = k + 1 := by omega
      rw [hsimp1, hsimp2, Nat.choose_succ_succ' (k + ℓ + 1) k]
      have h1_simp : (k + 1) + (ℓ + 2) - 2 = k + ℓ + 1 := by omega
      have h2_simp : (k + 1) - 1 = k := by omega
      have h3_simp : (k + 2) + (ℓ + 1) - 2 = k + ℓ + 1 := by omega
      have h1 := ihk (ℓ + 1)
      rw [h1_simp, h2_simp] at h1
      have h2 := ihℓ
      rw [h3_simp, hsimp2] at h2
      exact ramsey_step h1 h2 (by have := Nat.choose_pos (by omega : k ≤ k + ℓ + 1); omega)

end SimpleGraph
