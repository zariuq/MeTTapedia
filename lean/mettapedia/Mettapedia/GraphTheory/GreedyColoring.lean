/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The greedy colouring bound

Every finite graph is `(Δ(G) + 1)`-colourable (Diestel, *Graph Theory*, Proposition 5.2.1):
colour the graph without one vertex, then give that vertex a colour none of its at most
`Δ(G)` neighbours uses.

## Main results

* `SimpleGraph.colorable_maxDegree_add_one`: `χ(G) ≤ Δ(G) + 1`.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Helper: if we can color G minus one vertex with k colors, and that vertex
    has fewer than k neighbors, we can extend the coloring to all of G.

    Proof: the colors used by v's neighbors form a subset of Fin k with
    cardinality ≤ deg(v) < k, so by pigeonhole there exists a free color.
    Extend the coloring: use the original colors for non-v vertices and
    the free color for v. Adjacent pairs remain properly colored because:
    - Two non-v vertices: the original coloring was proper
    - v and a neighbor w: w's color is "used," but v's free color avoids all used colors -/
private theorem extend_coloring_one_vertex
    (v : V) (k : ℕ) (hk : 0 < k)
    (hc : (G.induce ({v} : Set V)ᶜ).Colorable k)
    (hd : G.degree v < k) :
    G.Colorable k := by
  classical
  obtain ⟨c⟩ := hc
  -- For w ≠ v, get color of w from existing coloring; for w = v, use dummy
  let colorOf : V → Fin k := fun w =>
    if h : w = v then ⟨0, hk⟩
    else c ⟨w, by simp [Set.mem_compl_iff, Set.mem_singleton_iff, h]⟩
  -- Colors used by v's neighbors
  let usedColors := (G.neighborFinset v).image colorOf
  -- Pigeonhole: |used| ≤ deg(v) < k = |Fin k|, so ∃ free color
  have hfree : (Finset.univ \ usedColors).Nonempty := by
    rw [Finset.sdiff_nonempty]; intro hsub
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact absurd (lt_of_le_of_lt (le_trans h1 Finset.card_image_le) hd) (lt_irrefl _)
  obtain ⟨j, hj⟩ := hfree
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
  -- Build extended coloring: v ↦ j, everything else keeps its color
  let f : V → Fin k := fun w => if w = v then j else colorOf w
  refine ⟨⟨f, fun {a b} hab => ?_⟩⟩
  show f a ≠ f b; simp only [f]
  by_cases ha : a = v <;> by_cases hb : b = v
  · -- a = v, b = v: impossible (self-loop)
    subst ha; subst hb; exact absurd hab G.irrefl
  · -- a = v, b ≠ v: j ≠ colorOf b (b is neighbor, its color is used, j is free)
    subst ha; rw [if_pos rfl, if_neg hb]
    exact fun heq => hj (by rw [heq]; exact Finset.mem_image_of_mem colorOf (Set.mem_toFinset.mpr hab))
  · -- a ≠ v, b = v: colorOf a ≠ j (symmetric)
    subst hb; rw [if_neg ha, if_pos rfl]
    exact fun heq => hj (by rw [← heq]; exact Finset.mem_image_of_mem colorOf (Set.mem_toFinset.mpr hab.symm))
  · -- a ≠ v, b ≠ v: original coloring is valid
    rw [if_neg ha, if_neg hb]; simp only [colorOf, dif_neg ha, dif_neg hb]
    exact c.valid (by simp [SimpleGraph.comap_adj]; exact hab)

/-- Auxiliary: maxDegree of the complement-singleton induced subgraph ≤ maxDegree G. -/
private theorem maxDegree_induce_compl_singleton_le (v : V) :
    (G.induce ({v} : Set V)ᶜ).maxDegree ≤ G.maxDegree := by
  classical
  -- For each vertex w ≠ v, deg_{G\v}(w) ≤ deg_G(w) ≤ Δ(G).
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro ⟨w, hw⟩
  -- deg_{G[S]}(w) ≤ deg_G(w): neighbors in induced subgraph ⊆ neighbors in G
  have hdeg : (G.induce ({v} : Set V)ᶜ).degree ⟨w, hw⟩ ≤ G.degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
        ← Finset.card_map (Function.Embedding.subtype _),
        SimpleGraph.map_neighborFinset_induce]
    exact Finset.card_le_card Finset.inter_subset_left
  exact le_trans hdeg (G.degree_le_maxDegree w)

theorem colorable_maxDegree_add_one [Nonempty V] :
    G.Colorable (G.maxDegree + 1) := by
  classical
  -- Prove by strong induction on |V| for all types simultaneously
  suffices h : ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = n → H.Colorable (H.maxDegree + 1) from
    h (Fintype.card V) V G rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W instFW instDW instNW H instDH hn
    -- Easy case: |W| ≤ Δ+1
    by_cases hle : n ≤ H.maxDegree + 1
    · exact H.colorable_of_fintype.mono (hn ▸ hle)
    · -- Hard case: |W| > Δ+1, so n ≥ 2
      push Not at hle
      have hn2 : 2 ≤ n := by omega
      -- Pick a vertex v
      obtain ⟨v⟩ := instNW
      -- The induced subgraph H[W\{v}] has n-1 vertices
      set S := ({v} : Set W)ᶜ with hS_def
      have hcardS : Fintype.card ↥S = n - 1 := by
        have h1 := Fintype.card_compl_set ({v} : Set W)
        have h2 : Fintype.card ↥({v} : Set W) = 1 := by
          have : Fintype.card {x : W // x = v} = 1 := Fintype.card_subtype_eq v
          exact this
        rw [h1, h2, hn]
      -- H[S] has maxDegree ≤ Δ(H)
      have hmaxDeg : (H.induce S).maxDegree ≤ H.maxDegree :=
        maxDegree_induce_compl_singleton_le H v
      -- S is nonempty (since n ≥ 2)
      have hneS : Nonempty ↥S := by
        rw [← not_isEmpty_iff]; intro hempty
        have : Fintype.card ↥S = 0 := Fintype.card_eq_zero
        omega
      -- IH: H[S] is (Δ(H[S])+1)-colorable
      have hIH := @ih (n - 1) (by omega) ↥S _ _ hneS (H.induce S) _ hcardS
      -- Mono: H[S] is (Δ(H)+1)-colorable
      have hc : (H.induce S).Colorable (H.maxDegree + 1) :=
        hIH.mono (Nat.succ_le_succ hmaxDeg)
      -- Extend via the pigeonhole lemma
      exact extend_coloring_one_vertex H v (H.maxDegree + 1) (by omega) hc
        (Nat.lt_succ_of_le (H.degree_le_maxDegree v))

end SimpleGraph
