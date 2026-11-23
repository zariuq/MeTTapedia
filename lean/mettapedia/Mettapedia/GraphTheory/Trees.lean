/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Trees in graphs of large minimum degree

Diestel, *Graph Theory*, Corollary 1.5.4: if `T` is a tree and `δ(G) ≥ |T| - 1`, then `G`
contains a copy of `T` (not necessarily induced). Induction on `|T|`: remove a leaf, embed the
rest, and send the leaf to a neighbour of its parent's image outside the image, which exists
because that vertex has at least `|T| - 1` neighbours.

## Main results

* `SimpleGraph.IsTree.isContained_of_card_le_minDegree_add_one`: `T ⊑ G`.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem exists_injective_hom_of_isTree {W : Type*} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    [Nonempty V]
    (hδ : Fintype.card W ≤ G.minDegree + 1) :
    ∃ (f : T →g G), Function.Injective f := by
  classical
  -- Prove by strong induction on |W| for all tree types simultaneously
  -- Use strong induction on |W|, quantified over all tree types
  suffices gen : ∀ (n : ℕ) (W' : Type _) [Fintype W'] [DecidableEq W']
      (T' : SimpleGraph W') [DecidableRel T'.Adj],
      T'.IsTree → Fintype.card W' = n → Fintype.card W' ≤ G.minDegree + 1 →
      ∃ (f : T' →g G), Function.Injective f from
    gen (Fintype.card W) W T hT rfl hδ
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W' instFW' instDW' T' instDT' hT' hn' hδ'
    -- Base: |W'| ≤ 1
    by_cases hn1 : n ≤ 1
    · obtain ⟨v₀⟩ := ‹Nonempty V›
      by_cases hW : IsEmpty W'
      · exact ⟨⟨hW.elim, fun {a} => hW.elim a⟩, fun {a} => hW.elim a⟩
      · rw [not_isEmpty_iff] at hW
        have hsub : Subsingleton W' := ⟨Fintype.card_le_one_iff.mp (hn' ▸ hn1)⟩
        exact ⟨⟨fun _ => v₀, fun {a b} h => absurd (hsub.allEq a b) (T'.ne_of_adj h)⟩,
               fun {a b} _ => hsub.allEq a b⟩
    · -- Inductive step: |W'| = n ≥ 2
      push Not at hn1
      have hnt : Nontrivial W' := by
        rw [← Fintype.one_lt_card_iff_nontrivial]; omega
      -- T' has a leaf (degree 1 vertex)
      obtain ⟨l, hl⟩ := hT'.exists_vert_degree_one_of_nontrivial
      -- T'\l is a tree
      set S := ({l} : Set W')ᶜ with hS_def
      have hconn_sub := hT'.connected.induce_compl_singleton_of_degree_eq_one hl
      have hT'_sub : (T'.induce S).IsTree := ⟨hconn_sub, hT'.isAcyclic.induce _⟩
      -- |S| = n - 1
      have hcardS : Fintype.card ↥S = n - 1 := by
        have h1 := Fintype.card_compl_set ({l} : Set W')
        have h2 : Fintype.card ↥({l} : Set W') = 1 := Fintype.card_subtype_eq l
        rw [h1, h2, hn']
      have hneS : Nonempty ↥S := by
        rw [← not_isEmpty_iff]; intro hempty
        have : Fintype.card ↥S = 0 := Fintype.card_eq_zero; omega
      -- IH: T'\l embeds injectively into G
      have hδ_sub : Fintype.card ↥S ≤ G.minDegree + 1 := by omega
      obtain ⟨f', hf'_inj⟩ := ih (n - 1) (by omega) ↥S (T'.induce S) hT'_sub hcardS hδ_sub
      -- Get the unique neighbor u of the leaf l
      obtain ⟨u, hlu, hu_unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
      have hu_ne_l : u ≠ l := (T'.ne_of_adj hlu).symm
      have hu_in_S : u ∈ S := by simp [hS_def, Set.mem_compl_iff, Set.mem_singleton_iff, hu_ne_l]
      -- f'(⟨u, hu_in_S⟩) has ≥ δ(G) ≥ n-1 neighbors in G
      -- The image of f' (injective on n-1 vertices) has n-1 elements
      -- By pigeonhole: ∃ w ∈ G.neighborFinset(f'(u)) \ im(f')
      -- (since |neighbors| ≥ n-1 and |im(f') \ {f'(u)}| ≤ n-2)
      set fu := f' ⟨u, hu_in_S⟩
      -- Build the image finset
      let imF : Finset V := Finset.univ.image (fun (x : ↥S) => f' x)
      have him_card : imF.card = n - 1 := by
        rw [Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, hcardS]
      -- Pigeonhole: fu has ≥ δ(G) ≥ n-1 neighbors, imF has n-1 elements
      have hmind2 : n - 1 ≤ G.minDegree := by
        have h_copy := hδ'; rw [hn'] at h_copy; omega
      have hfu_deg : n - 1 ≤ G.degree fu :=
        le_trans hmind2 (G.minDegree_le_degree fu)
      -- fu ∈ imF but fu ∉ neighborFinset fu (no self-loops)
      -- So neighborFinset fu ⊆ imF would give neighborFinset fu ⊆ imF \ {fu}
      -- But |imF \ {fu}| ≤ n-2 < n-1 ≤ |neighborFinset fu|. Contradiction.
      have hfu_in_imF : fu ∈ imF :=
        Finset.mem_image_of_mem _ (Finset.mem_univ (⟨u, hu_in_S⟩ : ↥S))
      have hsdiff : (G.neighborFinset fu \ imF).Nonempty := by
        rw [Finset.sdiff_nonempty]; intro hsub
        -- neighborFinset ⊆ imF, but fu ∉ neighborFinset (no loops)
        -- So neighborFinset ⊆ imF \ {fu}, giving |neighbors| ≤ |imF| - 1
        have hfu_not_nbr : fu ∉ G.neighborFinset fu :=
          SimpleGraph.notMem_neighborFinset_self G fu
        have hsub' : G.neighborFinset fu ⊆ imF.erase fu :=
          fun x hx => Finset.mem_erase.mpr ⟨fun h => hfu_not_nbr (h ▸ hx), hsub hx⟩
        have h1 := Finset.card_le_card hsub'
        simp only [Finset.card_erase_of_mem hfu_in_imF, him_card,
            SimpleGraph.card_neighborFinset_eq_degree] at h1
        omega
      obtain ⟨w, hw⟩ := hsdiff
      rw [Finset.mem_sdiff] at hw
      have hw_adj : G.Adj fu w := (SimpleGraph.mem_neighborFinset ..).mp hw.1
      have hw_not_im : w ∉ imF := hw.2
      -- Define extended map: l ↦ w, x ↦ f'(x) for x ∈ S
      let mem_S : ∀ x : W', x ≠ l → x ∈ S := fun x hx => by
        simp only [hS_def, Set.mem_compl_iff, Set.mem_singleton_iff]; exact hx
      refine ⟨⟨fun x => if h : x = l then w else f' ⟨x, mem_S x h⟩,
              fun {a b} hab => ?_⟩, fun {a b} heq => ?_⟩
      · -- Adjacency: T'.Adj a b → G.Adj (ext a) (ext b)
        by_cases ha : a = l <;> by_cases hb : b = l
        · -- a = l, b = l: impossible (irreflexive)
          subst ha; subst hb; exact absurd hab (SimpleGraph.irrefl T')
        · -- a = l, b ≠ l: b = u, need G.Adj w fu
          have hbu : b = u := hu_unique b (ha ▸ hab)
          show G.Adj (dite (a = l) _ _) (dite (b = l) _ _)
          rw [dif_pos ha, dif_neg hb]
          have : f' ⟨b, mem_S b hb⟩ = fu := congr_arg f' (Subtype.ext hbu)
          rw [this]; exact hw_adj.symm
        · -- a ≠ l, b = l: a = u, need G.Adj fu w
          have hau : a = u := hu_unique a (T'.adj_symm (hb ▸ hab))
          show G.Adj (dite (a = l) _ _) (dite (b = l) _ _)
          rw [dif_neg ha, dif_pos hb]
          have : f' ⟨a, mem_S a ha⟩ = fu := congr_arg f' (Subtype.ext hau)
          rw [this]; exact hw_adj
        · -- a ≠ l, b ≠ l: f' preserves adjacency
          show G.Adj (dite (a = l) _ _) (dite (b = l) _ _)
          rw [dif_neg ha, dif_neg hb]
          exact f'.map_rel' (by simp [SimpleGraph.comap_adj]; exact hab)
      · -- Injectivity: ext a = ext b → a = b
        by_cases ha : a = l <;> by_cases hb : b = l
        · exact ha.trans hb.symm
        · -- a = l, b ≠ l: w ∉ imF but f'(b) ∈ imF
          exfalso
          have heq' : w = f' ⟨b, mem_S b hb⟩ := by
            change (dite (a = l) _ _) = (dite (b = l) _ _) at heq
            rwa [dif_pos ha, dif_neg hb] at heq
          exact hw_not_im (heq' ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
        · -- a ≠ l, b = l: f'(a) ∈ imF but w ∉ imF
          exfalso
          have heq' : f' ⟨a, mem_S a ha⟩ = w := by
            change (dite (a = l) _ _) = (dite (b = l) _ _) at heq
            rwa [dif_neg ha, dif_pos hb] at heq
          exact hw_not_im (heq'.symm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
        · -- a ≠ l, b ≠ l: f' injective
          have heq' : f' ⟨a, mem_S a ha⟩ = f' ⟨b, mem_S b hb⟩ := by
            change (dite (a = l) _ _) = (dite (b = l) _ _) at heq
            rwa [dif_neg ha, dif_neg hb] at heq
          exact congrArg Subtype.val (hf'_inj heq')

/-- Diestel, Corollary 1.5.4: a graph whose minimum degree is at least `|T| - 1` contains a
copy of the tree `T`. -/
theorem IsTree.isContained_of_card_le_minDegree_add_one {W : Type*} [Fintype W]
    [DecidableEq W] {T : SimpleGraph W} [DecidableRel T.Adj] (hT : T.IsTree) [Nonempty V]
    (hδ : Fintype.card W ≤ G.minDegree + 1) : T ⊑ G := by
  obtain ⟨f, hf⟩ := exists_injective_hom_of_isTree G T hT hδ
  exact ⟨⟨f, hf⟩⟩

end SimpleGraph
