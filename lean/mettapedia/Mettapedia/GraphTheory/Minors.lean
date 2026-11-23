/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Minors and topological minors

Graph minors through branch sets, and topological minors through subdivision paths
(Diestel, *Graph Theory*, §1.7). Mathlib has minors only for matroids.

## Main definitions

* `SimpleGraph.MinorModel X G`, `SimpleGraph.IsMinor X G`: `X` is a minor of `G`.
* `SimpleGraph.TopMinorModel X G`, `SimpleGraph.IsTopMinor X G`: `G` contains a subdivision of
  `X`.

## Main results

* `SimpleGraph.IsTopMinor.isMinor`: every topological minor is a minor (Diestel,
  Proposition 1.7.2 (i)).
-/

namespace SimpleGraph

open Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Minor models (branch sets)

Diestel defines: "X is a minor of G" when there exist pairwise disjoint
connected subgraphs (branch sets) V_x ⊆ V(G) for each x ∈ V(X), such
that for every edge xy ∈ E(X), G has an edge between V_x and V_y.

This is the *branch-set* formulation.  We formalise it as a structure.
-/

/-- A **minor model** of `X` inside `G` assigns to each vertex `x` of `X`
    a non-empty connected subgraph of `G` (the *branch set*), with disjoint
    branch sets and an edge in `G` between any two branch sets whose
    vertices are adjacent in `X`. -/
structure MinorModel {W : Type*} [Fintype W] [DecidableEq W]
    (X : SimpleGraph W) [DecidableRel X.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  branchSet : W → Finset V
  branchNonempty : ∀ x, (branchSet x).Nonempty
  branchDisjoint : ∀ x y, x ≠ y → Disjoint (branchSet x) (branchSet y)
  branchConnected : ∀ x, (G.induce (↑(branchSet x) : Set V)).Preconnected
  branchAdj : ∀ x y, X.Adj x y →
    ∃ u ∈ branchSet x, ∃ v ∈ branchSet y, G.Adj u v

/-- `X` is a **minor** of `G` if there exists a minor model of `X` in `G`. -/
def IsMinor {W : Type*} [Fintype W] [DecidableEq W]
    (X : SimpleGraph W) [DecidableRel X.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty (MinorModel X G)

/-! ### Subdivision (topological minor)

A **subdivision** of `X` (denoted TX) replaces each edge of `X` with an
independent path.  `X` is a topological minor of `G` if some subdivision
of `X` is a subgraph of `G`.

We define this via an embedding structure.  The key conditions are:
1. `vertexMap` maps vertices of `X` injectively to `V(G)` (branch vertices)
2. For each edge `xy` of `X`, a path in `G` from `vertexMap x` to `vertexMap y`
3. Each such path is an actual path (no repeated vertices)
-/

/-- A **topological minor model** of `X` in `G` maps each vertex of `X`
    injectively to `V(G)` (branch vertices) and each edge of `X` to a
    path in `G` connecting the corresponding branch vertices.

    The paths must be pairwise *internally disjoint*: each non-branch vertex
    appears in the support of at most one edge path (up to direction).
    This ensures the subdivision is well-defined.

    Diestel §1.7, p. 18: "A subdivision of a graph X is obtained by replacing
    each edge of X by an independent path." -/
structure TopMinorModel {W : Type*} [Fintype W] [DecidableEq W]
    (X : SimpleGraph W) [DecidableRel X.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  vertexMap : W ↪ V
  edgePath : ∀ x y, X.Adj x y → G.Walk (vertexMap x) (vertexMap y)
  edgePath_isPath : ∀ x y (h : X.Adj x y), (edgePath x y h).IsPath
  /-- Non-branch vertices appear in at most one edge path (per undirected edge). -/
  edgePath_internally_disjoint : ∀ (v : V), v ∉ Set.range vertexMap →
    ∀ x₁ y₁ x₂ y₂ (h₁ : X.Adj x₁ y₁) (h₂ : X.Adj x₂ y₂),
    v ∈ (edgePath x₁ y₁ h₁).support → v ∈ (edgePath x₂ y₂ h₂).support →
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ y₁ = x₂)
  /-- Branch vertices only appear as endpoints of their incident edge paths. -/
  edgePath_avoids_branch : ∀ (z : W) (x y : W) (h : X.Adj x y),
    vertexMap z ∈ (edgePath x y h).support → z = x ∨ z = y

/-- `X` is a **topological minor** of `G` if there exists a topological
    minor model of `X` in `G`. -/
def IsTopMinor {W : Type*} [Fintype W] [DecidableEq W]
    (X : SimpleGraph W) [DecidableRel X.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty (TopMinorModel X G)

/-! ### Proposition 1.7.2 (Diestel §1.7, p. 20)

> "(i) Every TX is also an MX; thus, every topological minor is also a minor."
> "(ii) If Δ(X) ≤ 3, every MX contains a TX."
-/

omit [Fintype V] in
/-- The endpoint of a path cannot appear in the `takeUntil` prefix
    when the `takeUntil` target is not the endpoint. -/
private theorem endpoint_not_in_takeUntil
    {u v w : V} {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (p : G'.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) (hne : w ≠ v) :
    v ∉ (p.takeUntil w hw).support := by
  intro hv_in
  have hnodup := hp.support_nodup
  rw [← Walk.take_spec p hw, Walk.support_append] at hnodup
  have hdisjoint := (List.nodup_append.mp hnodup).2.2
  have hv_drop := Walk.end_mem_support (p.dropUntil w hw)
  -- dropUntil.support = w :: rest; since v ≠ w, v ∈ rest = tail
  obtain ⟨rest, hrest⟩ : ∃ l, (p.dropUntil w hw).support = w :: l := by
    cases p.dropUntil w hw with
    | nil => exact ⟨[], rfl⟩
    | cons _ q => exact ⟨q.support, rfl⟩
  rw [hrest, List.tail_cons] at hnodup hdisjoint
  rw [hrest] at hv_drop
  rcases List.mem_cons.mp hv_drop with rfl | hv_rest
  · exact absurd rfl hne
  · exact absurd rfl (hdisjoint v hv_in v hv_rest)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Given a walk in G with all support vertices in S, the endpoints
    are reachable in the induced subgraph G[S]. -/
private theorem reachable_in_induced_of_walk
    {S : Set V} {u v : V}
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ S) :
    (G.induce S).Reachable
      ⟨u, hp u p.start_mem_support⟩
      ⟨v, hp v p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj tail ih =>
    have hp_tail : ∀ w ∈ tail.support, w ∈ S :=
      fun w hw => hp w (List.mem_cons_of_mem _ hw)
    exact Reachable.trans
      ⟨Walk.cons (show (G.induce S).Adj ⟨_, _⟩ ⟨_, _⟩ from hadj) Walk.nil⟩
      (ih hp_tail)

omit [Fintype V] in
/-- **Proposition 1.7.2 (i)**: every topological minor is a minor.

    Proof: given a TopMinorModel, construct branch sets B(x) =
    {vertexMap x} ∪ {non-branch internal vertices on edge paths from x
    in canonical direction}. A linear order on W (from Fintype via Fin)
    provides canonical edge direction: for edge {x,y}, assign internal
    vertices to B(min(x,y)) only. This ensures disjointness (the
    bidirectional overlap case gives x < y ∧ y < x, contradiction).
    Connectivity follows from Walk.takeUntil prefix staying within B(x).
    Adjacency uses the penultimate vertex of the relevant edge path. -/
theorem IsTopMinor.isMinor {W : Type*} [Fintype W] [DecidableEq W]
    {X : SimpleGraph W} [DecidableRel X.Adj] (h : IsTopMinor X G) :
    IsMinor X G := by
  classical
  obtain ⟨tm⟩ := h
  -- Canonical direction: linear order on W from Fintype via Fin equivalence
  let : LinearOrder W :=
    LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  -- Branch set: {vertexMap x} ∪ non-branch internal vertices on
  -- edgePaths x→y for y > x only (canonical direction).
  let B : W → Finset V := fun x =>
    {tm.vertexMap x} ∪
      Finset.biUnion Finset.univ (fun y =>
        if hxy : X.Adj x y then
          if x < y then
            (tm.edgePath x y hxy).support.toFinset.filter
              (fun v => v ∉ Set.range tm.vertexMap)
          else ∅
        else ∅)
  refine ⟨⟨B, ?_, ?_, ?_, ?_⟩⟩
  · -- branchNonempty
    intro x
    exact ⟨tm.vertexMap x, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
  · -- branchDisjoint: canonical direction eliminates bidirectional overlap
    intro x y hxy
    rw [Finset.disjoint_left]
    intro v hv_x hv_y
    simp only [B, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at hv_x hv_y
    rcases hv_x with rfl | ⟨z₁, hz₁⟩
    · -- v = vertexMap x ∈ B(y): filter excludes branch vertices
      rcases hv_y with h_eq | ⟨z₂, hz₂⟩
      · exact hxy (tm.vertexMap.injective h_eq)
      · by_cases hadj_yz₂ : X.Adj y z₂
        · simp only [dif_pos hadj_yz₂] at hz₂
          by_cases hlt_yz₂ : y < z₂
          · simp only [if_pos hlt_yz₂] at hz₂
            exact (Finset.mem_filter.mp hz₂).2 ⟨x, rfl⟩
          · simp only [if_neg hlt_yz₂] at hz₂
            exact absurd hz₂ (by simp)
        · simp only [dif_neg hadj_yz₂] at hz₂
          exact absurd hz₂ (by simp)
    · -- v non-branch on some edgePath x z₁ with x < z₁
      by_cases hadj_xz₁ : X.Adj x z₁
      · simp only [dif_pos hadj_xz₁] at hz₁
        by_cases hlt_xz₁ : x < z₁
        · simp only [if_pos hlt_xz₁] at hz₁
          have hv_data₁ := Finset.mem_filter.mp hz₁
          have hv_not_branch : v ∉ Set.range tm.vertexMap := hv_data₁.2
          have hv_supp₁ : v ∈ (tm.edgePath x z₁ hadj_xz₁).support :=
            List.mem_toFinset.mp hv_data₁.1
          rcases hv_y with rfl | ⟨z₂, hz₂⟩
          · exact hv_not_branch ⟨y, rfl⟩
          · by_cases hadj_yz₂ : X.Adj y z₂
            · simp only [dif_pos hadj_yz₂] at hz₂
              by_cases hlt_yz₂ : y < z₂
              · simp only [if_pos hlt_yz₂] at hz₂
                have hv_data₂ := Finset.mem_filter.mp hz₂
                have hv_supp₂ : v ∈ (tm.edgePath y z₂ hadj_yz₂).support :=
                  List.mem_toFinset.mp hv_data₂.1
                rcases tm.edgePath_internally_disjoint v hv_not_branch
                  x z₁ y z₂ hadj_xz₁ hadj_yz₂ hv_supp₁ hv_supp₂ with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
                · exact hxy rfl
                · -- After subst: x < y and y < x — contradiction
                  exact absurd (lt_trans hlt_xz₁ hlt_yz₂) (lt_irrefl _)
              · simp only [if_neg hlt_yz₂] at hz₂; exact absurd hz₂ (by simp)
            · simp only [dif_neg hadj_yz₂] at hz₂; exact absurd hz₂ (by simp)
        · simp only [if_neg hlt_xz₁] at hz₁; exact absurd hz₁ (by simp)
      · simp only [dif_neg hadj_xz₁] at hz₁; exact absurd hz₁ (by simp)
  · -- branchConnected: hub connectivity through vertexMap x
    intro x ⟨u, hu⟩ ⟨v, hv⟩
    have hx_mem : (tm.vertexMap x : V) ∈ (↑(B x) : Set V) :=
      Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    -- Every vertex in B(x) is reachable from vertexMap x in G[B(x)]
    suffices hub : ∀ (w : V) (hw : w ∈ (↑(B x) : Set V)),
      (G.induce (↑(B x) : Set V)).Reachable ⟨tm.vertexMap x, hx_mem⟩ ⟨w, hw⟩ by
      exact (hub u hu).symm.trans (hub v hv)
    intro w hw
    by_cases heq : w = tm.vertexMap x
    · subst heq; exact Reachable.refl _
    · -- w is non-branch on some edgePath x y' with x < y'
      have hw_finset : w ∈ B x := Finset.mem_coe.mp hw
      simp only [B, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at hw_finset
      rcases hw_finset with rfl | ⟨y', hy'⟩
      · exact absurd rfl heq
      · by_cases hadj_xy' : X.Adj x y'
        · simp only [dif_pos hadj_xy'] at hy'
          by_cases hlt_xy' : x < y'
          · simp only [if_pos hlt_xy'] at hy'
            have hw_data := Finset.mem_filter.mp hy'
            have hw_supp : w ∈ (tm.edgePath x y' hadj_xy').support :=
              List.mem_toFinset.mp hw_data.1
            have hw_not_branch : w ∉ Set.range tm.vertexMap := hw_data.2
            -- All vertices on the takeUntil prefix are in B(x)
            have hpfx_in_B : ∀ z ∈ ((tm.edgePath x y' hadj_xy').takeUntil w hw_supp).support,
                z ∈ (↑(B x) : Set V) := by
              intro z hz
              have hz_path : z ∈ (tm.edgePath x y' hadj_xy').support :=
                Walk.support_takeUntil_subset_support _ hw_supp hz
              by_cases hz_branch : z ∈ Set.range tm.vertexMap
              · -- z is a branch vertex on the path: must be x or y'
                obtain ⟨w'', hw''⟩ := hz_branch
                rcases tm.edgePath_avoids_branch w'' x y' hadj_xy'
                    (hw''.symm ▸ hz_path) with rfl | h_eq_y'
                · -- w'' = x, so z = vertexMap x ∈ B(x)
                  exact Finset.mem_coe.mpr
                    (Finset.mem_union_left _ (hw''.symm ▸ Finset.mem_singleton_self _))
                · -- w'' = y': z = vertexMap y', impossible on prefix
                  exfalso
                  have hz_eq : z = tm.vertexMap y' := (h_eq_y' ▸ hw'').symm
                  exact endpoint_not_in_takeUntil (tm.edgePath x y' hadj_xy')
                    (tm.edgePath_isPath x y' hadj_xy') hw_supp
                    (fun h => hw_not_branch ⟨y', h.symm⟩) (hz_eq ▸ hz)
              · -- z is non-branch, on edgePath x y' with x < y' → z ∈ B(x)
                exact Finset.mem_coe.mpr (Finset.mem_union_right _
                  (Finset.mem_biUnion.mpr ⟨y', Finset.mem_univ y', by
                    simp only [dif_pos hadj_xy', if_pos hlt_xy']
                    exact Finset.mem_filter.mpr
                      ⟨List.mem_toFinset.mpr hz_path, hz_branch⟩⟩))
            -- Convert prefix walk to induced-subgraph reachability
            exact reachable_in_induced_of_walk G
              ((tm.edgePath x y' hadj_xy').takeUntil w hw_supp) hpfx_in_B
          · simp only [if_neg hlt_xy'] at hy'
            exact absurd hy' (by simp)
        · simp only [dif_neg hadj_xy'] at hy'
          exact absurd hy' (by simp)
  · -- branchAdj: case split on canonical direction
    intro x y hadj
    have hne_xy := X.ne_of_adj hadj
    by_cases hlt : x < y
    · -- Case x < y: use edgePath x y, penultimate vertex ∈ B(x)
      set p := tm.edgePath x y hadj
      have hne : tm.vertexMap x ≠ tm.vertexMap y :=
        tm.vertexMap.injective.ne hne_xy
      have hp_len : 0 < p.length :=
        Walk.not_nil_iff_lt_length.mp (fun h => hne (Walk.Nil.eq h))
      set u := p.getVert (p.length - 1)
      have hadj_u_y : G.Adj u (tm.vertexMap y) := by
        have := p.adj_getVert_succ (show p.length - 1 < p.length by omega)
        rwa [show p.length - 1 + 1 = p.length by omega, Walk.getVert_length] at this
      have hu_support : u ∈ p.support := Walk.getVert_mem_support p (p.length - 1)
      have hu_ne_y : u ≠ tm.vertexMap y := by
        intro h_eq
        have h_inj := (tm.edgePath_isPath x y hadj).getVert_injOn
        have h1 : p.length - 1 ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
        have h2 : p.length ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr le_rfl
        have := h_inj h1 h2 (h_eq.trans (Walk.getVert_length p).symm)
        omega
      have hu_Bx : u ∈ B x := by
        by_cases h_len1 : p.length = 1
        · have : u = tm.vertexMap x := by simp [u, h_len1, Walk.getVert_zero]
          exact this ▸ Finset.mem_union_left _ (Finset.mem_singleton_self _)
        · have hu_ne_x : u ≠ tm.vertexMap x := by
            intro h_eq
            have h_inj := (tm.edgePath_isPath x y hadj).getVert_injOn
            have h1 : p.length - 1 ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
            have h0 : (0 : ℕ) ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
            exact absurd (h_inj h1 h0 (h_eq.trans (Walk.getVert_zero p).symm)) (by omega)
          have hu_not_branch : u ∉ Set.range tm.vertexMap := by
            intro ⟨w, hw⟩
            rcases tm.edgePath_avoids_branch w x y hadj (hw ▸ hu_support) with rfl | rfl
            · exact hu_ne_x hw.symm
            · exact hu_ne_y hw.symm
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
            simp only [dif_pos hadj, if_pos hlt]
            exact Finset.mem_filter.mpr
              ⟨List.mem_toFinset.mpr hu_support, hu_not_branch⟩⟩)
      exact ⟨u, hu_Bx, tm.vertexMap y,
        Finset.mem_union_left _ (Finset.mem_singleton_self _), hadj_u_y⟩
    · -- Case y < x: use edgePath y x, penultimate vertex ∈ B(y)
      have hlt_yx : y < x := by
        rcases lt_trichotomy y x with h | rfl | h
        · exact h
        · exact absurd rfl (Ne.symm hne_xy)
        · exact absurd h hlt
      have hadj_yx := X.adj_symm hadj
      set p := tm.edgePath y x hadj_yx
      have hne : tm.vertexMap y ≠ tm.vertexMap x :=
        tm.vertexMap.injective.ne (Ne.symm hne_xy)
      have hp_len : 0 < p.length :=
        Walk.not_nil_iff_lt_length.mp (fun h => hne (Walk.Nil.eq h))
      set u := p.getVert (p.length - 1)
      have hadj_u_x : G.Adj u (tm.vertexMap x) := by
        have := p.adj_getVert_succ (show p.length - 1 < p.length by omega)
        rwa [show p.length - 1 + 1 = p.length by omega, Walk.getVert_length] at this
      have hu_support : u ∈ p.support := Walk.getVert_mem_support p (p.length - 1)
      have hu_ne_x : u ≠ tm.vertexMap x := by
        intro h_eq
        have h_inj := (tm.edgePath_isPath y x hadj_yx).getVert_injOn
        have h1 : p.length - 1 ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
        have h2 : p.length ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr le_rfl
        have := h_inj h1 h2 (h_eq.trans (Walk.getVert_length p).symm)
        omega
      have hu_By : u ∈ B y := by
        by_cases h_len1 : p.length = 1
        · have : u = tm.vertexMap y := by simp [u, h_len1, Walk.getVert_zero]
          exact this ▸ Finset.mem_union_left _ (Finset.mem_singleton_self _)
        · have hu_ne_y : u ≠ tm.vertexMap y := by
            intro h_eq
            have h_inj := (tm.edgePath_isPath y x hadj_yx).getVert_injOn
            have h1 : p.length - 1 ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
            have h0 : (0 : ℕ) ∈ {i | i ≤ p.length} := Set.mem_ofPred.mpr (by omega)
            exact absurd (h_inj h1 h0 (h_eq.trans (Walk.getVert_zero p).symm)) (by omega)
          have hu_not_branch : u ∉ Set.range tm.vertexMap := by
            intro ⟨w, hw⟩
            rcases tm.edgePath_avoids_branch w y x hadj_yx (hw ▸ hu_support) with rfl | rfl
            · exact hu_ne_y hw.symm
            · exact hu_ne_x hw.symm
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, by
            simp only [dif_pos hadj_yx, if_pos hlt_yx]
            exact Finset.mem_filter.mpr
              ⟨List.mem_toFinset.mpr hu_support, hu_not_branch⟩⟩)
      exact ⟨tm.vertexMap x, Finset.mem_union_left _ (Finset.mem_singleton_self _),
        u, hu_By, G.adj_symm hadj_u_x⟩

end SimpleGraph
