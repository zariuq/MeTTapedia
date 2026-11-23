/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Long paths, long cycles and short cycles

Diestel, *Graph Theory*, Propositions 1.3.1 and 1.3.2, for finite graphs.

## Main results

* `SimpleGraph.exists_isPath_minDegree_le_length`: a path of length at least `δ(G)`.
* `SimpleGraph.exists_isCycle_minDegree_add_one_le_length`: if `δ(G) ≥ 2`, a cycle of
  length at least `δ(G) + 1`.
* `SimpleGraph.girth_le_two_mul_diam_add_one`, `SimpleGraph.egirth_le_two_mul_ediam_add_one`:
  a graph with a cycle has girth at most `2 · diam + 1` (two TODOs of Mathlib's
  `SimpleGraph/Girth.lean`, here for finite graphs).
-/

namespace SimpleGraph

open Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- If `p` is a path of maximum length ending at `v`, then every
    neighbour of `v` lies on `p`. -/
private theorem mem_support_of_adj_of_longest_path [Nonempty V]
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length)
    {w : V} (hadj : G.Adj v w) :
    w ∈ p.support := by
  by_contra hw
  have hle := hmax u w (p.concat hadj) (hp.concat hw hadj)
  rw [length_concat] at hle; omega

/-- Given a longest path, its length is at least the minimum degree. -/
private theorem minDegree_le_length_of_longest_path [Nonempty V]
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length) :
    G.minDegree ≤ p.length := by
  have hmem : ∀ w, G.Adj v w → w ∈ p.support :=
    fun w hadj => mem_support_of_adj_of_longest_path G hp hmax hadj
  have hsub : G.neighborFinset v ⊆ p.support.toFinset.erase v := by
    intro w hw
    rw [Finset.mem_erase, List.mem_toFinset]
    have hadj : G.Adj v w := by rwa [mem_neighborFinset] at hw
    exact ⟨hadj.ne', hmem w hadj⟩
  calc G.minDegree
      ≤ G.degree v := G.minDegree_le_degree v
    _ ≤ (p.support.toFinset.erase v).card := Finset.card_le_card hsub
    _ ≤ p.length := by
        rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr (end_mem_support p)),
            List.toFinset_card_of_nodup hp.support_nodup, length_support]
        omega

/-- Diestel, Proposition 1.3.1 (path part).
    Every finite non-empty graph contains a path of length ≥ δ(G). -/
theorem exists_isPath_minDegree_le_length [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ G.minDegree ≤ p.length := by
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  exact ⟨u, v, p, hp, minDegree_le_length_of_longest_path G hp hmax⟩

/-! ### Cycle part of Proposition 1.3.1

Key structural lemma: in a path of length ≥ 2, the edge between the
endpoints is not among the walk's edges. Combined with `cons_isCycle_iff`,
this lets us close a long sub-path into a genuine cycle.
-/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a path of length ≥ 2, the edge between start and end vertices
    does not appear among the walk's edges. -/
theorem endpoints_notMem_edges_of_isPath
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  intro hmem
  -- v must be the second vertex of p (by eq_snd_of_mem_edges)
  have hsnd : v = p.snd := hp.eq_snd_of_mem_edges hmem
  -- But snd = getVert 1 and the endpoint = getVert length.
  -- By path injectivity, 1 = length, contradicting length ≥ 2.
  have hinj := hp.getVert_injOn
  have heq : p.getVert 1 = p.getVert p.length := by
    show p.snd = p.getVert p.length; rw [← hsnd, p.getVert_length]
  exact absurd (hinj (show (1 : ℕ) ∈ {i | i ≤ p.length} by simp; omega)
    (show p.length ∈ {i | i ≤ p.length} by simp) heq) (by omega)

/-- Diestel, Proposition 1.3.1 (cycle part).
    If δ(G) ≥ 2, then G contains a cycle of length ≥ δ(G) + 1.

    Proof outline: take the longest path x₀ ··· xₖ.  Among the ≥ δ(G)
    neighbours of xₖ that lie on the path, pick the one closest to x₀.
    The sub-path from that neighbour to xₖ, closed by the return edge,
    forms a cycle whose length ≥ δ(G) + 1 by a counting argument.

    The pigeonhole step finds the optimal neighbour via
    `Finset.exists_min_image`: mapping neighbours to their `idxOf` in
    the path support gives an injection into `Finset.Ico`, whose
    cardinality bounds the minimum index. -/
theorem exists_isCycle_minDegree_add_one_le_length [Nonempty V] (hδ : 2 ≤ G.minDegree) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ G.minDegree + 1 ≤ c.length := by
  -- Step 1: longest path and basic setup
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have hplen : G.minDegree ≤ p.length := minDegree_le_length_of_longest_path G hp hmax
  have hmem : ∀ w, G.Adj v w → w ∈ p.support :=
    fun w hadj => mem_support_of_adj_of_longest_path G hp hmax hadj
  -- Step 2: find a neighbour w with large dropUntil length
  -- (pigeonhole: d(v) distinct positions in {0,…,k−1} ⟹
  --  smallest position ≤ k − d(v) ⟹ dropUntil length ≥ d(v) ≥ δ(G))
  suffices h : ∃ w, ∃ hadj : G.Adj v w,
      G.minDegree ≤ (p.dropUntil w (hmem w hadj)).length by
    obtain ⟨w, hadj, hdrop⟩ := h
    -- Step 3: construct cycle  v →(edge)→ w →(subpath)→ v
    set q := p.dropUntil w (hmem w hadj) with hq_def
    have hq_path : q.IsPath := hp.dropUntil _
    have hq_len : 2 ≤ q.length := le_trans hδ hdrop
    refine ⟨v, cons hadj q, ?_, ?_⟩
    · rw [cons_isCycle_iff]
      exact ⟨hq_path, Sym2.eq_swap ▸ endpoints_notMem_edges_of_isPath G hq_path hq_len⟩
    · rw [length_cons]; omega
  -- Pigeonhole: among ≥ δ(G) neighbour-indices in {0,…,p.length−1},
  -- the smallest is ≤ p.length − δ(G), so the corresponding dropUntil is long enough.
  have hne : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    exact lt_of_lt_of_le (by omega : (0 : ℕ) < G.minDegree) (G.minDegree_le_degree v)
  obtain ⟨w₀, hw₀, hmin⟩ :=
    Finset.exists_min_image (G.neighborFinset v) (fun w => p.support.idxOf w) hne
  have hadj₀ : G.Adj v w₀ := by rwa [mem_neighborFinset] at hw₀
  refine ⟨w₀, hadj₀, ?_⟩
  rw [length_dropUntil]
  have hadj_of : ∀ w, w ∈ G.neighborFinset v → G.Adj v w :=
    fun w hw => by rwa [mem_neighborFinset] at hw
  have hidx_lt : ∀ w ∈ G.neighborFinset v, p.support.idxOf w < p.length := by
    intro w hw
    rw [← length_takeUntil p (hmem w (hadj_of w hw))]
    exact length_takeUntil_lt_length _ (hadj_of w hw).ne'
  have hinj : Set.InjOn (fun w => p.support.idxOf w) ↑(G.neighborFinset v) := by
    intro w₁ hw₁ w₂ hw₂ heq
    rw [mem_coe] at hw₁ hw₂
    have e₁ := getVert_length_takeUntil (hmem w₁ (hadj_of w₁ hw₁))
    have e₂ := getVert_length_takeUntil (hmem w₂ (hadj_of w₂ hw₂))
    rw [length_takeUntil] at e₁ e₂
    have heq' : p.support.idxOf w₁ = p.support.idxOf w₂ := heq
    rw [← e₁, heq', e₂]
  have himg : (G.neighborFinset v).image (fun w => p.support.idxOf w) ⊆
      Finset.Ico (p.support.idxOf w₀) p.length := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr ⟨hmin w hw, hidx_lt w hw⟩
  calc G.minDegree
      ≤ (G.neighborFinset v).card := G.minDegree_le_degree v
    _ = ((G.neighborFinset v).image (fun w => p.support.idxOf w)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Ico (p.support.idxOf w₀) p.length).card := Finset.card_le_card himg
    _ = p.length - p.support.idxOf w₀ := Nat.card_Ico _ _

/-! ### Proposition 1.3.2 (Diestel §1.3, p. 8)

> "Every graph G containing a cycle satisfies g(G) ≤ 2 diam G + 1."
-/

omit [DecidableRel G.Adj] in
/-- **Proposition 1.3.2** (Diestel §1.3): girth ≤ 2 · diameter + 1.

    If G contains a cycle and has diameter d, then its girth g satisfies
    g ≤ 2d + 1.

    Proof idea: take a shortest cycle C of length g. Pick a vertex v on C.
    The two "halves" of C from v have lengths ⌊g/2⌋ and ⌈g/2⌉.
    The distance between the endpoints of these halves is ≤ d.
    So g = ⌊g/2⌋ + ⌈g/2⌉ ≤ d + d + 1 = 2d + 1. -/
theorem exists_isCycle_length_le_two_mul_add_one
    [Nonempty V]
    (hcycle : ∃ (v : V) (c : G.Walk v v), c.IsCycle)
    (d : ℕ) (hd : ∀ u v : V, G.dist u v ≤ d) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ 2 * d + 1 := by
  classical
  have hnotAcyclic : ¬ G.IsAcyclic := by
    intro hacyc
    obtain ⟨v, c, hc⟩ := hcycle
    exact hacyc c hc
  obtain ⟨v, c, hc, hg⟩ := (SimpleGraph.exists_girth_eq_length (G := G)).mpr hnotAcyclic
  by_cases hshort : c.length ≤ 2 * d + 1
  · exact ⟨v, c, hc, hshort⟩
  · have hlong : 2 * d + 1 < c.length := by omega
    let n : ℕ := d + 1
    let w : V := c.getVert n
    have hn_lt : n < c.length := by
      dsimp [n]
      omega
    have hw : w ∈ c.support := by
      dsimp [w]
      exact c.getVert_mem_support n
    have hwend : w ≠ v := by
      intro hwv
      have hendpoint : n = 0 ∨ n = c.length := by
        have : c.getVert n = v := by simpa [w] using hwv
        exact (hc.getVert_endpoint_iff (i := n) (hl := le_of_lt hn_lt)).mp this
      dsimp [n] at hendpoint
      omega
    let a : G.Walk v w := c.takeUntil w hw
    have ha_path : a.IsPath := by
      simpa [a] using hc.isPath_takeUntil hw
    have ha_len : a.length = d + 1 := by
      have ha_len_lt : a.length < c.length := by
        simpa [a] using c.length_takeUntil_lt_length (u := w) hw hwend
      have hget : c.getVert a.length = c.getVert n := by
        simpa [a, w] using (c.getVert_length_takeUntil (u := w) hw)
      have hlen_eq : a.length = n := hc.getVert_injOn'
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega)
        hget
      simpa [n] using hlen_eq
    have hreach : G.Reachable v w := ⟨a⟩
    obtain ⟨p, hpdist⟩ := hreach.exists_walk_length_eq_dist
    let q : G.Path v w := p.toPath
    have hq_len : ((q : G.Walk v w).length) = G.dist v w := by
      apply le_antisymm
      · calc
          ((q : G.Walk v w).length) = p.bypass.length := rfl
          _ ≤ p.length := Walk.length_bypass_le_length p
          _ = G.dist v w := hpdist
      · exact G.dist_le (q : G.Walk v w)
    have hq_len_le : ((q : G.Walk v w).length) ≤ d := by
      rw [hq_len]
      exact hd v w
    have hq_lt_a : ((q : G.Walk v w).length) < a.length := by
      rw [ha_len]
      omega
    let qW : G.Walk v w := q
    have hqW_len_le : qW.length ≤ d := by
      simpa [qW] using hq_len_le
    let H : SimpleGraph V := a.toSubgraph.spanningCoe ⊔ qW.toSubgraph.spanningCoe
    have hAle : a.toSubgraph.spanningCoe ≤ H := by
      dsimp [H]
      exact le_sup_left
    have hQle : qW.toSubgraph.spanningCoe ≤ H := by
      dsimp [H]
      exact le_sup_right
    have hHle : H ≤ G := by
      dsimp [H]
      exact sup_le a.toSubgraph.spanningCoe_le qW.toSubgraph.spanningCoe_le
    have hH_notAcyclic : ¬ H.IsAcyclic := by
      intro hacyc
      have ha_mem_H : ∀ e ∈ a.edges, e ∈ H.edgeSet := by
        intro e he
        exact (SimpleGraph.edgeSet_mono hAle) <| by
          change e ∈ a.toSubgraph.edgeSet
          exact a.mem_edges_toSubgraph.mpr he
      have hq_mem_H : ∀ e ∈ qW.edges, e ∈ H.edgeSet := by
        intro e he
        exact (SimpleGraph.edgeSet_mono hQle) <| by
          change e ∈ qW.toSubgraph.edgeSet
          exact qW.mem_edges_toSubgraph.mpr he
      let aH : H.Path v w := ⟨a.transfer H ha_mem_H, Walk.IsPath.transfer ha_mem_H ha_path⟩
      let qH : H.Path v w := ⟨qW.transfer H hq_mem_H, Walk.IsPath.transfer hq_mem_H q.property⟩
      have huniq : qH = aH := (hacyc.subsingleton_path _ _).elim qH aH
      have hlen_eq : ((qH : H.Walk v w).length) = (aH : H.Walk v w).length := by
        simpa using congrArg (fun r : H.Path v w => ((r : H.Walk v w).length)) huniq
      have : qW.length = a.length := by
        simpa [qH, aH, qW, Walk.length_transfer] using hlen_eq
      exact (Nat.ne_of_lt hq_lt_a) this
    obtain ⟨uH, cH, hcH, _⟩ := (SimpleGraph.exists_girth_eq_length (G := H)).mpr hH_notAcyclic
    have hcg_le : c.length ≤ cH.length := by
      have : G.girth ≤ cH.length := by
        simpa using (SimpleGraph.girth_le_length (G := G) (h := hcH.mapLe hHle))
      simpa [hg] using this
    have hHedge :
        H.edgeFinset = a.toSubgraph.spanningCoe.edgeFinset ∪ qW.toSubgraph.spanningCoe.edgeFinset := by
      dsimp [H]
      exact
        (SimpleGraph.edgeFinset_sup
          (G₁ := a.toSubgraph.spanningCoe) (G₂ := qW.toSubgraph.spanningCoe))
    have ha_edgeFinset : a.toSubgraph.spanningCoe.edgeFinset = a.edges.toFinset := by
      ext e
      simp [SimpleGraph.edgeFinset]
    have hq_edgeFinset : qW.toSubgraph.spanningCoe.edgeFinset = qW.edges.toFinset := by
      ext e
      simp [SimpleGraph.edgeFinset]
    have ha_edges_card : a.edges.toFinset.card = a.length := by
      rw [List.toFinset_card_of_nodup ha_path.isTrail.edges_nodup, Walk.length_edges]
    have hq_edges_card : qW.edges.toFinset.card = qW.length := by
      rw [List.toFinset_card_of_nodup q.property.isTrail.edges_nodup, Walk.length_edges]
    have hHcard : H.edgeFinset.card ≤ a.length + qW.length := by
      rw [hHedge, ha_edgeFinset, hq_edgeFinset]
      calc
        (a.edges.toFinset ∪ qW.edges.toFinset).card
            ≤ a.edges.toFinset.card + qW.edges.toFinset.card := Finset.card_union_le _ _
        _ = a.length + qW.length := by rw [ha_edges_card, hq_edges_card]
    have hcH_lt : cH.length < c.length := by
      calc
        cH.length ≤ H.edgeFinset.card := hcH.isTrail.length_le_card_edgeFinset
        _ ≤ a.length + qW.length := hHcard
        _ < c.length := by
          rw [ha_len]
          have := hqW_len_le
          omega
    exact False.elim ((Nat.not_lt_of_ge hcg_le) hcH_lt)

omit [DecidableRel G.Adj] in
/-- Diestel, Proposition 1.3.2, in Mathlib's terms: a graph with a cycle and nonzero diameter
has girth at most `2 * diam + 1`. -/
theorem girth_le_two_mul_diam_add_one (hG : ¬G.IsAcyclic) (hd : G.diam ≠ 0) :
    G.girth ≤ 2 * G.diam + 1 := by
  have := nontrivial_of_diam_ne_zero hd
  have hcycle : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
    simpa [IsAcyclic] using hG
  obtain ⟨v, c, hc, hlen⟩ := exists_isCycle_length_le_two_mul_add_one G hcycle G.diam
    (fun _ _ => dist_le_diam (ediam_ne_top_of_diam_ne_zero hd))
  exact (girth_le_length hc).trans hlen

omit [DecidableRel G.Adj] in
/-- The extended form: a graph with a cycle has extended girth at most `2 * ediam + 1`. -/
theorem egirth_le_two_mul_ediam_add_one (hG : ¬G.IsAcyclic) :
    G.egirth ≤ 2 * G.ediam + 1 := by
  by_cases htop : G.ediam = ⊤
  · simp [htop]
  have hcycle : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
    simpa [IsAcyclic] using hG
  have : Nonempty V := ⟨hcycle.choose⟩
  obtain ⟨v, c, hc, hlen⟩ := exists_isCycle_length_le_two_mul_add_one G hcycle G.diam
    (fun _ _ => dist_le_diam htop)
  calc G.egirth ≤ c.length := egirth_le_length hc
    _ ≤ ((2 * G.diam + 1 : ℕ) : ℕ∞) := by exact_mod_cast hlen
    _ = 2 * G.ediam + 1 := by
      rw [diam]
      push_cast
      rw [ENat.natCast_toNat htop]

end SimpleGraph
