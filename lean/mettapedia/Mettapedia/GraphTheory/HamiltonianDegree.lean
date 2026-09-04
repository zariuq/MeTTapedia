/-
# Degree conditions for Hamiltonian cycles

A Mathlib-facing rotation-extension development of Ore's and Dirac's
theorems for finite simple graphs.

## Contents
- Hamiltonian graph definitions
- Connected from minimum degree / Ore condition
- Theorem 10.1.2 (Ore 1960): d(u) + d(v) ≥ n for non-adjacent ⟹ Hamiltonian
- Theorem 10.1.1 (Dirac 1952): δ(G) ≥ n/2 ⟹ Hamiltonian
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option linter.unusedSectionVars false

open SimpleGraph Walk Finset

namespace Mettapedia.GraphTheory.HamiltonianDegree

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### A path endpoint lemma -/

/-- In a path of length at least two, the edge between its endpoints is not
among the path edges. -/
private theorem edge_endpoints_not_mem_edges
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  intro member
  have endpointIsSecond : v = p.snd := hp.eq_snd_of_mem_edges member
  have equalVertices : p.getVert 1 = p.getVert p.length := by
    show p.snd = p.getVert p.length
    rw [← endpointIsSecond, p.getVert_length]
  have injective := hp.getVert_injOn
  exact absurd
    (injective
      (show (1 : ℕ) ∈ {index | index ≤ p.length} by simp; omega)
      (show p.length ∈ {index | index ≤ p.length} by simp)
      equalVertices)
    (by omega)

/-! ### Connectivity from minimum degree -/

/-- If δ(G) ≥ |V|/2, then G is connected.
    Proof: disjoint neighborhoods of unreachable pair. -/
theorem connected_of_minDegree_ge_half [Nonempty V]
    (hδ : Fintype.card V / 2 ≤ G.minDegree) :
    G.Connected where
  preconnected u v := by
    by_contra h
    have huv : u ≠ v := fun heq => h ⟨heq ▸ Walk.nil⟩
    have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hu hv
      rw [mem_neighborFinset] at hu hv
      exact h ⟨Walk.cons hu (Walk.cons hv.symm Walk.nil)⟩
    have hNu_sub : G.neighborFinset u ⊆ Finset.univ \ {u, v} := by
      intro w hw; rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩; push Not
      exact ⟨(mem_neighborFinset G u w |>.mp hw).ne',
             fun heq => h (heq ▸ ⟨Walk.cons (mem_neighborFinset G u w |>.mp hw) Walk.nil⟩)⟩
    have hNv_sub : G.neighborFinset v ⊆ Finset.univ \ {u, v} := by
      intro w hw; rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩; push Not
      exact ⟨fun heq => h (heq ▸ ⟨(Walk.cons (mem_neighborFinset G v w |>.mp hw) Walk.nil).reverse⟩),
             (mem_neighborFinset G v w |>.mp hw).ne'⟩
    have hcard_bound : G.degree u + G.degree v ≤ Fintype.card V - 2 := by
      have h_le : (G.neighborFinset u ∪ G.neighborFinset v).card ≤
          (Finset.univ \ ({u, v} : Finset V)).card :=
        Finset.card_le_card (Finset.union_subset hNu_sub hNv_sub)
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Finset.card_pair huv] at h_le
      exact h_le
    have hn : 2 ≤ Fintype.card V :=
      Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨u, v, huv⟩⟩
    have h_du := le_trans hδ (G.minDegree_le_degree u)
    have h_dv := le_trans hδ (G.minDegree_le_degree v)
    have h_mod := Nat.div_add_mod (Fintype.card V) 2
    omega

/-! ### Ore's condition implies connectivity -/

/-- Ore's condition implies connectivity: if ∀ non-adjacent u,v: d(u)+d(v) ≥ n,
    and n ≥ 3, then G is connected. -/
theorem connected_of_ore [Nonempty V]
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    G.Connected where
  preconnected u v := by
    by_contra h
    have huv : u ≠ v := fun heq => h ⟨heq ▸ Walk.nil⟩
    have hnadj : ¬G.Adj u v := fun hadj => h ⟨Walk.cons hadj Walk.nil⟩
    have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hu hv
      rw [mem_neighborFinset] at hu hv
      exact h ⟨Walk.cons hu (Walk.cons hv.symm Walk.nil)⟩
    have hNu_sub : G.neighborFinset u ⊆ Finset.univ \ {u, v} := by
      intro w hw; rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩; push Not
      exact ⟨(mem_neighborFinset G u w |>.mp hw).ne',
             fun heq => h (heq ▸ ⟨Walk.cons (mem_neighborFinset G u w |>.mp hw) Walk.nil⟩)⟩
    have hNv_sub : G.neighborFinset v ⊆ Finset.univ \ {u, v} := by
      intro w hw; rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩; push Not
      exact ⟨fun heq => h (heq ▸ ⟨(Walk.cons (mem_neighborFinset G v w |>.mp hw) Walk.nil).reverse⟩),
             (mem_neighborFinset G v w |>.mp hw).ne'⟩
    have hcard_bound : G.degree u + G.degree v ≤ Fintype.card V - 2 := by
      have h_le : (G.neighborFinset u ∪ G.neighborFinset v).card ≤
          (Finset.univ \ ({u, v} : Finset V)).card :=
        Finset.card_le_card (Finset.union_subset hNu_sub hNv_sub)
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Finset.card_pair huv] at h_le
      exact h_le
    have hore' := hore u v huv hnadj
    omega

/-! ### Ore's theorem (Diestel §10.1)

> "If d(u) + d(v) ≥ n for every pair of non-adjacent vertices u, v
>  in a graph G of order n ≥ 3, then G is Hamiltonian."

The proof uses the rotation-extension argument:
1. G is connected (by `connected_of_ore`).
2. Take a longest path P; all endpoint neighbors lie on P.
3. Show P visits all n vertices (otherwise extend via connectivity).
4. Close P into a Hamilton cycle via the rotation pigeonhole.
-/

/-- A path visiting all vertices has length |V| - 1. -/
private lemma path_length_of_all_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (h_all : ∀ w : V, w ∈ p.support) :
    p.length = Fintype.card V - 1 := by
  have hsup : p.support.toFinset = Finset.univ := by
    ext w; simp [List.mem_toFinset, h_all w]
  have hlen : p.support.length = Fintype.card V := by
    rw [← Finset.card_univ, ← hsup, List.toFinset_card_of_nodup hp.support_nodup]
  rw [Walk.length_support] at hlen
  omega

/-- The support tail of a rotation cycle (u→⋯→xₖ→v→⋯→xₖ₊₁→u) is a permutation
    of the original path support. Hence nodup transfers. -/
private lemma rotation_cycle_support_tail_perm {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    {k : ℕ} (hk_lt : k < p.length)
    (hadj_v_xk : G.Adj v (p.getVert k))
    (hadj_u_xk1 : G.Adj u (p.getVert (k + 1))) :
    ((p.take k).append (Walk.cons hadj_v_xk.symm
      ((p.drop (k + 1)).reverse.append
        (Walk.cons hadj_u_xk1.symm Walk.nil)))).support.tail.Perm p.support := by
  let part1 := p.take k
  let part2_rev := (p.drop (k + 1)).reverse
  let cyc := part1.append (Walk.cons hadj_v_xk.symm
    (part2_rev.append (Walk.cons hadj_u_xk1.symm Walk.nil)))
  show cyc.support.tail.Perm p.support
  -- Step 1: Compute cyc.support
  have h_cycle_sup : cyc.support =
      (p.take k).support ++ ((p.drop (k + 1)).reverse.support ++ [u]) := by
    show (part1.append (Walk.cons hadj_v_xk.symm
      (part2_rev.append (Walk.cons hadj_u_xk1.symm Walk.nil)))).support = _
    rw [Walk.support_append, Walk.support_cons, List.tail_cons,
        Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons]
  -- Step 2: Rewrite using take/drop/reverse support lemmas
  have h_take_sup : (p.take k).support = p.support.take (k + 1) :=
    Walk.support_take p k
  have h_drop_rev_sup : (p.drop (k + 1)).reverse.support =
      (p.support.drop ((k + 1) ⊓ p.length)).reverse := by
    rw [Walk.support_reverse, Walk.drop_support_eq_support_drop_min]
  have hk1_min : (k + 1) ⊓ p.length = k + 1 := Nat.min_eq_left (by omega)
  -- Step 3: Compute tail
  have h_tail : cyc.support.tail =
      p.support.tail.take k ++ (p.support.drop (k + 1)).reverse ++ [u] := by
    rw [h_cycle_sup, h_take_sup, h_drop_rev_sup, hk1_min]
    rw [List.tail_append_of_ne_nil]
    · rw [← List.drop_one, ← List.drop_one, List.drop_take,
          Nat.add_sub_cancel, ← List.append_assoc]
    · simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, Walk.support_ne_nil p⟩
  -- Step 4: Permutation chain
  rw [h_tail]
  have h_drop_tail : p.support.drop (k + 1) = p.support.tail.drop k := by
    rw [← List.drop_one, List.drop_drop, Nat.add_comm 1 k]
  rw [h_drop_tail]
  have h_sup_eq : p.support = u :: p.support.tail := by cases p <;> rfl
  have h1 : (p.support.tail.take k ++ (p.support.tail.drop k).reverse).Perm
      p.support.tail := by
    have := List.Perm.append_left (p.support.tail.take k)
      (List.reverse_perm (p.support.tail.drop k))
    rwa [List.take_append_drop] at this
  have h2 : (p.support.tail ++ [u]).Perm p.support := by
    have h_comm : (p.support.tail ++ [u]).Perm ([u] ++ p.support.tail) :=
      List.perm_append_comm
    have h_eq : [u] ++ p.support.tail = p.support := by
      change u :: p.support.tail = p.support; exact h_sup_eq.symm
    rwa [h_eq] at h_comm
  exact (h1.append_right _).trans h2

/-- **Rotation lemma**: given a Hamilton path (visits all vertices) in a graph
    satisfying Ore's condition, construct a Hamiltonian cycle.

    If endpoints are adjacent, close directly. Otherwise, the pigeonhole
    principle on d(u)+d(v) ≥ n among {0,...,n-2} gives a rotation index i
    where u ~ P.getVert(i+1) and v ~ P.getVert(i). The rotated walk
    u→⋯→xᵢ→v→⋯→xᵢ₊₁→u is a Hamiltonian cycle. -/
private lemma hamilton_path_to_cycle {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (h_all : ∀ w : V, w ∈ p.support)
    (hore_uv : ¬G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (c : G.Walk u u), c.IsHamiltonianCycle := by
  have hp_len := path_length_of_all_mem G p hp h_all
  by_cases hadj : G.Adj u v
  · -- Case 1: endpoints adjacent. Cycle = edge u→v then reverse path v→u.
    refine ⟨Walk.cons hadj p.reverse, ?_⟩
    rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
    refine ⟨?_, ?_⟩
    · rw [cons_isCycle_iff]
      exact ⟨hp.reverse, by
        rw [Walk.edges_reverse]
        exact fun h => edge_endpoints_not_mem_edges
          G hp (by omega) (List.mem_reverse.mp h)⟩
    · simp [Walk.length_cons, Walk.length_reverse, hp_len]; omega
  · -- Case 2: endpoints not adjacent. Rotation via pigeonhole.
    have hore_applied := hore_uv hadj
    -- Define index sets for the rotation:
    -- A = {i < n-1 : v ~ p.getVert i}
    -- B = {i < n-1 : u ~ p.getVert (i+1)}
    -- |A| + |B| ≥ d(u) + d(v) ≥ n > n-1, so A ∩ B ≠ ∅.
    -- Step 1: Find rotation index via pigeonhole
    have ⟨i, hi_lt, hadj_v_xi, hadj_u_xi1⟩ :
        ∃ i, i < p.length ∧ G.Adj v (p.getVert i) ∧ G.Adj u (p.getVert (i + 1)) := by
      -- Pigeonhole: define A = {i < p.length | v ~ xᵢ}, B = {i < p.length | u ~ xᵢ₊₁}
      -- Show |A| ≥ d(v), |B| ≥ d(u), both ⊆ range p.length, |A|+|B| > p.length
      classical
      let A := (Finset.range p.length).filter (fun i => G.Adj v (p.getVert i))
      let B := (Finset.range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))
      -- Key: |A| ≥ d(v) (injection: neighbor w ↦ idxOf w on path)
      have hA_card : G.degree v ≤ A.card := by
        apply Finset.card_le_card_of_injOn (fun w => p.support.idxOf w)
        · -- Maps neighborFinset v into A
          intro w hw
          have hw_sup := h_all w
          have hw_adj := mem_neighborFinset G v w |>.mp hw
          have hw_ne_v : w ≠ v := hw_adj.ne'
          show p.support.idxOf w ∈ (Finset.range p.length).filter
            (fun i => G.Adj v (p.getVert i))
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · have := List.idxOf_lt_length_of_mem hw_sup
            rw [Walk.length_support] at this
            have : p.support.idxOf w ≠ p.length := by
              intro heq
              have := p.getVert_support_idxOf hw_sup
              rw [heq, Walk.getVert_length] at this; exact hw_ne_v this.symm
            omega
          · rw [p.getVert_support_idxOf hw_sup]; exact hw_adj
        · -- Injective on neighborFinset v
          intro w₁ hw₁ w₂ hw₂ heq
          have e1 := p.getVert_support_idxOf (h_all w₁)
          have e2 := p.getVert_support_idxOf (h_all w₂)
          exact e1.symm.trans ((congrArg p.getVert heq).trans e2)
      -- Key: |B| ≥ d(u) (injection: neighbor w ↦ (idxOf w) - 1)
      have hB_card : G.degree u ≤ B.card := by
        apply Finset.card_le_card_of_injOn (fun w => p.support.idxOf w - 1)
        · -- Maps neighborFinset u into B
          intro w hw
          have hw_sup := h_all w
          have hw_adj := mem_neighborFinset G u w |>.mp hw
          have hw_ne_u : w ≠ u := hw_adj.ne'
          have hidx_pos : 0 < p.support.idxOf w := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf hw_sup
            rw [show p.support.idxOf w = 0 by omega, Walk.getVert_zero] at this
            exact hw_ne_u this.symm
          have hidx_lt : p.support.idxOf w < p.length + 1 := by
            rw [← Walk.length_support]; exact List.idxOf_lt_length_of_mem hw_sup
          show p.support.idxOf w - 1 ∈ (Finset.range p.length).filter
            (fun i => G.Adj u (p.getVert (i + 1)))
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
          rw [show p.support.idxOf w - 1 + 1 = p.support.idxOf w from by omega]
          rw [p.getVert_support_idxOf hw_sup]; exact hw_adj
        · -- Injective on neighborFinset u
          intro w₁ hw₁ w₂ hw₂ heq
          have hadj1 := (mem_neighborFinset G u w₁ |>.mp hw₁)
          have hadj2 := (mem_neighborFinset G u w₂ |>.mp hw₂)
          have hpos1 : 0 < p.support.idxOf w₁ := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf (h_all w₁)
            rw [show p.support.idxOf w₁ = 0 by omega, Walk.getVert_zero] at this
            exact hadj1.ne' this.symm
          have hpos2 : 0 < p.support.idxOf w₂ := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf (h_all w₂)
            rw [show p.support.idxOf w₂ = 0 by omega, Walk.getVert_zero] at this
            exact hadj2.ne' this.symm
          have hidx_eq : p.support.idxOf w₁ = p.support.idxOf w₂ := by
            have h : p.support.idxOf w₁ - 1 = p.support.idxOf w₂ - 1 := heq
            omega
          exact (p.getVert_support_idxOf (h_all w₁)).symm |>.trans
            ((congrArg p.getVert hidx_eq).trans (p.getVert_support_idxOf (h_all w₂)))
      -- Pigeonhole: |A| + |B| > |range p.length| = p.length
      have hpig : A.card + B.card > p.length := by
        calc A.card + B.card
            ≥ G.degree v + G.degree u := Nat.add_le_add hA_card hB_card
          _ ≥ Fintype.card V := by omega
          _ > Fintype.card V - 1 := by omega
          _ = p.length := by omega
      -- A and B are subsets of range p.length
      have hA_sub : A ⊆ Finset.range p.length := Finset.filter_subset _ _
      have hB_sub : B ⊆ Finset.range p.length := Finset.filter_subset _ _
      -- By pigeonhole: A ∩ B ≠ ∅
      have hinter : (A ∩ B).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hunion : (A ∪ B).card ≤ (Finset.range p.length).card :=
          Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
        simp at hunion
        have := Finset.card_union_add_card_inter A B
        rw [hempty, Finset.card_empty] at this
        omega
      obtain ⟨j, hj⟩ := hinter
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
      exact ⟨j, Finset.mem_range.mp hj.1.1, hj.1.2, hj.2.2⟩
    -- Step 2: Construct the rotation cycle
    -- u → x₁ → ⋯ → xᵢ → v → xₙ₋₂ → ⋯ → xᵢ₊₁ → u
    have hi1_le : i + 1 ≤ p.length := by omega
    let part1 := p.take i                       -- u → ⋯ → xᵢ
    let edge1 := hadj_v_xi.symm                 -- xᵢ → v
    let part2_rev := (p.drop (i + 1)).reverse    -- v → ⋯ → xᵢ₊₁
    let edge2 := hadj_u_xi1.symm                 -- xᵢ₊₁ → u
    let cycle : G.Walk u u :=
      part1.append (Walk.cons edge1 (part2_rev.append (Walk.cons edge2 Walk.nil)))
    refine ⟨cycle, ?_⟩
    -- Step 3: Show it's a Hamiltonian cycle
    rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
    refine ⟨?_, ?_⟩
    · -- IsCycle: the rotated walk is a cycle
      rw [isCycle_iff_isPath_tail_and_le_length]
      refine ⟨?_, ?_⟩
      · -- cycle.tail.IsPath: show cycle.support.tail ~ p.support (permutation), hence nodup
        -- Step 1: Compute cycle.support.tail
        -- cycle = part1.append (cons edge1 (part2_rev.append (cons edge2 nil)))
        -- cycle.support = part1.support ++ (cons edge1 inner).support.tail
        --              = (p.take i).support ++ inner.support
        -- where inner = part2_rev.append (cons edge2 nil)
        -- inner.support = part2_rev.support ++ (cons edge2 nil).support.tail = part2_rev.support ++ [u]
        -- = (p.drop(i+1)).reverse.support ++ [u] = (p.support.drop(i+1)).reverse ++ [u]
        -- cycle.support = p.support.take(i+1) ++ (p.support.drop(i+1)).reverse ++ [u]
        -- cycle.support.tail = (p.support.take(i+1)).tail ++ ... = p.support.tail.take i ++ ...
        -- cycle.support.tail is a permutation of p.support, hence nodup.
        -- Build the permutation chain step by step.
        -- Step 1: Compute cycle.support using Walk support lemmas
        have h_cycle_sup : cycle.support =
            (p.take i).support ++ ((p.drop (i + 1)).reverse.support ++ [u]) := by
          show (part1.append (Walk.cons edge1
            (part2_rev.append (Walk.cons edge2 Walk.nil)))).support = _
          rw [Walk.support_append, Walk.support_cons, List.tail_cons,
              Walk.support_append, Walk.support_cons, Walk.support_nil, List.tail_cons]
        -- Step 2: Rewrite using take/drop/reverse support lemmas
        have h_take_sup : (p.take i).support = p.support.take (i + 1) :=
          Walk.support_take p i
        have h_drop_rev_sup : (p.drop (i + 1)).reverse.support =
            (p.support.drop ((i + 1) ⊓ p.length)).reverse := by
          rw [Walk.support_reverse, Walk.drop_support_eq_support_drop_min]
        have hi1_min : (i + 1) ⊓ p.length = i + 1 := Nat.min_eq_left (by omega)
        -- Step 3: cycle.support.tail = p.support.tail.take i ++ (p.support.drop(i+1)).reverse ++ [u]
        have h_tail : cycle.support.tail =
            p.support.tail.take i ++ (p.support.drop (i + 1)).reverse ++ [u] := by
          rw [h_cycle_sup, h_take_sup, h_drop_rev_sup, hi1_min]
          -- (p.support.take(i+1) ++ ...).tail = p.support.tail.take i ++ ...
          rw [List.tail_append_of_ne_nil]
          · -- (take(i+1)).tail ++ (rev ++ [u]) = (tail.take i ++ rev) ++ [u]
            -- Use drop_take: (take j l).drop i = (drop i l).take (j - i)
            rw [← List.drop_one, ← List.drop_one, List.drop_take,
                Nat.add_sub_cancel, ← List.append_assoc]
          · simp only [ne_eq, List.take_eq_nil_iff, not_or]
            exact ⟨by omega, Walk.support_ne_nil p⟩
        -- Step 4: Show this is a permutation of p.support
        have h_perm : cycle.support.tail.Perm p.support := by
          rw [h_tail]
          have h_drop_tail : p.support.drop (i + 1) = p.support.tail.drop i := by
            rw [← List.drop_one, List.drop_drop, Nat.add_comm 1 i]
          rw [h_drop_tail]
          have h_sup_eq : p.support = u :: p.support.tail := by cases p <;> rfl
          -- take i ++ (drop i).reverse ~ tail (via reverse_perm + take_append_drop)
          have h1 : (p.support.tail.take i ++ (p.support.tail.drop i).reverse).Perm
              p.support.tail := by
            have := List.Perm.append_left (p.support.tail.take i)
              (List.reverse_perm (p.support.tail.drop i))
            rwa [List.take_append_drop] at this
          -- tail ++ [u] ~ p.support (via perm_append_comm)
          have h2 : (p.support.tail ++ [u]).Perm p.support := by
            have h_comm : (p.support.tail ++ [u]).Perm ([u] ++ p.support.tail) :=
              List.perm_append_comm
            have h_eq : [u] ++ p.support.tail = p.support := by
              change u :: p.support.tail = p.support; exact h_sup_eq.symm
            rwa [h_eq] at h_comm
          exact (h1.append_right _).trans h2
        have h_not_nil : ¬ cycle.Nil :=
          fun h => Walk.not_nil_cons (Walk.nil_append_iff.mp h).2
        exact Walk.IsPath.mk'
          (Walk.support_tail_of_not_nil cycle h_not_nil ▸
           h_perm.nodup_iff.mpr hp.support_nodup)
      · -- 3 ≤ cycle.length: follows from length = n ≥ 3
        have h2' : part1.length = i := by
          show (p.take i).length = i
          rw [Walk.take_length, Nat.min_eq_left (by omega : i ≤ p.length)]
        have h3' : part2_rev.length = p.length - (i + 1) := by
          show (p.drop (i + 1)).reverse.length = p.length - (i + 1)
          rw [Walk.length_reverse, Walk.drop_length]
        show 3 ≤ (part1.append (Walk.cons edge1 (part2_rev.append (Walk.cons edge2 Walk.nil)))).length
        rw [Walk.length_append, Walk.length_cons, Walk.length_append,
            Walk.length_cons, Walk.length_nil, h2', h3', hp_len]
        omega
    · -- Length = n: i + 1 + (p.length - (i+1)) + 1 = p.length + 1 = n
      have h2 : part1.length = i := by
        show (p.take i).length = i
        rw [Walk.take_length, Nat.min_eq_left (by omega : i ≤ p.length)]
      have h3 : part2_rev.length = p.length - (i + 1) := by
        show (p.drop (i + 1)).reverse.length = p.length - (i + 1)
        rw [Walk.length_reverse, Walk.drop_length]
      show (part1.append (Walk.cons edge1 (part2_rev.append (Walk.cons edge2 Walk.nil)))).length
           = Fintype.card V
      rw [Walk.length_append, Walk.length_cons, Walk.length_append,
          Walk.length_cons, Walk.length_nil]
      rw [h2, h3, hp_len]; omega

/-- **Extension lemma**: in a connected graph satisfying Ore's condition
    with n ≥ 3, the longest path visits all vertices.

    If some vertex w is missing, connectivity gives a path from w to P.
    The rotation (from the Ore degree condition) creates a cycle through
    P's vertices. Breaking the cycle at w's connection point yields a
    longer path, contradicting maximality. -/
private lemma longest_path_visits_all [Nonempty V]
    (hconn : G.Connected)
    (hore : ∀ u v : V, u ≠ v → ¬G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length) :
    ∀ w : V, w ∈ p.support := by
  -- By contradiction: if some vertex is missing from the longest path,
  -- we can construct a longer path, contradicting maximality.
  by_contra h; push Not at h
  obtain ⟨w, hw⟩ := h
  -- Step 1: All neighbors of u are on P (otherwise extend at u-end)
  have h_nbrs_u : ∀ z, G.Adj u z → z ∈ p.support := by
    intro z hz; by_contra hz_not
    have hpath : (Walk.cons hz.symm p).IsPath :=
      (Walk.cons_isPath_iff _ _).mpr ⟨hp, hz_not⟩
    have hlen := Walk.length_cons hz.symm p
    exact absurd (hmax _ _ _ hpath) (by omega)
  -- Step 2: All neighbors of v are on P (otherwise extend at v-end)
  have h_nbrs_v : ∀ z, G.Adj v z → z ∈ p.support := by
    intro z hz; by_contra hz_not
    have hpath : (Walk.cons hz.symm p.reverse).IsPath := by
      rw [Walk.cons_isPath_iff]
      exact ⟨hp.reverse, by rwa [Walk.support_reverse, List.mem_reverse]⟩
    have hlen := Walk.length_cons hz.symm p.reverse
    rw [Walk.length_reverse] at hlen
    exact absurd (hmax _ _ _ hpath) (by omega)
  -- Step 3: Since G connected and V(P) ⊊ V, ∃ edge from V\V(P) to V(P)
  -- Walk from w to u crosses from V\V(P) to V(P); the crossing edge is our witness.
  have ⟨z, hz_not, xj, hxj_mem, hadj⟩ :
      ∃ z, z ∉ p.support ∧ ∃ xj, xj ∈ p.support ∧ G.Adj z xj := by
    obtain ⟨q⟩ := hconn w u  -- walk from w to u
    have hu_mem : u ∈ p.support := Walk.start_mem_support p
    -- Walk from w (∉ V(P)) to u (∈ V(P)) crosses boundary via getVert indexing.
    -- Find first index j where q.getVert j ∈ p.support; then j-1 gives the outside vertex.
    have hq_end : q.getVert q.length ∈ p.support := by rwa [Walk.getVert_length]
    have hq_start : q.getVert 0 ∉ p.support := by rwa [Walk.getVert_zero]
    -- Use Nat.find to get the first touching index
    classical
    let P := fun i => q.getVert i ∈ p.support ∧ i ≤ q.length
    have hP_exists : ∃ i, P i := ⟨q.length, hq_end, le_rfl⟩
    let j := Nat.find hP_exists
    have hj_spec := Nat.find_spec hP_exists
    have hj_mem : q.getVert j ∈ p.support := hj_spec.1
    have hj_le : j ≤ q.length := hj_spec.2
    have hj_min : ∀ k, k < j → ¬P k := fun k hk => Nat.find_min hP_exists hk
    -- j ≥ 1 since q.getVert 0 = w ∉ p.support
    have hj_pos : 0 < j := by
      by_contra h0; push Not at h0
      have h0' : j = 0 := by omega
      exact hq_start (h0' ▸ hj_mem)
    -- q.getVert (j-1) ∉ p.support (by minimality of j)
    have hprev_not : q.getVert (j - 1) ∉ p.support := by
      intro hmem
      exact hj_min (j - 1) (by omega) ⟨hmem, by omega⟩
    -- j-1 < q.length
    have hprev_lt : j - 1 < q.length := by omega
    -- Adjacent: q.getVert (j-1) ~ q.getVert j
    have hadj_cross := q.adj_getVert_succ hprev_lt
    rw [show j - 1 + 1 = j from by omega] at hadj_cross
    exact ⟨q.getVert (j - 1), hprev_not, q.getVert j, hj_mem, hadj_cross⟩
  -- Step 4: z can't be adjacent to u or v (steps 1,2 + z ∉ V(P))
  have hxj_ne_u : xj ≠ u := by
    intro heq; subst heq; exact hz_not (h_nbrs_u z hadj.symm)
  have hxj_ne_v : xj ≠ v := by
    intro heq; subst heq; exact hz_not (h_nbrs_v z hadj.symm)
  -- Step 5: z adjacent to interior vertex xj → construct longer path → contradiction
  -- Since xj ∈ p.support and xj ≠ u, xj ≠ v, we can find its index j on the path.
  have hxj_sup := hxj_mem
  -- Get the index j of xj on the path
  let j := p.support.idxOf xj
  have hj_lt : j < p.support.length := List.idxOf_lt_length_of_mem hxj_sup
  have hj_vert : p.getVert j = xj := p.getVert_support_idxOf hxj_sup
  have hj_lt_len : j < p.length + 1 := by rwa [Walk.length_support] at hj_lt
  -- j ≥ 1 since xj ≠ u = p.getVert 0
  have hj_pos : 0 < j := by
    by_contra h0; push Not at h0
    have : j = 0 := by omega
    rw [this, Walk.getVert_zero] at hj_vert
    exact hxj_ne_u hj_vert.symm
  -- j ≤ p.length - 1 since xj ≠ v = p.getVert p.length
  have hj_lt_len' : j < p.length := by
    by_contra h_ge; push Not at h_ge
    have : j = p.length := by omega
    rw [this, Walk.getVert_length] at hj_vert
    exact hxj_ne_v hj_vert.symm
  -- Case split: u ~ v (direct cycle) or u ≁ v (rotation via Ore)
  by_cases hadj_uv : G.Adj u v
  · -- Case A: u ~ v. Construct longer path via cycle.
    -- Path: z → xj → xj+1 → ... → v → u → x₁ → ... → xj₋₁
    -- Length: 1 + (p.length - j) + 1 + (j - 1) = p.length + 1
    -- Rewrite adjacency to use path indexing
    have hadj' : G.Adj z (p.getVert j) := hj_vert ▸ hadj
    let extended : G.Walk z (p.getVert (j - 1)) :=
      Walk.cons hadj'
        ((p.drop j).append (Walk.cons hadj_uv.symm (p.take (j - 1))))
    have hext_len : extended.length = p.length + 1 := by
      show (Walk.cons hadj' ((p.drop j).append
        (Walk.cons hadj_uv.symm (p.take (j - 1))))).length = p.length + 1
      rw [Walk.length_cons, Walk.length_append, Walk.length_cons, Walk.drop_length,
          Walk.take_length, Nat.min_eq_left (by omega : j - 1 ≤ p.length)]
      omega
    -- The extended walk is a path: its support = z :: (rotation of p.support)
    have hext_path : extended.IsPath := by
      apply Walk.IsPath.mk'
      -- extended.support = z :: (p.drop j).support ++ (p.take (j-1)).support
      show (Walk.cons hadj' ((p.drop j).append
        (Walk.cons hadj_uv.symm (p.take (j - 1))))).support.Nodup
      rw [Walk.support_cons, Walk.support_append]
      -- = z :: (p.drop j).support ++ (Walk.cons hadj_uv.symm (p.take (j-1))).support.tail
      -- (Walk.cons h q).support.tail = q.support
      simp only [Walk.support_cons, List.tail_cons]
      -- = z :: (p.drop j).support ++ (p.take (j-1)).support
      -- Now show this is z :: p.support.rotate j
      rw [Walk.drop_support_eq_support_drop_min, Walk.support_take,
          show j ⊓ p.length = j from Nat.min_eq_left (by omega),
          show j - 1 + 1 = j from by omega]
      -- = z :: p.support.drop j ++ p.support.take j = z :: p.support.rotate j
      rw [← List.rotate_eq_drop_append_take (by rw [Walk.length_support]; omega)]
      -- Nodup: z ∉ p.support.rotate j and p.support.rotate j is nodup
      apply List.Nodup.cons
      · -- z ∉ p.support.rotate j
        rw [List.mem_rotate]; exact hz_not
      · -- p.support.rotate j is nodup (rotation preserves nodup)
        rw [List.nodup_rotate]; exact hp.support_nodup
    exact absurd (hmax _ _ _ hext_path) (by omega)
  · -- Case B: u ≁ v. By Ore: d(u) + d(v) ≥ n > p.length + 1.
    -- Step B1: u ≠ v (a closed path of length ≥ 1 repeats its endpoint)
    have huv_ne : u ≠ v := by
      intro heq; subst heq
      have nilPath := SimpleGraph.Walk.isPath_iff_nil.mp hp
      rw [nilPath.length_eq_zero] at hj_lt_len'
      omega
    -- Step B2: Apply Ore condition
    have hore_uv := hore u v huv_ne hadj_uv
    -- Step B3: p.length < n (since w ∉ p.support and p is a path)
    have hp_short : p.length + 1 < Fintype.card V := by
      have h_card_sub : p.support.toFinset.card < Fintype.card V := by
        have := Finset.card_lt_card (s := p.support.toFinset) (t := Finset.univ)
          ⟨fun x hx => Finset.mem_univ x,
           fun h => hw (List.mem_toFinset.mp (h (Finset.mem_univ w)))⟩
        simpa
      rwa [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at h_card_sub
    -- Step B4: Pigeonhole — find rotation index k
    have ⟨k, hk_lt, hadj_v_xk, hadj_u_xk1⟩ :
        ∃ k, k < p.length ∧ G.Adj v (p.getVert k) ∧ G.Adj u (p.getVert (k + 1)) := by
      classical
      let A := (Finset.range p.length).filter (fun i => G.Adj v (p.getVert i))
      let B := (Finset.range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))
      have hA_card : G.degree v ≤ A.card := by
        apply Finset.card_le_card_of_injOn (fun w => p.support.idxOf w)
        · intro x hx
          have hx_sup := h_nbrs_v x (mem_neighborFinset G v x |>.mp hx)
          have hx_ne_v := (mem_neighborFinset G v x |>.mp hx).ne'
          show p.support.idxOf x ∈ (Finset.range p.length).filter
            (fun i => G.Adj v (p.getVert i))
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · have := List.idxOf_lt_length_of_mem hx_sup
            rw [Walk.length_support] at this
            have : p.support.idxOf x ≠ p.length := by
              intro heq
              have := p.getVert_support_idxOf hx_sup
              rw [heq, Walk.getVert_length] at this
              exact hx_ne_v this.symm
            omega
          · rw [p.getVert_support_idxOf hx_sup]
            exact mem_neighborFinset G v x |>.mp hx
        · intro w₁ hw₁ w₂ hw₂ heq
          have e1 := p.getVert_support_idxOf (h_nbrs_v w₁ (mem_neighborFinset G v w₁ |>.mp hw₁))
          have e2 := p.getVert_support_idxOf (h_nbrs_v w₂ (mem_neighborFinset G v w₂ |>.mp hw₂))
          exact e1.symm.trans ((congrArg p.getVert heq).trans e2)
      have hB_card : G.degree u ≤ B.card := by
        apply Finset.card_le_card_of_injOn (fun w => p.support.idxOf w - 1)
        · intro x hx
          have hx_sup := h_nbrs_u x (mem_neighborFinset G u x |>.mp hx)
          have hx_adj := mem_neighborFinset G u x |>.mp hx
          have hx_ne_u := hx_adj.ne'
          have hidx_pos : 0 < p.support.idxOf x := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf hx_sup
            rw [show p.support.idxOf x = 0 by omega, Walk.getVert_zero] at this
            exact hx_ne_u this.symm
          have hidx_lt : p.support.idxOf x < p.length + 1 := by
            rw [← Walk.length_support]; exact List.idxOf_lt_length_of_mem hx_sup
          show p.support.idxOf x - 1 ∈ (Finset.range p.length).filter
            (fun i => G.Adj u (p.getVert (i + 1)))
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
          rw [show p.support.idxOf x - 1 + 1 = p.support.idxOf x from by omega]
          rw [p.getVert_support_idxOf hx_sup]; exact hx_adj
        · intro w₁ hw₁ w₂ hw₂ heq
          have hadj1 := mem_neighborFinset G u w₁ |>.mp hw₁
          have hadj2 := mem_neighborFinset G u w₂ |>.mp hw₂
          have hpos1 : 0 < p.support.idxOf w₁ := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf (h_nbrs_u w₁ hadj1)
            rw [show p.support.idxOf w₁ = 0 by omega, Walk.getVert_zero] at this
            exact hadj1.ne' this.symm
          have hpos2 : 0 < p.support.idxOf w₂ := by
            by_contra h0; push Not at h0
            have := p.getVert_support_idxOf (h_nbrs_u w₂ hadj2)
            rw [show p.support.idxOf w₂ = 0 by omega, Walk.getVert_zero] at this
            exact hadj2.ne' this.symm
          have hidx_eq : p.support.idxOf w₁ = p.support.idxOf w₂ := by
            have h : p.support.idxOf w₁ - 1 = p.support.idxOf w₂ - 1 := heq
            omega
          exact (p.getVert_support_idxOf (h_nbrs_u w₁ hadj1)).symm |>.trans
            ((congrArg p.getVert hidx_eq).trans (p.getVert_support_idxOf (h_nbrs_u w₂ hadj2)))
      have hpig : A.card + B.card > p.length := by
        calc A.card + B.card
            ≥ G.degree v + G.degree u := Nat.add_le_add hA_card hB_card
          _ ≥ Fintype.card V := by omega
          _ > p.length + 1 := hp_short
          _ > p.length := by omega
      have hA_sub : A ⊆ Finset.range p.length := Finset.filter_subset _ _
      have hB_sub : B ⊆ Finset.range p.length := Finset.filter_subset _ _
      have hinter : (A ∩ B).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hunion : (A ∪ B).card ≤ (Finset.range p.length).card :=
          Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
        simp at hunion
        have := Finset.card_union_add_card_inter A B
        rw [hempty, Finset.card_empty] at this; omega
      obtain ⟨m, hm⟩ := hinter
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hm
      exact ⟨m, Finset.mem_range.mp hm.1.1, hm.1.2, hm.2.2⟩
    -- Step B5: Construct rotation cycle
    have hk1_le : k + 1 ≤ p.length := by omega
    let cyc : G.Walk u u :=
      (p.take k).append (Walk.cons hadj_v_xk.symm
        ((p.drop (k + 1)).reverse.append (Walk.cons hadj_u_xk1.symm Walk.nil)))
    -- Step B6: Show xj ∈ cyc.support (cycle visits all p vertices)
    have hxj_in_cyc : xj ∈ cyc.support := by
      show xj ∈ ((p.take k).append _).support
      rw [Walk.mem_support_append_iff]
      by_cases hjk : j ≤ k
      · -- xj is in (p.take k).support
        left
        have : (p.take k).getVert j = xj := by
          rw [Walk.take_getVert, show k ⊓ j = j from Nat.min_eq_right hjk, hj_vert]
        exact this ▸ Walk.getVert_mem_support (p.take k) j
      · -- xj is in (p.drop(k+1)).reverse.support, hence in cycle
        push Not at hjk
        right
        have hxj_rev : xj ∈ (p.drop (k + 1)).reverse.support := by
          rw [Walk.support_reverse, List.mem_reverse]
          have : (p.drop (k + 1)).getVert (j - (k + 1)) = xj := by
            rw [Walk.drop_getVert, show k + 1 + (j - (k + 1)) = j from by omega, hj_vert]
          exact this ▸ Walk.getVert_mem_support (p.drop (k + 1)) (j - (k + 1))
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ ((Walk.mem_support_append_iff _ _).mpr (Or.inl hxj_rev))
    -- Step B7: Rotate cycle to start at xj, use tail.reverse for extension
    have hadj_z_xj : G.Adj z xj := hadj
    let cyc' := cyc.rotate xj hxj_in_cyc
    -- Cycle length = p.length + 1
    have hcyc_len : cyc.length = p.length + 1 := by
      show ((p.take k).append (Walk.cons hadj_v_xk.symm
        ((p.drop (k + 1)).reverse.append (Walk.cons hadj_u_xk1.symm Walk.nil)))).length
        = p.length + 1
      rw [Walk.length_append, Walk.length_cons, Walk.length_append,
          Walk.length_cons, Walk.length_nil, Walk.take_length,
          Nat.min_eq_left (by omega : k ≤ p.length),
          Walk.length_reverse, Walk.drop_length]
      omega
    -- Rotated cycle length = cycle length
    have hcyc'_len : cyc'.length = p.length + 1 := by
      show (cyc.rotate xj hxj_in_cyc).length = p.length + 1
      unfold Walk.rotate
      rw [Walk.length_append]
      have := Walk.take_spec cyc hxj_in_cyc
      have h := congrArg Walk.length this
      simp only [Walk.length_append] at h
      omega
    have h_not_nil : ¬ cyc'.Nil :=
      Walk.not_nil_iff_lt_length.mpr (by rw [hcyc'_len]; omega)
    -- Extended walk: z → xj → (reverse of cyc'.tail)
    let ext := Walk.cons hadj_z_xj cyc'.tail.reverse
    -- Step B8: ext.length = p.length + 1
    have hext_len : ext.length = p.length + 1 := by
      show (Walk.cons hadj_z_xj cyc'.tail.reverse).length = p.length + 1
      rw [Walk.length_cons, Walk.length_reverse,
          Walk.length_tail_add_one h_not_nil, hcyc'_len]
    -- Step B9: ext.IsPath (nodup from cycle tail nodup)
    have h_cyc_tail_perm := rotation_cycle_support_tail_perm G p hp hk_lt hadj_v_xk hadj_u_xk1
    have h_cyc_tail_nodup : cyc.support.tail.Nodup :=
      h_cyc_tail_perm.nodup_iff.mpr hp.support_nodup
    have h_cyc'_tail_nodup : cyc'.support.tail.Nodup :=
      (Walk.support_rotate cyc xj hxj_in_cyc).nodup_iff.mpr h_cyc_tail_nodup
    have h_tail_sup := Walk.support_tail_of_not_nil cyc' h_not_nil
    have hext_path : ext.IsPath := by
      apply Walk.IsPath.mk'
      show (Walk.cons hadj_z_xj cyc'.tail.reverse).support.Nodup
      rw [Walk.support_cons, Walk.support_reverse]
      apply List.Nodup.cons
      · -- z ∉ cyc'.tail.support.reverse
        rw [List.mem_reverse, h_tail_sup]
        intro h_mem
        have h_mem_cyc : z ∈ cyc.support :=
          (Walk.mem_support_rotate_iff cyc xj hxj_in_cyc).mp
            (List.mem_of_mem_tail h_mem)
        have h_cyc_sub : ∀ w, w ∈ cyc.support → w ∈ p.support := by
          intro w hw
          have : w ∈ ((p.take k).append _).support := hw
          rw [Walk.mem_support_append_iff] at this
          rcases this with hw₁ | hw₂
          · rw [Walk.support_take] at hw₁
            exact List.take_subset _ _ hw₁
          · rw [Walk.support_cons, List.mem_cons] at hw₂
            rcases hw₂ with rfl | hw₃
            · exact Walk.getVert_mem_support p k
            · rw [Walk.mem_support_append_iff] at hw₃
              rcases hw₃ with hw₄ | hw₅
              · rw [Walk.support_reverse, List.mem_reverse,
                    Walk.drop_support_eq_support_drop_min,
                    show (k + 1) ⊓ p.length = k + 1 from
                      Nat.min_eq_left (by omega)] at hw₄
                exact List.drop_subset _ _ hw₄
              · rw [Walk.support_cons, Walk.support_nil,
                    List.mem_cons, List.mem_singleton] at hw₅
                rcases hw₅ with rfl | rfl
                · exact Walk.getVert_mem_support p (k + 1)
                · exact Walk.start_mem_support p
        exact hz_not (h_cyc_sub z h_mem_cyc)
      · -- cyc'.tail.support.reverse.Nodup
        rw [List.nodup_reverse, h_tail_sup]
        exact h_cyc'_tail_nodup
    exact absurd (hmax _ _ _ hext_path) (by omega)

/-- **Theorem 10.1.2** (Ore 1960): if |V| ≥ 3 and d(u) + d(v) ≥ |V|
    for all non-adjacent pairs, then G is Hamiltonian.
    (Diestel §10.1, p. 233)

    Proof structure:
    1. G is connected (by `connected_of_ore`).
    2. Take a longest path P.
    3. P visits all n vertices (by `longest_path_visits_all`).
    4. Close P into a Hamilton cycle (by `hamilton_path_to_cycle`). -/
theorem ore_theorem (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff]; omega
  have hconn := connected_of_ore G hn hore
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have h_all := longest_path_visits_all G hconn hore p hp hmax
  have huv : u ≠ v := by
    intro heq; subst heq
    have hp_len := path_length_of_all_mem G p hp h_all
    have hp_nil := SimpleGraph.Walk.isPath_iff_nil.mp hp
    rw [hp_nil.length_eq_zero] at hp_len
    omega
  obtain ⟨c, hc⟩ := hamilton_path_to_cycle G p hp h_all
    (fun hnadj => hore u v huv hnadj) hn
  intro _; exact ⟨u, c, hc⟩

/-! ### Dirac's theorem (Diestel §10.1)

> "Every graph G with n ≥ 3 vertices and δ(G) ≥ n/2 has a Hamilton cycle."

Dirac's condition implies Ore's condition: if δ ≥ ⌈n/2⌉ (i.e., n ≤ 2δ),
then for every non-adjacent pair u,v: d(u) + d(v) ≥ 2δ ≥ n.
-/

/-- **Theorem 10.1.1** (Dirac 1952): if |V| ≥ 3 and δ(G) ≥ ⌈|V|/2⌉,
    then G is Hamiltonian.
    (Diestel §10.1, p. 233)

    The condition `|V| ≤ 2 * δ(G)` is equivalent to `δ(G) ≥ ⌈|V|/2⌉`,
    matching Diestel's "δ(G) ≥ n/2" (real division).

    Proof: Dirac's condition implies Ore's condition. -/
theorem dirac_theorem (hn : 3 ≤ Fintype.card V)
    (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    G.IsHamiltonian := by
  apply ore_theorem G hn
  intro u v _ _
  have h_du := G.minDegree_le_degree u
  have h_dv := G.minDegree_le_degree v
  omega

end Mettapedia.GraphTheory.HamiltonianDegree
