/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge Lemma: Bitwise Computation Correctness

This file proves that the efficient bitwise computation in Critical17.lean
correctly computes the graph properties (triangle-free, no 6-IS).

## Strategy

For the bitwise computation to be correct, we need to prove:

1. **Adjacency Correctness**:
   `bitwiseAdj v w = true ↔ criticalGraph17.Adj v w`

2. **Triangle-Free Correctness**:
   `checkTriangleFreeBitwise = true ↔ TriangleFree criticalGraph17`

3. **No 6-IS Correctness**:
   `checkNo6IndepBitwise = true ↔ NoKIndepSet 6 criticalGraph17`

Once we prove these, the computational verification is sound.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bits
import Ramsey36.Basic
import Ramsey36.Critical17

open SimpleGraph Finset

abbrev V := Fin 17

/-! ## Define the Graph Directly (instead of importing Critical17Clean) -/

/-- The critical graph's adjacency -/
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

instance : DecidableRel adj17 := by
  intro v w
  unfold adj17
  exact Finset.decidableMem w (neighbors17 v)

def criticalGraph17 : SimpleGraph V where
  Adj := adj17
  symm := by
    intros v w h
    unfold adj17 neighbors17 at h ⊢
    fin_cases v <;> fin_cases w <;> simp at h ⊢ <;> try exact h
  loopless := by
    intro v h
    unfold adj17 neighbors17 at h
    fin_cases v <;> simp at h

/-! ## Bridge Lemma 1: Adjacency Correctness -/

/-- **Key Property**: The adjacency mask correctly encodes neighbors.

    For this to work, we need:
    - adjMask v should be a nat with bits set at positions corresponding to neighbors
    - Bit i is set iff vertex i is adjacent to v

    Strategy: Exhaustive check all 17×17 = 289 pairs using `fin_cases`.
    This is exactly what Gemini's `neighbors17_symm` did!
-/
lemma adjMask_correct (v w : V) :
    (adjMask v).testBit w.val ↔ criticalGraph17.Adj v w := by
  -- Unfold definitions
  unfold adjMask adjMasks criticalGraph17 adj17 neighbors17
  -- Check all 289 pairs exhaustively
  fin_cases v <;> fin_cases w <;> decide

/-- From adjMask correctness, we get bitwiseAdj correctness -/
lemma bitwiseAdj_correct (v w : V) :
    bitwiseAdj v w = true ↔ criticalGraph17.Adj v w := by
  sorry
  -- Should follow from:
  -- bitwiseAdj v w = (adjMask v).testBit w.val
  -- and adjMask_correct

/-! ## Bridge Lemma 2: Triangle-Free Correctness -/

/-- **Key Idea**: A graph has a triangle iff there exist v < w < u such that
    all three are pairwise adjacent.

    In bitwise terms: (adjMask v & adjMask w).testBit u = true
    means u is adjacent to both v and w, and we already know v ~ w.
-/
lemma triangle_exists_iff_bitwise :
    (∃ v w u : V, v < w ∧ w < u ∧
      criticalGraph17.Adj v w ∧
      criticalGraph17.Adj v u ∧
      criticalGraph17.Adj w u) ↔
    (∃ v w : V, v < w ∧
      (adjMask v).testBit w.val ∧  -- v ~ w
      ((adjMask v &&& adjMask w) ≠ 0)) -- ∃ u adjacent to both
    := by
  sorry
  -- Key step: show (adjMask v &&& adjMask w) has bit u set
  --   iff u is adjacent to both v and w

/-- Main bridge: checkTriangleFreeBitwise computes triangle-freedom -/
lemma checkTriangleFreeBitwise_correct :
    checkTriangleFreeBitwise = true ↔ TriangleFree criticalGraph17 := by
  sorry
  -- Should implement: check all pairs v < w where v ~ w,
  -- ensure (adjMask v &&& adjMask w) has no bits set

/-! ## Bridge Lemma 3: No 6-IS Correctness -/

/-- **Key Idea**: A set S is independent iff no two vertices in S are adjacent.

    In bitwise terms: For each v ∈ S, adjMask v should have no bits set
    at positions corresponding to other vertices in S.
-/
lemma indep_set_iff_bitwise (S : Finset V) :
    criticalGraph17.IsIndepSet (S : Set V) ↔
    (∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬(adjMask v).testBit w.val) := by
  sorry
  -- Expand IsIndepSet definition
  -- Apply adjMask_correct

/-- We can represent a set as a bitmask and check independence -/
lemma indep_set_bitmask (S : Finset V) (mask : Nat)
    (h_mask : ∀ v : V, mask.testBit v.val ↔ v ∈ S) :
    criticalGraph17.IsIndepSet (S : Set V) ↔
    (∀ v ∈ S, (adjMask v &&& mask) = (1 <<< v.val)) := by
  sorry
  -- The intersection adjMask v &&& mask should only have bit v set
  -- (every other bit in S should not be in v's neighborhood)

/-- Main bridge: checkNo6IndepBitwise computes no-6-IS -/
lemma checkNo6IndepBitwise_correct :
    checkNo6IndepBitwise = true ↔ NoKIndepSet 6 criticalGraph17 := by
  sorry
  -- Should implement: check all 6-subsets (as bitmasks),
  -- ensure at least one is not independent

/-! ## What This Tells Us About the Bitwise File -/

/-- Based on these bridge lemmas, the bitwise file should provide:

1. **adjMask**: Array of 17 naturals, where adjMask[v] has bit i set iff v ~ i
   - Easy to verify: just list the 17 masks explicitly
   - Verify by comparing to explicit neighborhood lists

2. **bitwiseAdj**: Should be: (adjMask v).testBit w
   - Trivial to verify

3. **checkTriangleFreeBitwise**:
   ```
   List.all (List.range 17) (fun v =>
     List.all (List.range 17) (fun w =>
       if v < w && (adjMask v).testBit w then
         (adjMask v &&& adjMask w) == 0
       else
         true))
   ```
   - O(17²) check, very fast

4. **checkNo6IndepBitwise**:
   ```
   List.all (allSubsets 6 17) (fun subset_mask =>
     ∃ v ∈ subset, (adjMask v &&& subset_mask) ≠ (1 <<< v))
   ```
   - Still needs to check C(17,6) = 12,376 subsets
   - But each check is just bitwise operations, much faster

The key insight: We do the SAME computation, but in a way that
- Uses native Nat operations (fast bitwise)
- Is structured so Lean can evaluate it without running out of memory
- Has clear correctness properties we can prove
-/
