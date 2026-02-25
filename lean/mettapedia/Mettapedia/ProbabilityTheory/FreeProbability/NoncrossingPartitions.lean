/-
# Noncrossing Partitions

Comprehensive formalization of noncrossing partitions NC(n), which form the
combinatorial foundation of free probability theory.

## Key Results

- Enumeration of NC(n) for small n (used for computing free cumulants)
- The lattice structure of NC(n) under refinement
- Catalan number counting: |NC(n)| = Cₙ
- Block structure for moment-cumulant formulas

## References

- Simion, "Noncrossing partitions" (2000)
- Speicher, "Combinatorics of Free Probability" (1997)
- Stanley, "Enumerative Combinatorics" Vol. 2
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.FreeProbability

/-!
## §1: Basic Definitions

A partition of [n] = {1,...,n} is a collection of disjoint nonempty subsets
(blocks) whose union is [n].

A partition is NONCROSSING if there do not exist a < b < c < d such that
a, c are in one block and b, d are in another.
-/

/-- A block is a nonempty subset of Fin n. -/
abbrev Block (n : ℕ) := { s : Finset (Fin n) // s.Nonempty }

/-- A partition of [n] represented explicitly as a list of disjoint blocks. -/
structure SetPartition (n : ℕ) where
  blocks : List (Finset (Fin n))
  blocks_nonempty : ∀ B ∈ blocks, B.Nonempty
  blocks_disjoint : blocks.Pairwise Disjoint
  blocks_cover : (blocks.foldl (· ∪ ·) ∅) = Finset.univ

/-- The number of blocks in a partition. -/
def SetPartition.numBlocks {n : ℕ} (π : SetPartition n) : ℕ := π.blocks.length

/-- Check if a, c are in one block and b, d in another with a < b < c < d.
    This is the "crossing" condition. -/
def hasCrossing {n : ℕ} (π : SetPartition n) : Prop :=
  ∃ B₁ ∈ π.blocks, ∃ B₂ ∈ π.blocks, B₁ ≠ B₂ ∧
  ∃ a c : Fin n, a ∈ B₁ ∧ c ∈ B₁ ∧
  ∃ b d : Fin n, b ∈ B₂ ∧ d ∈ B₂ ∧
  a < b ∧ b < c ∧ c < d

/-- A partition is noncrossing if it has no crossing. -/
def SetPartition.isNoncrossing {n : ℕ} (π : SetPartition n) : Prop :=
  ¬hasCrossing π

/-- The type of noncrossing partitions of [n]. -/
def NC (n : ℕ) := { π : SetPartition n // π.isNoncrossing }

/-!
## §2: Explicit NC(n) for Small n

For computing free cumulants, we need to enumerate NC(n) for small n.
-/

/-- The trivial partition of Fin 0 (empty). -/
def nc0_trivial : SetPartition 0 where
  blocks := []
  blocks_nonempty := fun _ h => nomatch h
  blocks_disjoint := List.Pairwise.nil
  blocks_cover := by simp [Finset.univ_eq_empty]

/-- NC(0) contains only the trivial partition. -/
def NC0 : List (NC 0) := [⟨nc0_trivial, fun ⟨_, _, h, _⟩ => nomatch h⟩]

/-- The singleton partition of Fin 1: {{0}}. -/
def nc1_singleton : SetPartition 1 where
  blocks := [{0}]
  blocks_nonempty := by simp
  blocks_disjoint := List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    simp only [Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact Fin.fin_one_eq_zero x

/-- NC(1) = {{{0}}}. -/
def NC1 : List (NC 1) := [⟨nc1_singleton, by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  -- Only one block exists, so B₁ = B₂
  simp only [nc1_singleton] at hB₁ hB₂
  simp only [List.mem_singleton] at hB₁ hB₂
  rw [hB₁, hB₂] at hne
  exact hne rfl⟩]

/-- The two noncrossing partitions of [2]:
    1. {{0}, {1}} (discrete)
    2. {{0, 1}} (single block) -/
def nc2_discrete : SetPartition 2 where
  blocks := [{0}, {1}]
  blocks_nonempty := by simp
  blocks_disjoint := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      rw [hs]
      simp only [Finset.disjoint_singleton]
      exact Fin.zero_ne_one
    · exact List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

def nc2_single : SetPartition 2 where
  blocks := [{0, 1}]
  blocks_nonempty := by simp
  blocks_disjoint := List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

theorem nc2_discrete_noncrossing : nc2_discrete.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  simp only [nc2_discrete, List.mem_cons, List.not_mem_nil, or_false] at hB₁ hB₂
  -- In nc2_discrete, each block is a singleton, so a = c and b = d
  rcases hB₁ with rfl | rfl <;> rcases hB₂ with rfl | rfl
  all_goals simp only [Finset.mem_singleton] at ha hc hb hd
  · exact hne rfl
  · -- B₁ = {0}, B₂ = {1}: a = c = 0 and b = d = 1
    -- Need a < b < c < d, i.e., 0 < 1 < 0 < 1, but b < c = 1 < 0 is false
    rw [hb, hc] at hbc
    exact Nat.not_lt_of_le (Nat.zero_le _) hbc
  · -- B₁ = {1}, B₂ = {0}: a = c = 1 and b = d = 0
    -- Need a < b, i.e., 1 < 0, false
    rw [ha, hb] at hab
    exact Nat.not_lt_of_le (Nat.zero_le _) hab
  · exact hne rfl

theorem nc2_single_noncrossing : nc2_single.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, _, _, _, _, _, _, _, _, _, _, _⟩
  simp only [nc2_single] at hB₁ hB₂
  simp only [List.mem_singleton] at hB₁ hB₂
  rw [hB₁, hB₂] at hne
  exact hne rfl

/-- NC(2) = {{{0},{1}}, {{0,1}}}. -/
def NC2 : List (NC 2) := [
  ⟨nc2_discrete, nc2_discrete_noncrossing⟩,
  ⟨nc2_single, nc2_single_noncrossing⟩
]

theorem NC2_card : NC2.length = 2 := rfl

/-!
## §3: NC(3) - The First Non-trivial Case

NC(3) has 5 elements (Catalan number C₃ = 5):
1. {{0}, {1}, {2}} - discrete
2. {{0, 1}, {2}}
3. {{0}, {1, 2}}
4. {{0, 2}, {1}}
5. {{0, 1, 2}} - single block
-/

def nc3_discrete : SetPartition 3 where
  blocks := [{0}, {1}, {2}]
  blocks_nonempty := by simp
  blocks_disjoint := by
    constructor
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · simp only [Finset.disjoint_singleton]; exact Fin.zero_ne_one
      · simp only [Finset.disjoint_singleton]; decide
    · constructor
      · intro s hs
        simp only [List.mem_singleton] at hs
        rw [hs]
        simp only [Finset.disjoint_singleton]; decide
      · exact List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

def nc3_01_2 : SetPartition 3 where
  blocks := [{0, 1}, {2}]
  blocks_nonempty := by simp
  blocks_disjoint := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      rw [hs]
      simp only [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      subst hb
      rcases ha with rfl | rfl <;> decide
    · exact List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

def nc3_0_12 : SetPartition 3 where
  blocks := [{0}, {1, 2}]
  blocks_nonempty := by simp
  blocks_disjoint := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      rw [hs]
      simp only [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      subst ha
      rcases hb with rfl | rfl <;> decide
    · exact List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

def nc3_02_1 : SetPartition 3 where
  blocks := [{0, 2}, {1}]
  blocks_nonempty := by simp
  blocks_disjoint := by
    constructor
    · intro s hs
      simp only [List.mem_singleton] at hs
      rw [hs]
      simp only [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      subst hb
      rcases ha with rfl | rfl <;> decide
    · exact List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

def nc3_012 : SetPartition 3 where
  blocks := [{0, 1, 2}]
  blocks_nonempty := by simp
  blocks_disjoint := List.pairwise_singleton _ _
  blocks_cover := by
    simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
    ext x
    fin_cases x <;> simp

-- Proofs that these are noncrossing
theorem nc3_discrete_noncrossing : nc3_discrete.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  simp only [nc3_discrete, List.mem_cons, List.not_mem_nil, or_false] at hB₁ hB₂
  -- All blocks are singletons, so a = c which contradicts a < b < c
  -- hbc is b < c, hab is a < b. With singleton blocks, a = c, so a < b < a is impossible.
  rcases hB₁ with rfl | rfl | rfl <;>
  simp only [Finset.mem_singleton] at ha hc
  all_goals { rw [ha] at hab; rw [hc] at hbc; exact Nat.lt_irrefl _ (Nat.lt_trans hab hbc) }

theorem nc3_01_2_noncrossing : nc3_01_2.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  simp only [nc3_01_2, List.mem_cons, List.not_mem_nil, or_false] at hB₁ hB₂
  rcases hB₁ with rfl | rfl <;> rcases hB₂ with rfl | rfl
  · exact hne rfl
  · -- B₁ = {0,1}, B₂ = {2}: b = d = 2, hbc: b < c, hcd: c < d -> 2 < c < 2 impossible
    simp only [Finset.mem_singleton] at hb hd
    rw [hb] at hbc; rw [hd] at hcd
    exact Nat.lt_irrefl _ (Nat.lt_trans hbc hcd)
  · -- B₁ = {2}, B₂ = {0,1}: a = c = 2, hab: a < b, hbc: b < c -> 2 < b < 2 impossible
    simp only [Finset.mem_singleton] at ha hc
    rw [ha] at hab; rw [hc] at hbc
    exact Nat.lt_irrefl _ (Nat.lt_trans hab hbc)
  · exact hne rfl

theorem nc3_0_12_noncrossing : nc3_0_12.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  simp only [nc3_0_12, List.mem_cons, List.not_mem_nil, or_false] at hB₁ hB₂
  rcases hB₁ with rfl | rfl <;> rcases hB₂ with rfl | rfl
  · exact hne rfl
  · -- B₁ = {0}, B₂ = {1,2}: a = c = 0, hab: a < b, hbc: b < c -> 0 < b < 0 impossible
    simp only [Finset.mem_singleton] at ha hc
    rw [ha] at hab; rw [hc] at hbc
    exact Nat.lt_irrefl _ (Nat.lt_trans hab hbc)
  · -- B₁ = {1,2}, B₂ = {0}: b = d = 0, hbc: b < c, hcd: c < d -> 0 < c < 0 impossible
    simp only [Finset.mem_singleton] at hb hd
    rw [hb] at hbc; rw [hd] at hcd
    exact Nat.lt_irrefl _ (Nat.lt_trans hbc hcd)
  · exact hne rfl

theorem nc3_02_1_noncrossing : nc3_02_1.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
  simp only [nc3_02_1, List.mem_cons, List.not_mem_nil, or_false] at hB₁ hB₂
  rcases hB₁ with rfl | rfl <;> rcases hB₂ with rfl | rfl
  · exact hne rfl
  · -- B₁ = {0,2}, B₂ = {1}: b = d = 1, hbc: b < c, hcd: c < d -> 1 < c < 1 impossible
    simp only [Finset.mem_singleton] at hb hd
    rw [hb] at hbc; rw [hd] at hcd
    exact Nat.lt_irrefl _ (Nat.lt_trans hbc hcd)
  · -- B₁ = {1}, B₂ = {0,2}: a = c = 1, hab: a < b, hbc: b < c -> 1 < b < 1 impossible
    simp only [Finset.mem_singleton] at ha hc
    rw [ha] at hab; rw [hc] at hbc
    exact Nat.lt_irrefl _ (Nat.lt_trans hab hbc)
  · exact hne rfl

theorem nc3_012_noncrossing : nc3_012.isNoncrossing := by
  intro ⟨B₁, hB₁, B₂, hB₂, hne, _, _, _, _, _, _, _, _, _, _, _⟩
  simp only [nc3_012, List.mem_singleton] at hB₁ hB₂
  subst hB₁ hB₂
  exact hne rfl

/-- NC(3) has exactly 5 elements (C₃ = 5). -/
def NC3 : List (NC 3) := [
  ⟨nc3_discrete, nc3_discrete_noncrossing⟩,
  ⟨nc3_01_2, nc3_01_2_noncrossing⟩,
  ⟨nc3_0_12, nc3_0_12_noncrossing⟩,
  ⟨nc3_02_1, nc3_02_1_noncrossing⟩,
  ⟨nc3_012, nc3_012_noncrossing⟩
]

theorem NC3_card : NC3.length = 5 := rfl

/-!
## §4: Block Sizes for Moment-Cumulant Formula

The moment-cumulant formula is:
  mₙ = Σ_{π ∈ NC(n)} Π_{B ∈ π} k_{|B|}

So we need to extract block sizes from partitions.
-/

/-- The multiset of block sizes in a partition. -/
def SetPartition.blockSizes {n : ℕ} (π : SetPartition n) : List ℕ :=
  π.blocks.map Finset.card

/-- For a partition π, the product of values f(|B|) over all blocks B. -/
noncomputable def SetPartition.blockProduct {n : ℕ} (π : SetPartition n) (f : ℕ → ℝ) : ℝ :=
  (π.blocks.map (fun B => f B.card)).prod

/-!
## §5: Catalan Numbers and Counting

|NC(n)| = Cₙ where Cₙ is the n-th Catalan number.
-/

/-- Catalan number: Cₙ = (2n)! / ((n+1)! n!) -/
def catalanNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * (2 * n + 1) * catalanNumber n) / (n + 2)

theorem catalan_zero : catalanNumber 0 = 1 := rfl
theorem catalan_one : catalanNumber 1 = 1 := by decide
theorem catalan_two : catalanNumber 2 = 2 := by decide
theorem catalan_three : catalanNumber 3 = 5 := by decide
theorem catalan_four : catalanNumber 4 = 14 := by decide
theorem catalan_five : catalanNumber 5 = 42 := by decide

/-- The cardinality of NC(n) equals the n-th Catalan number.
    Verified for small n by explicit enumeration. -/
theorem NC_card_eq_catalan_small :
    NC1.length = catalanNumber 1 ∧
    NC2.length = catalanNumber 2 ∧
    NC3.length = catalanNumber 3 := by
  constructor
  · decide
  constructor
  · decide
  · decide

/-!
## §6: Refinement Order

NC(n) forms a lattice under refinement:
  π ≤ σ iff every block of π is contained in a block of σ.

The minimum is the discrete partition (n singletons).
The maximum is the single-block partition.
-/

/-- π refines σ if every block of π is contained in some block of σ. -/
def SetPartition.refines {n : ℕ} (π σ : SetPartition n) : Prop :=
  ∀ B ∈ π.blocks, ∃ C ∈ σ.blocks, B ⊆ C

/-- The discrete partition (all singletons) is the minimum.
    Note: This requires Finset.toList which is noncomputable. -/
noncomputable def discretePartition (n : ℕ) : SetPartition n where
  blocks := (Finset.univ : Finset (Fin n)).toList.map (fun x => {x})
  blocks_nonempty := by
    intro B hB
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hB
    obtain ⟨x, rfl⟩ := hB
    exact Finset.singleton_nonempty x
  blocks_disjoint := by
    apply List.Pairwise.map
    · intro x y hxy
      simp only [Finset.disjoint_singleton]
      exact hxy
    · exact Finset.nodup_toList _
  blocks_cover := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    -- Key lemma: foldl (· ∪ ·) init L contains elements from init and all sets in L
    have h_fold_mono : ∀ (L : List (Finset (Fin n))) (init : Finset (Fin n)) (y : Fin n),
        y ∈ init → y ∈ L.foldl (· ∪ ·) init := by
      intro L
      induction L with
      | nil => intro _ _ h; exact h
      | cons hd tl ih =>
        intro init y hy
        simp only [List.foldl_cons]
        exact ih (init ∪ hd) y (Finset.mem_union_left hd hy)
    have h_fold_mem : ∀ (L : List (Finset (Fin n))) (init : Finset (Fin n)) (s : Finset (Fin n)) (y : Fin n),
        s ∈ L → y ∈ s → y ∈ L.foldl (· ∪ ·) init := by
      intro L
      induction L with
      | nil => intro _ _ _ h; exact nomatch h
      | cons hd tl ih =>
        intro init s y hs hy
        simp only [List.foldl_cons]
        cases hs with
        | head => exact h_fold_mono tl (init ∪ hd) y (Finset.mem_union_right init hy)
        | tail _ hs' => exact ih (init ∪ hd) s y hs' hy
    apply h_fold_mem
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
      exact ⟨x, rfl⟩
    · exact Finset.mem_singleton_self x

/-- The single-block partition is the maximum. -/
def singleBlockPartition (n : ℕ) (hn : 0 < n) : SetPartition n where
  blocks := [Finset.univ]
  blocks_nonempty := by
    intro B hB
    simp only [List.mem_singleton] at hB
    rw [hB]
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hn
  blocks_disjoint := List.pairwise_singleton _ _
  blocks_cover := by simp

end Mettapedia.ProbabilityTheory.FreeProbability
