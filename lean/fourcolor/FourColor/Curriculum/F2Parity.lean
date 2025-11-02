/-
# Module 1: F₂ Parity Arguments

## The Pattern

**Given**: A sum equals zero in F₂² = (ZMod 2) × (ZMod 2)
**Prove**: The cardinality of a subset has certain parity properties

## Why This Matters

This pattern appears in:
- `even_alphaBeta_incident` (KempeAPI.lean:320) - THE critical blocker
- Any proof involving zero-boundary colorings
- Parity arguments in graph edge colorings

## The Minimal Example

We'll start TINY and build up:
1. Single coordinate, single subset
2. Product coordinates, single subset
3. Product coordinates, multiple subsets (actual pattern)

-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

open Finset

/-! ## Exercise 1: Warmup - ZMod 2 Basics -/

-- First, understand what `Even` means
example : Even 0 := ⟨0, rfl⟩
example : Even 2 := ⟨1, rfl⟩
example : Even 4 := ⟨2, rfl⟩

-- Key lemma: casting to ZMod 2 preserves parity
-- This is THE critical connection we need
#check ZMod.intCast_zmod_eq_zero_iff_even

/-
**Exercise 1a**: Prove that if `n : ℕ` casts to 0 in ZMod 2, then n is even.

Hint: Use `ZMod.intCast_zmod_eq_zero_iff_even` and the fact that
`(n : ZMod 2) = 0` is equivalent to `Even n`.
-/
example (n : ℕ) (h : (n : ZMod 2) = 0) : Even n := by
  -- In ZMod 2, a nat casts to 0 iff 2 divides it, i.e., iff it's even
  rw [Nat.even_iff_two_dvd]
  exact ZMod.natCast_zmod_eq_zero_iff_dvd.mp h

/-! ## Exercise 2: Single Coordinate Sum -/

/-
**Exercise 2a**: If the sum of a list equals 0 in ZMod 2, the list has even length.

This is the CORE pattern in one dimension.
-/
example (xs : List (ZMod 2)) (h : xs.sum = 0) (h_all_one : ∀ x ∈ xs, x = 1) :
    Even xs.length := by
  -- Strategy: sum = length * 1 = length (in ZMod 2)
  -- So (length : ZMod 2) = 0, hence length is even

  -- First, show that xs.sum = (xs.length : ZMod 2)
  have hsum_eq : xs.sum = (xs.length : ZMod 2) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.sum_cons, List.length_cons]
      rw [h_all_one x (List.mem_cons_self x xs)]
      rw [ih]
      · simp only [Nat.cast_add, Nat.cast_one]
        ring
      · intros y hy
        exact h_all_one y (List.mem_cons_of_mem x hy)

  -- Now (xs.length : ZMod 2) = xs.sum = 0
  rw [hsum_eq] at h

  -- Apply Exercise 1a
  rw [Nat.even_iff_two_dvd]
  exact ZMod.natCast_zmod_eq_zero_iff_dvd.mp h

/-! ## Exercise 3: Product Coordinates (F₂²) -/

/-
**Exercise 3a**: In F₂² = (ZMod 2) × (ZMod 2), if sum is (0,0), then...

This is getting closer to our actual problem!
-/
def Color := (ZMod 2) × (ZMod 2)

-- The four colors in F₂²
def color_00 : Color := (0, 0)
def color_10 : Color := (1, 0)
def color_01 : Color := (0, 1)
def color_11 : Color := (1, 1)

/-
**Exercise 3b**: If sum of colors is (0,0), and we filter for colors in {α, β},
              what can we say about the count?

This is the EXACT pattern from `even_alphaBeta_incident`!
-/
example (colors : List Color) (α β : Color)
    (h_sum : colors.sum = (0, 0))
    (hα : α ≠ (0, 0)) (hβ : β ≠ (0, 0)) :
    Even ((colors.filter (fun c => c = α ∨ c = β)).length) := by
  -- Strategy: Break sum into coordinates, use F₂ structure

  -- Let n_α = count of α, n_β = count of β
  let n_α := (colors.filter (· = α)).length
  let n_β := (colors.filter (· = β)).length

  -- Goal: show n_α + n_β is even
  suffices Even (n_α + n_β) by
    have : (colors.filter (fun c => c = α ∨ c = β)).length = n_α + n_β := by
      rw [← List.filter_union]
      · congr 1
        ext c
        simp
      · intros c hc₁ hc₂
        simp at hc₁ hc₂
        exact hα (hc₁.symm.trans hc₂)
    rw [this]
    exact this

  -- Extract first and second coordinate sums
  have h_fst : (colors.map Prod.fst).sum = 0 := by
    rw [← List.map_map]
    have : colors.sum.fst = (colors.map Prod.fst).sum := List.sum_map_fst
    rw [h_sum] at this
    exact this

  have h_snd : (colors.map Prod.snd).sum = 0 := by
    rw [← List.map_map]
    have : colors.sum.snd = (colors.map Prod.snd).sum := List.sum_map_snd
    rw [h_sum] at this
    exact this

  -- Now we need to use the structure of α and β
  -- Since α, β ≠ (0,0), they have at least one nonzero coordinate

  -- Case split on α and β
  have hα_cases : α = (1, 0) ∨ α = (0, 1) ∨ α = (1, 1) := by
    obtain ⟨a₁, a₂⟩ := α
    interval_cases a₁ <;> interval_cases a₂ <;> (try simp at hα) <;> simp

  have hβ_cases : β = (1, 0) ∨ β = (0, 1) ∨ β = (1, 1) := by
    obtain ⟨b₁, b₂⟩ := β
    interval_cases b₁ <;> interval_cases b₂ <;> (try simp at hβ) <;> simp

  -- This gets complex - need to handle 9 cases
  sorry -- This pattern requires deeper F₂ theory

/-! ## Exercise 4: With Finsets (actual KempeAPI pattern) -/

/-
**Exercise 4**: The ACTUAL problem from KempeAPI.lean:320

Given:
- incident : V → Finset E  (edges at each vertex)
- x : E → Color  (edge coloring)
- Zero-boundary: ∀ v, ∑ e ∈ incident v, x e = (0, 0)

Prove:
- ∀ v, Even |{e ∈ incident v : x e ∈ {α, β}}|
-/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

example (incident : V → Finset E) (x : E → Color) (α β : Color)
    (h_zero : ∀ v : V, ∑ e ∈ incident v, x e = (0, 0))
    (hα : α ≠ (0, 0)) (hβ : β ≠ (0, 0)) :
    ∀ v : V, Even ((incident v).filter (fun e => x e = α ∨ x e = β)).card := by
  sorry
  /-
  This is EXACTLY `even_alphaBeta_incident`.

  Strategy (from F2_PARITY_PROOF_GUIDE.md):

  1. Fix a vertex v
  2. Let S = incident v
  3. Partition S into S_α, S_β, S_other
  4. Have: ∑ e ∈ S, x e = (0,0)
  5. Rewrite: S_α.card • α + S_β.card • β + ∑ e ∈ S_other, x e = (0,0)
  6. Extract coordinates (use Prod.fst, Prod.snd)
  7. In each coordinate, solve for parity
  8. Case analysis on α, β structure
  -/

/-! ## Mathlib Resources -/

-- Key lemmas you'll need:
#check ZMod.intCast_zmod_eq_zero_iff_even  -- Connect ZMod 2 to parity
#check Finset.sum_partition                -- Partition a sum
#check Finset.filter_union                 -- Combine filters
#check Finset.card_union_of_disjoint      -- Count disjoint union
#check nsmul_eq_zero                       -- n • x = 0 in additive groups
#check Nat.cast_add                        -- (m + n : ZMod 2) = (m : ZMod 2) + (n : ZMod 2)

-- For product types:
#check Prod.fst_sum                        -- (∑ x).fst = ∑ x.fst
#check Prod.snd_sum                        -- (∑ x).snd = ∑ x.snd

-- Search for similar proofs:
-- rg "ZMod 2.*Even" lake-packages/mathlib
-- rg "sum.*filter.*card" lake-packages/mathlib

/-! ## Next Steps -/

/-
After completing these exercises:

1. Apply the pattern to `even_alphaBeta_incident` in KempeAPI.lean:320
2. This unlocks ALL of KempeAPI (only remaining blocker)
3. Can proceed to KempeExistence.lean proofs
4. Similar F₂ arguments appear in other parts of the formalization

**Time estimate**:
- Exercises 1-3: 1-2 hours
- Exercise 4: 2-3 hours (first time doing it)
- Actual application: 30 minutes (once pattern is mastered)

**Learning outcome**: Ability to handle ANY F₂ parity argument in formal math
-/
