/-
# Lattice Summation Infrastructure

Utilities for summing functions over principal ideals in finite lattices.
This provides the foundation for belief functions on orthomodular lattices
without requiring sigma-algebra machinery.

## Key Definitions

- `finsetBelow a`: The Finset {x | x ≤ a}
- `sumBelow f a`: Sum of f over all elements below a

## Key Property

For finite lattices, these sums are well-defined Finset sums,
giving us "measure theory on lattices" without the complexity.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Common

/-!
## §1: Finset of Elements Below
-/

section FiniteLattice

variable {L : Type*} [Lattice L] [BoundedOrder L] [Fintype L] [DecidableEq L]

/-- The Finset of elements below a. Requires decidable ≤. -/
def finsetBelow [DecidableRel (α := L) (· ≤ ·)] (a : L) : Finset L :=
  Finset.filter (· ≤ a) Finset.univ

namespace finsetBelow

variable [DecidableRel (α := L) (· ≤ ·)]

omit [BoundedOrder L] [DecidableEq L] in
@[simp]
theorem mem_iff (a x : L) : x ∈ finsetBelow a ↔ x ≤ a := by
  simp [finsetBelow]

omit [BoundedOrder L] [DecidableEq L] in
theorem subset_of_le {a b : L} (h : a ≤ b) : finsetBelow a ⊆ finsetBelow b := by
  intro x hx
  rw [mem_iff] at hx ⊢
  exact le_trans hx h

@[simp]
theorem bot_eq_singleton : finsetBelow (⊥ : L) = {⊥} := by
  ext x
  simp [finsetBelow, le_bot_iff]

omit [DecidableEq L] in
@[simp]
theorem top_eq_univ : finsetBelow (⊤ : L) = Finset.univ := by
  ext x
  simp [finsetBelow]

omit [BoundedOrder L] [DecidableEq L] in
@[simp]
theorem self_mem (a : L) : a ∈ finsetBelow a := by simp

omit [DecidableEq L] in
theorem bot_mem (a : L) : ⊥ ∈ finsetBelow a := by simp [bot_le]

end finsetBelow

/-!
## §2: Sum Below
-/

/-- Sum a function over all elements below a in a finite lattice. -/
def sumBelow [DecidableRel (α := L) (· ≤ ·)] (f : L → ℝ) (a : L) : ℝ :=
  Finset.sum (finsetBelow a) f

namespace sumBelow

variable [DecidableRel (α := L) (· ≤ ·)] (f : L → ℝ)

/-- Summing below ⊥ gives just f(⊥). -/
@[simp]
theorem bot : sumBelow f (⊥ : L) = f ⊥ := by
  simp [sumBelow]

omit [DecidableEq L] in
/-- Summing below ⊤ gives the sum over all elements. -/
@[simp]
theorem top : sumBelow f (⊤ : L) = Finset.sum Finset.univ f := by
  simp [sumBelow]

omit [BoundedOrder L] [DecidableEq L] in
/-- Monotonicity: if f ≥ 0 and a ≤ b, then sumBelow f a ≤ sumBelow f b. -/
theorem mono_of_nonneg (hf : ∀ x, 0 ≤ f x) {a b : L} (hab : a ≤ b) :
    sumBelow f a ≤ sumBelow f b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact finsetBelow.subset_of_le hab
  · intro x _ _
    exact hf x

omit [BoundedOrder L] [DecidableEq L] in
/-- If f ≥ 0, then f(a) ≤ sumBelow f a. -/
theorem self_le_of_nonneg (hf : ∀ x, 0 ≤ f x) (a : L) : f a ≤ sumBelow f a := by
  have ha : a ∈ finsetBelow a := finsetBelow.self_mem a
  calc f a = Finset.sum {a} f := by simp
       _ ≤ sumBelow f a := by
         apply Finset.sum_le_sum_of_subset_of_nonneg
         · intro x hx
           simp only [Finset.mem_singleton] at hx
           simp [hx]
         · intro x _ _
           exact hf x

omit [BoundedOrder L] [DecidableEq L] in
/-- sumBelow is non-negative when f is non-negative. -/
theorem nonneg_of_nonneg (hf : ∀ x, 0 ≤ f x) (a : L) : 0 ≤ sumBelow f a := by
  apply Finset.sum_nonneg
  intro x _
  exact hf x

omit [BoundedOrder L] [DecidableEq L] in
/-- Linearity in f: sumBelow (f + g) = sumBelow f + sumBelow g. -/
theorem add (g : L → ℝ) (a : L) :
    sumBelow (f + g) a = sumBelow f a + sumBelow g a := by
  simp only [sumBelow, Pi.add_apply, Finset.sum_add_distrib]

omit [BoundedOrder L] [DecidableEq L] in
/-- Scalar multiplication: sumBelow (c • f) = c * sumBelow f. -/
theorem smul (c : ℝ) (a : L) :
    sumBelow (c • f) a = c * sumBelow f a := by
  simp only [sumBelow, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

omit [DecidableEq L] in
/-- f(⊥) ≤ sumBelow f a for any a (when f ≥ 0). -/
theorem bot_le_of_nonneg (hf : ∀ x, 0 ≤ f x) (a : L) : f ⊥ ≤ sumBelow f a := by
  have hbot : ⊥ ∈ finsetBelow a := finsetBelow.bot_mem a
  calc f ⊥ = Finset.sum {⊥} f := by simp
       _ ≤ sumBelow f a := by
         apply Finset.sum_le_sum_of_subset_of_nonneg
         · intro x hx
           simp only [Finset.mem_singleton] at hx
           simp [hx]
         · intro x _ _
           exact hf x

end sumBelow

/-!
## §3: Singleton Support Functions

When a function has support only at a single element, sumBelow simplifies.
-/

/-- A function with singleton support at x: f(y) = 0 for all y ≠ x. -/
def hasSingletonSupport [DecidableRel (α := L) (· ≤ ·)] (f : L → ℝ) (x : L) : Prop :=
  ∀ y, y ≠ x → f y = 0

namespace hasSingletonSupport

variable [DecidableRel (α := L) (· ≤ ·)] {f : L → ℝ} {x : L}

omit [BoundedOrder L] in
/-- For singleton support at x, sumBelow f a = f x if x ≤ a, else 0. -/
theorem sumBelow_eq (hf : hasSingletonSupport f x) (a : L) :
    sumBelow f a = if x ≤ a then f x else 0 := by
  simp only [sumBelow]
  split_ifs with hxa
  · -- x ≤ a: only x contributes
    have hmem : x ∈ finsetBelow a := by simp [finsetBelow.mem_iff, hxa]
    have heq : ∀ y ∈ finsetBelow a, f y = if y = x then f x else 0 := by
      intro y _
      by_cases hyx : y = x
      · simp [hyx]
      · simp [hyx, hf y hyx]
    calc Finset.sum (finsetBelow a) f
        = Finset.sum (finsetBelow a) (fun y => if y = x then f x else 0) := by
          apply Finset.sum_congr rfl heq
      _ = f x := by simp [hmem]
  · -- x ≰ a: x doesn't contribute, and everything else is 0
    apply Finset.sum_eq_zero
    intro y hy
    simp only [finsetBelow.mem_iff] at hy
    by_cases hyx : y = x
    · subst hyx; exact absurd hy hxa
    · exact hf y hyx

/-- For singleton support, sumBelow f a = sumBelow f ⊤ iff x ≤ a (when f x ≠ 0). -/
theorem sumBelow_eq_total_iff (hf : hasSingletonSupport f x) (hfx : f x ≠ 0) (a : L) :
    sumBelow f a = sumBelow f ⊤ ↔ x ≤ a := by
  rw [sumBelow_eq hf a, sumBelow_eq hf ⊤]
  simp only [le_top, ↓reduceIte]
  constructor
  · intro h
    by_contra hna
    simp [hna] at h
    exact hfx h.symm
  · intro h
    simp [h]

/-- For singleton support at x with f x > 0, if x ≰ a then sumBelow f a < sumBelow f ⊤. -/
theorem sumBelow_lt_total_of_not_le (hf : hasSingletonSupport f x) (hfx : 0 < f x)
    {a : L} (hna : ¬x ≤ a) :
    sumBelow f a < sumBelow f ⊤ := by
  rw [sumBelow_eq hf a, sumBelow_eq hf ⊤]
  simp only [le_top, ↓reduceIte, hna, ↓reduceIte]
  exact hfx

end hasSingletonSupport

/-!
## §4: Total Mass
-/

/-- The total mass is the sum over all elements. -/
def totalSum [DecidableRel (α := L) (· ≤ ·)] (f : L → ℝ) : ℝ :=
  Finset.sum Finset.univ f

omit [DecidableEq L] in
theorem totalSum_eq_sumBelow_top [DecidableRel (α := L) (· ≤ ·)] (f : L → ℝ) :
    totalSum f = sumBelow f ⊤ := by
  simp [totalSum, sumBelow]

end FiniteLattice

end Mettapedia.ProbabilityTheory.Common
