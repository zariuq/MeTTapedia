import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

-- Use `bounded_by_iterate` from SandwichSeparation (requires [KSSeparation α])

/-!
# Growth Rate Theory for K-S Algebras

This file develops the theory of comparing growth rates of iterated operations
WITHOUT using logarithms or real number representations.

## Main Results

1. **Base Comparison**: If `a < b`, then `a^k < b^k` for all `k > 0`
2. **Exponent Monotonicity**: For `a > ident`, if `m < n` then `a^m < a^n`
3. **Scaling Laws**: Growth rate comparisons are preserved under scaling
4. **Separation Constraints**: Using KSSeparation to bound growth rates

These provide algebraic tools for comparing exponential growth without needing ℝ.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Section 1: Fundamental Growth Rate Lemmas (No Separation Needed)
-/

/-- If a < b, then powers preserve this inequality: a^k < b^k for all k > 0 -/
theorem iterate_op_lt_of_base_lt {a b : α} (hab : a < b) (k : ℕ) (hk : 0 < k) :
    iterate_op a k < iterate_op b k := by
  induction k with
  | zero => exact absurd hk (Nat.not_lt_zero 0)
  | succ k ih =>
    cases Nat.eq_zero_or_pos k with
    | inl hzero =>
      subst hzero
      simp [iterate_op_one]
      exact hab
    | inr hpos =>
      calc iterate_op a (k + 1)
          = op a (iterate_op a k) := rfl
        _ < op a (iterate_op b k) := op_strictMono_right a (ih hpos)
        _ < op b (iterate_op b k) := op_strictMono_left (iterate_op b k) hab
        _ = iterate_op b (k + 1) := rfl

/-- Exponent monotonicity: for a > ident, a^m < a^n when m < n -/
theorem iterate_op_strictMono' (a : α) (ha : ident < a) : StrictMono (iterate_op a) :=
  KnuthSkillingAlgebra.iterate_op_strictMono a ha

/-!
## Section 2: Multiplication and Addition Laws for Growth
-/

/-- Adding one iteration on the left (by definition of iterate_op) -/
theorem iterate_op_succ_left (a : α) (n : ℕ) :
    op a (iterate_op a n) = iterate_op a (n + 1) := by
  rfl

/-
Note: op (iterate_op a n) a = iterate_op a (n + 1) would require commutativity!
The definition is iterate_op a (n+1) = op a (iterate_op a n), not op (iterate_op a n) a.
-/

/-- Iteration n times equals n+1 fold composition starting from ident -/
theorem iterate_op_unfold (a : α) (n : ℕ) :
    iterate_op a (n + 1) = op a (iterate_op a n) := by
  rfl

/-!
## Section 3: Growth Rate Comparisons Without Commutativity

These results DON'T require commutativity.
-/

/-- If a < b and a^m ≤ b^m, then a < b (contrapositive form) -/
theorem base_ordering_from_powers {a b : α} (m : ℕ) (hm : 0 < m)
    (h : iterate_op a m < iterate_op b m) : a < b := by
  by_contra hnot
  push_neg at hnot
  cases le_iff_lt_or_eq.mp hnot with
  | inl hba =>
    -- b < a case
    have : iterate_op b m < iterate_op a m := iterate_op_lt_of_base_lt hba m hm
    exact absurd h (not_lt_of_gt this)
  | inr heq =>
    -- b = a case
    rw [heq] at h
    exact LT.lt.false h

/-- Comparing different bases when larger base has larger exponent -/
theorem mixed_power_comparison_favorable {a b : α} (hb : ident < b) (hab : a < b)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    iterate_op a m < iterate_op b n := by
  have h1 : iterate_op a m < iterate_op b m := iterate_op_lt_of_base_lt hab m hm
  have h2 : iterate_op b m ≤ iterate_op b n := by
    cases le_iff_lt_or_eq.mp hmn with
    | inl hlt =>
      exact le_of_lt (iterate_op_strictMono' b hb hlt)
    | inr heq =>
      rw [heq]
  exact lt_of_lt_of_le h1 h2

/-!
## Section 4: Impossibility Results

Show what CANNOT happen with growth rates.
-/

/-- Key impossibility: smaller base cannot overtake with same exponent -/
theorem smaller_base_same_exp_cannot_overtake {a b : α} (hab : a < b) (k : ℕ) (hk : 0 < k) :
    ¬(iterate_op a k ≥ iterate_op b k) := by
  intro h_contra
  have h_lt : iterate_op a k < iterate_op b k := iterate_op_lt_of_base_lt hab k hk
  exact absurd h_lt (not_lt_of_ge h_contra)

/-- Contrapositive: if a^m ≥ b^m then ¬(a < b) -/
theorem power_ge_implies_base_ge {a b : α} (m : ℕ) (hm : 0 < m)
    (h : iterate_op a m ≥ iterate_op b m) : b ≤ a := by
  by_contra hnot
  push_neg at hnot
  -- hnot: a < b
  exact smaller_base_same_exp_cannot_overtake hnot m hm h

/-!
## Section 5: Separation-Based Growth Rate Bounds
-/

section WithSeparation

variable [KSSeparation α]

/-- Powers grow without bound (from Archimedean property) -/
theorem powers_unbounded (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x < iterate_op a n :=
  bounded_by_iterate a ha x

/-- Using separation to bound growth rates -/
theorem separation_gives_growth_bound (a x y : α)
    (ha : ident < a) (hx : ident < x) (hy : ident < y) (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧
    iterate_op x m < iterate_op a n ∧
    iterate_op a n ≤ iterate_op y m := by
  exact KSSeparation.separation ha hx hy hxy

/-- Separation with self as base gives exponent constraints -/
theorem separation_self_base (x y : α) (hx : ident < x) (hy : ident < y)
    (hlt : x < y) :
    ∃ n m : ℕ, 0 < m ∧ m < n ∧
    iterate_op x n ≤ iterate_op y m := by
  -- Prove x < y implies ident < x and ident < y
  have hxy_pos : ident < x := hx

  -- Apply KSSeparation with base a = x
  obtain ⟨n, m, hm_pos, h_left, h_right⟩ :=
    KSSeparation.separation hx hxy_pos hy hlt

  -- From h_left: x^m < x^n, which gives m < n
  have hmn : m < n := by
    by_contra h_not
    push_neg at h_not
    cases le_iff_lt_or_eq.mp h_not with
    | inl hgt =>
      -- m > n case
      have : iterate_op x n < iterate_op x m := iterate_op_strictMono' x hx hgt
      exact absurd this (not_lt_of_ge (le_of_lt h_left))
    | inr heq =>
      -- m = n case
      subst heq
      exact LT.lt.false h_left

  exact ⟨n, m, hm_pos, hmn, h_right⟩

end WithSeparation

/-!
## Section 6: Well-Founded Order Properties

Growth rates induce a well-founded ordering.
-/

/-- The "dominates" relation: a dominates b if ∃k: ∀m > k, a^m > b^m -/
def eventually_dominates (a b : α) : Prop :=
  ∃ k : ℕ, ∀ m : ℕ, m > k → iterate_op a m > iterate_op b m

/-- If a > b > ident, then a eventually dominates b -/
theorem larger_base_dominates {a b : α} (_hb : ident < b) (hab : b < a) :
    eventually_dominates a b := by
  use 0
  intro m hm
  have hm_pos : 0 < m := hm
  exact iterate_op_lt_of_base_lt hab m hm_pos

/-!
## Section 7: Application to Commutativity (What We Know)

Without commutativity, we can still prove some results.
-/

/-- If we assume non-commutativity, we can derive constraints -/
theorem noncommutativity_gives_constraints (x y : α)
    (_hx : ident < x) (hy : ident < y) (hlt : op x y < op y x) :
    x < op x y ∧ op x y < op y x := by
  constructor
  · calc x = op x ident := (op_ident_right x).symm
         _ < op x y := op_strictMono_right x hy
  · exact hlt

/-- The gap between x⊕y and y⊕x persists in powers -/
theorem gap_persists_in_powers (x y : α) (hlt : op x y < op y x) (k : ℕ) (hk : 0 < k) :
    iterate_op (op x y) k < iterate_op (op y x) k :=
  iterate_op_lt_of_base_lt hlt k hk

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core
