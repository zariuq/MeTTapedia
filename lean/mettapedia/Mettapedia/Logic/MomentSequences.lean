import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Forward Differences and Completely Monotone Sequences

This file isolates the forward-difference machinery used by de Finetti and
Hausdorff-moment arguments, avoiding import cycles between the two developments.
-/

namespace Mettapedia.Logic.MomentSequences

open Finset BigOperators

/-- Forward difference operator (Hausdorff convention): `Δ m k = m k - m (k+1)`. -/
def fwdDiff (m : ℕ → ℝ) : ℕ → ℝ :=
  fun k => m k - m (k + 1)

/-- Iterated forward differences `Δⁿ m` in the Hausdorff convention.

We define this via Mathlib's forward difference operator:
`_root_.fwdDiff (h := 1) m k = m (k+1) - m k`.
Our convention is the alternating-sign variant `m k - m (k+1)`, so we multiply by `(-1)^n`.
-/
def fwdDiffIter (n : ℕ) (m : ℕ → ℝ) : ℕ → ℝ :=
  fun k => ((-1 : ℝ) ^ n) * ((_root_.fwdDiff (h := (1 : ℕ)))^[n] m k)

/-- A sequence is *completely monotone* if all iterated forward differences are nonnegative. -/
def CompletelyMonotone (m : ℕ → ℝ) : Prop :=
  ∀ n k, 0 ≤ fwdDiffIter n m k

/-- Recurrence for Hausdorff forward differences:
`Δ^{n+1} m k = Δ^n m k - Δ^n m (k+1)`. -/
lemma fwdDiffIter_succ (m : ℕ → ℝ) (n k : ℕ) :
    fwdDiffIter (n + 1) m k = fwdDiffIter n m k - fwdDiffIter n m (k + 1) := by
  -- Unfold into Mathlib forward differences (`f (k+1) - f k`) and simplify signs.
  unfold fwdDiffIter
  -- Write `Δ := _root_.fwdDiff (h := 1)` and use the iterate-succ rule.
  simp [Function.iterate_succ_apply', _root_.fwdDiff, pow_succ, sub_eq_add_neg, add_comm, mul_comm,
    mul_add]

/-- Simplify the alternating signs coming from the translation between conventions:
for `j ≤ n`, we have `(-1)^n * (-1)^(n-j) = (-1)^j`. -/
lemma neg_one_pow_mul_neg_one_pow_sub (n j : ℕ) (hj : j ≤ n) :
    ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n - j)) = (-1 : ℝ) ^ j := by
  -- Rewrite `n` as `j + (n-j)`, then cancel the duplicated factor using `(-1)^2 = 1`.
  have hn : n = j + (n - j) := (Nat.add_sub_of_le hj).symm
  calc
    ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n - j))
        = ((-1 : ℝ) ^ (j + (n - j))) * ((-1 : ℝ) ^ (n - j)) := by
            -- Avoid `simp` here (it can loop trying to simplify nested `Nat.sub`).
            have hpow : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (j + (n - j)) :=
              congrArg (fun t : ℕ => (-1 : ℝ) ^ t) hn
            rw [hpow]
    _ = (((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ (n - j))) * ((-1 : ℝ) ^ (n - j)) := by
          simp [pow_add]
    _ = ((-1 : ℝ) ^ j) * (((-1 : ℝ) ^ (n - j)) * ((-1 : ℝ) ^ (n - j))) := by
          simp [mul_assoc]
    _ = ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ ((n - j) + (n - j))) := by
          simp [pow_add]
    _ = ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ (2 * (n - j))) := by
          -- `a + a = 2*a`
          simp [two_mul]
    _ = ((-1 : ℝ) ^ j) * ((((-1 : ℝ) ^ 2) ^ (n - j))) := by
          -- `(-1)^(2*(n-j)) = ((-1)^2)^(n-j)`
          simp [pow_mul]
    _ = (-1 : ℝ) ^ j := by
          simp

/-- Closed form for iterated forward differences (binomial alternating sum). -/
theorem fwdDiffIter_eq_sum_choose (m : ℕ → ℝ) :
    ∀ n k, fwdDiffIter n m k =
      ∑ j ∈ Finset.range (n + 1), ((-1 : ℝ) ^ j) * (Nat.choose n j : ℝ) * m (k + j) := by
  classical
  intro n k
  have h :=
    _root_.fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) (f := m) (n := n) (y := k)
  -- Push the outer `(-1)^n` inside the sum and simplify casts; the remaining work is the
  -- sign identity `(-1)^n * (-1)^(n-j) = (-1)^j`.
  simp [fwdDiffIter, h, Finset.mul_sum, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, mul_left_comm, mul_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp [neg_one_pow_mul_neg_one_pow_sub n j hjle]

end Mettapedia.Logic.MomentSequences
