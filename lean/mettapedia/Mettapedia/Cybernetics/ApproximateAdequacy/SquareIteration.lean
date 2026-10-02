import Mettapedia.Cybernetics.MindWorldApproximation
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Iterating approximate update squares

An approximate update square (`Mettapedia.GSLT.Scope.ApproxSquare`) with
error `δ` certifies a **one-step prediction**: from the exact current view,
the abstract update predicts the view of the next world state within `δ`.
Predictions over `n` steps iterate the abstract update on its own output, so
the error propagates through the abstract dynamics.  With a modulus
`t ↦ κ t` (a `κ`-Lipschitz abstract update) the error after `n` steps is at
most `δ (1 + κ + ⋯ + κ^(n-1))` (`ApproxSquare.iterate_lipschitz`).  Three
regimes follow.
* `κ < 1`, a contraction: the error stays below `δ / (1 - κ)` for every `n`
  (`ApproxSquare.iterate_contraction`).  Lane A's
  `isApproxBisimulation_of_contraction` turns the same condition into an
  approximate bisimulation at precision `δ / (1 - κ)`.  The bound is the
  supremum of the errors and is not attained (`Halving.error_iterate`,
  `Halving.error_lt`).
* `κ = 1`, a nonexpansive update: the error is at most `n δ`
  (`Mettapedia.GSLT.Scope.ApproxSquare.iterate`), attained by
  `Mettapedia.GSLT.Scope.Succ.error_iterate`.
* `κ > 1`, an expanding update: the error can grow like `κ ^ n`, as
  `Mettapedia.GSLT.Scope.Doubling.error_iterate` shows with `2 ^ n - 1`.

A square is not closed under composition at a fixed precision
(`Mettapedia.GSLT.Scope.Succ.not_within_one`); a contraction is exactly what
makes a single precision work for every horizon.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset
open Mettapedia.GSLT.Scope

variable {X Y D : Type*}

/-- **`n` steps along a `κ`-Lipschitz abstract update err by at most
`δ · Σ_{k<n} κ^k`.** -/
theorem ApproxSquare.iterate_lipschitz [CommSemiring D] [PartialOrder D] [IsOrderedRing D]
    {dist : Y → Y → D} (dist_self : ∀ y, dist y y = 0)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c) {view : X → Y} {f : X → X}
    {f' : Y → Y} {δ κ : D} (κ_nonneg : 0 ≤ κ)
    (lipschitz : ∀ a b, dist (f' a) (f' b) ≤ κ * dist a b)
    (square : ApproxSquare dist view view f f' δ) :
    ∀ n : ℕ, ApproxSquare dist view view f^[n] f'^[n] (δ * ∑ k ∈ range n, κ ^ k)
  | 0 => by
    rw [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact ApproxSquare.of_exact dist_self fun _ => rfl
  | n + 1 => by
    have composite := ApproxSquare.comp triangle (ω := fun t => κ * t)
      (fun _ _ le => mul_le_mul_of_nonneg_left le κ_nonneg) lipschitz
      (ApproxSquare.iterate_lipschitz dist_self triangle κ_nonneg lipschitz square n) square
    rw [Function.iterate_succ', Function.iterate_succ']
    have total : δ * ∑ k ∈ range (n + 1), κ ^ k = δ + κ * (δ * ∑ k ∈ range n, κ ^ k) := by
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ]
      ring
    rw [total]
    exact composite

/-- **Under a contraction the error is uniformly bounded**: every horizon errs
by at most `δ / (1 - κ)`. -/
theorem ApproxSquare.iterate_contraction [Field D] [LinearOrder D] [IsStrictOrderedRing D]
    {dist : Y → Y → D} (dist_self : ∀ y, dist y y = 0)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c) {view : X → Y} {f : X → X}
    {f' : Y → Y} {δ κ : D} (δ_nonneg : 0 ≤ δ) (κ_nonneg : 0 ≤ κ) (κ_lt : κ < 1)
    (lipschitz : ∀ a b, dist (f' a) (f' b) ≤ κ * dist a b)
    (square : ApproxSquare dist view view f f' δ) (n : ℕ) :
    ApproxSquare dist view view f^[n] f'^[n] (δ / (1 - κ)) := by
  refine (ApproxSquare.iterate_lipschitz dist_self triangle κ_nonneg lipschitz square n).mono ?_
  have geometric : ∑ k ∈ range n, κ ^ k ≤ 1 / (1 - κ) := by
    have bound := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) κ_nonneg κ_lt
    rwa [pow_zero, ← Finset.range_eq_Ico] at bound
  calc δ * ∑ k ∈ range n, κ ^ k ≤ δ * (1 / (1 - κ)) := mul_le_mul_of_nonneg_left geometric δ_nonneg
    _ = δ / (1 - κ) := by rw [mul_one_div]

/-! ## Control: the contraction bound is the supremum, not attained -/

namespace Halving

open Mettapedia.Cybernetics.MindWorldApproximation.Halving

theorem world_iterate (n : ℕ) (x : ℝ) :
    world^[n] x = x / 2 ^ n + (2 - 2 * (1 / 2) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold world
    rw [pow_succ, pow_succ]
    field_simp
    ring

theorem abstract_iterate (n : ℕ) (y : ℝ) : abstract^[n] y = y / 2 ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold abstract
    rw [pow_succ]
    field_simp

/-- **The error after `n` steps is `2 - 2 (1/2)^n`**: it increases to the
contraction bound `1 / (1 - 1/2) = 2`. -/
theorem error_iterate (n : ℕ) (x : ℝ) :
    dist (world^[n] x) (abstract^[n] x) = 2 - 2 * (1 / 2) ^ n := by
  rw [world_iterate, abstract_iterate, Real.dist_eq, add_sub_cancel_left]
  apply abs_of_nonneg
  have small : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- **The bound is uniform** (the contraction theorem at `δ = 1`, `κ = 1/2`). -/
theorem uniform (n : ℕ) : ApproxSquare dist id id world^[n] abstract^[n] 2 := by
  have bound := ApproxSquare.iterate_contraction (dist_self (α := ℝ)) dist_triangle
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (fun a b => lipschitz a b) square n
  norm_num at bound
  exact bound

/-- **And not attained**: every horizon errs by strictly less than `2`. -/
theorem error_lt (n : ℕ) (x : ℝ) : dist (world^[n] x) (abstract^[n] x) < 2 := by
  rw [error_iterate]
  have positive : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

end Halving

end Mettapedia.Cybernetics.ApproximateAdequacy
