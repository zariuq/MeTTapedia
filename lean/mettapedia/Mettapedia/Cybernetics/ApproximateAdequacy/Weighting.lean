import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Goal-weighted averages: exactly what they certify

The mind–world correspondence principle (B. Goertzel, C. Pennachin and
N. Geisweiller, *Engineering General Intelligence, Part 1*, 2014, §11.3–11.4)
asks that the average of the correspondence defects be small, where the
average is taken under a distribution over paths that balances simplicity
with directedness toward goal nodes.  This module states what such an average
certifies, for any error function on a finitely supported weighting.

* **An expectation bound**, by definition (`FiniteWeighting.expectation`); a
  uniform bound implies it (`FiniteWeighting.expectation_le_of_le`).
* **A tail bound**: the weight of the paths with error at least `t` is at most
  the expectation divided by `t` (Markov's inequality,
  `FiniteWeighting.tailMass_le_div`).
* **Nothing more.**  The tail bound is sharp: every set of paths whose weight
  is consistent with Markov's inequality can carry error `t`
  (`FiniteWeighting.markov_sharp`).  No uniform bound follows: for every `ε > 0` and every
  `M`, some weighting has expected error at most `ε` and error `M` on a path
  of positive weight (`exists_small_expectation_large_error`).
* **Blind off the goal paths**: the expectation ignores every value off the
  support (`FiniteWeighting.expectation_congr`).
* **Goal change.**  A guarantee for today's weighting transfers to
  tomorrow's with factor `K` when tomorrow's weight is at most `K` times
  today's on every path (`FiniteWeighting.expectation_le_mul_of_le`), a bounded likelihood
  ratio.  When tomorrow charges a path outside today's support, nothing
  transfers: the expected error can be zero today and arbitrary tomorrow
  (`FiniteWeighting.exists_no_transfer`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ι : Type*}

/-- **A finitely supported probability weighting** of paths (or of any
index). -/
structure FiniteWeighting (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] (ι : Type*) where
  support : Finset ι
  weight : ι → 𝕜
  nonneg : ∀ i ∈ support, 0 ≤ weight i
  sum_eq_one : ∑ i ∈ support, weight i = 1

namespace FiniteWeighting

variable (w : FiniteWeighting 𝕜 ι)

/-- The expectation of an error function. -/
def expectation (X : ι → 𝕜) : 𝕜 :=
  ∑ i ∈ w.support, w.weight i * X i

/-- The weight of the supported paths with error at least `t`. -/
def tailMass (X : ι → 𝕜) (t : 𝕜) : 𝕜 :=
  ∑ i ∈ w.support with t ≤ X i, w.weight i

variable {w}

theorem expectation_nonneg {X : ι → 𝕜} (nonneg : ∀ i ∈ w.support, 0 ≤ X i) :
    0 ≤ w.expectation X :=
  Finset.sum_nonneg fun i member => mul_nonneg (w.nonneg i member) (nonneg i member)

/-- **A uniform bound implies the expectation bound.** -/
theorem expectation_le_of_le {X : ι → 𝕜} {B : 𝕜} (bound : ∀ i ∈ w.support, X i ≤ B) :
    w.expectation X ≤ B := by
  calc w.expectation X ≤ ∑ i ∈ w.support, w.weight i * B :=
        Finset.sum_le_sum fun i member => mul_le_mul_of_nonneg_left (bound i member)
          (w.nonneg i member)
    _ = B := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

omit [IsStrictOrderedRing 𝕜] in
/-- **Blind off the goal paths**: the expectation depends only on the values
on the support. -/
theorem expectation_congr {X X' : ι → 𝕜} (same : ∀ i ∈ w.support, X i = X' i) :
    w.expectation X = w.expectation X' :=
  Finset.sum_congr rfl fun i member => by rw [same i member]

/-- **Markov's inequality**: `t` times the weight of the paths with error at
least `t` is at most the expected error. -/
theorem mul_tailMass_le {X : ι → 𝕜} (nonneg : ∀ i ∈ w.support, 0 ≤ X i) (t : 𝕜) :
    t * w.tailMass X t ≤ w.expectation X := by
  unfold tailMass expectation
  rw [Finset.mul_sum]
  calc ∑ i ∈ w.support with t ≤ X i, t * w.weight i
      ≤ ∑ i ∈ w.support with t ≤ X i, w.weight i * X i :=
        Finset.sum_le_sum fun i member => by
          rw [Finset.mem_filter] at member
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left member.2 (w.nonneg i member.1)
    _ ≤ ∑ i ∈ w.support, w.weight i * X i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i member _ => mul_nonneg (w.nonneg i member) (nonneg i member)

theorem tailMass_le_div {X : ι → 𝕜} (nonneg : ∀ i ∈ w.support, 0 ≤ X i) {t : 𝕜}
    (t_pos : 0 < t) : w.tailMass X t ≤ w.expectation X / t := by
  rw [le_div_iff₀ t_pos, mul_comm]
  exact mul_tailMass_le nonneg t

omit [IsStrictOrderedRing 𝕜] in
/-- **Markov's inequality is sharp**: for every set `D` of supported paths and
every `t ≥ 0` with `t` times the weight of `D` at most `ε`, the error `t` on
`D` and `0` elsewhere has expectation at most `ε`. -/
theorem markov_sharp [DecidableEq ι] {D : Finset ι} (inside : D ⊆ w.support) {t ε : 𝕜}
    (bound : t * ∑ i ∈ D, w.weight i ≤ ε) :
    w.expectation (fun i => if i ∈ D then t else 0) ≤ ε ∧
      ∀ i ∈ D, t ≤ (fun i => if i ∈ D then t else 0) i := by
  refine ⟨?_, fun i member => by simp [member]⟩
  have value : w.expectation (fun i => if i ∈ D then t else 0) = t * ∑ i ∈ D, w.weight i := by
    unfold expectation
    have split : ∀ i ∈ w.support, w.weight i * (if i ∈ D then t else 0) =
        if i ∈ D then t * w.weight i else 0 := fun i _ => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl split, ← Finset.sum_filter, Finset.mul_sum]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun both => both.2, fun member => ⟨inside member, member⟩⟩
  rw [value]
  exact bound

/-- **Goal transfer with a bounded likelihood ratio.** -/
theorem expectation_le_mul_of_le {w' : FiniteWeighting 𝕜 ι} {X : ι → 𝕜}
    (nonneg : ∀ i ∈ w.support, 0 ≤ X i) {K : 𝕜} (K_nonneg : 0 ≤ K)
    (dominated : ∀ i ∈ w'.support, i ∈ w.support ∧ w'.weight i ≤ K * w.weight i) :
    w'.expectation X ≤ K * w.expectation X := by
  unfold expectation
  rw [Finset.mul_sum]
  calc ∑ i ∈ w'.support, w'.weight i * X i
      ≤ ∑ i ∈ w'.support, K * (w.weight i * X i) :=
        Finset.sum_le_sum fun i member => by
          obtain ⟨inside, le⟩ := dominated i member
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right le (nonneg i inside)
    _ ≤ ∑ i ∈ w.support, K * (w.weight i * X i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun i member => (dominated i member).1)
          fun i member _ => mul_nonneg K_nonneg (mul_nonneg (w.nonneg i member) (nonneg i member))

omit [IsStrictOrderedRing 𝕜] in
/-- **No transfer to a path outside today's support**: the expected error can
be zero under today's weighting and `w' i * M` under tomorrow's, for every
`M`. -/
theorem exists_no_transfer [DecidableEq ι] (w' : FiniteWeighting 𝕜 ι) {i : ι}
    (outside : i ∉ w.support) (charged : i ∈ w'.support) (M : 𝕜) :
    w.expectation (fun j => if j = i then M else 0) = 0 ∧
      w'.expectation (fun j => if j = i then M else 0) = w'.weight i * M := by
  constructor
  · refine Finset.sum_eq_zero fun j member => ?_
    have different : j ≠ i := fun same => outside (same ▸ member)
    simp only [if_neg different, mul_zero]
  · unfold expectation
    have single : ∀ j ∈ w'.support, w'.weight j * (if j = i then M else 0) =
        if j = i then w'.weight i * M else 0 := fun j _ => by
      split_ifs with same
      · rw [same]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl single, Finset.sum_ite_eq' w'.support i, if_pos charged]

end FiniteWeighting

/-! ## No uniform bound follows from an expectation bound -/

/-- The weighting of two outcomes, the first with weight `p`. -/
def twoPoint (p : 𝕜) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1) : FiniteWeighting 𝕜 Bool where
  support := {true, false}
  weight b := if b then p else 1 - p
  nonneg b _ := by cases b <;> simp [p_nonneg, p_le]
  sum_eq_one := by simp

/-- **No uniform bound**: for every `ε > 0` and `M ≥ 0` there is a weighting
with expected error at most `ε` and error `M` on a path of positive weight. -/
theorem exists_small_expectation_large_error {ε M : 𝕜} (ε_pos : 0 < ε) (M_nonneg : 0 ≤ M) :
    ∃ (w : FiniteWeighting 𝕜 Bool) (X : Bool → 𝕜), w.expectation X ≤ ε ∧
      ∃ i ∈ w.support, 0 < w.weight i ∧ X i = M := by
  have denominator : 0 < ε + M := by linarith
  have p_pos : 0 < ε / (ε + M) := div_pos ε_pos denominator
  have p_le : ε / (ε + M) ≤ 1 := (div_le_one denominator).mpr (by linarith)
  refine ⟨twoPoint (ε / (ε + M)) p_pos.le p_le, fun b => if b then M else 0, ?_,
    true, by simp [twoPoint], by simpa [twoPoint] using p_pos, rfl⟩
  have value : (twoPoint (ε / (ε + M)) p_pos.le p_le).expectation (fun b => if b then M else 0) =
      ε / (ε + M) * M := by
    simp [FiniteWeighting.expectation, twoPoint]
  rw [value, div_mul_eq_mul_div, div_le_iff₀ denominator]
  nlinarith

end Mettapedia.Cybernetics.ApproximateAdequacy
