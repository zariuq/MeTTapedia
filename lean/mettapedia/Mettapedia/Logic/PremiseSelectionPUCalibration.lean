import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# PU-Style Weak-Negative Calibration Lemmas

This module formalizes a minimal weak-negative adjustment family for premise-selection
scores in a proof-driven way.

The core idea is intentionally lightweight:
- start from a base score `s`
- subtract a weak penalty `λ * z` where `z` is an unlabeled/negative indicator signal

We prove three foundational facts:
1. zero penalty recovers the base score exactly
2. increasing penalty weight only decreases adjusted scores (for nonnegative signal)
3. perturbation magnitude is bounded by `λ * B` when `|z| ≤ B`
-/

namespace Mettapedia.Logic.PremiseSelection

/-- Weak-negative adjusted score: base score minus a weighted weak-negative signal. -/
def weakNegativeAdjusted {X : Type*} (s z : X → ℝ) (w : ℝ) : X → ℝ :=
  fun x => s x - w * z x

@[simp] theorem weakNegativeAdjusted_zero {X : Type*} (s z : X → ℝ) :
    weakNegativeAdjusted s z 0 = s := by
  funext x
  simp [weakNegativeAdjusted]

/-- If the weak-negative signal is nonnegative, a larger penalty weight cannot increase
any adjusted score. -/
theorem weakNegativeAdjusted_antitone_in_weight
    {X : Type*} (s z : X → ℝ)
    {w1 w2 : ℝ}
    (hw : w1 ≤ w2)
    (hz : ∀ x, 0 ≤ z x) :
    ∀ x, weakNegativeAdjusted s z w2 x ≤ weakNegativeAdjusted s z w1 x := by
  intro x
  have hz' : 0 ≤ z x := hz x
  have hmul : w1 * z x ≤ w2 * z x := by
    exact mul_le_mul_of_nonneg_right hw hz'
  have hnegmul : -(w2 * z x) ≤ -(w1 * z x) := by
    exact neg_le_neg hmul
  simpa [weakNegativeAdjusted, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    add_le_add_left hnegmul (s x)

/-- Pointwise perturbation from weak-negative adjustment is bounded by `λ * B`
when `|z| ≤ B` and `λ ≥ 0`. -/
theorem weakNegativeAdjusted_abs_diff_le
    {X : Type*} (s z : X → ℝ)
    (w B : ℝ)
    (hw : 0 ≤ w)
    (hz : ∀ x, |z x| ≤ B) :
    ∀ x, |weakNegativeAdjusted s z w x - s x| ≤ w * B := by
  intro x
  have hzB : |z x| ≤ B := hz x
  have hmul : w * |z x| ≤ w * B := mul_le_mul_of_nonneg_left hzB hw
  calc
    |weakNegativeAdjusted s z w x - s x|
        = |-(w * z x)| := by
            simp [weakNegativeAdjusted]
    _ = |w * z x| := by simp
    _ = |w| * |z x| := by simp [abs_mul]
    _ = w * |z x| := by simp [abs_of_nonneg hw]
    _ ≤ w * B := hmul

/-- Special case of the perturbation bound with unit-bounded weak-negative signal. -/
theorem weakNegativeAdjusted_abs_diff_le_weight
    {X : Type*} (s z : X → ℝ)
    (w : ℝ)
    (hw : 0 ≤ w)
    (hz : ∀ x, |z x| ≤ 1) :
    ∀ x, |weakNegativeAdjusted s z w x - s x| ≤ w := by
  intro x
  have hbase := weakNegativeAdjusted_abs_diff_le s z w 1 hw hz x
  simpa using hbase

/-- Delta-form bound for use in generic perturbation stability theorems. -/
theorem weakNegativeDelta_abs_le_weight
    {X : Type*} (z : X → ℝ)
    (w : ℝ)
    (hw : 0 ≤ w)
    (hz : ∀ x, |z x| ≤ 1) :
    ∀ x, |(-w * z x)| ≤ w := by
  intro x
  calc
    |(-w * z x)| = |w| * |z x| := by
      simp [abs_mul]
    _ = w * |z x| := by simp [abs_of_nonneg hw]
    _ ≤ w * 1 := mul_le_mul_of_nonneg_left (hz x) hw
    _ = w := by ring

end Mettapedia.Logic.PremiseSelection
