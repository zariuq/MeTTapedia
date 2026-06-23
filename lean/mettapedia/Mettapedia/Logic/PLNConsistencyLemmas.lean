import Mathlib.Tactic

/-!
# PLN Consistency Lemmas

This file proves that the conditional probability consistency bounds imply
the constraints needed for the deduction formula to stay in [0,1].

## Main Results

* `bounded_conditional_implies_bounded_intersection` - Upper bound implies pA * sAB ≤ pB
* `bounded_conditional_implies_complement_bound` - Lower Fréchet bound implies
  pC - pB*sBC ≤ 1 - pB

These lemmas complete the proof of `deduction_formula_in_unit_interval`.
-/

namespace Mettapedia.Logic.PLNConsistencyLemmas

noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left 0 _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := by
  unfold clamp01
  exact max_le (by norm_num) (min_le_right x 1)

noncomputable def largestIntersectionProbability (pA pB : ℝ) : ℝ :=
  clamp01 (pB / pA)

/-- If sAB ≤ clamp01(pB/pA), then pA * sAB ≤ pB.

This shows that the upper bound from consistency implies the intersection
doesn't exceed the marginal probability. -/
theorem bounded_conditional_implies_bounded_intersection
    (pA pB sAB : ℝ)
    (hpA_pos : 0 < pA)
    (hpB_nonneg : 0 ≤ pB)
    (_hsAB_nonneg : 0 ≤ sAB)
    (h_upper : sAB ≤ largestIntersectionProbability pA pB) :
    pA * sAB ≤ pB := by
  unfold largestIntersectionProbability clamp01 at h_upper
  -- sAB ≤ max 0 (min (pB/pA) 1)
  -- Since sAB ≥ 0, we have sAB ≤ min (pB/pA) 1
  have h_div_nonneg : 0 ≤ pB / pA := by positivity
  have h_min_nonneg : 0 ≤ min (pB / pA) 1 := by
    apply le_min
    · exact h_div_nonneg
    · norm_num
  have h : sAB ≤ min (pB / pA) 1 := by
    calc sAB ≤ max 0 (min (pB / pA) 1) := h_upper
         _ = min (pB / pA) 1 := by simp [max_eq_right h_min_nonneg]
  -- sAB ≤ min(pB/pA, 1) ≤ pB/pA
  have h_ratio : sAB ≤ pB / pA := by
    calc sAB ≤ min (pB / pA) 1 := h
         _ ≤ pB / pA := min_le_left _ _
  -- Multiply both sides by pA (positive)
  calc pA * sAB ≤ pA * (pB / pA) := by nlinarith
       _ = pB := by field_simp

/-- If `sBC` satisfies the lower Fréchet conditional bound, then
`pC - pB * sBC ≤ 1 - pB`.

The upper bound alone is not enough: e.g. `pB = pC = 0.9`, `sBC = 0` satisfies
`sBC ≤ largestIntersectionProbability pB pC` but violates this conclusion.
The needed information is the lower Fréchet side of conditional-probability
consistency. -/
theorem bounded_conditional_implies_complement_bound
    (pB pC sBC : ℝ)
    (hpB_bounds : 0 < pB ∧ pB ≤ 1)
    (_hpC_bounds : 0 ≤ pC ∧ pC ≤ 1)
    (hsBC_nonneg : 0 ≤ sBC)
    (h_lower : max 0 ((pB + pC - 1) / pB) ≤ sBC) :
    pC - pB * sBC ≤ 1 - pB := by
  suffices pC + pB * (1 - sBC) ≤ 1 by nlinarith
  by_cases h_case : pB + pC ≤ 1
  · nlinarith [hsBC_nonneg]
  · push Not at h_case
    have h_ratio_pos : 0 < (pB + pC - 1) / pB := by
      exact div_pos (by linarith) hpB_bounds.1
    have h_ratio_le : (pB + pC - 1) / pB ≤ sBC := by
      calc
        (pB + pC - 1) / pB =
            max 0 ((pB + pC - 1) / pB) := by
              rw [max_eq_right (le_of_lt h_ratio_pos)]
        _ ≤ sBC := h_lower
    have h_mul : pB * ((pB + pC - 1) / pB) = pB + pC - 1 := by
      field_simp [hpB_bounds.1.ne']
    nlinarith [mul_le_mul_of_nonneg_left h_ratio_le (le_of_lt hpB_bounds.1), h_mul]

end Mettapedia.Logic.PLNConsistencyLemmas
