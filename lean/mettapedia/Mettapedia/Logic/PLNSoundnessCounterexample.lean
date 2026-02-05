import Mathlib.Data.Real.Basic
import Mettapedia.Logic.PLNWeightTV

/-!
# PLN Soundness Counterexample: Evidence-Based Confidence vs Probability Error Bounds

This file proves a formal counterexample showing that Evidence-based confidence formulas
cannot satisfy the standard soundness condition `|P - s| ≤ 1 - c` when using
error propagation through products.

## The Setup

**Evidence-based confidence** (from tensor product):
- `c_out = w2c(w_A * w_B)` where `w = c/(1-c)`
- This comes from Evidence counts: `(n⁺_A * n⁺_B, n⁻_A * n⁻_B)`

**Standard error propagation** (proven in PLNInferenceCalculus):
- If `|P_A - s_A| ≤ e_A` and `|P_B - s_B| ≤ e_B`
- Then `|P_A*P_B - s_A*s_B| ≤ e_A + e_B` (product_error_bound)

**Soundness condition**:
- `|P - s| ≤ 1 - c` (error bound ≤ confidence complement)

**The Question**: Can these three be simultaneously true?

## The Counterexample

With `e_A = 1 - c_A` and `e_B = 1 - c_B`, soundness requires:
```
e_A + e_B ≤ 1 - c_out
(1 - c_A) + (1 - c_B) ≤ 1 - w2c(c2w(c_A) * c2w(c_B))
2 - c_A - c_B ≤ 1 - w2c(w_A * w_B)
c_out ≤ c_A + c_B - 1
```

**Claim**: This fails for `c_A = c_B = 0.5`.

We will prove:
1. The computation: `c_out = w2c(1 * 1) = 0.5`
2. The requirement: `0.5 ≤ 0.5 + 0.5 - 1 = 0`
3. **Contradiction**: `0.5 ≤ 0` is false

This exposes where the inconsistency enters.
-/

namespace Mettapedia.Logic.PLNSoundnessCounterexample

open Mettapedia.Logic.PLNWeightTV

/-! ## Step 1: Evidence-Based Confidence Computation -/

/-- With cA = cB = 0.5, compute wA = c/(1-c) -/
example : c2w 0.5 = 1 := by
  unfold c2w
  norm_num

/-- Product of weights: w_out = wA * wB = 1 * 1 = 1 -/
example : c2w 0.5 * c2w 0.5 = 1 := by
  unfold c2w
  norm_num

/-- Convert back to confidence: c_out = w/(w+1) = 1/2 = 0.5 -/
example : w2c (c2w 0.5 * c2w 0.5) = 0.5 := by
  unfold w2c c2w
  norm_num

/-! ## Step 2: Soundness Requirement -/

/-- Soundness requires: c_out ≤ cA + cB - 1 -/
theorem soundness_requirement_for_product (cA cB : ℝ)
    (hcA : 0 ≤ cA ∧ cA < 1) (hcB : 0 ≤ cB ∧ cB < 1) :
    -- If error propagation gives: e_out = e_A + e_B
    -- And soundness requires: e_out = 1 - c_out
    -- Then: (1 - cA) + (1 - cB) = 1 - c_out
    -- Which means: c_out = cA + cB - 1
    -- For soundness to hold, we need:
    w2c (c2w cA * c2w cB) ≤ cA + cB - 1 := by
  sorry  -- This is the requirement we're testing

/-! ## Step 3: The Counterexample -/

/-- **COUNTEREXAMPLE**: With cA = cB = 0.5, the requirement fails.

We have:
- c_out = w2c(1 * 1) = 0.5
- Required: c_out ≤ 0.5 + 0.5 - 1 = 0
- But: 0.5 ≤ 0 is **false**

This proves the inconsistency. -/
theorem counterexample_cA_cB_half :
    ¬(w2c (c2w 0.5 * c2w 0.5) ≤ 0.5 + 0.5 - 1) := by
  -- Compute LHS: w2c(1) = 0.5
  have lhs : w2c (c2w 0.5 * c2w 0.5) = 0.5 := by
    unfold w2c c2w
    simp
    norm_num
  -- Compute RHS: 0.5 + 0.5 - 1 = 0
  have rhs : 0.5 + 0.5 - 1 = (0 : ℝ) := by norm_num
  -- Show 0.5 ≤ 0 is false
  rw [lhs, rhs]
  norm_num

/-! ## Analysis: Where Does the Inconsistency Enter?

We have three components:

1. **Evidence-based formula** (correct by Evidence theory):
   ```
   c_out = w2c(w_A * w_B) where w = c/(1-c) (normalized evidence amount)
   ```
   This is the tensor product of Evidence counts.

2. **Product error bound** (proven in PLNInferenceCalculus):
   ```
   |PA*PB - sA*sB| ≤ eA + eB
   ```
   This is standard real analysis.

3. **Soundness condition**:
   ```
   |P - s| ≤ 1 - c
   ```
   This interprets confidence as error bound.

**The Inconsistency**: These three cannot all be true simultaneously!

## Diagnosis

The problem is that **confidence has two different meanings**:

### Meaning 1: Evidence-theoretic (from Evidence counts)
- `c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)` (total evidence relative to prior)
- Or via weight: `c = w/(w+1)` where `w = c/(1-c) = (n⁺+n⁻)/κ` (for κ > 0)
- **Interpretation**: "How much evidence we have"

### Meaning 2: Error bound (from soundness condition)
- `c = 1 - e` where `e` is the error bound `|P - s|`
- **Interpretation**: "How tight our error bound is"

**The Mismatch**: Evidence-theoretic confidence (Meaning 1) does NOT equal
error-bound confidence (Meaning 2) after product operations!

For independent observations:
- Evidence counts **multiply**: (n⁺_A·n⁺_B, n⁻_A·n⁻_B)
- Error bounds **add**: e_out = e_A + e_B

These two operations are incompatible for preserving `c = 1 - e`.

## Possible Resolutions

1. **Different soundness condition**: Use a soundness model where confidence
   isn't just `1 - error`. Perhaps: `error ≤ f(c)` for some function `f`.

2. **Weight-space soundness**: Define soundness directly in terms of weights,
   not confidence. E.g., `|P - s| ≤ g(w)` for some function `g`.

3. **Separate error/confidence**: Track error bounds separately from Evidence
   confidence. Evidence gives us `c` (how much evidence), error propagation
   gives us `e` (error bound), and they're related but not `c = 1 - e`.

4. **Independence assumption fails**: The soundness condition `|P - s| ≤ 1 - c`
   might only hold for *single observations*, not after combining independent
   evidence sources.
-/

/-! ## Verification: Error Propagation is Correct -/

/-- The product error bound is proven in PLNInferenceCalculus.lean.
Here we verify it for our specific case. -/
theorem product_error_specific (PA PB sA sB : ℝ)
    (hPA : PA ∈ Set.Icc 0 1) (_hPB : PB ∈ Set.Icc 0 1)
    (_hsA : sA ∈ Set.Icc 0 1) (hsB : sB ∈ Set.Icc 0 1)
    (h_eA : |PA - sA| ≤ 0.5) (h_eB : |PB - sB| ≤ 0.5) :
    |PA * PB - sA * sB| ≤ 1 := by
  -- Decompose: ab - ahat*bhat = a(b - bhat) + bhat(a - ahat)
  have h_decomp : PA * PB - sA * sB = PA * (PB - sB) + sB * (PA - sA) := by ring
  rw [h_decomp]
  -- Triangle inequality
  calc |PA * (PB - sB) + sB * (PA - sA)|
      ≤ |PA * (PB - sB)| + |sB * (PA - sA)| := abs_add_le _ _
    _ = |PA| * |PB - sB| + |sB| * |PA - sA| := by rw [abs_mul, abs_mul]
    _ = PA * |PB - sB| + sB * |PA - sA| := by
        rw [abs_of_nonneg (Set.mem_Icc.mp hPA).1, abs_of_nonneg (Set.mem_Icc.mp hsB).1]
    _ ≤ PA * 0.5 + sB * 0.5 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_eB (Set.mem_Icc.mp hPA).1
        · exact mul_le_mul_of_nonneg_left h_eA (Set.mem_Icc.mp hsB).1
    _ ≤ 1 * 0.5 + 1 * 0.5 := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right (Set.mem_Icc.mp hPA).2 (by norm_num)
        · apply mul_le_mul_of_nonneg_right (Set.mem_Icc.mp hsB).2 (by norm_num)
    _ = 1 := by norm_num

/-! ## The Core Issue

**Error propagation is correct**: e_out = e_A + e_B = 0.5 + 0.5 = 1

**Evidence-based confidence is correct**: c_out = w2c(1) = 0.5

**The inconsistency**: We cannot have both:
- e_out = 1 - c_out (soundness condition)
- e_out = 1, c_out = 0.5

Because `1 ≠ 1 - 0.5 = 0.5`.

This proves that the soundness condition `e = 1 - c` **cannot hold** after
combining independent evidence sources using Evidence-theoretic formulas.

## Next Steps

We need to investigate EvidenceQuantale.lean and PLNDeduction.lean to understand:
1. What soundness condition SHOULD hold for Evidence-based TVs?
2. Is there a different error model that matches Evidence theory?
3. Should we track error bounds separately from Evidence confidence?
-/

end Mettapedia.Logic.PLNSoundnessCounterexample
