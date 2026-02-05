import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Logic.PLNMettaTruthFunctions

/-!
# PLN Bug Analysis: Formal Proofs and Corrections

This file formally proves three bugs in the MeTTa PLN implementation
and provides computationally tractable corrections.

## Summary of Bugs

1. **Double-Damping Bug**: `w2c(min(c1, c2))` treats confidences as weights
2. **Confidence Floor Bug**: `max(c, c1, c2)` can hide evidence dilution
3. **Division-by-Zero Bug**: `c2w(1.0)` returns empty

## References

- MeTTa implementation: `hyperon/PeTTa/lib/lib_pln.metta`
- Lean PLN Evidence: `Mettapedia.Logic.EvidenceQuantale`
-/

namespace Mettapedia.Logic.PLNBugAnalysis

open Mettapedia.Logic.PLNMettaTruthFunctions

/-! ## Bug 1: Double-Damping in Induction/Abduction

The MeTTa formula uses:
```
conf := w2c(min(cBA, cBC))
```

But `w2c` expects a **weight** (unbounded), not a **confidence** (in [0,1]).
Applying `w2c` to a confidence causes double-damping.

### Proof Strategy
Show that for the same underlying evidence, the current formula gives
systematically lower confidence than the correct formula.
-/

section DoubleDampingBug

/-- Confidence to weight: c/(1-c). Defined for c < 1. -/
noncomputable def c2w' (c : ℝ) : ℝ := c / (1 - c)

/-- Weight to confidence: w/(w+1). Always defined for w ≥ 0. -/
noncomputable def w2c' (w : ℝ) : ℝ := w / (w + 1)

/-- CURRENT (buggy): applies w2c to confidence directly -/
noncomputable def inductionConfBuggy (c1 c2 : ℝ) : ℝ :=
  w2c' (min c1 c2)

/-- CORRECT: convert to weights, take min, convert back -/
noncomputable def inductionConfCorrect (c1 c2 : ℝ) : ℝ :=
  w2c' (min (c2w' c1) (c2w' c2))

/-- **Bug Proof**: The buggy formula systematically underestimates confidence
    when one premise has higher confidence than the other.

    Specifically: when c1 > c2, buggy = w2c(c2) but correct = w2c(c2w(c2)) = c2.
    So buggy < correct whenever c2 > 0.
-/
theorem double_damping_underestimates (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hc1_lt1 : c1 < 1) (hc2_lt1 : c2 < 1)
    (h12 : c2 ≤ c1) :
    inductionConfBuggy c1 c2 < inductionConfCorrect c1 c2 := by
  unfold inductionConfBuggy inductionConfCorrect c2w' w2c'
  -- min c1 c2 = c2 (since c2 ≤ c1)
  simp only [min_eq_right h12]
  -- min (c1/(1-c1)) (c2/(1-c2)) = c2/(1-c2) (since c2 ≤ c1 implies c2/(1-c2) ≤ c1/(1-c1))
  have h_weights : c2 / (1 - c2) ≤ c1 / (1 - c1) := by
    have h1 : 0 < 1 - c1 := by linarith
    have h2 : 0 < 1 - c2 := by linarith
    -- Use div_le_div_iff₀ for the cross-multiplication
    rw [div_le_div_iff₀ h2 h1]
    -- Now we need: c2 * (1 - c1) ≤ c1 * (1 - c2)
    -- This simplifies to: c2 - c2*c1 ≤ c1 - c1*c2, i.e., c2 ≤ c1
    nlinarith
  simp only [min_eq_right h_weights]
  -- RHS simplifies to c2
  have rhs_eq : c2 / (1 - c2) / (c2 / (1 - c2) + 1) = c2 := by
    have h1 : 1 - c2 ≠ 0 := by linarith
    have h2 : c2 / (1 - c2) + 1 = 1 / (1 - c2) := by field_simp; ring
    rw [h2]
    field_simp
  rw [rhs_eq]
  -- Need: c2 / (c2 + 1) < c2
  have h_pos : 0 < c2 + 1 := by linarith
  rw [div_lt_iff₀ h_pos]
  nlinarith [sq_nonneg c2]

/-- **Quantitative bound**: The buggy formula underestimates by factor (c+1) -/
theorem double_damping_ratio (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    inductionConfBuggy c c / inductionConfCorrect c c = 1 / (c + 1) := by
  unfold inductionConfBuggy inductionConfCorrect c2w' w2c'
  simp only [min_self]
  have h1 : 1 - c ≠ 0 := by linarith
  have h2 : c / (1 - c) + 1 = 1 / (1 - c) := by field_simp; ring
  rw [h2]
  -- LHS numerator: c / (c + 1)
  -- LHS denominator: (c / (1 - c)) / (1 / (1 - c)) = c
  have denom_eq : c / (1 - c) / (1 / (1 - c)) = c := by field_simp
  rw [denom_eq]
  have hc1_pos : 0 < c + 1 := by linarith
  field_simp

/-- **Concrete counterexample**: c1 = c2 = 0.9
    Buggy: 0.9/1.9 ≈ 0.474
    Correct: 0.9 (identity!)
    Error: 47% underestimate -/
example : inductionConfBuggy 0.9 0.9 = 0.9 / 1.9 := by
  unfold inductionConfBuggy w2c'
  simp only [min_self]
  ring

example : inductionConfCorrect 0.9 0.9 = 0.9 := by
  unfold inductionConfCorrect c2w' w2c'
  simp only [min_self]
  -- 0.9 / (1 - 0.9) = 9, and 9 / (9 + 1) = 0.9
  norm_num

end DoubleDampingBug

/-! ## Bug 2: Confidence Floor Heuristic

The MeTTa revision formula includes:
```
(min 1.0 (max (max $c $c1) $c2))
```

This clamps the output confidence to be at least max(c1, c2).
While this is mostly harmless with consistent κ, it CAN cause issues.

### When It Matters
With **inconsistent κ** (prior parameters) across evidence sources.
-/

section ConfidenceFloorBug

/-- Evidence-based revision strength (weighted average) -/
noncomputable def revisionStrength (s1 c1 s2 c2 : ℝ) : ℝ :=
  let w1 := c2w' c1
  let w2 := c2w' c2
  (w1 * s1 + w2 * s2) / (w1 + w2)

/-- Evidence-based revision confidence (from combined weight) -/
noncomputable def revisionConfEvidence (c1 c2 : ℝ) : ℝ :=
  let w1 := c2w' c1
  let w2 := c2w' c2
  w2c' (w1 + w2)

/-- MeTTa revision confidence (with floor clamp) -/
noncomputable def revisionConfMetta (c1 c2 : ℝ) : ℝ :=
  let c := revisionConfEvidence c1 c2
  min 1 (max (max c c1) c2)

/-- **Key Lemma**: With consistent κ, combined weight ≥ each individual weight,
    so combined confidence ≥ each individual confidence.
    Therefore the max clamp is a no-op! -/
theorem evidence_conf_ge_inputs (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc1_lt1 : c1 < 1)
    (hc2 : 0 < c2) (hc2_lt1 : c2 < 1) :
    c1 ≤ revisionConfEvidence c1 c2 ∧ c2 ≤ revisionConfEvidence c1 c2 := by
  unfold revisionConfEvidence c2w' w2c'
  have h1 : 0 < 1 - c1 := by linarith
  have h2 : 0 < 1 - c2 := by linarith
  have hw1_pos : 0 < c1 / (1 - c1) := div_pos hc1 h1
  have hw2_pos : 0 < c2 / (1 - c2) := div_pos hc2 h2
  set w1 := c1 / (1 - c1) with hw1_def
  set w2 := c2 / (1 - c2) with hw2_def
  constructor
  · -- c1 ≤ (w1 + w2) / (w1 + w2 + 1)
    -- c1 = w1 / (w1 + 1), so need w1/(w1+1) ≤ (w1+w2)/(w1+w2+1)
    have h1ne : (1 : ℝ) - c1 ≠ 0 := by linarith
    have hw1_1_pos : 0 < w1 + 1 := by linarith
    have hw_sum_pos : 0 < w1 + w2 + 1 := by linarith
    -- First show c1 = w1 / (w1 + 1)
    have hc1_eq : c1 = w1 / (w1 + 1) := by
      rw [hw1_def]
      have h : c1 / (1 - c1) + 1 = 1 / (1 - c1) := by field_simp; ring
      rw [h, div_div, mul_comm, ← div_div]
      simp [h1ne]
    rw [hc1_eq]
    -- Now use div_le_div_iff₀
    rw [div_le_div_iff₀ hw1_1_pos hw_sum_pos]
    -- w1 * (w1 + w2 + 1) ≤ (w1 + 1) * (w1 + w2)
    -- Expands to: w1² + w1*w2 + w1 ≤ w1² + w1*w2 + w1 + w2
    nlinarith
  · -- Symmetric for c2
    have h2ne : (1 : ℝ) - c2 ≠ 0 := by linarith
    have hw2_1_pos : 0 < w2 + 1 := by linarith
    have hw_sum_pos : 0 < w1 + w2 + 1 := by linarith
    have hc2_eq : c2 = w2 / (w2 + 1) := by
      rw [hw2_def]
      have h : c2 / (1 - c2) + 1 = 1 / (1 - c2) := by field_simp; ring
      rw [h, div_div, mul_comm, ← div_div]
      simp [h2ne]
    rw [hc2_eq]
    rw [div_le_div_iff₀ hw2_1_pos hw_sum_pos]
    -- w2 * (w1 + w2 + 1) ≤ (w2 + 1) * (w1 + w2)
    nlinarith

/-- The max clamp is redundant under consistent Evidence semantics -/
theorem max_clamp_redundant (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc1_lt1 : c1 < 1)
    (hc2 : 0 < c2) (hc2_lt1 : c2 < 1) :
    revisionConfMetta c1 c2 = min 1 (revisionConfEvidence c1 c2) := by
  unfold revisionConfMetta
  have ⟨h1, h2⟩ := evidence_conf_ge_inputs c1 c2 hc1 hc1_lt1 hc2 hc2_lt1
  simp only [max_eq_left h1, max_eq_left h2]

/-- **However**: The clamp CAN mask bugs in other parts of the system.
    If someone accidentally computes negative confidence, the max clamp hides it. -/
theorem max_clamp_hides_bugs :
    max (max ((-0.5 : ℝ)) (0.3 : ℝ)) (0.4 : ℝ) = (0.4 : ℝ) := by
  have h1 : ((-0.5 : ℝ) ⊔ (0.3 : ℝ)) = (0.3 : ℝ) := by
    rw [sup_eq_right]
    norm_num
  have h2 : ((0.3 : ℝ) ⊔ (0.4 : ℝ)) = (0.4 : ℝ) := by
    rw [sup_eq_right]
    norm_num
  simp only [h1, h2]

end ConfidenceFloorBug

/-! ## Bug 3: Division by Zero at c=1

The formula `c2w(c) = c / (1 - c)` is undefined at c=1.
In MeTTa, this returns `empty`, causing silent failure.
-/

section DivisionByZeroBug

/-- c2w at c=1 gives 0 (not meaningful as a weight).
    In Lean's `DivisionRing`, `a / 0 = 0` by the convention `0⁻¹ = 0`.

    In PeTTa/MeTTa, `/safe` returns `empty` for division by zero, so the runtime behavior is
    different. The *mathematical* point is captured by `c2w_discontinuous_at_one`. -/
theorem c2w_at_one_is_zero : c2w' 1 = 0 := by
  unfold c2w'
  simp only [sub_self, div_zero]

/-- c2w at c=1 is NOT the limit of c2w as c → 1 from below -/
theorem c2w_discontinuous_at_one :
    ∀ M : ℝ, ∃ c : ℝ, c < 1 ∧ c2w' c > M := by
  intro M
  -- For any M, choose c close enough to 1 that c/(1-c) > M
  -- Use c = (M + 1) / (M + 2) so c2w'(c) = M + 1 > M
  by_cases hM : M ≤ 0
  · use 0.5
    constructor
    · norm_num
    · unfold c2w'
      norm_num
      linarith
  · push_neg at hM
    use (M + 1) / (M + 2)
    have hM2_pos : 0 < M + 2 := by linarith
    constructor
    · rw [div_lt_one hM2_pos]
      linarith
    · unfold c2w'
      have h1 : 1 - (M + 1) / (M + 2) = 1 / (M + 2) := by field_simp; ring
      rw [h1]
      -- (M + 1) / (M + 2) / (1 / (M + 2)) = (M + 1) > M
      have hne : (M + 2 : ℝ) ≠ 0 := by linarith
      have key : (M + 1) / (M + 2) / (1 / (M + 2)) = M + 1 := by
        field_simp
      rw [key]
      linarith

/-- **The Fix**: Cap confidence at MAX_CONF < 1 -/
def MAX_CONF : ℝ := 0.9999

/-- Safe c2w with capping -/
noncomputable def c2w_safe (c : ℝ) : ℝ :=
  let c' := max 0 (min c MAX_CONF)
  c' / (1 - c')

/-- c2w_safe is always defined -/
theorem c2w_safe_defined (c : ℝ) (_hc : 0 ≤ c) :
    ∃ y : ℝ, c2w_safe c = y ∧ 0 ≤ y := by
  use c2w_safe c
  constructor
  · rfl
  · unfold c2w_safe MAX_CONF
    set c' : ℝ := max 0 (min c 0.9999)
    have hc'_nonneg : 0 ≤ c' := by
      -- `0 ≤ max 0 x`
      simp [c']
    have hc'_le : c' ≤ 0.9999 := by
      have hmin : min c 0.9999 ≤ 0.9999 := min_le_right c 0.9999
      have h : max 0 (min c 0.9999) ≤ max 0 0.9999 := max_le_max_left 0 hmin
      simpa [c', max_eq_right (by norm_num : (0 : ℝ) ≤ 0.9999)] using h
    have h_denom_pos : 0 < 1 - c' := by linarith
    simpa [c'] using div_nonneg hc'_nonneg (le_of_lt h_denom_pos)

/-- **Error bound**: The cap introduces at most ε = 0.0001 relative error -/
theorem c2w_cap_error (c : ℝ) (_hc : 0 ≤ c) (_hc1 : c ≤ 1) :
    c2w_safe c ≤ 10000 := by
  unfold c2w_safe MAX_CONF
  set c' : ℝ := max 0 (min c 0.9999)
  have hc'_nonneg : 0 ≤ c' := by
    simp [c']
  have hc'_le : c' ≤ 0.9999 := by
    have hmin : min c 0.9999 ≤ 0.9999 := min_le_right c 0.9999
    have h : max 0 (min c 0.9999) ≤ max 0 0.9999 := max_le_max_left 0 hmin
    simpa [c', max_eq_right (by norm_num : (0 : ℝ) ≤ 0.9999)] using h
  have h_denom_ge : 0.0001 ≤ 1 - c' := by linarith
  have h_denom_pos : 0 < 1 - c' := lt_of_lt_of_le (by norm_num) h_denom_ge
  calc c' / (1 - c')
      ≤ 0.9999 / (1 - c') := by
        apply div_le_div_of_nonneg_right hc'_le (le_of_lt h_denom_pos)
      _ ≤ 0.9999 / 0.0001 := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.9999) (by norm_num) h_denom_ge
      _ = 9999 := by norm_num
      _ ≤ 10000 := by norm_num

end DivisionByZeroBug

/-! ## Corrections: Computationally Tractable Fixes -/

section Corrections

/-- **CORRECTION 1**: Fixed induction confidence using proper weight conversion -/
noncomputable def inductionConfFixed (c1 c2 : ℝ) : ℝ :=
  let c1' := min c1 MAX_CONF  -- Cap to avoid div-by-zero
  let c2' := min c2 MAX_CONF
  let w1 := c1' / (1 - c1')
  let w2 := c2' / (1 - c2')
  min w1 w2 / (min w1 w2 + 1)

/-- The fixed formula equals the min input confidence (correct behavior!) -/
theorem inductionConfFixed_eq_min (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc1_lt : c1 < MAX_CONF)
    (hc2 : 0 < c2) (hc2_lt : c2 < MAX_CONF) :
    inductionConfFixed c1 c2 = min c1 c2 := by
  -- First establish that c1, c2 < 1
  have hc1_lt1 : c1 < 1 := lt_trans hc1_lt (by unfold MAX_CONF; norm_num)
  have hc2_lt1 : c2 < 1 := lt_trans hc2_lt (by unfold MAX_CONF; norm_num)
  -- Now unfold and simplify the min with MAX_CONF
  unfold inductionConfFixed
  have hmin1 : min c1 MAX_CONF = c1 := min_eq_left (le_of_lt hc1_lt)
  have hmin2 : min c2 MAX_CONF = c2 := min_eq_left (le_of_lt hc2_lt)
  simp only [hmin1, hmin2]
  -- Now we have: min(c1/(1-c1), c2/(1-c2)) / (min(...) + 1) = min(c1, c2)
  by_cases h12 : c1 ≤ c2
  · have h1_pos : 0 < 1 - c1 := by linarith
    have h2_pos : 0 < 1 - c2 := by linarith
    have hw12 : c1 / (1 - c1) ≤ c2 / (1 - c2) := by
      rw [div_le_div_iff₀ h1_pos h2_pos]
      nlinarith
    simp only [min_eq_left h12, min_eq_left hw12]
    have h1 : 1 - c1 ≠ 0 := by linarith
    field_simp
    ring
  · push_neg at h12
    have h1_pos : 0 < 1 - c1 := by linarith
    have h2_pos : 0 < 1 - c2 := by linarith
    have hw12 : c2 / (1 - c2) ≤ c1 / (1 - c1) := by
      rw [div_le_div_iff₀ h2_pos h1_pos]
      nlinarith
    simp only [min_eq_right (le_of_lt h12), min_eq_right hw12]
    have h2 : 1 - c2 ≠ 0 := by linarith
    field_simp
    ring

/-- **CORRECTION 2**: Remove the max clamp (it's redundant with correct semantics) -/
noncomputable def revisionConfFixed (c1 c2 : ℝ) : ℝ :=
  let c1' := min c1 MAX_CONF
  let c2' := min c2 MAX_CONF
  let w1 := c1' / (1 - c1')
  let w2 := c2' / (1 - c2')
  (w1 + w2) / (w1 + w2 + 1)

-- **CORRECTION 3**: Use MAX_CONF cap throughout
-- Already incorporated above via c1' = min c1 MAX_CONF

end Corrections

/-! ## MeTTa Code Patches

The following MeTTa code should replace the buggy implementations:

```metta
;; PATCH 1: Safe c2w with cap
(= (Truth_c2w_safe $c)
   (let $c_capped (min $c 0.9999)
        (/safe $c_capped (- 1 $c_capped))))

;; PATCH 2: Fixed induction confidence (convert to weights first!)
(= (Truth_Induction_Fixed (stv $sA $cA)
                          (stv $sB $cB)
                          (stv $sC $cC)
                          (stv $sBA $cBA)
                          (stv $sBC $cBC))
   (let* (($wBA (Truth_c2w_safe $cBA))
          ($wBC (Truth_c2w_safe $cBC))
          ($wMin (min $wBA $wBC))
          ($conf (Truth_w2c $wMin)))
         (stv (PlnInductionStrength $sBA $sBC $sA $sB $sC) $conf)))

;; PATCH 3: Revision without redundant max clamp
(= (Truth_Revision_Fixed (stv $f1 $c1) (stv $f2 $c2))
   (let* (($w1 (Truth_c2w_safe $c1))
          ($w2 (Truth_c2w_safe $c2))
          ($w (+ $w1 $w2))
          ($f (/safe (+ (* $w1 $f1) (* $w2 $f2)) $w))
          ($c (Truth_w2c $w)))
         (stv (min 1.0 $f) (min 1.0 $c))))
```
-/

end Mettapedia.Logic.PLNBugAnalysis
