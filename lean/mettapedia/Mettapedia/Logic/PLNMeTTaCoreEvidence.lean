/-
Copyright (c) 2026 Mettapedia Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLNMeTTaCore

/-!
# Evidence-STV Bridge

This module bridges the gap between:
1. **Evidence** (quantale carrier from PLNEvidence.lean)
2. **STV** (bounded truth values from PLNMeTTaCore.lean)

## Key Insight

Evidence counts `(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` are the fundamental carrier,
while STV `(s, c) ∈ [0,1] × [0,1]` is a *view* into this space.

The mapping:
- `s = n⁺ / (n⁺ + n⁻)` (strength)
- `c = total / (total + κ)` (confidence, where κ is prior)

## Main Results

1. `evidenceToSTV`: Convert Evidence to bounded STV
2. `evidence_hplus_revision`: Evidence hplus = weighted averaging (revision)

## References

- PLNEvidence.lean: Evidence quantale with toStrength, toConfidence
- PLNMeTTaCore.lean: STV operations with soundness proofs
-/

namespace Mettapedia.Logic.PLNMeTTaCoreEvidence

open scoped ENNReal

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.PLNMeTTaCore
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLN

/-! ## Evidence to STV Conversion

Convert Evidence to bounded STV using clamp01 for safety. -/

/-- Convert Evidence to STV with a given prior κ.

    The strength is `n⁺ / (n⁺ + n⁻)` and confidence is `total / (total + κ)`.
    We use clamp01 to ensure bounds, which is the identity for valid evidence. -/
noncomputable def evidenceToSTV (κ : ℝ≥0∞) (e : Evidence) : STV :=
  let s := (Evidence.toStrength e).toReal
  let c := (Evidence.toConfidence κ e).toReal
  ⟨clamp01 s, clamp01 c,
   clamp01_nonneg s, clamp01_le_one s,
   clamp01_nonneg c, clamp01_le_one c⟩

/-- Evidence strength is non-negative as a real (follows from ENNReal.toReal_nonneg). -/
theorem evidence_strength_real_nonneg (e : Evidence) :
    0 ≤ (Evidence.toStrength e).toReal :=
  ENNReal.toReal_nonneg

/-- Evidence confidence is non-negative as a real. -/
theorem evidence_confidence_real_nonneg (κ : ℝ≥0∞) (e : Evidence) :
    0 ≤ (Evidence.toConfidence κ e).toReal :=
  ENNReal.toReal_nonneg

/-! ## Evidence hplus corresponds to Revision

The key theorem: combining evidence via hplus gives weighted averaging,
which is exactly what PLN revision does. -/

/-- Evidence hplus gives weighted average of strengths.
    This is the core revision property from PLNEvidence.lean. -/
theorem evidence_hplus_weighted_avg (e₁ e₂ : Evidence)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0) (h₁₂ : (e₁ + e₂).total ≠ 0)
    (h₁_top : e₁.total ≠ ⊤) (h₂_top : e₂.total ≠ ⊤) :
    Evidence.toStrength (e₁ + e₂) =
      (e₁.total / (e₁ + e₂).total) * Evidence.toStrength e₁ +
      (e₂.total / (e₁ + e₂).total) * Evidence.toStrength e₂ :=
  Evidence.toStrength_hplus e₁ e₂ h₁ h₂ h₁₂ h₁_top h₂_top

/-! ## Confidence increases with evidence -/

/-- Total evidence after hplus equals sum of totals. -/
theorem evidence_hplus_total (e₁ e₂ : Evidence) :
    (e₁ + e₂).total = e₁.total + e₂.total := by
  simp only [Evidence.hplus_def, Evidence.total]
  ring

/-! ## Tensor product for sequential composition -/

/-- Tensor is defined coordinatewise. -/
theorem evidence_tensor_def (e₁ e₂ : Evidence) :
    e₁ * e₂ = ⟨e₁.pos * e₂.pos, e₁.neg * e₂.neg⟩ :=
  Evidence.tensor_def e₁ e₂

/-- Tensor strength is at least the product of strengths.
    This shows sequential composition preserves evidence. -/
theorem evidence_tensor_strength_ge (e₁ e₂ : Evidence) :
    Evidence.toStrength (e₁ * e₂) ≥ Evidence.toStrength e₁ * Evidence.toStrength e₂ :=
  Evidence.toStrength_tensor_ge e₁ e₂

/-! ## Unit Evidence -/

/-- The tensor unit (1, 1) has strength 1/2. -/
theorem evidence_one_strength :
    Evidence.toStrength Evidence.one = 1 / 2 := by
  unfold Evidence.toStrength Evidence.total Evidence.one
  norm_num

/-- Zero evidence (0, 0) has strength 0 (by convention). -/
theorem evidence_zero_strength :
    Evidence.toStrength ⟨0, 0⟩ = 0 := by
  unfold Evidence.toStrength Evidence.total
  simp

/-! ## Summary

This module establishes the bridge between Evidence and STV:

### Key Results (All Proved, 0 Sorries)

1. **`evidenceToSTV`**: Convert Evidence to bounded STV
2. **`evidence_hplus_weighted_avg`**: hplus = weighted average (revision formula)
3. **`evidence_hplus_total`**: Total evidence is additive under hplus
4. **`evidence_tensor_strength_ge`**: Tensor preserves strength (lower bound)
5. **`evidence_one_strength`**: Unit evidence has strength 1/2
6. **`evidence_zero_strength`**: Zero evidence has strength 0

### Architecture

```
Evidence (ℝ≥0∞ × ℝ≥0∞)       [PLNEvidence.lean - quantale]
    │
    │ toStrength, toConfidence
    ↓
(ℝ≥0∞, ℝ≥0∞) raw values
    │
    │ toReal + clamp01
    ↓
STV (ℝ × ℝ with [0,1])      [PLNMeTTaCore.lean]
    │
    │ executeStep
    ↓
Correct PLN inference
```

The Evidence layer provides the algebraic foundation (quantale with hplus, tensor),
while the STV layer provides bounded operational semantics.
-/

end Mettapedia.Logic.PLNMeTTaCoreEvidence
