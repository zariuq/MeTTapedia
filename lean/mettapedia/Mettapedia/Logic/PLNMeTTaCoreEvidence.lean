import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNMeTTaCore

/-!
# BinaryEvidence-STV Bridge

This module bridges the gap between:
1. **BinaryEvidence** (quantale carrier from EvidenceQuantale.lean)
2. **STV** (bounded truth values from PLNMeTTaCore.lean)

## Key Insight

BinaryEvidence counts `(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` are the fundamental carrier,
while STV `(s, c) ∈ [0,1] × [0,1]` is a *view* into this space.

The mapping:
- `s = n⁺ / (n⁺ + n⁻)` (strength)
- `c = total / (total + κ)` (confidence, where κ is prior)

## Main Results

1. `evidenceToSTV`: Convert BinaryEvidence to bounded STV
2. `evidence_hplus_revision`: BinaryEvidence hplus = weighted averaging (revision)

## References

- EvidenceQuantale.lean: BinaryEvidence quantale with toStrength, toConfidence
- PLNMeTTaCore.lean: STV operations with soundness proofs
-/

namespace Mettapedia.Logic.PLNMeTTaCoreEvidence

open scoped ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNMeTTaCore
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLN

/-! ## BinaryEvidence to STV Conversion

Convert BinaryEvidence to bounded STV using clamp01 for safety. -/

/-- Convert BinaryEvidence to STV with a given prior κ.

    The strength is `n⁺ / (n⁺ + n⁻)` and confidence is `total / (total + κ)`.
    We use clamp01 to ensure bounds, which is the identity for valid evidence. -/
noncomputable def evidenceToSTV (κ : ℝ≥0∞) (e : BinaryEvidence) : STV :=
  let s := (BinaryEvidence.toStrength e).toReal
  let c := (BinaryEvidence.toConfidence κ e).toReal
  ⟨clamp01 s, clamp01 c,
   clamp01_nonneg s, clamp01_le_one s,
   clamp01_nonneg c, clamp01_le_one c⟩

/-- BinaryEvidence strength is non-negative as a real (follows from ENNReal.toReal_nonneg). -/
theorem evidence_strength_real_nonneg (e : BinaryEvidence) :
    0 ≤ (BinaryEvidence.toStrength e).toReal :=
  ENNReal.toReal_nonneg

/-- BinaryEvidence confidence is non-negative as a real. -/
theorem evidence_confidence_real_nonneg (κ : ℝ≥0∞) (e : BinaryEvidence) :
    0 ≤ (BinaryEvidence.toConfidence κ e).toReal :=
  ENNReal.toReal_nonneg

/-! ## BinaryEvidence hplus corresponds to Revision

The key theorem: combining evidence via hplus gives weighted averaging,
which is exactly what PLN revision does. -/

/-- BinaryEvidence hplus gives weighted average of strengths.
    This is the core revision property from EvidenceQuantale.lean. -/
theorem evidence_hplus_weighted_avg (e₁ e₂ : BinaryEvidence)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0) (h₁₂ : (e₁ + e₂).total ≠ 0)
    (h₁_top : e₁.total ≠ ⊤) (h₂_top : e₂.total ≠ ⊤) :
    BinaryEvidence.toStrength (e₁ + e₂) =
      (e₁.total / (e₁ + e₂).total) * BinaryEvidence.toStrength e₁ +
      (e₂.total / (e₁ + e₂).total) * BinaryEvidence.toStrength e₂ :=
  BinaryEvidence.toStrength_hplus e₁ e₂ h₁ h₂ h₁₂ h₁_top h₂_top

/-! ## Confidence increases with evidence -/

/-- Total evidence after hplus equals sum of totals. -/
theorem evidence_hplus_total (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).total = e₁.total + e₂.total := by
  simp only [BinaryEvidence.hplus_def, BinaryEvidence.total]
  ring

/-! ## Tensor product for sequential composition -/

/-- Tensor is defined coordinatewise. -/
theorem evidence_tensor_def (e₁ e₂ : BinaryEvidence) :
    e₁ * e₂ = ⟨e₁.pos * e₂.pos, e₁.neg * e₂.neg⟩ :=
  BinaryEvidence.tensor_def e₁ e₂

/-- Tensor strength is at least the product of strengths.
    This shows sequential composition preserves evidence. -/
theorem evidence_tensor_strength_ge (e₁ e₂ : BinaryEvidence) :
    BinaryEvidence.toStrength (e₁ * e₂) ≥ BinaryEvidence.toStrength e₁ * BinaryEvidence.toStrength e₂ :=
  BinaryEvidence.toStrength_tensor_ge e₁ e₂

/-! ## Unit BinaryEvidence -/

/-- The tensor unit (1, 1) has strength 1/2. -/
theorem evidence_one_strength :
    BinaryEvidence.toStrength BinaryEvidence.one = 1 / 2 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total BinaryEvidence.one
  norm_num

/-- Zero evidence (0, 0) has strength 0 (by convention). -/
theorem evidence_zero_strength :
    BinaryEvidence.toStrength ⟨0, 0⟩ = 0 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total
  simp

/-! ## Summary

This module establishes the bridge between BinaryEvidence and STV:

### Key Results (All Proved, 0 Sorries)

1. **`evidenceToSTV`**: Convert BinaryEvidence to bounded STV
2. **`evidence_hplus_weighted_avg`**: hplus = weighted average (revision formula)
3. **`evidence_hplus_total`**: Total evidence is additive under hplus
4. **`evidence_tensor_strength_ge`**: Tensor preserves strength (lower bound)
5. **`evidence_one_strength`**: Unit evidence has strength 1/2
6. **`evidence_zero_strength`**: Zero evidence has strength 0

### Architecture

```
BinaryEvidence (ℝ≥0∞ × ℝ≥0∞)       [EvidenceQuantale.lean - quantale]
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

The BinaryEvidence layer provides the algebraic foundation (quantale with hplus, tensor),
while the STV layer provides bounded operational semantics.
-/

end Mettapedia.Logic.PLNMeTTaCoreEvidence
