/-
# NARS Induction/Abduction from Weakness Composition

This file derives the NARS induction/abduction confidence formulas from
reference class quality and weakness composition.

## The Key Insight

NARS formulas (Wang 2013):
- **Induction** (M → P, M → S ⊢ S → P): f = f₁, c = w2c(f₂ · c₁ · c₂)
- **Abduction** (M → P, S → M ⊢ S → P): f = f₂, c = w2c(f₁ · c₁ · c₂)

The frequency factor (f₁ or f₂) is the **reference class quality**: it measures
how well the intermediate term M covers the inference path.

## References

- Goertzel, "Weakness and Its Quantale"
- Wang, "Non-Axiomatic Logic" (2013)
-/

import Mathlib.Tactic
import Mettapedia.Logic.NARSMettaTruthFunctions
import Mettapedia.Logic.NARSEvidenceBridge
import Mettapedia.Logic.NARSSecondOrderProbability

namespace Mettapedia.Logic.NARSInductionWeakness

open Mettapedia.Logic.NARSMettaTruthFunctions
open Mettapedia.Logic.NARSEvidenceBridge
open Mettapedia.Logic.NARSSecondOrderProbability

/-! ## Reference Class Quality Interpretation

In weak inference (induction/abduction), the intermediate term M serves as a
"reference class" for the inference. The frequency of the M-premise measures
how well M covers the inference path.

For induction (M → P, M → S ⊢ S → P):
- M is the common source
- Quality of M for S→P is proportional to f₂ = P(S|M) from premise M → S

For abduction (M → P, S → M ⊢ S → P):
- M is the intermediate node
- Quality of M for S→P is proportional to f₁ = P(P|M) from premise M → P
-/

/-- The effective evidence weight in weak inference.

For induction/abduction: effective_w = quality × c₁ × c₂

This represents:
- c₁ × c₂: Base evidence from premise confidences (tensor composition)
- quality: Scaling by how good M is as a reference class -/
def effectiveEvidenceWeight (quality c1 c2 : ℝ) : ℝ := quality * c1 * c2

/-! ## Induction Confidence Derivation -/

/-- The NARS induction confidence formula arises from reference class quality.

For induction (M → P, M → S ⊢ S → P):
- Premise 1: M → P with TV (f₁, c₁)
- Premise 2: M → S with TV (f₂, c₂)
- Conclusion: S → P with confidence c = w2c(f₂ × c₁ × c₂)

The f₂ factor is the reference class quality: how much of M overlaps with S. -/
theorem induction_conf_formula (t1 t2 : TV) :
    (truthInduction t1 t2).c = w2c (t2.f * t1.c * t2.c) := by
  -- truthInduction t1 t2 = truthAbduction t2 t1
  -- truthAbduction t2 t1 = ⟨t1.f, w2c (t2.f * t2.c * t1.c)⟩
  simp only [truthInduction, truthAbduction]
  ring_nf

/-- Alternative form with the interpretation as effective evidence. -/
theorem induction_conf_from_effective_weight (t1 t2 : TV) :
    (truthInduction t1 t2).c = w2c (effectiveEvidenceWeight t2.f t1.c t2.c) := by
  simp only [effectiveEvidenceWeight]
  exact induction_conf_formula t1 t2

/-- The induction frequency comes from the first premise. -/
theorem induction_freq_formula (t1 t2 : TV) :
    (truthInduction t1 t2).f = t1.f := by
  simp only [truthInduction, truthAbduction]

/-! ## Abduction Confidence Derivation -/

/-- The NARS abduction confidence formula arises from reference class quality.

For abduction (M → P, S → M ⊢ S → P):
- Premise 1: M → P with TV (f₁, c₁)
- Premise 2: S → M with TV (f₂, c₂)
- Conclusion: S → P with confidence c = w2c(f₁ × c₁ × c₂)

The f₁ factor is the reference class quality: how much of M connects to P. -/
theorem abduction_conf_formula (t1 t2 : TV) :
    (truthAbduction t1 t2).c = w2c (t1.f * t1.c * t2.c) := by
  simp only [truthAbduction]

/-- Alternative form with the interpretation as effective evidence. -/
theorem abduction_conf_from_effective_weight (t1 t2 : TV) :
    (truthAbduction t1 t2).c = w2c (effectiveEvidenceWeight t1.f t1.c t2.c) := by
  simp only [effectiveEvidenceWeight]
  exact abduction_conf_formula t1 t2

/-- The abduction frequency comes from the second premise. -/
theorem abduction_freq_formula (t1 t2 : TV) :
    (truthAbduction t1 t2).f = t2.f := by
  simp only [truthAbduction]

/-! ## Symmetry Property -/

/-- Induction and abduction are related by swapping premises and
using the "complementary" reference class quality. -/
theorem induction_is_abduction_swapped (t1 t2 : TV) :
    truthInduction t1 t2 = truthAbduction t2 t1 := rfl

/-- The confidence factors swap: induction uses f₂, abduction uses f₁. -/
theorem conf_factor_swap (t1 t2 : TV) :
    -- Induction confidence uses f₂ (from second premise M → S)
    (truthInduction t1 t2).c = w2c (t2.f * t1.c * t2.c) ∧
    -- Abduction confidence uses f₁ (from first premise M → P)
    (truthAbduction t1 t2).c = w2c (t1.f * t1.c * t2.c) :=
  ⟨induction_conf_formula t1 t2, abduction_conf_formula t1 t2⟩

/-! ## Confidence Bounds (Weak Inference)

Weak inference confidence is bounded by 0.5 (with k=1).
This follows from the fact that the effective evidence weight is at most 1.
-/

/-- Effective evidence weight is bounded by 1 for valid inputs. -/
theorem effectiveEvidenceWeight_le_one (quality c1 c2 : ℝ)
    (hq0 : 0 ≤ quality) (hq1 : quality ≤ 1)
    (_hc1_0 : 0 ≤ c1) (hc1_1 : c1 ≤ 1)
    (hc2_0 : 0 ≤ c2) (hc2_1 : c2 ≤ 1) :
    effectiveEvidenceWeight quality c1 c2 ≤ 1 := by
  unfold effectiveEvidenceWeight
  have h1 : quality * c1 ≤ 1 := by nlinarith
  have h2 : quality * c1 * c2 ≤ 1 * c2 := mul_le_mul_of_nonneg_right h1 hc2_0
  calc quality * c1 * c2 ≤ c2 := by linarith
    _ ≤ 1 := hc2_1

/-- Induction confidence is bounded by 0.5 for valid truth values. -/
theorem induction_conf_le_half (t1 t2 : TV)
    (ht1 : IsProbTV t1) (ht2 : IsProbTV t2) :
    (truthInduction t1 t2).c ≤ 1 / 2 := by
  rw [induction_conf_formula]
  exact weak_inference_conf_bound t2.f t1.c t2.c
    ht2.f_nonneg ht2.f_le_one
    ht1.c_nonneg (le_of_lt ht1.c_lt_one)
    ht2.c_nonneg (le_of_lt ht2.c_lt_one)

/-- Abduction confidence is bounded by 0.5 for valid truth values. -/
theorem abduction_conf_le_half (t1 t2 : TV)
    (ht1 : IsProbTV t1) (ht2 : IsProbTV t2) :
    (truthAbduction t1 t2).c ≤ 1 / 2 := by
  rw [abduction_conf_formula]
  exact weak_inference_conf_bound t1.f t1.c t2.c
    ht1.f_nonneg ht1.f_le_one
    ht1.c_nonneg (le_of_lt ht1.c_lt_one)
    ht2.c_nonneg (le_of_lt ht2.c_lt_one)

/-! ## Summary: The Derivation Architecture

The NARS induction/abduction confidence formulas arise from:

1. **Evidence Quantale Foundation** (EvidenceQuantale.lean):
   - Evidence = (n⁺, n⁻) with tensor product for composition
   - Confidence c = total/(total + k) represents evidence weight

2. **Weight Transform** (NARSMettaTruthFunctions.lean):
   - c2w: c ↦ c/(1-c) converts confidence to weight
   - w2c: w ↦ w/(w+1) converts weight to confidence
   - Round-trip: w2c(c2w(c)) = c

3. **Reference Class Quality** (this file):
   - Intermediate term M serves as "reference class" for inference
   - Quality = frequency of the relevant premise (f₁ or f₂)
   - Higher quality → more of M participates in inference path

4. **Effective Evidence**:
   - effective_w = quality × c₁ × c₂
   - Combines tensor composition (c₁ × c₂) with reference class scaling

5. **Weak Inference Formula**:
   - c = w2c(effective_w) = quality × c₁ × c₂ / (quality × c₁ × c₂ + 1)
   - Bounded by 0.5 because effective_w ≤ 1
-/

end Mettapedia.Logic.NARSInductionWeakness
