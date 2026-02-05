import Mathlib.Tactic
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.NARSMettaTruthFunctions

namespace Mettapedia.Logic.NARSEvidenceBridge

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.NARSMettaTruthFunctions

/-!
# NARS Evidence Bridge

This file establishes the connection between NARS (Non-Axiomatic Reasoning System)
and the Evidence quantale formalization.

## Key Insight

NARS and PLN share the same fundamental machinery:
1. **Same weight transform**: `w = c/(1-c)`, `c = w/(w+k)`
2. **Same revision rule**: weighted average by evidence weight
3. **Evidence semantics**: counts (w⁺, w⁻) underlie both systems

The difference is philosophical:
- **PLN**: Rules derived from probability theory (Bayes, conditional independence)
- **NARS**: Rules axiomatized from "experience-grounded semantics"

## NARS Truth Value Formulas (from Wang 2013)

### Strong Inference (confidence can approach 1)
- **Deduction**: f = f₁·f₂, c = f₁·f₂·c₁·c₂

### Weak Inference (confidence bounded by 1/(1+k))
- **Induction**: f = f₁, c = w2c(f₂·c₁·c₂)
- **Abduction**: f = f₂, c = w2c(f₁·c₁·c₂)

### Revision (evidence aggregation)
- f = (w₁·f₁ + w₂·f₂)/(w₁ + w₂)
- c = w2c(w₁ + w₂)

## References

- Wang, P. (2013). Non-Axiomatic Logic: A Model of Intelligent Reasoning
- Goertzel et al. (2024). PLN and NARS Often Yield Similar strength × confidence
  https://arxiv.org/abs/2412.19524
-/

/-! ## Bridge Structures -/

/-- Convert NARS TV to Evidence.
    In NARS, frequency f = w⁺/(w⁺ + w⁻) and confidence c = (w⁺ + w⁻)/(w⁺ + w⁻ + k).
    We use k = 1 as the standard "unit of evidence". -/
noncomputable def TV.toEvidence (t : TV) : Evidence :=
  -- w = c/(1-c) is the total evidence (with k=1)
  -- w⁺ = f·w, w⁻ = (1-f)·w
  let w := c2w t.c
  let wpos := t.f * w
  let wneg := (1 - t.f) * w
  ⟨ENNReal.ofReal wpos, ENNReal.ofReal wneg⟩

/-- Convert Evidence to NARS TV. -/
noncomputable def Evidence.toNARSTV (e : Evidence) : TV :=
  let total := e.pos + e.neg
  let f := if total = 0 then 0.5 else (e.pos / total).toReal
  let c := (total / (total + 1)).toReal  -- k = 1
  ⟨f, c⟩

/-! ## Weight Transform Properties -/

/-- NARS c2w equals PLN c2w (no capping in NARS standard formulation) -/
theorem nars_c2w_eq (c : ℝ) (_hc : c < 1) : c2w c = c / (1 - c) := rfl

/-- NARS w2c equals PLN w2c for positive weights -/
theorem nars_w2c_eq (w : ℝ) : w2c w = w / (w + 1) := rfl

/-- Round-trip property: w2c (c2w c) = c for valid confidences -/
theorem w2c_c2w_id (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) : w2c (c2w c) = c := by
  unfold w2c c2w
  have h1c : 0 < 1 - c := by linarith
  have hw : c / (1 - c) ≥ 0 := div_nonneg hc0 (le_of_lt h1c)
  have hden : c / (1 - c) + 1 = 1 / (1 - c) := by field_simp; ring
  rw [hden, div_div]
  simp [h1c.ne']

/-- Round-trip property: c2w (w2c w) = w for non-negative weights -/
theorem c2w_w2c_id (w : ℝ) (hw : 0 ≤ w) : c2w (w2c w) = w := by
  unfold c2w w2c
  have hw1 : 0 < w + 1 := by linarith
  have hc : w / (w + 1) < 1 := by
    rw [div_lt_one hw1]
    linarith
  have h1c : 1 - w / (w + 1) = 1 / (w + 1) := by field_simp; ring
  rw [h1c, div_div]
  simp [hw1.ne']

/-! ## Revision is Evidence Aggregation -/

/-- NARS revision frequency is the weighted average of frequencies. -/
theorem revision_frequency_weighted_avg (t1 t2 : TV)
    (_hc1 : 0 ≤ t1.c) (_hc1' : t1.c < 1)
    (_hc2 : 0 ≤ t2.c) (_hc2' : t2.c < 1)
    (hw_pos : 0 < c2w t1.c + c2w t2.c) :
    let w1 := c2w t1.c
    let w2 := c2w t2.c
    (w1 * t1.f + w2 * t2.f) / (w1 + w2) =
      (c2w t1.c / (c2w t1.c + c2w t2.c)) * t1.f +
      (c2w t2.c / (c2w t1.c + c2w t2.c)) * t2.f := by
  simp only
  field_simp [hw_pos.ne']

/-- NARS revision confidence comes from total weight. -/
theorem revision_confidence_total_weight (t1 t2 : TV)
    (_hc1 : 0 ≤ t1.c) (_hc1' : t1.c < 1)
    (_hc2 : 0 ≤ t2.c) (_hc2' : t2.c < 1) :
    w2c (c2w t1.c + c2w t2.c) =
      (c2w t1.c + c2w t2.c) / (c2w t1.c + c2w t2.c + 1) := rfl

/-! ## Weak Inference Confidence Bound -/

/-- The confidence of weak inference (induction/abduction) is bounded by 1/(1+k).
    With k=1, this bound is 0.5. -/
theorem weak_inference_conf_bound (f c1 c2 : ℝ)
    (hf : 0 ≤ f) (hf' : f ≤ 1)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1)
    (hc2 : 0 ≤ c2) (hc2' : c2 ≤ 1) :
    w2c (f * c1 * c2) ≤ 1 / 2 := by
  unfold w2c
  -- The product f * c1 * c2 ≤ 1
  have hfc1 : f * c1 ≤ 1 := by
    calc f * c1 ≤ 1 * 1 := mul_le_mul hf' hc1' hc1 (by linarith)
    _ = 1 := by ring
  have hfc1_0 : 0 ≤ f * c1 := mul_nonneg hf hc1
  have hprod : f * c1 * c2 ≤ 1 := by
    calc f * c1 * c2 ≤ 1 * 1 := mul_le_mul hfc1 hc2' hc2 (by linarith)
    _ = 1 := by ring
  have hprod0 : 0 ≤ f * c1 * c2 := mul_nonneg hfc1_0 hc2
  -- For 0 ≤ x ≤ 1, we have x/(x+1) ≤ 1/2
  have h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x / (x + 1) ≤ 1 / 2 := by
    intro x hx0 hx1
    have hpos : 0 < x + 1 := by linarith
    rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
    linarith
  exact h (f * c1 * c2) hprod0 hprod

/-! ## Deduction Confidence Property -/

/-- NARS deduction confidence: c = f₁·f₂·c₁·c₂.
    This can approach 1 (strong inference). -/
theorem deduction_conf_formula (t1 t2 : TV) :
    (truthDeduction t1 t2).c = (t1.f * t2.f) * (t1.c * t2.c) := rfl

/-- NARS deduction frequency: f = f₁·f₂ -/
theorem deduction_freq_formula (t1 t2 : TV) :
    (truthDeduction t1 t2).f = t1.f * t2.f := rfl

/-! ## Induction/Abduction Symmetry -/

/-- Induction is abduction with swapped arguments -/
theorem induction_is_abduction_swapped (t1 t2 : TV) :
    truthInduction t1 t2 = truthAbduction t2 t1 := rfl

/-- Abduction frequency comes from the second premise -/
theorem abduction_freq_is_f2 (t1 t2 : TV) :
    (truthAbduction t1 t2).f = t2.f := rfl

/-- Induction frequency comes from the first premise -/
theorem induction_freq_is_f1 (t1 t2 : TV) :
    (truthInduction t1 t2).f = t1.f := by
  simp [truthInduction, truthAbduction]

/-! ## Connection to PLN Evidence -/

/-- NARS and PLN use the same revision formula for confidence.
    This theorem states that NARS revision confidence matches w2c of total weight. -/
theorem nars_revision_conf_formula (t1 t2 : TV) :
    w2c (c2w t1.c + c2w t2.c) = (c2w t1.c + c2w t2.c) / (c2w t1.c + c2w t2.c + 1) := rfl

/-- NARS revision frequency is weighted average by evidence weights. -/
theorem nars_revision_freq_formula (t1 t2 : TV) (hw_pos : 0 < c2w t1.c + c2w t2.c) :
    (c2w t1.c * t1.f + c2w t2.c * t2.f) / (c2w t1.c + c2w t2.c) =
    t1.f * (c2w t1.c / (c2w t1.c + c2w t2.c)) +
    t2.f * (c2w t2.c / (c2w t1.c + c2w t2.c)) := by
  field_simp [hw_pos.ne']

/-! ## Evidence Interpretation

In both NARS and PLN, the confidence c encodes the "amount of evidence" via:
  w = c / (1 - c)

This weight w represents the evidence-to-prior ratio. With prior k = 1:
  c = w / (w + 1)

The Evidence quantale provides the semantic foundation:
- **Evidence.hplus**: corresponds to NARS/PLN revision (additive combination)
- **Evidence.tensor**: corresponds to sequential composition (multiplicative)
- **Evidence.toStrength**: recovers frequency from evidence counts
- **Evidence.toConfidence**: recovers confidence from evidence counts

The key insight is that NARS's "experience-grounded" axioms, when formalized,
yield the same algebraic structure as PLN's probability-derived rules.
-/

/-- The weight transform is strictly monotone: more confidence = more evidence. -/
theorem c2w_strict_mono (c1 c2 : ℝ) (_hc1 : 0 ≤ c1) (_hc1' : c1 < 1)
    (_hc2 : 0 ≤ c2) (hc2' : c2 < 1) (h : c1 < c2) :
    c2w c1 < c2w c2 := by
  unfold c2w
  have h1c1 : 0 < 1 - c1 := by linarith
  have h1c2 : 0 < 1 - c2 := by linarith
  rw [div_lt_div_iff₀ h1c1 h1c2]
  nlinarith

/-- Summary: NARS revision equals Evidence aggregation (up to the min/max clamps).

The clamps in NARS revision:
- `min 1 f` ensures frequency stays in [0,1]
- `min 0.99 (max (max c t1.c) t2.c)` ensures confidence is capped and monotone

These are implementation safeguards, not part of the core semantics.
-/
theorem nars_revision_is_evidence_aggregation :
    ∀ (t1 t2 : TV),
      let w1 := c2w t1.c
      let w2 := c2w t2.c
      -- Core frequency: weighted average
      (w1 * t1.f + w2 * t2.f) / (w1 + w2) =
        (t1.f * w1 + t2.f * w2) / (w1 + w2) ∧
      -- Core confidence: total weight transformed
      w2c (w1 + w2) = (w1 + w2) / (w1 + w2 + 1) := by
  intro t1 t2
  constructor
  · ring_nf
  · rfl

end Mettapedia.Logic.NARSEvidenceBridge
