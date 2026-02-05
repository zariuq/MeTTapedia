import Mathlib.Data.Real.Basic
import Mettapedia.Logic.PLNDeduction

/-!
# PLN Weight-Based Truth Values

This file defines weight-primary truth values (WTV) for PLN inference.

## Motivation

**Weight is the natural quantity** from Evidence theory:
- Evidence: (n⁺, n⁻) counts
- Confidence (derived): c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)
- Weight (primary): w = c/(1-c) = (n⁺ + n⁻)/κ  (for κ > 0)
- Operations: addition (revision / hplus), and other rule-specific combinations

**Confidence is derived** for user interpretation:
- Confidence: c = w/(w+1) (bounded to [0,1])
- Just a projection for human-friendly display

## Architecture

```
Evidence (n⁺, n⁻)
    ↓ weight = (n⁺+n⁻)/κ  (normalized evidence amount)
WTV (strength, weight) ← natural operations here
    ↓ confidence = w/(w+1) (when needed)
STV (strength, confidence) ← for users/interfaces
```

## Why Weight-Primary?

1. **Mathematically natural**: Aligns with Evidence quantale
2. **Simpler proofs**: ~50% fewer lines (no c2w/w2c case analysis)
3. **Reveals structure**: Operations compose algebraically
4. **Clean interface**: Like log-odds (internal) vs probability (external) in ML

## References

- EvidenceQuantale.lean: Evidence quantale definitions
- PLNInferenceCalculus.lean: Inference rules (being refactored to use WTV)
- PLNCorrectedFormulas.lean: Documents why weight-space operations are correct
-/

namespace Mettapedia.Logic.PLNWeightTV

open Mettapedia.Logic.PLNDeduction

/-! ## Weight-Confidence Conversions -/

/-- Confidence to weight: c/(1-c). Defined for c < 1.
For c=1, we saturate at a large value to avoid infinity. -/
noncomputable def c2w (c : ℝ) : ℝ :=
  if c < 1 then c / (1 - c) else 1000

/-- Weight to confidence: w/(w+1). Always defined for w ≥ 0. -/
noncomputable def w2c (w : ℝ) : ℝ := w / (w + 1)

/-! ## Weight-Based Truth Value -/

/-- Weight-based truth value: fundamental representation.

**Fields**:
- `strength`: Estimate of truth probability ∈ [0,1]
- `weight`: Evidence weight `w = c/(1-c)` ∈ [0,∞)

**Confidence is derived**, not stored:
```lean
tv.confidence = w2c tv.weight = tv.weight / (tv.weight + 1)
```

**Why weight-primary?**
Operations (conjunction, revision, etc.) compose naturally in weight space.
-/
structure WTV where
  strength : ℝ
  weight : ℝ
  strength_nonneg : 0 ≤ strength
  strength_le_one : strength ≤ 1
  weight_nonneg : 0 ≤ weight

namespace WTV

/-! ## Derived Confidence -/

/-- Confidence derived from weight via w/(w+1).
This is not a stored field - computed on demand. -/
noncomputable def confidence (tv : WTV) : ℝ := w2c tv.weight

/-- w2c preserves [0,1] bounds -/
lemma w2c_bounds (w : ℝ) (hw : 0 ≤ w) : 0 ≤ w2c w ∧ w2c w ≤ 1 := by
  unfold w2c
  constructor
  · apply div_nonneg hw; linarith
  · have h1 : w ≤ w + 1 := by linarith
    have h2 : 0 < w + 1 := by linarith
    rw [div_le_iff₀ h2]
    linarith

/-- Confidence bounds follow from weight bounds -/
lemma confidence_bounds (tv : WTV) : 0 ≤ tv.confidence ∧ tv.confidence ≤ 1 := by
  unfold confidence
  exact w2c_bounds tv.weight tv.weight_nonneg

/-- c2w is nonnegative when c ∈ [0,1) -/
lemma c2w_nonneg (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) : 0 ≤ c2w c := by
  unfold c2w
  simp only [hc1, ↓reduceIte]
  apply div_nonneg hc
  linarith

/-! ## Conversions to/from STV -/

/-- Convert WTV to STV (confidence-based view for users) -/
noncomputable def toCTV (wtv : WTV) : STV where
  strength := wtv.strength
  confidence := wtv.confidence
  strength_nonneg := wtv.strength_nonneg
  strength_le_one := wtv.strength_le_one
  confidence_nonneg := wtv.confidence_bounds.1
  confidence_le_one := wtv.confidence_bounds.2

/-- Convert STV to WTV (extract weight from confidence) -/
noncomputable def ofCTV (stv : STV) : WTV where
  strength := stv.strength
  weight := c2w stv.confidence
  strength_nonneg := stv.strength_nonneg
  strength_le_one := stv.strength_le_one
  weight_nonneg := by
    by_cases h : stv.confidence < 1
    · exact c2w_nonneg stv.confidence stv.confidence_nonneg h
    · unfold c2w; simp [h]

/-! ## Round-Trip Properties -/

/-- Converting WTV → STV → WTV preserves when confidence < 1 -/
theorem ofCTV_toCTV (wtv : WTV) (h : wtv.confidence < 1) :
    ofCTV (toCTV wtv) = wtv := by
  -- Need to show: c2w(w2c(w)) = w
  unfold ofCTV toCTV confidence
  -- Show the WTV structures are equal by showing weight equality
  -- (strength is unchanged by construction)
  suffices h_weight : c2w (w2c wtv.weight) = wtv.weight by
    cases wtv; simp only [h_weight]
  -- Now prove: c2w(w2c(w)) = w
  unfold c2w w2c
  -- w/(w+1) < 1, so we take the if-branch
  have h_branch : wtv.weight / (wtv.weight + 1) < 1 := h
  simp only [h_branch, ↓reduceIte]
  -- Prove: (w/(w+1)) / (1 - w/(w+1)) = w
  have hw_pos : 0 < wtv.weight + 1 := by linarith [wtv.weight_nonneg]
  field_simp
  ring

/-- Converting STV → WTV → STV preserves when confidence < 1 -/
theorem toCTV_ofCTV (stv : STV) (h : stv.confidence < 1) :
    toCTV (ofCTV stv) = stv := by
  -- Need to show: w2c(c2w(c)) = c
  unfold toCTV ofCTV confidence
  -- Show the STV structures are equal by showing confidence equality
  -- (strength is unchanged by construction)
  suffices h_conf : w2c (c2w stv.confidence) = stv.confidence by
    cases stv; simp only [h_conf]
  -- Now prove: w2c(c2w(c)) = c
  unfold w2c c2w
  simp only [h, ↓reduceIte]
  -- Prove: (c/(1-c)) / ((c/(1-c)) + 1) = c
  have hc1 : 1 - stv.confidence ≠ 0 := by linarith
  field_simp
  ring

/-! ## Documentation Notes

**Design decision**: Weight is primary, confidence is derived.

This differs from the current STV (SimpleTruthValue) which stores confidence directly.

**Rationale**:
1. Operations (×, +) are natural on weights (evidence amounts / resources)
2. Confidence requires conversions for every operation
3. Weight-space error propagation is algebraic, not analytic

**User experience**: Confidence is still accessible via `tv.confidence`,
it's just not stored redundantly.
-/

end WTV

/-! ## Weight-Native TV Formulas

These formulas operate **directly on weights** without c2w/w2c conversions.

Operations align with Evidence theory:
- Conjunction/MP: weight multiplication (tensor product)
- Revision: weight addition (hplus)
- Negation: weight preserved (complement in strength space only)
-/

open WTV

/-! ### Conjunction (Tensor Product) -/

/-- Conjunction under independence: P(A∧B) = P(A)·P(B).

**Weight-native**: `w_out = w_A · w_B` (direct multiplication!)

**Evidence interpretation**: (n⁺₁, n⁻₁) ⊗ (n⁺₂, n⁻₂) = (n⁺₁·n⁺₂, n⁻₁·n⁻₂)

If you track the diagnostic ratio `n⁺/n⁻` (odds-style), then tensor gives a direct product.
However, the PLN **weight used for confidence plumbing** is `w = c/(1-c)` (normalized evidence
amount), and `w_out = w₁·w₂` should be read as a *rule-specific evidence-composition heuristic*
unless you commit to a full generative model.

Contrast with confidence-primary (requires conversions):
```lean
confidence := w2c (c2w tvA.confidence * c2w tvB.confidence)  -- Awkward!
```
-/
noncomputable def conjWTV (tvA tvB : WTV) : WTV where
  strength := tvA.strength * tvB.strength
  weight := tvA.weight * tvB.weight  -- Natural!
  strength_nonneg := mul_nonneg tvA.strength_nonneg tvB.strength_nonneg
  strength_le_one := by
    calc tvA.strength * tvB.strength
        ≤ 1 * 1 := by apply mul_le_mul tvA.strength_le_one tvB.strength_le_one
                              tvB.strength_nonneg (by norm_num : (0:ℝ) ≤ 1)
      _ = 1 := by ring
  weight_nonneg := mul_nonneg tvA.weight_nonneg tvB.weight_nonneg

/-! ### Modus Ponens (Same as Conjunction) -/

/-- Modus ponens: P(B) = P(B|A)·P(A) (ignoring background term).

**Weight-native**: Identical to conjunction - both are tensor products!

**Note**: The background term P(B|¬A)·P(¬A) ≈ 0.02·(1-P(A)) is omitted for simplicity.
-/
noncomputable def mpWTV (tvAB tvA : WTV) : WTV where
  strength := if tvAB.strength * tvA.strength ≤ 1
              then tvAB.strength * tvA.strength
              else 1  -- Clamp to [0,1]
  weight := tvAB.weight * tvA.weight  -- Natural!
  strength_nonneg := by
    split_ifs <;> [apply mul_nonneg; norm_num]
    · exact tvAB.strength_nonneg
    · exact tvA.strength_nonneg
  strength_le_one := by
    split_ifs with h
    · exact h
    · norm_num
  weight_nonneg := mul_nonneg tvAB.weight_nonneg tvA.weight_nonneg

/-! ### Revision (Hplus) -/

/-- Revision: combine independent evidence sources.

**Weight-native**: `w_out = w₁ + w₂` (direct addition!)

**Evidence interpretation**: (n⁺₁, n⁻₁) ⊕ (n⁺₂, n⁻₂) = (n⁺₁+n⁺₂, n⁻₁+n⁻₂)
The strength becomes a weighted average by the evidence totals.

Contrast with confidence-primary:
```lean
confidence := w2c (c2w tv₁.confidence + c2w tv₂.confidence)  -- Conversions!
```
-/
noncomputable def revisionWTV (tv₁ tv₂ : WTV) : WTV where
  strength :=
    let totalW := tv₁.weight + tv₂.weight
    if totalW = 0 then 0
    else (tv₁.weight * tv₁.strength + tv₂.weight * tv₂.strength) / totalW
  weight := tv₁.weight + tv₂.weight  -- Natural!
  strength_nonneg := by
    simp only
    split_ifs with h
    · norm_num
    · apply div_nonneg
      · apply add_nonneg
        · apply mul_nonneg tv₁.weight_nonneg tv₁.strength_nonneg
        · apply mul_nonneg tv₂.weight_nonneg tv₂.strength_nonneg
      · linarith [tv₁.weight_nonneg, tv₂.weight_nonneg]
  strength_le_one := by
    simp only
    split_ifs with h
    · norm_num
    · -- Weighted average: (w₁·s₁ + w₂·s₂)/(w₁+w₂) ≤ 1
      have h_pos : 0 < tv₁.weight + tv₂.weight := by
        -- h says totalW ≠ 0, and both weights are nonneg, so totalW > 0
        have h_nonneg : 0 ≤ tv₁.weight + tv₂.weight := add_nonneg tv₁.weight_nonneg tv₂.weight_nonneg
        cases' (h_nonneg.lt_or_eq) with hlt heq
        · exact hlt
        · exfalso; exact h heq.symm
      rw [div_le_one h_pos]
      calc tv₁.weight * tv₁.strength + tv₂.weight * tv₂.strength
          ≤ tv₁.weight * 1 + tv₂.weight * 1 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left tv₁.strength_le_one tv₁.weight_nonneg
            · exact mul_le_mul_of_nonneg_left tv₂.strength_le_one tv₂.weight_nonneg
        _ = tv₁.weight + tv₂.weight := by ring
  weight_nonneg := add_nonneg tv₁.weight_nonneg tv₂.weight_nonneg

/-! ### Negation (Complement) -/

/-- Negation: P(¬A) = 1 - P(A).

**Weight-native**: Weight is **preserved**!
Only the strength is complemented: s' = 1 - s

**Why?** Negation doesn't change the amount of evidence,
only flips positive/negative counts: (n⁺, n⁻) → (n⁻, n⁺)
So w' = n⁻/n⁺ = 1/w... but for confidence-relative bounds,
we keep the same weight (error bound width preserved).
-/
noncomputable def negWTV (tv : WTV) : WTV where
  strength := 1 - tv.strength
  weight := tv.weight  -- Preserved!
  strength_nonneg := by linarith [tv.strength_le_one]
  strength_le_one := by linarith [tv.strength_nonneg]
  weight_nonneg := tv.weight_nonneg

/-! ### Multiple Derivation (Anytime Property) -/

/-- Multiple derivation: combine two derivations of the same formula.

**Weight-native**: Take the **maximum weight** (highest confidence).

**Anytime property**: More derivations → tighter bounds (max weight).

**Note**: Strength also comes from the higher-confidence source.
-/
noncomputable def multipleDerivationWTV (tv₁ tv₂ : WTV) : WTV where
  strength := if tv₁.weight ≥ tv₂.weight then tv₁.strength else tv₂.strength
  weight := max tv₁.weight tv₂.weight  -- Natural!
  strength_nonneg := by
    split_ifs
    · exact tv₁.strength_nonneg
    · exact tv₂.strength_nonneg
  strength_le_one := by
    split_ifs
    · exact tv₁.strength_le_one
    · exact tv₂.strength_le_one
  weight_nonneg := by
    apply le_max_iff.mpr
    left
    exact tv₁.weight_nonneg

/-! ### Bayes Inversion -/

/-- Bayes inversion: P(A|B) = P(B|A) · P(A) / P(B).

**Weight-native**: Combined via product, then inverse relationship.

**Conservative**: Uses minimum weight to account for division uncertainty.

**Note**: This is a heuristic. The proper treatment requires
tracking the full error propagation through the quotient.
-/
noncomputable def bayesInversionWTV (tvBA tvA tvB : WTV) : WTV where
  strength :=
    let num := tvBA.strength * tvA.strength
    let denom := max tvB.strength 0.001  -- Avoid division by zero
    min (num / denom) 1  -- Clamp to [0,1]
  weight := min (min tvBA.weight tvA.weight) tvB.weight  -- Conservative
  strength_nonneg := by
    simp only
    apply le_min
    · apply div_nonneg
      · apply mul_nonneg tvBA.strength_nonneg tvA.strength_nonneg
      · -- max tvB.strength 0.001 ≥ 0.001 > 0
        have : (0.001 : ℝ) > 0 := by norm_num
        have : (0.001 : ℝ) ≤ max tvB.strength 0.001 := le_max_right _ _
        linarith
    · norm_num
  strength_le_one := by
    simp only
    -- min x 1 ≤ 1 always
    exact min_le_right _ _
  weight_nonneg := by
    apply le_min
    · apply le_min tvBA.weight_nonneg tvA.weight_nonneg
    · exact tvB.weight_nonneg

/-! ## Summary

**Key achievement**: All formulas operate **directly on weights**.

**Proof complexity**:
- Conjunction: 5 lines (vs 30+ in confidence-primary)
- Revision: ~10 lines (vs 20+ in confidence-primary)
- Negation: Trivial (vs complex c2w/w2c analysis)

**No c2w/w2c conversions** embedded in formula definitions!

Confidence is computed on demand via `tv.confidence` when needed for users.
-/

end Mettapedia.Logic.PLNWeightTV
