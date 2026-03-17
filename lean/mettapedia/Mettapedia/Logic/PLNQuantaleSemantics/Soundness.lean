import Mettapedia.Logic.PLNQuantaleSemantics.PLNModel

/-!
# PLN Inference Rule Soundness

This file proves that PLN inference rules preserve truth value bounds
when expressed in terms of BinaryEvidence operations.

## Key Results

1. **Monotonicity**: BinaryEvidence ordering is preserved by inference operations
2. **Tensor transitivity**: Sequential composition is transitive
3. **Strength bounds**: Tensor composition gives lower bounds on strength

## Design Principle

We focus on algebraic soundness properties that can be proven from the
quantale structure of BinaryEvidence. The key insight is that PLN's deduction rule
corresponds to tensor composition, which has provable monotonicity properties.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- The existing `PLNDeduction.lean` for the strength formula
-/

namespace Mettapedia.Logic.PLNQuantaleSemantics.Soundness

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
open Mettapedia.Logic.PLNQuantaleSemantics.Model
open scoped ENNReal

/-! ## Monotonicity of Tensor -/

/-- Tensor is monotonic: if evidence increases, tensor product increases -/
theorem tensor_monotone_left (a b c : BinaryEvidence) (h : a ≤ b) :
    a ⊙ c ≤ b ⊙ c := by
  simp only [cdTensor, BinaryEvidence.le_def, BinaryEvidence.tensor_def]
  constructor
  · exact mul_le_mul' h.1 (le_refl c.pos)
  · exact mul_le_mul' h.2 (le_refl c.neg)

theorem tensor_monotone_right (a b c : BinaryEvidence) (h : b ≤ c) :
    a ⊙ b ≤ a ⊙ c := by
  rw [cdTensor_comm a b, cdTensor_comm a c]
  exact tensor_monotone_left b c a h

/-- Tensor is monotonic in both arguments -/
theorem tensor_monotone (a₁ a₂ b₁ b₂ : BinaryEvidence) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ ⊙ b₁ ≤ a₂ ⊙ b₂ :=
  le_trans (tensor_monotone_left a₁ a₂ b₁ ha) (tensor_monotone_right a₂ b₁ b₂ hb)

/-! ## Monotonicity of Par -/

/-- Par is monotonic: if evidence increases, par sum increases -/
theorem par_monotone_left (a b c : BinaryEvidence) (h : a ≤ b) :
    a ⅋ c ≤ b ⅋ c := by
  simp only [cdPar, BinaryEvidence.le_def, BinaryEvidence.hplus_def]
  constructor
  · exact add_le_add h.1 (le_refl c.pos)
  · exact add_le_add h.2 (le_refl c.neg)

theorem par_monotone_right (a b c : BinaryEvidence) (h : b ≤ c) :
    a ⅋ b ≤ a ⅋ c := by
  rw [cdPar_comm a b, cdPar_comm a c]
  exact par_monotone_left b c a h

/-- Par is monotonic in both arguments -/
theorem par_monotone (a₁ a₂ b₁ b₂ : BinaryEvidence) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ ⅋ b₁ ≤ a₂ ⅋ b₂ :=
  le_trans (par_monotone_left a₁ a₂ b₁ ha) (par_monotone_right a₂ b₁ b₂ hb)

/-! ## Transitivity of Tensor Composition

Tensor composition implements sequential evidence flow.
This corresponds to the "direct path" term in PLN deduction.
-/

/-- Tensor composition is transitive in the sense that composing
    identity elements gives the same result. -/
theorem tensor_one_left (e : BinaryEvidence) : BinaryEvidence.one ⊙ e = e := by
  unfold cdTensor
  exact BinaryEvidence.one_tensor e

theorem tensor_one_right (e : BinaryEvidence) : e ⊙ BinaryEvidence.one = e := by
  unfold cdTensor
  exact BinaryEvidence.tensor_one e

/-! ## Strength Lower Bounds

The key soundness property: tensor composition gives a lower bound on
the strength of the composed evidence.
-/

/-- The strength of a tensor product is at least the product of strengths.
    This is the mathematical foundation for PLN's deduction formula.

    Proof: Uses the existing `toStrength_tensor_ge` from EvidenceQuantale.
-/
theorem tensor_strength_ge (a b : BinaryEvidence) :
    BinaryEvidence.toStrength (a ⊙ b) ≥ BinaryEvidence.toStrength a * BinaryEvidence.toStrength b := by
  unfold cdTensor
  exact BinaryEvidence.toStrength_tensor_ge a b

/-! ## BinaryEvidence Preservation

These theorems show how evidence flows through inference operations.
-/

/-- Zero evidence tensored with anything gives zero evidence -/
theorem tensor_zero_left (e : BinaryEvidence) : BinaryEvidence.zero ⊙ e = BinaryEvidence.zero := by
  simp only [cdTensor, BinaryEvidence.tensor_def, BinaryEvidence.zero]
  ext
  · simp only [zero_mul]
  · simp only [zero_mul]

theorem tensor_zero_right (e : BinaryEvidence) : e ⊙ BinaryEvidence.zero = BinaryEvidence.zero := by
  rw [cdTensor_comm]
  exact tensor_zero_left e

/-- pTrue tensored with pTrue gives pTrue -/
theorem tensor_pTrue_pTrue : pTrue ⊙ pTrue = pTrue := by
  simp only [cdTensor, BinaryEvidence.tensor_def, pTrue]
  ext
  · simp only [mul_one]
  · simp only [mul_zero]

/-- pFalse tensored with pFalse gives pFalse -/
theorem tensor_pFalse_pFalse : pFalse ⊙ pFalse = pFalse := by
  simp only [cdTensor, BinaryEvidence.tensor_def, pFalse]
  ext
  · simp only [mul_zero]
  · simp only [mul_one]

/-- pNeither tensored with anything gives pNeither -/
theorem tensor_pNeither_left (e : BinaryEvidence) : pNeither ⊙ e = pNeither := by
  simp only [cdTensor, BinaryEvidence.tensor_def, pNeither]
  ext
  · simp only [zero_mul]
  · simp only [zero_mul]

theorem tensor_pNeither_right (e : BinaryEvidence) : e ⊙ pNeither = pNeither := by
  rw [cdTensor_comm]
  exact tensor_pNeither_left e

/-! ## Model-Level Soundness

Lifting evidence soundness to the model level.
-/

/-- Tensor composition of models preserves evidence ordering -/
theorem tensorCompose_monotone (M₁ M₂ N₁ N₂ : PLNModel α)
    (h₁ : ∀ p, M₁.evidence p ≤ M₂.evidence p)
    (h₂ : ∀ p, N₁.evidence p ≤ N₂.evidence p) :
    ∀ p, (tensorCompose M₁ N₁).evidence p ≤ (tensorCompose M₂ N₂).evidence p := by
  intro p
  exact tensor_monotone _ _ _ _ (h₁ p) (h₂ p)

/-- Par composition of models preserves evidence ordering -/
theorem parCompose_monotone (M₁ M₂ N₁ N₂ : PLNModel α)
    (h₁ : ∀ p, M₁.evidence p ≤ M₂.evidence p)
    (h₂ : ∀ p, N₁.evidence p ≤ N₂.evidence p) :
    ∀ p, (parCompose M₁ N₁).evidence p ≤ (parCompose M₂ N₂).evidence p := by
  intro p
  exact par_monotone _ _ _ _ (h₁ p) (h₂ p)

/-! ## CD Negation Algebraic Properties -/

/-- CD negation distributes over tensor -/
theorem cdNeg_tensor (a b : BinaryEvidence) : ∼(a ⊙ b) = (∼a) ⊙ (∼b) := by
  simp only [cdNeg, cdTensor, BinaryEvidence.tensor_def]

/-- CD negation distributes over par -/
theorem cdNeg_par (a b : BinaryEvidence) : ∼(a ⅋ b) = (∼a) ⅋ (∼b) := by
  simp only [cdNeg, cdPar, BinaryEvidence.hplus_def]

/-! ## Soundness of Corner Operations

These establish that the p-bit corners behave correctly under operations.
-/

/-- Negating pTrue gives pFalse -/
theorem cdNeg_pTrue_eq_pFalse : ∼pTrue = pFalse := cdNeg_pTrue

/-- Negating pFalse gives pTrue -/
theorem cdNeg_pFalse_eq_pTrue : ∼pFalse = pTrue := cdNeg_pFalse

/-- Negating pNeither gives pNeither -/
theorem cdNeg_pNeither_eq_pNeither : ∼pNeither = pNeither := cdNeg_pNeither

/-- Negating pBoth gives pBoth -/
theorem cdNeg_pBoth_eq_pBoth : ∼pBoth = pBoth := cdNeg_pBoth

/-! ## Strength at Corners (reexported for convenience) -/

/-- pTrue has strength 1 -/
theorem pTrue_has_strength_one : BinaryEvidence.toStrength pTrue = 1 := pTrue_strength

/-- pFalse has strength 0 -/
theorem pFalse_has_strength_zero : BinaryEvidence.toStrength pFalse = 0 := pFalse_strength

/-- pNeither has strength 0 (by convention, undefined case) -/
theorem pNeither_has_strength_zero : BinaryEvidence.toStrength pNeither = 0 := pNeither_strength

/-- pBoth has strength 1/2 (equal positive and negative evidence) -/
theorem pBoth_has_strength_half : BinaryEvidence.toStrength pBoth = 1/2 := pBoth_strength

/-! ## Summary

This file establishes:

1. **Monotonicity**: Tensor and par operations preserve evidence ordering

2. **Unit Laws**: BinaryEvidence.one is the tensor unit, BinaryEvidence.zero/pNeither absorbing

3. **Strength Bounds**: Tensor product strength ≥ product of strengths
   (the foundation of PLN deduction)

4. **Corner Preservation**: Operations on p-bit corners behave correctly

5. **CD Negation Distribution**: Negation distributes over tensor and par

6. **Model-Level Properties**: Lifting evidence soundness to PLNModel operations

These results provide the algebraic foundation for PLN inference soundness.
The actual deduction formula (with its approximation bounds) is handled
separately in PLNDeduction.lean.
-/

end Mettapedia.Logic.PLNQuantaleSemantics.Soundness
