import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN Negation: Evidence Swap

This file defines the **probabilistic negation** for PLN Evidence.

## Key Insight

The PLN negation is NOT the Heyting complement (a ⇨ ⊥). Instead, it swaps
the positive and negative evidence counts:

    ¬(n⁺, n⁻) = (n⁻, n⁺)

This gives the expected probabilistic behavior:
- `s(¬A) = 1 - s(A)` (strength inverts)
- `c(¬A) = c(A)` (confidence unchanged - same total evidence)

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 10
-/

namespace Mettapedia.Logic.PLNNegation

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Evidence

/-! ## PLN Negation Definition -/

/-- PLN probabilistic negation: swap positive and negative evidence.
    ¬(n⁺, n⁻) = (n⁻, n⁺) -/
def plnNeg (e : Evidence) : Evidence :=
  ⟨e.neg, e.pos⟩

/-- Notation for PLN negation -/
scoped prefix:max "∼" => plnNeg

/-! ## Basic Properties -/

/-- PLN negation is involutive (unlike Heyting complement) -/
@[simp]
theorem plnNeg_plnNeg (e : Evidence) : ∼(∼e) = e := by
  simp only [plnNeg]

/-- PLN negation preserves total evidence -/
theorem plnNeg_total (e : Evidence) : (∼e).total = e.total := by
  simp only [plnNeg, total, add_comm]

/-- PLN negation swaps pos and neg -/
@[simp]
theorem plnNeg_pos (e : Evidence) : (∼e).pos = e.neg := rfl

@[simp]
theorem plnNeg_neg (e : Evidence) : (∼e).neg = e.pos := rfl

/-! ## Strength Transformation -/

/-- Key result: Negation inverts strength.
    s(¬A) = n⁻/(n⁺+n⁻) and s(A) = n⁺/(n⁺+n⁻)
    So s(¬A) + s(A) = 1 when total ≠ 0 and total ≠ ⊤
-/
theorem plnNeg_strength_add (e : Evidence) (h : e.total ≠ 0) (hne_top : e.total ≠ ⊤) :
    toStrength (∼e) + toStrength e = 1 := by
  unfold toStrength
  have htot : (∼e).total = e.total := plnNeg_total e
  rw [htot]
  simp only [h, ↓reduceIte, plnNeg_pos]
  rw [← ENNReal.add_div, add_comm]
  exact ENNReal.div_self h hne_top

/-- Negation preserves confidence (same total evidence) -/
theorem plnNeg_confidence (kappa : ℝ≥0∞) (e : Evidence) :
    toConfidence kappa (∼e) = toConfidence kappa e := by
  unfold toConfidence
  rw [plnNeg_total]

/-! ## Negation and Tensor/Hplus -/

/-- Negation distributes over tensor (coordinatewise multiplication). -/
theorem plnNeg_tensor (a b : Evidence) : ∼(a * b) = ∼a * ∼b := by
  simp only [plnNeg, tensor_def, mul_comm a.neg b.neg, mul_comm a.pos b.pos]

/-- Negation distributes over hplus (coordinatewise addition). -/
theorem plnNeg_hplus (a b : Evidence) : ∼(a + b) = ∼a + ∼b := by
  simp only [plnNeg, hplus_def, add_comm a.neg b.neg, add_comm a.pos b.pos]

/-! ## Order Properties -/

/-- Negation relation to order -/
theorem plnNeg_le_plnNeg_iff (a b : Evidence) :
    ∼a ≤ ∼b ↔ a.neg ≤ b.neg ∧ a.pos ≤ b.pos := by
  simp only [le_def, plnNeg_pos, plnNeg_neg]

/-! ## Special Cases -/

/-- Negation of zero evidence -/
@[simp]
theorem plnNeg_zero : ∼(0 : Evidence) = 0 := by
  unfold plnNeg
  rfl

/-- Negation of unit evidence -/
@[simp]
theorem plnNeg_one : ∼one = one := by
  simp only [plnNeg, one]

/-- Negation of top -/
@[simp]
theorem plnNeg_top : ∼(⊤ : Evidence) = ⊤ := by
  unfold plnNeg
  rfl

/-! ## Negation as Bijection -/

/-- PLN negation is a bijection (self-inverse) -/
theorem plnNeg_bijective : Function.Bijective plnNeg := by
  constructor
  · intro a b hab
    have : ∼(∼a) = ∼(∼b) := by rw [hab]
    simp only [plnNeg_plnNeg] at this
    exact this
  · intro b
    use ∼b
    simp only [plnNeg_plnNeg]

/-! ## Relation to Heyting Complement -/

/-- PLN negation is NOT the same as Heyting complement.
    Example: ∼⟨1,2⟩ = ⟨2,1⟩ but compl ⟨1,2⟩ = ⟨0,0⟩ -/
theorem plnNeg_ne_compl_example : ∃ e : Evidence,
    ∼e ≠ Evidence.compl e := by
  use ⟨1, 2⟩
  intro heq
  -- ∼⟨1,2⟩ = ⟨2,1⟩, so (∼⟨1,2⟩).pos = 2
  -- compl ⟨1,2⟩ = himp ⟨1,2⟩ ⊥ = ⟨if 1≤0 then ⊤ else 0, if 2≤0 then ⊤ else 0⟩ = ⟨0,0⟩
  -- So if heq, then 2 = 0, contradiction
  have h1 : (∼(⟨1, 2⟩ : Evidence)).pos = 2 := rfl
  have h2 : (Evidence.compl (⟨1, 2⟩ : Evidence)).pos = 0 := by
    simp only [Evidence.compl, Evidence.himp, Bot.bot]
    have : ¬((1 : ℝ≥0∞) ≤ 0) := by
      push_neg
      exact zero_lt_one
    simp only [this, ↓reduceIte]
  rw [heq] at h1
  rw [h2] at h1
  exact absurd h1.symm (ne_of_gt (by norm_num : (0 : ℝ≥0∞) < 2))

end Mettapedia.Logic.PLNNegation
