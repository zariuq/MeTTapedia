import Mettapedia.Logic.EvidenceQuantale

/-!
# P-Bits: Goertzel's Paraconsistent Truth Values

This file establishes the connection between PLN's `BinaryEvidence` type and Goertzel's
**p-bits** (paraconsistent bits) from the paper "Paraconsistent Foundations for
Probabilistic Reasoning, Programming and Concept Learning" (arXiv:2012.14474).

## Key Insight

The existing `BinaryEvidence` type `(pos, neg : ℝ≥0∞)` IS already a p-bit structure.

## References

- Goertzel et al., "Paraconsistent Foundations for Probabilistic Reasoning..."
  (arXiv:2012.14474), Section 2
- Belnap, "How a Computer Should Think" (1977)
-/

namespace Mettapedia.Logic.PLNQuantaleSemantics.PBit

open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## P-Bit Corner Constants -/

/-- The "true" corner: pure positive evidence -/
def pTrue : BinaryEvidence := ⟨1, 0⟩

/-- The "false" corner: pure negative evidence -/
def pFalse : BinaryEvidence := ⟨0, 1⟩

/-- The "neither" corner: no evidence (complete ignorance) -/
def pNeither : BinaryEvidence := ⟨0, 0⟩

/-- The "both" corner: contradictory evidence -/
def pBoth : BinaryEvidence := ⟨1, 1⟩

/-! ## Classification Predicates -/

/-- BinaryEvidence is "true-ish": has positive support and no negative support -/
def isTrue (e : BinaryEvidence) : Prop := e.pos > 0 ∧ e.neg = 0

/-- BinaryEvidence is "false-ish": has negative support and no positive support -/
def isFalse (e : BinaryEvidence) : Prop := e.pos = 0 ∧ e.neg > 0

/-- BinaryEvidence is "neither": no support either way (complete ignorance) -/
def isNeither (e : BinaryEvidence) : Prop := e.pos = 0 ∧ e.neg = 0

/-- BinaryEvidence is "both": has support for AND against (contradiction) -/
def isBoth (e : BinaryEvidence) : Prop := e.pos > 0 ∧ e.neg > 0

/-! ## Basic Properties of Corners -/

theorem pTrue_isTrue : isTrue pTrue := ⟨zero_lt_one, rfl⟩

theorem pFalse_isFalse : isFalse pFalse := ⟨rfl, zero_lt_one⟩

theorem pNeither_isNeither : isNeither pNeither := ⟨rfl, rfl⟩

theorem pBoth_isBoth : isBoth pBoth := ⟨zero_lt_one, zero_lt_one⟩

/-! ## Mutual Exclusivity -/

/-- True and False are mutually exclusive -/
theorem isTrue_not_isFalse (e : BinaryEvidence) (h : isTrue e) : ¬isFalse e := by
  intro ⟨hpos, _⟩
  exact (ne_of_gt h.1) hpos

/-- True and Neither are mutually exclusive -/
theorem isTrue_not_isNeither (e : BinaryEvidence) (h : isTrue e) : ¬isNeither e := by
  intro ⟨hpos, _⟩
  exact (ne_of_gt h.1) hpos

/-- True and Both are mutually exclusive -/
theorem isTrue_not_isBoth (e : BinaryEvidence) (h : isTrue e) : ¬isBoth e := by
  intro ⟨_, hneg⟩
  exact (ne_of_gt hneg) h.2

/-- False and Neither are mutually exclusive -/
theorem isFalse_not_isNeither (e : BinaryEvidence) (h : isFalse e) : ¬isNeither e := by
  intro ⟨_, hneg⟩
  exact (ne_of_gt h.2) hneg

/-- False and Both are mutually exclusive -/
theorem isFalse_not_isBoth (e : BinaryEvidence) (h : isFalse e) : ¬isBoth e := by
  intro ⟨hpos, _⟩
  exact (ne_of_gt hpos) h.1

/-- Neither and Both are mutually exclusive -/
theorem isNeither_not_isBoth (e : BinaryEvidence) (h : isNeither e) : ¬isBoth e := by
  intro ⟨hpos, _⟩
  exact (ne_of_gt hpos) h.1

/-! ## Quadrant Classification -/

/-- Classification of evidence into quadrants -/
inductive Quadrant
  | true    -- pos > 0, neg = 0
  | false   -- pos = 0, neg > 0
  | neither -- pos = 0, neg = 0
  | both    -- pos > 0, neg > 0
  deriving DecidableEq, Inhabited

/-- Classify evidence into its quadrant -/
noncomputable def quadrant (e : BinaryEvidence) : Quadrant :=
  if e.pos = 0 then
    if e.neg = 0 then Quadrant.neither
    else Quadrant.false
  else
    if e.neg = 0 then Quadrant.true
    else Quadrant.both

theorem quadrant_true_iff (e : BinaryEvidence) :
    quadrant e = Quadrant.true ↔ isTrue e := by
  unfold quadrant isTrue
  constructor
  · intro h
    by_cases hp : e.pos = 0
    · simp only [hp, ite_true] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h; cases h
    · simp only [hp, ite_false] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h
        exact ⟨pos_iff_ne_zero.mpr hp, hn⟩
      · simp only [hn, ite_false] at h; cases h
  · intro ⟨hpos, hneg⟩
    have hp : e.pos ≠ 0 := pos_iff_ne_zero.mp hpos
    simp [hp, hneg]

theorem quadrant_false_iff (e : BinaryEvidence) :
    quadrant e = Quadrant.false ↔ isFalse e := by
  unfold quadrant isFalse
  constructor
  · intro h
    by_cases hp : e.pos = 0
    · simp only [hp, ite_true] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h
        exact ⟨hp, pos_iff_ne_zero.mpr hn⟩
    · simp only [hp, ite_false] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h; cases h
  · intro ⟨hpos, hneg⟩
    have hn : e.neg ≠ 0 := pos_iff_ne_zero.mp hneg
    simp [hpos, hn]

theorem quadrant_neither_iff (e : BinaryEvidence) :
    quadrant e = Quadrant.neither ↔ isNeither e := by
  unfold quadrant isNeither
  constructor
  · intro h
    by_cases hp : e.pos = 0
    · simp only [hp, ite_true] at h
      by_cases hn : e.neg = 0
      · exact ⟨hp, hn⟩
      · simp only [hn, ite_false] at h; cases h
    · simp only [hp, ite_false] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h; cases h
  · intro ⟨hpos, hneg⟩
    simp [hpos, hneg]

theorem quadrant_both_iff (e : BinaryEvidence) :
    quadrant e = Quadrant.both ↔ isBoth e := by
  unfold quadrant isBoth
  constructor
  · intro h
    by_cases hp : e.pos = 0
    · simp only [hp, ite_true] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h; cases h
    · simp only [hp, ite_false] at h
      by_cases hn : e.neg = 0
      · simp only [hn, ite_true] at h; cases h
      · simp only [hn, ite_false] at h
        exact ⟨pos_iff_ne_zero.mpr hp, pos_iff_ne_zero.mpr hn⟩
  · intro ⟨hpos, hneg⟩
    have hp : e.pos ≠ 0 := pos_iff_ne_zero.mp hpos
    have hn : e.neg ≠ 0 := pos_iff_ne_zero.mp hneg
    simp [hp, hn]

/-! ## Lattice Position of Corners -/

theorem pNeither_eq_bot : pNeither = ⊥ := rfl

/-- pTrue and pFalse are incomparable in the BinaryEvidence lattice -/
theorem pTrue_pFalse_incomparable : ¬(pTrue ≤ pFalse) ∧ ¬(pFalse ≤ pTrue) := by
  constructor
  · intro h
    have hp : pTrue.pos ≤ pFalse.pos := h.1
    simp only [pTrue, pFalse] at hp
    exact absurd hp (not_le.mpr zero_lt_one)
  · intro h
    have hn : pFalse.neg ≤ pTrue.neg := h.2
    simp only [pTrue, pFalse] at hn
    exact absurd hn (not_le.mpr zero_lt_one)

theorem pNeither_le_pTrue : pNeither ≤ pTrue := ⟨zero_le _, zero_le _⟩
theorem pNeither_le_pFalse : pNeither ≤ pFalse := ⟨zero_le _, zero_le _⟩
theorem pNeither_le_pBoth : pNeither ≤ pBoth := ⟨zero_le _, zero_le _⟩
theorem pTrue_le_pBoth : pTrue ≤ pBoth := ⟨le_refl _, zero_le _⟩
theorem pFalse_le_pBoth : pFalse ≤ pBoth := ⟨zero_le _, le_refl _⟩

/-! ## Heyting Algebra Properties -/

/-- Helper: ⊥ for BinaryEvidence is ⟨0, 0⟩ -/
theorem evidence_bot_def : (⊥ : BinaryEvidence) = ⟨0, 0⟩ := rfl

/-- BinaryEvidence is Heyting but NOT Boolean: ¬¬a ≠ a in general. -/
theorem evidence_not_boolean : ∃ a : BinaryEvidence, BinaryEvidence.compl (BinaryEvidence.compl a) ≠ a := by
  use pTrue
  intro h
  -- compl pTrue = himp pTrue ⊥ = himp ⟨1,0⟩ ⟨0,0⟩
  --            = ⟨if 1≤0 then ⊤ else 0, if 0≤0 then ⊤ else 0⟩ = ⟨0, ⊤⟩
  -- compl ⟨0, ⊤⟩ = himp ⟨0,⊤⟩ ⟨0,0⟩
  --            = ⟨if 0≤0 then ⊤ else 0, if ⊤≤0 then ⊤ else 0⟩ = ⟨⊤, 0⟩
  -- So compl (compl pTrue) = ⟨⊤, 0⟩
  -- But pTrue = ⟨1, 0⟩, so ⊤ ≠ 1 gives contradiction
  have h1 : ¬((1 : ℝ≥0∞) ≤ 0) := not_le.mpr zero_lt_one
  have h2 : ¬((⊤ : ℝ≥0∞) ≤ 0) := not_le.mpr ENNReal.zero_lt_top
  have h3 : (0 : ℝ≥0∞) ≤ 0 := le_refl 0
  -- Compute compl pTrue step by step
  have step1 : BinaryEvidence.compl pTrue = ⟨0, ⊤⟩ := by
    unfold BinaryEvidence.compl BinaryEvidence.himp pTrue
    simp only [evidence_bot_def, h1, ite_false, h3, ite_true]
  -- Compute compl of that
  have step2 : BinaryEvidence.compl ⟨0, ⊤⟩ = ⟨⊤, 0⟩ := by
    unfold BinaryEvidence.compl BinaryEvidence.himp
    simp only [evidence_bot_def, h3, ite_true, h2, ite_false]
  -- Now derive contradiction
  rw [step1, step2] at h
  -- h : ⟨⊤, 0⟩ = pTrue = ⟨1, 0⟩
  have hpos : (⊤ : ℝ≥0∞) = 1 := by
    have := congrArg BinaryEvidence.pos h
    simp only [pTrue] at this
    exact this
  exact ENNReal.top_ne_one hpos

/-! ## Strength at Corners -/

theorem pTrue_strength : BinaryEvidence.toStrength pTrue = 1 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total pTrue
  simp only [add_zero, one_ne_zero, ↓reduceIte]
  exact ENNReal.div_self one_ne_zero ENNReal.one_ne_top

theorem pFalse_strength : BinaryEvidence.toStrength pFalse = 0 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total pFalse
  simp only [zero_add, one_ne_zero, ↓reduceIte, ENNReal.zero_div]

theorem pNeither_strength : BinaryEvidence.toStrength pNeither = 0 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total pNeither
  simp only [add_zero, ↓reduceIte]

theorem pBoth_strength : BinaryEvidence.toStrength pBoth = 1/2 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total pBoth
  norm_num

/-! ## Summary

This file establishes:
1. The four p-bit corners: pTrue, pFalse, pNeither, pBoth
2. Classification predicates: isTrue, isFalse, isNeither, isBoth
3. Mutual exclusivity of quadrants
4. Lattice structure: Neither = ⊥, True/False incomparable
5. BinaryEvidence is Heyting but NOT Boolean
6. Strength values at corners

Key insight: The existing BinaryEvidence type IS Goertzel's p-bit structure.
-/

end Mettapedia.Logic.PLNQuantaleSemantics.PBit
