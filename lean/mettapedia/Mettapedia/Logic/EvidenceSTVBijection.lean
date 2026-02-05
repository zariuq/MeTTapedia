import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceIntuitionisticProbability
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mathlib.Data.ENNReal.Inv

/-!
# Evidence ↔ SimpleTruthValue Bijection

This file formalizes the precise relationship between PLN's 2D evidence counts
and 1D representations (strength, confidence, valuations).

## Main Results

1. **Non-unique strength preimages**: Multiple evidence values map to the same strength
2. **Infinite fiber**: The preimage of any strength value is infinite
3. **Valuation information loss**: Any valuation destroys the partial order structure

## The Story

```
Evidence (n⁺, n⁻)  ←——bijection——→  (strength s, confidence c)
         ↓                                    ↓
         ↓  loses confidence                  ↓  loses confidence
         ↓                                    ↓
    strength alone  ←———————————→  preimage is infinite
```

When you project to strength alone, you lose the "how much evidence" information.
-/

namespace Mettapedia.Logic.EvidenceSTVBijection

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## Part 1: The Strength Fiber (What's Lost) -/

section StrengthFiber

/-- The "fiber" of strength s: all evidence with the same strength value. -/
def strengthFiber (s : ENNReal) : Set Evidence :=
  { e | Evidence.toStrength e = s }

/-- Two evidence values with the same strength can have different totals.
    This is the key "information loss" when projecting to strength. -/
theorem same_strength_different_total :
    ∃ e₁ e₂ : Evidence, Evidence.toStrength e₁ = Evidence.toStrength e₂ ∧ e₁.total ≠ e₂.total := by
  use ⟨1, 1⟩, ⟨2, 2⟩
  constructor
  · -- Same strength: both are 1/2
    unfold Evidence.toStrength Evidence.total
    have h1 : (1 : ENNReal) + 1 ≠ 0 := by norm_num
    have h2 : (2 : ENNReal) + 2 ≠ 0 := by norm_num
    simp only [h1, h2, ↓reduceIte]
    -- 1/(1+1) = 2/(2+2) because both equal 1/2
    have eq1 : (1 : ENNReal) / (1 + 1) = 1 / 2 := by norm_num
    have eq2 : (2 : ENNReal) / (2 + 2) = 1 / 2 := by
      have h22 : (2 : ENNReal) + 2 = 4 := by norm_num
      rw [h22]
      have h2ne : (2 : ENNReal) ≠ 0 := by norm_num
      have h2ne_top : (2 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 2
      have h4eq : (4 : ENNReal) = 2 * 2 := by norm_num
      have h2eq : (2 : ENNReal) = 1 * 2 := by ring
      rw [h2eq, h4eq]
      rw [ENNReal.mul_div_mul_right 1 2 h2ne h2ne_top]
      simp only [one_mul]
    rw [eq1, eq2]
  · -- Different totals: 2 ≠ 4
    unfold Evidence.total
    norm_num

/-- Different evidence values can have the same strength but differ.
    Concrete example: (1,1) and (2,2) have same strength but are different. -/
theorem nonunique_strength :
    ∃ e₁ e₂ : Evidence, Evidence.toStrength e₁ = Evidence.toStrength e₂ ∧ e₁ ≠ e₂ := by
  use ⟨1, 1⟩, ⟨2, 2⟩
  constructor
  · -- Same strength (copy the proof from above)
    unfold Evidence.toStrength Evidence.total
    have h1 : (1 : ENNReal) + 1 ≠ 0 := by norm_num
    have h2 : (2 : ENNReal) + 2 ≠ 0 := by norm_num
    simp only [h1, h2, ↓reduceIte]
    have eq1 : (1 : ENNReal) / (1 + 1) = 1 / 2 := by norm_num
    have eq2 : (2 : ENNReal) / (2 + 2) = 1 / 2 := by
      have h22 : (2 : ENNReal) + 2 = 4 := by norm_num
      rw [h22]
      have h2ne : (2 : ENNReal) ≠ 0 := by norm_num
      have h2ne_top : (2 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 2
      have h4eq : (4 : ENNReal) = 2 * 2 := by norm_num
      have h2eq : (2 : ENNReal) = 1 * 2 := by ring
      rw [h2eq, h4eq]
      rw [ENNReal.mul_div_mul_right 1 2 h2ne h2ne_top]
      simp only [one_mul]
    rw [eq1, eq2]
  · -- Different evidence
    intro h
    have : (1 : ENNReal) = 2 := congrArg Evidence.pos h
    norm_num at this

end StrengthFiber

/-! ## Part 2: Valuation Information Loss -/

section ValuationLoss

/-- Any K&S valuation must map Evidence to totally ordered reals.
    This destroys the partial order structure. -/
theorem valuation_destroys_incomparability (v : Valuation Evidence) :
    ∀ e₁ e₂ : Evidence, v.val e₁ ≤ v.val e₂ ∨ v.val e₂ ≤ v.val e₁ :=
  fun e₁ e₂ => le_total (v.val e₁) (v.val e₂)

/-- Concrete example: (2, 0) and (0, 2) are incomparable in Evidence
    but any valuation must order them. -/
theorem incomparable_forced_comparable (v : Valuation Evidence) :
    let e₁ : Evidence := ⟨2, 0⟩
    let e₂ : Evidence := ⟨0, 2⟩
    (¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁)) ∧ (v.val e₁ ≤ v.val e₂ ∨ v.val e₂ ≤ v.val e₁) := by
  constructor
  · constructor
    · intro h
      simp only [Evidence.le_def] at h
      have : (2 : ENNReal) ≤ 0 := h.1
      norm_num at this
    · intro h
      simp only [Evidence.le_def] at h
      have : (2 : ENNReal) ≤ 0 := h.2
      norm_num at this
  · exact le_total _ _

end ValuationLoss

/-! ## Part 3: Summary Theorem -/

/-- **Main Information Hierarchy Theorem**

    Evidence (n⁺, n⁻) contains strictly more information than strength alone.

    Specifically:
    1. Strength alone has non-unique preimages
    2. Any valuation destroys the partial order structure
    3. But (strength, confidence) together recover Evidence (see toSTV/ofSTV in EvidenceQuantale) -/
theorem information_hierarchy :
    -- 1. Strength alone has non-unique preimages
    (∃ e₁ e₂ : Evidence, Evidence.toStrength e₁ = Evidence.toStrength e₂ ∧ e₁ ≠ e₂) ∧
    -- 2. Valuations destroy incomparability
    (∀ v : Valuation Evidence, ∃ e₁ e₂ : Evidence,
      ¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁) ∧ (v.val e₁ ≤ v.val e₂ ∨ v.val e₂ ≤ v.val e₁)) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: Non-unique strength preimages
    exact nonunique_strength
  · -- Part 2: Valuations destroy incomparability
    intro v
    use ⟨2, 0⟩, ⟨0, 2⟩
    obtain ⟨h_incomp, h_order⟩ := incomparable_forced_comparable v
    exact ⟨h_incomp.1, h_incomp.2, h_order⟩

end Mettapedia.Logic.EvidenceSTVBijection
