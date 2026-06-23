import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds
import KnuthSkilling.Probability.BooleanRepresentation

/-!
# PLN Probability Bridge

This file proves that an event-level probability semantics satisfying the K&S
Boolean representation laws validates the exact PLN deduction formula.

This is a PLN bridge layer, not a proof-path module inside Knuth-Skilling.
-/

namespace Mettapedia.Logic.PLNProbabilityBridge

open Mettapedia.Logic.PLNDeduction
open KnuthSkilling.Probability.BooleanRepresentation

namespace KSBooleanRepresentation

variable {α : Type*} [BooleanAlgebra α] (R : KSBooleanRepresentation α)

/-- Conditional probability satisfies PLN consistency bounds. -/
theorem condProb_consistent (a b : α) (h : R.Θ ⊤ ≠ 0) (ha : R.probability a ≠ 0) :
    conditionalProbabilityConsistency (R.probability a) (R.probability b) (R.condProb b a) := by
  have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm ha)
  have hfrechet_lower := R.frechet_lower a b h
  have hfrechet_upper := R.frechet_upper a b
  constructor
  · exact ha_pos
  constructor
  · unfold smallestIntersectionProbability
    unfold KnuthSkilling.Probability.BooleanRepresentation.KSBooleanRepresentation.condProb
    simp only [ha, ↓reduceDIte]
    apply max_le
    · apply div_nonneg (R.probability_nonneg _) (le_of_lt ha_pos)
    · apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      exact le_trans (le_max_right 0 _) hfrechet_lower
  · unfold largestIntersectionProbability
    unfold KnuthSkilling.Probability.BooleanRepresentation.KSBooleanRepresentation.condProb
    simp only [ha, ↓reduceDIte]
    apply le_min
    · rw [div_le_one ha_pos]
      exact (le_min_iff.mp hfrechet_upper).1
    · apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
      exact (le_min_iff.mp hfrechet_upper).2

/-- Conditional probability is non-negative. -/
theorem condProb_nonneg (b a : α) : 0 ≤ R.condProb b a := by
  unfold KnuthSkilling.Probability.BooleanRepresentation.KSBooleanRepresentation.condProb
  split_ifs
  · exact le_refl 0
  · apply div_nonneg (R.probability_nonneg _) (R.probability_nonneg _)

/-- Conditional probability is at most `1`. -/
theorem condProb_le_one (b a : α) : R.condProb b a ≤ 1 := by
  unfold KnuthSkilling.Probability.BooleanRepresentation.KSBooleanRepresentation.condProb
  split_ifs with h
  · exact zero_le_one
  · have ha_pos : 0 < R.probability a := lt_of_le_of_ne (R.probability_nonneg a) (Ne.symm h)
    rw [div_le_one ha_pos]
    have hle := R.frechet_upper a b
    exact le_trans (le_min_iff.mp hle).1 (le_refl _)

/-- Conditional probability lies in `[0,1]`. -/
theorem condProb_mem_unit (b a : α) : R.condProb b a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨condProb_nonneg (R := R) b a, condProb_le_one (R := R) b a⟩

/-- A K&S Boolean representation validates the exact PLN deduction formula. -/
theorem ks_implies_pln_valid (a b c : α)
    (h : R.Θ ⊤ ≠ 0)
    (ha : R.probability a ≠ 0)
    (hb : R.probability b ≠ 0)
    (hb_small : R.probability b < 0.99) :
    simpleDeductionStrengthFormula
      (R.probability a) (R.probability b) (R.probability c)
      (R.condProb b a) (R.condProb c b) ∈ Set.Icc (0 : ℝ) 1 := by
  have h_consist_ab := condProb_consistent (R := R) a b h ha
  have h_consist_bc := condProb_consistent (R := R) b c h hb
  exact deduction_formula_in_unit_interval
    (R.probability a) (R.probability b) (R.probability c)
    (R.condProb b a) (R.condProb c b)
    (R.probability_mem_unit a) (R.probability_mem_unit b) (R.probability_mem_unit c)
    (condProb_mem_unit (R := R) b a)
    (condProb_mem_unit (R := R) c b)
    hb_small
    ⟨h_consist_ab, h_consist_bc⟩

end KSBooleanRepresentation

end Mettapedia.Logic.PLNProbabilityBridge
