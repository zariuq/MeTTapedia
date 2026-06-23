/-
# Reference Class Quality and Weakness Composition

Formalization of reference class quality from Goertzel's "Weakness and Its Quantale".

The key insight: NARS induction/abduction confidence formulas arise from
reference class quality and weakness composition via probabilistic OR.

## Core Definitions

- **Reference class quality**: Q(R → T) = μ(R ∩ T) / μ(T) = P(R|T)
- **Structural weakness**: w_struct(R → T) = 1 - Q(R → T) = P(¬R|T)
- **Probabilistic OR**: w₁ ⊕ w₂ = 1 - (1-w₁)(1-w₂)

## References

- Goertzel, "Weakness and Its Quantale"
- Wang, "Non-Axiomatic Logic" (2013)
-/

import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.Algebra.QuantaleWeakness

namespace Mettapedia.Algebra.ReferenceClassQuality

open scoped ENNReal
open Finset

open Mettapedia.Algebra.QuantaleWeakness

/-! ## Probabilistic OR

Weakness composes via probabilistic OR: w₁ ⊕ w₂ = 1 - (1-w₁)(1-w₂).
This is the "soft" version of Boolean OR that accumulates weakness
through inference chains.
-/

/-- Probabilistic OR: w₁ ⊕ w₂ = 1 - (1-w₁)(1-w₂)

This is the composition operator for weakness in inference chains.
When both weaknesses are small (close to 0), the result is approximately w₁ + w₂.
When either is 1, the result is 1 (total weakness). -/
noncomputable def probOr (w₁ w₂ : ℝ≥0∞) : ℝ≥0∞ :=
  1 - (1 - w₁) * (1 - w₂)

/-- Probabilistic OR is commutative. -/
theorem probOr_comm (w₁ w₂ : ℝ≥0∞) : probOr w₁ w₂ = probOr w₂ w₁ := by
  unfold probOr
  rw [mul_comm]

/-- Probabilistic OR has identity 0: probOr w 0 = w (for w ≤ 1). -/
theorem probOr_zero (w : ℝ≥0∞) (hw : w ≤ 1) : probOr w 0 = w := by
  unfold probOr
  simp only [tsub_zero, mul_one]
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hw]

/-- Probabilistic OR has absorbing element 1: probOr w 1 = 1. -/
theorem probOr_one (w : ℝ≥0∞) : probOr w 1 = 1 := by
  unfold probOr
  simp only [tsub_self, mul_zero, tsub_zero]

/-- Probabilistic OR is associative. -/
theorem probOr_assoc (w₁ w₂ w₃ : ℝ≥0∞) :
    probOr (probOr w₁ w₂) w₃ = probOr w₁ (probOr w₂ w₃) := by
  unfold probOr
  -- Both sides equal 1 - (1-w₁)(1-w₂)(1-w₃)
  congr 1
  by_cases hw₁ : w₁ ≤ 1
  · by_cases hw₂ : w₂ ≤ 1
    · by_cases hw₃ : w₃ ≤ 1
      · -- All bounded case
        have h12 : (1 - w₁) * (1 - w₂) ≤ 1 := by
          calc (1 - w₁) * (1 - w₂) ≤ 1 * 1 := mul_le_mul' tsub_le_self tsub_le_self
            _ = 1 := one_mul 1
        have h23 : (1 - w₂) * (1 - w₃) ≤ 1 := by
          calc (1 - w₂) * (1 - w₃) ≤ 1 * 1 := mul_le_mul' tsub_le_self tsub_le_self
            _ = 1 := one_mul 1
        rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top h12,
            ENNReal.sub_sub_cancel ENNReal.one_ne_top h23]
        ring
      · -- w₃ > 1: 1 - w₃ = 0
        have h3 : 1 - w₃ = 0 := tsub_eq_zero_of_le (not_le.mp hw₃).le
        simp [h3]
    · have h2 : 1 - w₂ = 0 := tsub_eq_zero_of_le (not_le.mp hw₂).le
      simp [h2]
  · have h1 : 1 - w₁ = 0 := tsub_eq_zero_of_le (not_le.mp hw₁).le
    simp [h1]

/-- probOr is bounded by 1 when inputs are bounded. -/
theorem probOr_le_one (w₁ w₂ : ℝ≥0∞) (_hw₁ : w₁ ≤ 1) (_hw₂ : w₂ ≤ 1) :
    probOr w₁ w₂ ≤ 1 := by
  unfold probOr
  exact tsub_le_self

/-! ## Reference Class Quality

Reference class quality measures how well a reference class R covers a target class T.
It is defined as Q(R → T) = μ(R ∩ T) / μ(T) = P(R|T).
-/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Reference class quality: Q(R → T) = μ(R ∩ T) / μ(T) = P(R|T)

This measures how well reference class R covers target T.
When μ(T) = 0, we define quality to be 0 (undefined case). -/
noncomputable def referenceClassQuality (pw : ProbWeight U) (R T : Finset U) : ℝ≥0∞ :=
  if ∑ u ∈ T, pw.μ u = 0 then 0
  else (∑ u ∈ R ∩ T, pw.μ u) / (∑ u ∈ T, pw.μ u)

/-- Structural weakness: w_struct(R → T) = 1 - Q(R → T) = P(¬R|T)

This is the complement of quality - the "coverage gap" of R over T. -/
noncomputable def structuralWeakness (pw : ProbWeight U) (R T : Finset U) : ℝ≥0∞ :=
  1 - referenceClassQuality pw R T

/-- Reference class quality is at most 1. -/
theorem referenceClassQuality_le_one (pw : ProbWeight U) (R T : Finset U) :
    referenceClassQuality pw R T ≤ 1 := by
  unfold referenceClassQuality
  split_ifs with h
  · exact zero_le
  · apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    apply Finset.sum_le_sum_of_subset
    exact inter_subset_right

/-- Structural weakness is at most 1. -/
theorem structuralWeakness_le_one (pw : ProbWeight U) (R T : Finset U) :
    structuralWeakness pw R T ≤ 1 := by
  unfold structuralWeakness
  exact tsub_le_self

/-- Quality of full universe is 1 (when target is non-empty). -/
theorem referenceClassQuality_univ (pw : ProbWeight U) (T : Finset U)
    (hT : ∑ u ∈ T, pw.μ u ≠ 0) :
    referenceClassQuality pw univ T = 1 := by
  unfold referenceClassQuality
  simp only [hT, ↓reduceIte, univ_inter]
  have hne_top : ∑ u ∈ T, pw.μ u ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑ u ∈ T, pw.μ u ≤ ∑ u : U, pw.μ u := by
           apply Finset.sum_le_sum_of_subset
           exact subset_univ T
      _ = 1 := pw.sum_one
  exact ENNReal.div_self hT hne_top

/-- Quality of empty reference class is 0. -/
theorem referenceClassQuality_empty (pw : ProbWeight U) (T : Finset U) :
    referenceClassQuality pw ∅ T = 0 := by
  unfold referenceClassQuality
  split_ifs
  · rfl
  · simp only [empty_inter, sum_empty, ENNReal.zero_div]

/-- Weakness of full universe is 0 (when target is non-empty). -/
theorem structuralWeakness_univ (pw : ProbWeight U) (T : Finset U)
    (hT : ∑ u ∈ T, pw.μ u ≠ 0) :
    structuralWeakness pw univ T = 0 := by
  unfold structuralWeakness
  rw [referenceClassQuality_univ pw T hT]
  simp

/-! ## Quality Monotonicity -/

/-- Quality is monotone in the reference class. -/
theorem referenceClassQuality_mono (pw : ProbWeight U) {R₁ R₂ T : Finset U}
    (h : R₁ ⊆ R₂) :
    referenceClassQuality pw R₁ T ≤ referenceClassQuality pw R₂ T := by
  unfold referenceClassQuality
  split_ifs with hT
  · exact le_refl 0
  · apply ENNReal.div_le_div_right
    apply Finset.sum_le_sum_of_subset
    exact inter_subset_inter_right h

/-- Weakness is antitone in the reference class. -/
theorem structuralWeakness_antimono (pw : ProbWeight U) {R₁ R₂ T : Finset U}
    (h : R₁ ⊆ R₂) :
    structuralWeakness pw R₂ T ≤ structuralWeakness pw R₁ T := by
  unfold structuralWeakness
  exact tsub_le_tsub_left (referenceClassQuality_mono pw h) 1

end Mettapedia.Algebra.ReferenceClassQuality
