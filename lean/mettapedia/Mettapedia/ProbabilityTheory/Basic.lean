/-
# Probability Theory - Kolmogorov Foundations

Refactored to use mathlib's probability infrastructure.
We work with `Measure` and `ProbabilityMeasure` directly instead of bespoke
structures.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Real.Basic


noncomputable section

namespace Mettapedia.ProbabilityTheory
open MeasureTheory
open Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Probability of the empty event for any measure. -/
theorem prob_empty (μ : Measure Ω) : μ ∅ = 0 := by
  simp

variable (μ : Measure Ω)

/-- Probability is monotone with respect to set inclusion (valid for any measure). -/
theorem prob_mono {A B : Set Ω} (hAB : A ⊆ B) : μ A ≤ μ B :=
  measure_mono hAB

/-- Union bound (sub-additivity) for any events. -/
theorem prob_union_le {A B : Set Ω} :
    μ (A ∪ B) ≤ μ A + μ B :=
  measure_union_le A B

/-- Sum rule for disjoint events: P(A ∪ B) = P(A) + P(B).

This is the Knuth-Skilling "sum rule" derived from symmetry, and it matches
mathlib's `measure_union` for disjoint measurable sets. The sum rule is
the probability-theoretic foundation that emerges from the Cox consistency
axioms in our framework. -/
theorem sum_rule_eq_measure_union {A B : Set Ω}
    (_hA : MeasurableSet A) (hB : MeasurableSet B) (hDisj : Disjoint A B) :
    μ (A ∪ B) = μ A + μ B :=
  measure_union hDisj hB

variable [IsProbabilityMeasure μ]

/-- Probability of the complement of a measurable event. -/
theorem prob_compl {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  have h := measure_compl (μ := μ) hA
  simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using h

/-- Classical conditional probability (values in `ℝ`). -/
def condProb (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) : ℝ :=
  if _ : μ B = 0 then 0 else μ.real (A ∩ B) / μ.real B

/-- Helper: real-valued measure of a set is nonzero if the measure is nonzero. -/
lemma measureReal_ne_zero_of_measure_ne_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : μ A ≠ 0) : μ.real A ≠ 0 := by
  intro h
  have h' : μ A = 0 :=
    (measureReal_eq_zero_iff (μ := μ) (s := A)).1 h
  exact hA h'

/-- Product rule: `P(A ∩ B) = P(A | B) * P(B)` provided `P(B) ≠ 0`. -/
theorem product_rule {A B : Set Ω} (hB : μ B ≠ 0) :
    μ.real (A ∩ B) = condProb μ A B * μ.real B := by
  have hBreal : μ.real B ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hB
  calc
    μ.real (A ∩ B)
        = μ.real (A ∩ B) * (μ.real B / μ.real B) := by field_simp [hBreal]
    _ = (μ.real (A ∩ B) / μ.real B) * μ.real B := by ring
    _ = condProb μ A B * μ.real B := by simp [condProb, hB]

/-- Bayes' theorem in the two-event form. -/
theorem bayes {A B : Set Ω} (hA : μ A ≠ 0) (hB : μ B ≠ 0) :
    condProb μ A B = condProb μ B A * μ.real A / μ.real B := by
  have hAreal : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hA
  have hBreal : μ.real B ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hB
  calc
    condProb μ A B
        = μ.real (A ∩ B) / μ.real B := by simp [condProb, hB]
    _ = μ.real (A ∩ B) / μ.real A * μ.real A / μ.real B := by
          field_simp [hAreal, hBreal]
    _ = μ.real (B ∩ A) / μ.real A * μ.real A / μ.real B := by
          rw [inter_comm]
    _ = condProb μ B A * μ.real A / μ.real B := by
          simp [condProb, hA]

/-- Law of total probability for a binary partition, assuming both parts have positive measure. -/
theorem total_probability_binary {A B : Set Ω}
    (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBpos : μ B ≠ 0) (hBcomplPos : μ Bᶜ ≠ 0) :
    μ.real A = condProb μ A B * μ.real B + condProb μ A Bᶜ * μ.real Bᶜ := by
  have hdecomp :=
    measureReal_inter_add_diff₀ (μ := μ) (s := A) (t := B) hB.nullMeasurableSet
      (h := by finiteness)
  have hcompl : A \ B = A ∩ Bᶜ := by
    ext x; constructor <;> intro hx <;> exact ⟨hx.1, hx.2⟩
  have h1 := product_rule (μ := μ) (A := A) (B := B) hBpos
  have h2 := product_rule (μ := μ) (A := A) (B := Bᶜ) hBcomplPos
  calc
    μ.real A
        = μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) := by
            simpa [hcompl, add_comm] using hdecomp.symm
    _ = condProb μ A B * μ.real B + condProb μ A Bᶜ * μ.real Bᶜ := by
            simp [h1, h2]

/-! ## Bridge to Mathlib's Conditional Probability

Mathlib defines conditional probability via `ProbabilityTheory.cond`:
  `cond μ B` is the conditional measure given B
  `(cond μ B) A` = `μ (A ∩ B) / μ B` (in ENNReal)

Our `condProb μ A B` is the real-valued scalar version. We prove they match.
-/

/-- Our `condProb` matches mathlib's conditional probability.

This proves that our definition is definitionally equivalent to the standard
mathlib API from `Mathlib.Probability.ConditionalProbability`, establishing
that we're doing standard probability theory.

Mathlib's `ProbabilityTheory.cond_apply` gives: `μ[A|B] = (μ B)⁻¹ * μ (B ∩ A)`
Our `condProb μ A B` is: `μ.real (A ∩ B) / μ.real B`

These are equal after accounting for intersection commutativity and the
ENNReal ↔ Real conversion. -/
theorem condProb_eq_cond (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} (_hA : MeasurableSet A) (hB : MeasurableSet B) (hBpos : μ B ≠ 0) :
    condProb μ A B = ((ProbabilityTheory.cond μ B) A).toReal := by
  -- Both sides compute to μ(A ∩ B) / μ(B), just in different representations
  have hBfin : μ B ≠ ⊤ := measure_ne_top μ B
  -- Expand our definition
  simp only [condProb, hBpos, dite_false]
  -- Expand mathlib's cond using cond_apply: μ[A|B] = (μ B)⁻¹ * μ (B ∩ A)
  rw [ProbabilityTheory.cond_apply hB μ A]
  -- Now RHS is (μ B)⁻¹ * μ (B ∩ A), need to convert to division and swap intersection
  rw [Set.inter_comm B A]
  -- Convert ENNReal multiplication to division
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  -- Unfold μ.real to (μ _).toReal
  simp only [Measure.real]
  -- Now: (μ (A ∩ B)).toReal / (μ B).toReal = (μ B).toReal⁻¹ * (μ (A ∩ B)).toReal
  -- Division is multiplication by inverse, then commutativity
  rw [div_eq_mul_inv, mul_comm]

end Mettapedia.ProbabilityTheory
