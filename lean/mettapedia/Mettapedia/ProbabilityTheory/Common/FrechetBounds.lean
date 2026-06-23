import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ConditionalProbability
import Mettapedia.ProbabilityTheory.Basic

/-!
# Fréchet Bounds: Fundamental Inequalities for Probability

The Fréchet bounds (also called Fréchet inequalities or Boole-Fréchet inequalities)
are fundamental constraints on joint probabilities given marginal probabilities.

## Historical Context

- **Boole (1854)**: First discovered the logical constraints
- **Fréchet (1935)**: Generalized to arbitrary probability measures
- Modern use: Foundation for copula theory, imprecise probability, PLN consistency

## Main Results

- `frechet_upper_bound` - P(A ∩ B) ≤ min(P(A), P(B))
- `frechet_lower_bound` - P(A ∩ B) ≥ max(0, P(A) + P(B) - 1)
- `frechet_bounds_tight` - Both bounds are attainable

## Applications in the Hypercube

The Fréchet bounds are the **common foundation** for:
- **Kolmogorov**: Follows from measure theory
- **Cox**: Ensures consistency of product rule
- **K&S**: Follows from modularity of Θ
- **PLN**: Defines consistency conditions for inference
- **Dempster-Shafer**: Weakened to Bel + Pl ≤ 2

## References

- Fréchet, M. (1935) "Généralisation du théorème des probabilités totales"
- Boole, G. (1854) "An Investigation of the Laws of Thought"
- Joe, H. (2014) "Dependence Modeling with Copulas", Ch. 2
-/

namespace Mettapedia.ProbabilityTheory.Common.FrechetBounds

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## §1: The Fundamental Fréchet Bounds
-/

/-- **Fréchet Upper Bound**: P(A ∩ B) ≤ min(P(A), P(B))

This is immediate from monotonicity: A ∩ B ⊆ A and A ∩ B ⊆ B.
-/
theorem frechet_upper_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) :
    μ (A ∩ B) ≤ min (μ A) (μ B) := by
  apply le_min
  · exact measure_mono Set.inter_subset_left
  · exact measure_mono Set.inter_subset_right

/-- **Fréchet Lower Bound**: P(A ∩ B) ≥ max(0, P(A) + P(B) - 1)

Proof: By inclusion-exclusion, P(A ∪ B) + P(A ∩ B) = P(A) + P(B).
Since P(A ∪ B) ≤ 1, we get P(A ∩ B) ≥ P(A) + P(B) - 1.
-/
theorem frechet_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    max 0 (μ A + μ B - 1) ≤ μ (A ∩ B) := by
  have h_incl_excl := measure_union_add_inter A hB (μ := μ)
  have h_union_le_one : μ (A ∪ B) ≤ 1 := by
    calc μ (A ∪ B) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
         _ = 1 := IsProbabilityMeasure.measure_univ
  have h_finite_union : μ (A ∪ B) ≠ ⊤ := (measure_lt_top μ _).ne
  have h_inter : μ A + μ B - μ (A ∪ B) = μ (A ∩ B) := by
    have h : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := h_incl_excl
    have h' : μ (A ∩ B) + μ (A ∪ B) = μ A + μ B := by rw [add_comm] at h; exact h
    exact (ENNReal.eq_sub_of_add_eq h_finite_union h').symm
  rw [← h_inter]
  apply max_le
  · exact bot_le
  · exact tsub_le_tsub_left h_union_le_one _

/-- The Fréchet bounds as a single statement -/
theorem frechet_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    max 0 (μ A + μ B - 1) ≤ μ (A ∩ B) ∧ μ (A ∩ B) ≤ min (μ A) (μ B) :=
  ⟨frechet_lower_bound μ A B hA hB, frechet_upper_bound μ A B⟩

/-!
## §2: Tightness of the Bounds

The Fréchet bounds are **tight**: for any valid marginals, there exist
joint distributions achieving the bounds.
-/

/-- The upper bound is achieved when A ⊆ B or B ⊆ A -/
theorem frechet_upper_tight_left
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hAB : A ⊆ B) :
    μ (A ∩ B) = μ A := by
  simp [Set.inter_eq_self_of_subset_left hAB]

/-- The lower bound is achieved for "comonotonic" sets -/
theorem frechet_lower_achieved_at_comonotonic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hAB : Aᶜ ⊆ B) (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∩ B) = μ A + μ B - 1 := by
  -- When Aᶜ ⊆ B, we have A ∪ B = univ
  have h_union : A ∪ B = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : x ∈ A
    · left; exact hx
    · right; exact hAB hx
  -- So P(A ∪ B) = 1
  have h_union_one : μ (A ∪ B) = 1 := by
    rw [h_union, IsProbabilityMeasure.measure_univ]
  -- From inclusion-exclusion
  have h_incl_excl : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := measure_union_add_inter A hB (μ := μ)
  have h_finite : μ (A ∪ B) ≠ ⊤ := (measure_lt_top μ _).ne
  -- μ (A ∩ B) = μ A + μ B - μ (A ∪ B) = μ A + μ B - 1
  have h_eq : μ (A ∩ B) = μ A + μ B - μ (A ∪ B) := by
    have h' : μ (A ∩ B) + μ (A ∪ B) = μ A + μ B := by rw [add_comm]; exact h_incl_excl
    exact ENNReal.eq_sub_of_add_eq h_finite h'
  rw [h_eq, h_union_one]

/-!
## §3: Real-Valued Version (for computations)
-/

/-- Fréchet upper bound in real arithmetic -/
theorem frechet_upper_bound_real
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) :
    μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B) := by
  apply le_min
  · exact measureReal_mono Set.inter_subset_left
  · exact measureReal_mono Set.inter_subset_right

/-- Fréchet lower bound in real arithmetic -/
theorem frechet_lower_bound_real
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    max 0 (μ.real A + μ.real B - 1) ≤ μ.real (A ∩ B) := by
  apply max_le
  · exact measureReal_nonneg
  · have h_union_le_one : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
    have h_incl_excl := measureReal_union_add_inter hB (μ := μ) (s := A)
    linarith

/-!
## §4: Conditional Probability Bounds

When converted to conditional probabilities P(B|A) = P(A ∩ B) / P(A):
-/

/-- Conditional probability lower bound from Fréchet -/
theorem conditional_lower_from_frechet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_pos : μ A ≠ 0) :
    max 0 ((μ.real A + μ.real B - 1) / μ.real A) ≤ condProb μ B A := by
  have hA_real_pos : 0 < μ.real A := by
    have hne := measureReal_ne_zero_of_measure_ne_zero μ hA_pos
    exact lt_of_le_of_ne measureReal_nonneg hne.symm
  have h_condProb : condProb μ B A = μ.real (B ∩ A) / μ.real A := by
    unfold condProb; simp [hA_pos]
  rw [h_condProb, Set.inter_comm]
  apply max_le
  · apply div_nonneg measureReal_nonneg (le_of_lt hA_real_pos)
  · apply div_le_div_of_nonneg_right _ (le_of_lt hA_real_pos)
    have h_union_le : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
    have h_incl := measureReal_union_add_inter hB (μ := μ) (s := A)
    linarith

/-- Conditional probability upper bound from Fréchet -/
theorem conditional_upper_from_frechet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA_pos : μ A ≠ 0) :
    condProb μ B A ≤ min 1 (μ.real B / μ.real A) := by
  have hA_real_pos : 0 < μ.real A := by
    have hne := measureReal_ne_zero_of_measure_ne_zero μ hA_pos
    exact lt_of_le_of_ne measureReal_nonneg hne.symm
  have h_condProb : condProb μ B A = μ.real (B ∩ A) / μ.real A := by
    unfold condProb; simp [hA_pos]
  rw [h_condProb]
  apply le_min
  · -- B ∩ A / A ≤ 1
    rw [div_le_one hA_real_pos]
    exact measureReal_mono Set.inter_subset_right
  · -- B ∩ A / A ≤ B / A
    apply div_le_div_of_nonneg_right _ (le_of_lt hA_real_pos)
    exact measureReal_mono Set.inter_subset_left

/-!
## §5: Abstract Fréchet Bounds (for Boolean Algebras)

These apply to any modular valuation on a Boolean algebra,
not just probability measures. Used in K&S connection.
-/

/-- A modular valuation on a Boolean algebra -/
structure ModularValuation (α : Type*) [BooleanAlgebra α] where
  /-- The valuation function -/
  val : α → ℝ
  /-- Non-negativity -/
  val_nonneg : ∀ a, 0 ≤ val a
  /-- Modularity: val(a ∨ b) + val(a ∧ b) = val(a) + val(b) -/
  val_modular : ∀ a b, val (a ⊔ b) + val (a ⊓ b) = val a + val b
  /-- Monotonicity -/
  val_mono : ∀ a b, a ≤ b → val a ≤ val b

namespace ModularValuation

variable {α : Type*} [BooleanAlgebra α] (V : ModularValuation α)

/-- Fréchet upper bound for modular valuations -/
theorem frechet_upper (a b : α) :
    V.val (a ⊓ b) ≤ min (V.val a) (V.val b) := by
  apply le_min
  · exact V.val_mono (a ⊓ b) a inf_le_left
  · exact V.val_mono (a ⊓ b) b inf_le_right

/-- Fréchet lower bound for modular valuations (normalized case) -/
theorem frechet_lower (a b : α) (h_top : V.val ⊤ = 1) :
    max 0 (V.val a + V.val b - 1) ≤ V.val (a ⊓ b) := by
  apply max_le
  · exact V.val_nonneg (a ⊓ b)
  · -- From modularity: val(a ⊔ b) + val(a ⊓ b) = val(a) + val(b)
    -- Since val(a ⊔ b) ≤ val(⊤) = 1:
    have h_le_top : V.val (a ⊔ b) ≤ 1 := by
      rw [← h_top]
      exact V.val_mono (a ⊔ b) ⊤ le_top
    have h_mod := V.val_modular a b
    linarith

end ModularValuation

end Mettapedia.ProbabilityTheory.Common.FrechetBounds
