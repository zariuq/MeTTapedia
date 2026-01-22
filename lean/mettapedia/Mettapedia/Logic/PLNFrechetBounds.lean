import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ConditionalProbability
import Mettapedia.ProbabilityTheory.Basic
import Mettapedia.Logic.PLNDeduction

/-!
# Fréchet Bounds and PLN Consistency

This file **proves** that PLN's `conditionalProbabilityConsistency` definition
is **equivalent** to the Fréchet bounds from probability theory.

## Main Results

- `frechet_lower_bound` - Proves P(A ∩ B) ≥ max(0, P(A) + P(B) - 1)
- `frechet_upper_bound` - Proves P(A ∩ B) ≤ min(P(A), P(B))
- `frechet_bounds_iff_consistency` - Shows consistency ↔ Fréchet bounds

This establishes that PLN's consistency check is **not just a definition**,
but is **derived from fundamental probability theory** (Fréchet 1935).

## References

- Fréchet, M. (1935) "Généralisation du théorème des probabilités totales"
- Boole, G. (1854) "An Investigation of the Laws of Thought"
- [Fréchet inequalities - Wikipedia](https://en.wikipedia.org/wiki/Fréchet_inequalities)
- [UCLA Causality Blog on Fréchet Bounds](https://causality.cs.ucla.edu/blog/index.php/2019/11/05/frechet-inequalities/)
-/

namespace Mettapedia.Logic.PLNFrechetBounds

open MeasureTheory
open Mettapedia.ProbabilityTheory
open Mettapedia.Logic.PLNDeduction

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Fréchet Bounds for Intersection

These are the **fundamental bounds** from probability theory.
-/

/-- **Fréchet Upper Bound**: P(A ∩ B) ≤ min(P(A), P(B))

Proof: Since A ∩ B ⊆ A and A ∩ B ⊆ B, we have P(A ∩ B) ≤ P(A) and P(A ∩ B) ≤ P(B).
-/
theorem frechet_upper_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) :
    μ (A ∩ B) ≤ min (μ A) (μ B) := by
  apply le_min
  · -- P(A ∩ B) ≤ P(A)
    exact measure_mono (Set.inter_subset_left)
  · -- P(A ∩ B) ≤ P(B)
    exact measure_mono (Set.inter_subset_right)

/-- **Fréchet Lower Bound**: P(A ∩ B) ≥ max(0, P(A) + P(B) - 1)

Proof: By inclusion-exclusion (mathlib's `measure_union_add_inter`):
  P(A ∪ B) + P(A ∩ B) = P(A) + P(B)
Since P(A ∪ B) ≤ 1:
  P(A ∩ B) = P(A) + P(B) - P(A ∪ B) ≥ P(A) + P(B) - 1
And since probabilities are non-negative: P(A ∩ B) ≥ max(0, P(A) + P(B) - 1)
-/
theorem frechet_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    max 0 (μ A + μ B - 1) ≤ μ (A ∩ B) := by
  -- Use mathlib's inclusion-exclusion: μ (A ∪ B) + μ (A ∩ B) = μ A + μ B
  have h_incl_excl := measure_union_add_inter A hB (μ := μ)
  -- Rearrange: μ (A ∩ B) = μ A + μ B - μ (A ∪ B)
  -- Since μ (A ∪ B) ≤ 1 (probability measure), we get μ (A ∩ B) ≥ μ A + μ B - 1
  have h_union_le_one : μ (A ∪ B) ≤ 1 := by
    calc μ (A ∪ B) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
         _ = 1 := IsProbabilityMeasure.measure_univ
  -- From inclusion-exclusion: μ (A ∩ B) = μ A + μ B - μ (A ∪ B)
  have h_finite_union : μ (A ∪ B) ≠ ⊤ := (measure_lt_top μ _).ne
  -- h_incl_excl: μ (A ∪ B) + μ (A ∩ B) = μ A + μ B
  -- Rearranging: μ (A ∩ B) = μ A + μ B - μ (A ∪ B)
  have h_inter : μ A + μ B - μ (A ∪ B) = μ (A ∩ B) := by
    have h : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := h_incl_excl
    -- From h: μ (A ∪ B) + μ (A ∩ B) = μ A + μ B
    -- Rewrite as: μ (A ∩ B) + μ (A ∪ B) = μ A + μ B
    have h' : μ (A ∩ B) + μ (A ∪ B) = μ A + μ B := by rw [add_comm] at h; exact h
    -- Now apply: a + c = b → a = b - c with a := μ (A ∩ B), c := μ (A ∪ B), b := μ A + μ B
    have h_eq := ENNReal.eq_sub_of_add_eq h_finite_union h'
    exact h_eq.symm
  -- max(0, μA + μB - 1) ≤ μA + μB - μ(A∪B) = μ(A∩B)
  rw [← h_inter]
  apply max_le
  · -- 0 ≤ μ A + μ B - μ (A ∪ B)
    exact zero_le _
  · -- μ A + μ B - 1 ≤ μ A + μ B - μ (A ∪ B)
    -- This holds because μ (A ∪ B) ≤ 1
    exact tsub_le_tsub_left h_union_le_one _

/-! ## Converting to Conditional Probability

Now we convert the Fréchet bounds on P(A ∩ B) to bounds on P(B|A) = P(A ∩ B) / P(A).
-/

/-- Upper bound for conditional probability from Fréchet bound -/
theorem conditional_upper_bound_from_frechet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : μ A ≠ 0) :
    condProb μ B A ≤ min 1 (μ.real B / μ.real A) := by
  -- condProb μ B A = μ.real (B ∩ A) / μ.real A
  -- Setup positivity
  have hA_real_ne : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero μ hA
  have hA_real_nonneg : 0 ≤ μ.real A := measureReal_nonneg
  have hA_real_pos : 0 < μ.real A := lt_of_le_of_ne hA_real_nonneg hA_real_ne.symm
  -- Expand condProb
  have h_condProb : condProb μ B A = μ.real (B ∩ A) / μ.real A := by
    unfold condProb; simp [hA]
  rw [h_condProb]
  -- Fréchet upper bound gives: μ.real (B ∩ A) ≤ min (μ.real B) (μ.real A)
  have h1 : μ.real (B ∩ A) ≤ μ.real B := measureReal_mono (Set.inter_subset_left)
  have h2 : μ.real (B ∩ A) ≤ μ.real A := measureReal_mono (Set.inter_subset_right)
  -- Need: μ.real (B ∩ A) / μ.real A ≤ min 1 (μ.real B / μ.real A)
  apply le_min
  · -- μ.real (B ∩ A) / μ.real A ≤ 1
    rw [div_le_one hA_real_pos]
    exact h2
  · -- μ.real (B ∩ A) / μ.real A ≤ μ.real B / μ.real A
    apply div_le_div_of_nonneg_right h1 (le_of_lt hA_real_pos)

/-- Lower bound for conditional probability from Fréchet bound -/
theorem conditional_lower_bound_from_frechet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_pos : μ A ≠ 0) :
    max 0 ((μ.real A + μ.real B - 1) / μ.real A) ≤ condProb μ B A := by
  -- Setup positivity
  have hA_real_ne : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero μ hA_pos
  have hA_real_nonneg : 0 ≤ μ.real A := measureReal_nonneg
  have hA_real_pos : 0 < μ.real A := lt_of_le_of_ne hA_real_nonneg hA_real_ne.symm
  -- Expand condProb
  have h_condProb : condProb μ B A = μ.real (B ∩ A) / μ.real A := by
    unfold condProb; simp [hA_pos]
  rw [h_condProb, Set.inter_comm]
  -- Need: max 0 ((μ.real A + μ.real B - 1) / μ.real A) ≤ μ.real (A ∩ B) / μ.real A
  apply max_le
  · -- 0 ≤ μ.real (A ∩ B) / μ.real A
    apply div_nonneg measureReal_nonneg (le_of_lt hA_real_pos)
  · -- (μ.real A + μ.real B - 1) / μ.real A ≤ μ.real (A ∩ B) / μ.real A
    apply div_le_div_of_nonneg_right _ (le_of_lt hA_real_pos)
    -- Need: μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B)
    -- Use that μ.real (A ∪ B) ≤ 1 and inclusion-exclusion
    have h_union_le_one : μ.real (A ∪ B) ≤ 1 := by
      have h := measureReal_mono (μ := μ) (Set.subset_univ (A ∪ B))
      simp only [measureReal_univ_eq_one] at h
      exact h
    -- Use inclusion-exclusion in real form
    have h_incl_excl_real : μ.real A + μ.real B = μ.real (A ∪ B) + μ.real (A ∩ B) := by
      have h := measureReal_union_add_inter hB (μ := μ) (s := A)
      linarith
    -- From h_incl_excl_real: μ.real (A ∩ B) = μ.real A + μ.real B - μ.real (A ∪ B)
    linarith

/-! ## The Main Equivalence Theorem

This proves that PLN's `conditionalProbabilityConsistency` is **equivalent**
to the Fréchet bounds from probability theory.
-/

/-- **Main Theorem**: PLN consistency ↔ Fréchet bounds

This establishes that `conditionalProbabilityConsistency` is not just a definition,
but is **derived from fundamental probability axioms** (Fréchet 1935).

The theorem shows:
1. If you have a valid probability measure μ on events A, B
2. And sAB represents the conditional probability P(B|A)
3. Then sAB satisfies our consistency check
4. **If and only if** the underlying intersection P(A ∩ B) satisfies Fréchet bounds

This means PLN's consistency check is **sound** - it correctly enforces
the constraints that follow from probability theory.
-/
theorem frechet_bounds_iff_consistency
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (_hA : MeasurableSet A) (_hB : MeasurableSet B)
    (hA_pos : μ A ≠ 0) :
    -- PLN consistency holds
    conditionalProbabilityConsistency (μ.real A) (μ.real B) (condProb μ B A)
    ↔
    -- If and only if Fréchet bounds hold
    (max 0 (μ.real A + μ.real B - 1) ≤ μ.real (A ∩ B) ∧
     μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B)) := by
  -- Setup: μ.real A > 0 follows from hA_pos
  have hA_real_ne : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero μ hA_pos
  have hA_real_nonneg : 0 ≤ μ.real A := measureReal_nonneg
  have hA_real_pos : 0 < μ.real A := lt_of_le_of_ne hA_real_nonneg hA_real_ne.symm
  -- condProb μ B A = μ.real (B ∩ A) / μ.real A = μ.real (A ∩ B) / μ.real A
  have h_condProb : condProb μ B A = μ.real (A ∩ B) / μ.real A := by
    unfold condProb
    simp [hA_pos]
    rw [Set.inter_comm]
  constructor
  · -- Forward: consistency → Fréchet bounds
    intro h_consist
    unfold conditionalProbabilityConsistency at h_consist
    obtain ⟨_, h_lower, h_upper⟩ := h_consist
    unfold smallestIntersectionProbability at h_lower
    unfold largestIntersectionProbability at h_upper
    rw [h_condProb] at h_lower h_upper
    constructor
    · -- Lower bound: max 0 (μ.real A + μ.real B - 1) ≤ μ.real (A ∩ B)
      -- From: max 0 ((μ.real A + μ.real B - 1) / μ.real A) ≤ μ.real (A ∩ B) / μ.real A
      -- Multiply both sides by μ.real A > 0
      have h_div_ineq := h_lower
      -- max(0, x/a) * a = max(0, x) when a > 0
      rw [le_div_iff₀ hA_real_pos] at h_div_ineq
      rw [max_mul_of_nonneg _ _ (le_of_lt hA_real_pos)] at h_div_ineq
      simp only [zero_mul, div_mul_cancel₀ _ hA_real_ne] at h_div_ineq
      exact h_div_ineq
    · -- Upper bound: μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B)
      -- From: μ.real (A ∩ B) / μ.real A ≤ min 1 (μ.real B / μ.real A)
      -- Multiply both sides by μ.real A > 0
      have h_div_ineq := h_upper
      rw [div_le_iff₀ hA_real_pos] at h_div_ineq
      rw [min_mul_of_nonneg _ _ (le_of_lt hA_real_pos)] at h_div_ineq
      simp only [one_mul, div_mul_cancel₀ _ hA_real_ne] at h_div_ineq
      exact h_div_ineq
  · -- Backward: Fréchet bounds → consistency
    intro ⟨h_lower, h_upper⟩
    unfold conditionalProbabilityConsistency
    constructor
    · -- 0 < pA
      exact hA_real_pos
    constructor
    · -- smallestIntersectionProbability ≤ sAB
      unfold smallestIntersectionProbability
      rw [h_condProb]
      -- Need: max 0 ((μ.real A + μ.real B - 1) / μ.real A) ≤ μ.real (A ∩ B) / μ.real A
      -- From: max 0 (μ.real A + μ.real B - 1) ≤ μ.real (A ∩ B)
      -- Divide both sides by μ.real A > 0
      rw [le_div_iff₀ hA_real_pos]
      rw [max_mul_of_nonneg _ _ (le_of_lt hA_real_pos)]
      simp only [zero_mul, div_mul_cancel₀ _ hA_real_ne]
      exact h_lower
    · -- sAB ≤ largestIntersectionProbability
      unfold largestIntersectionProbability
      rw [h_condProb]
      -- Need: μ.real (A ∩ B) / μ.real A ≤ min 1 (μ.real B / μ.real A)
      -- From: μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B)
      -- Divide both sides by μ.real A > 0
      rw [div_le_iff₀ hA_real_pos]
      rw [min_mul_of_nonneg _ _ (le_of_lt hA_real_pos)]
      simp only [one_mul, div_mul_cancel₀ _ hA_real_ne]
      exact h_upper

/-! ## Consequences: Soundness of PLN

These corollaries show that PLN's consistency check is **sound** and **complete**.
-/

/-- Conditional probability is in [0,1] -/
lemma condProb_mem_Icc (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) :
    condProb μ A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condProb
  split_ifs with h
  · exact ⟨le_refl 0, zero_le_one⟩
  · constructor
    · apply div_nonneg measureReal_nonneg
      exact measureReal_nonneg
    · have hB_le : μ.real (A ∩ B) ≤ μ.real B := measureReal_mono Set.inter_subset_right
      have hB_pos : 0 < μ.real B := by
        have hne := measureReal_ne_zero_of_measure_ne_zero μ h
        exact lt_of_le_of_ne measureReal_nonneg hne.symm
      rw [div_le_one hB_pos]
      exact hB_le

/-- If inputs satisfy PLN consistency, the deduction formula is valid.

This uses `deduction_formula_in_unit_interval` from PLNDeduction, showing that
when applied to actual probability measures, the formula produces valid probabilities.
-/
theorem pln_consistency_implies_valid_probability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B C : Set Ω)
    (_hA : MeasurableSet A) (_hB : MeasurableSet B) (_hC : MeasurableSet C)
    (_hA_pos : μ A ≠ 0) (_hB_pos : μ B ≠ 0)
    (h_AB : conditionalProbabilityConsistency (μ.real A) (μ.real B) (condProb μ B A))
    (h_BC : conditionalProbabilityConsistency (μ.real B) (μ.real C) (condProb μ C B)) :
    -- Then the computed deduction result is a valid probability
    simpleDeductionStrengthFormula (μ.real A) (μ.real B) (μ.real C)
      (condProb μ B A) (condProb μ C B) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Get bounds on marginals (all probabilities are in [0,1])
  have hpA : μ.real A ∈ Set.Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hpB : μ.real B ∈ Set.Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hpC : μ.real C ∈ Set.Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  -- Get bounds on conditional probabilities
  have hsAB : condProb μ B A ∈ Set.Icc (0 : ℝ) 1 := condProb_mem_Icc μ B A
  have hsBC : condProb μ C B ∈ Set.Icc (0 : ℝ) 1 := condProb_mem_Icc μ C B
  -- Case split on whether pB < 0.99
  by_cases hpB_small : μ.real B < 0.99
  · -- Use the main theorem from PLNDeduction
    exact deduction_formula_in_unit_interval (μ.real A) (μ.real B) (μ.real C)
      (condProb μ B A) (condProb μ C B) hpA hpB hpC hsAB hsBC hpB_small ⟨h_AB, h_BC⟩
  · -- When pB ≥ 0.99, handle the boundary case
    unfold simpleDeductionStrengthFormula
    simp only [h_AB, h_BC, and_self]
    -- pB ≥ 0.99 means pB > 0.99 or pB = 0.99
    push_neg at hpB_small
    by_cases hpB_big : μ.real B > 0.99
    · simp only [hpB_big, ↓reduceIte]; exact hpC
    · -- pB ≤ 0.99 and pB ≥ 0.99, so pB = 0.99
      have h : μ.real B = 0.99 := le_antisymm (le_of_not_gt hpB_big) hpB_small
      simp only [hpB_big, ↓reduceIte]
      -- The formula is: sAB * sBC + (1 - sAB) * (pC - pB * sBC) / (1 - pB)
      -- With pB = 0.99, this is well-defined since 1 - 0.99 = 0.01 > 0
      have h_1mpB_pos : 0 < 1 - μ.real B := by rw [h]; norm_num
      have hpB_pos : 0 < μ.real B := by rw [h]; norm_num
      -- Get product bound from consistency
      have h_product : μ.real B * condProb μ C B ≤ μ.real C :=
        consistency_implies_product_bound (μ.real B) (μ.real C) (condProb μ C B)
          hpB_pos h_BC
      -- Get complement bound
      have h_complement : μ.real C - μ.real B * condProb μ C B ≤ 1 - μ.real B :=
        consistency_implies_complement_bound (μ.real B) (μ.real C) (condProb μ C B)
          ⟨hpB_pos, hpB.2⟩ hsBC h_BC
      -- term2 bounds
      have h_term2_bounds : 0 ≤ (μ.real C - μ.real B * condProb μ C B) / (1 - μ.real B) ∧
                            (μ.real C - μ.real B * condProb μ C B) / (1 - μ.real B) ≤ 1 := by
        constructor
        · apply div_nonneg; linarith [h_product]; linarith
        · rw [div_le_one h_1mpB_pos]; exact h_complement
      -- Apply convex combination
      have h_goal : condProb μ B A * condProb μ C B +
                    (1 - condProb μ B A) * (μ.real C - μ.real B * condProb μ C B) / (1 - μ.real B) =
                    condProb μ B A * condProb μ C B +
                    (1 - condProb μ B A) * ((μ.real C - μ.real B * condProb μ C B) / (1 - μ.real B)) := by
        ring
      rw [h_goal]
      exact convex_combination_bounded (condProb μ C B)
        ((μ.real C - μ.real B * condProb μ C B) / (1 - μ.real B))
        (condProb μ B A) hsBC h_term2_bounds hsAB

/-- PLN consistency check is necessary - if violated, no valid probability exists
    (for non-degenerate cases where pA > 0).

This shows consistency is not just sufficient but **necessary** - if it fails
and pA > 0, there's no way to construct a probability measure with those parameters.

Note: When pA = 0, the consistency check trivially fails (requires 0 < pA),
but a probability measure CAN exist with μ A = 0. The theorem handles this
edge case by requiring pA > 0 implicitly through the existential requiring
μ A ≠ 0 for the Fréchet equivalence to apply.
-/
theorem pln_consistency_necessary
    (pA pB sAB : ℝ)
    (hpA_pos : 0 < pA)  -- Need non-degenerate case
    (h_not_consist : ¬conditionalProbabilityConsistency pA pB sAB) :
    -- Then there exists NO probability measure with these marginals and conditional
    ¬∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
       (_ : IsProbabilityMeasure μ) (A B : Set Ω),
      MeasurableSet A ∧ MeasurableSet B ∧
      μ.real A = pA ∧ μ.real B = pB ∧
      condProb μ B A = sAB := by
  -- Suppose such a probability space exists
  intro ⟨Ω, _, μ, _, A, B, hA, hB, hpA, hpB, hsAB⟩
  -- Since pA > 0 and μ.real A = pA, we have μ A ≠ 0
  have hA_pos : μ A ≠ 0 := by
    intro h_zero
    have : μ.real A = 0 := by simp only [measureReal_def, h_zero, ENNReal.toReal_zero]
    rw [hpA] at this
    linarith
  -- Now we can apply frechet_bounds_iff_consistency
  have h_frechet := (frechet_bounds_iff_consistency μ A B hA hB hA_pos).mpr
  -- We have the Fréchet bounds hold for any probability measure
  have h_lower : max 0 (μ.real A + μ.real B - 1) ≤ μ.real (A ∩ B) := by
    apply max_le
    · exact measureReal_nonneg
    · have h_union_le : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
      have h_incl_excl := measureReal_union_add_inter hB (μ := μ) (s := A)
      linarith
  have h_upper : μ.real (A ∩ B) ≤ min (μ.real A) (μ.real B) := by
    apply le_min
    · exact measureReal_mono Set.inter_subset_left
    · exact measureReal_mono Set.inter_subset_right
  have h_consist := h_frechet ⟨h_lower, h_upper⟩
  -- h_consist : conditionalProbabilityConsistency (μ.real A) (μ.real B) (condProb μ B A)
  -- Substitute the given equalities
  rw [hpA, hpB, hsAB] at h_consist
  -- Now h_consist contradicts h_not_consist
  exact h_not_consist h_consist

end Mettapedia.Logic.PLNFrechetBounds
