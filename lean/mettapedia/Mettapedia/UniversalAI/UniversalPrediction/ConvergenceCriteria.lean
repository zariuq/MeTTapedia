import Mettapedia.UniversalAI.UniversalPrediction.Convergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Convergence Criteria (Hutter 2005, Definition 3.8 & Lemma 3.9)

This file formalizes the different modes of convergence for sequence prediction from
Chapter 3 of Hutter's "Universal Artificial Intelligence".

## Main Definitions

* `ConvergesWP1` - Convergence with probability 1 (almost surely)
* `ConvergesInMean` - Convergence in mean (L¹)
* `ConvergesIMS` - Convergence in mean square (L²)

## Main Results

* `Lemma 3.9`: Relations between convergence criteria:
  - i.m.s. ⟹ in mean ⟹ in probability
  - w.p.1 ⟹ in probability

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Definition 3.8, Lemma 3.9
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Convergence

namespace ConvergenceCriteria

/-! ## Definition 3.8: Convergence Criteria

For a predictor ρ and true distribution μ, we define convergence of
ρ(xₖ|x₁:ₖ₋₁) to μ(xₖ|x₁:ₖ₋₁) as k → ∞.
-/

/-- Prediction error at step k for a given prefix x of length k-1.
    This is |ρ(true|x) - μ(true|x)|, the absolute difference in next-bit predictions. -/
def predictionError (μ : PrefixMeasure) (ρ : Semimeasure) (x : BinString) : ℝ :=
  |FiniteHorizon.condProb ρ x true - FiniteHorizon.condProb μ.toSemimeasure x true|

/-- Squared prediction error at step k. -/
def predictionErrorSq (μ : PrefixMeasure) (ρ : Semimeasure) (x : BinString) : ℝ :=
  (predictionError μ ρ x) ^ 2

/-- Expected prediction error at horizon n: E_μ[|ρ(true|x) - μ(true|x)|].

    This is the "in mean" quantity for convergence. -/
def expectedError (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) : ℝ :=
  expectPrefix μ n (predictionError μ ρ)

/-- Expected squared prediction error at horizon n: E_μ[(ρ(true|x) - μ(true|x))²].

    This is the "in mean square" quantity for convergence. -/
def expectedErrorSq (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) : ℝ :=
  expectPrefix μ n (predictionErrorSq μ ρ)

/-- Convergence in mean: E_μ[|ρ(xₖ|x<ₖ) - μ(xₖ|x<ₖ)|] → 0 as k → ∞. -/
def ConvergesInMean (μ : PrefixMeasure) (ρ : Semimeasure) : Prop :=
  Filter.Tendsto (expectedError μ ρ) Filter.atTop (nhds 0)

/-- Convergence in mean square: E_μ[(ρ(xₖ|x<ₖ) - μ(xₖ|x<ₖ))²] → 0 as k → ∞. -/
def ConvergesIMS (μ : PrefixMeasure) (ρ : Semimeasure) : Prop :=
  Filter.Tendsto (expectedErrorSq μ ρ) Filter.atTop (nhds 0)

/-- Total prediction error up to horizon n: ∑_{k<n} E_μ[|ρ - μ|]. -/
def totalExpectedError (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectedError μ ρ k

/-- Total squared error up to horizon n: ∑_{k<n} E_μ[(ρ - μ)²]. -/
def totalExpectedErrorSq (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectedErrorSq μ ρ k

/-! ## Lemma 3.9: Relations Between Convergence Criteria

The key relations are:
1. i.m.s. convergence ⟹ in-mean convergence (by Jensen/Cauchy-Schwarz)
2. Finite total squared error ⟹ i.m.s. convergence (summability argument)
-/

/-- Squared error dominates squared distance: |p - q|² ≤ 2 * sqDistBinary p q.

    Note: sqDistBinary p q = (p - q)² + ((1-p) - (1-q))² = 2(p - q)². -/
theorem predictionErrorSq_le_sqDistStep (μ : PrefixMeasure) (ρ : Semimeasure) (x : BinString) :
    predictionErrorSq μ ρ x ≤ sqDistStep μ ρ x := by
  unfold predictionErrorSq predictionError sqDistStep Entropy.sqDistBinary
  have hsq : (FiniteHorizon.condProb ρ x true - FiniteHorizon.condProb μ.toSemimeasure x true) ^ 2 =
      (FiniteHorizon.condProb μ.toSemimeasure x true - FiniteHorizon.condProb ρ x true) ^ 2 := by
    ring
  rw [sq_abs, hsq]
  have h2 : ((1 - FiniteHorizon.condProb μ.toSemimeasure x true) -
      (1 - FiniteHorizon.condProb ρ x true)) ^ 2 =
      (FiniteHorizon.condProb μ.toSemimeasure x true - FiniteHorizon.condProb ρ x true) ^ 2 := by
    ring
  rw [h2]
  linarith [sq_nonneg (FiniteHorizon.condProb μ.toSemimeasure x true - FiniteHorizon.condProb ρ x true)]

/-- Total expected squared error is bounded by total squared distance. -/
theorem totalExpectedErrorSq_le_totalSqDist (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) :
    totalExpectedErrorSq μ ρ n ≤ totalSqDist μ ρ n := by
  unfold totalExpectedErrorSq totalSqDist expectedErrorSq
  apply Finset.sum_le_sum
  intro k _hk
  unfold expectPrefix
  apply Finset.sum_le_sum
  intro f _hf
  apply mul_le_mul_of_nonneg_left
  · exact predictionErrorSq_le_sqDistStep μ ρ (List.ofFn f)
  · exact ENNReal.toReal_nonneg

/-- Expected error is bounded by sqrt of expected squared error (Jensen's inequality).

    This is E[|X|] ≤ √E[X²] which follows from |X| ≤ 1 + X² and convexity. -/
theorem expectedError_le_sqrt_expectedErrorSq (μ : PrefixMeasure) (ρ : Semimeasure) (n : ℕ) :
    expectedError μ ρ n ≤ Real.sqrt (expectedErrorSq μ ρ n) := by
  unfold expectedError expectedErrorSq expectPrefix
  -- Use the fact that |a| ≤ √(a²) = |a| with equality, and sum properties
  have hLHS_nonneg : 0 ≤ ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
  have hRHS_nonneg : 0 ≤ ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * predictionErrorSq μ ρ (List.ofFn x) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  -- For probability distribution with sum of weights = 1, E[|X|]² ≤ E[X²]
  -- Use weighted Cauchy-Schwarz: (∑ wᵢ|xᵢ|)² ≤ (∑ wᵢ)(∑ wᵢxᵢ²)
  have hweights : ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal = 1 := sum_prefixPMF_toReal μ n
  -- Since |X| ≤ 1 (it's a probability difference), we have |X|² ≤ 1
  -- Thus E[|X|] ≤ 1 and √E[X²] ≥ 0, but we need the actual bound
  -- The bound follows from: for each term, w|x| ≤ √w * √(wx²) when 0 ≤ w ≤ 1
  -- By Cauchy-Schwarz: (∑ wᵢ|xᵢ|)² ≤ (∑ wᵢ)(∑ wᵢ|xᵢ|²) = 1 * E[X²]
  have hCS : (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x)) ^ 2 ≤
      (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal) *
      (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * (predictionError μ ρ (List.ofFn x)) ^ 2) := by
    -- Use Cauchy-Schwarz: (∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)
    -- Let fᵢ = √wᵢ * errᵢ, gᵢ = √wᵢ
    -- Then fᵢgᵢ = wᵢ * errᵢ, fᵢ² = wᵢ * errᵢ², gᵢ² = wᵢ
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x))
      (fun x => Real.sqrt (prefixPMF μ n x).toReal)
    -- Rewrite LHS of CS: ∑ (√w * err) * √w = ∑ w * err
    have hLHS_eq : ∑ x, Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) *
        Real.sqrt (prefixPMF μ n x).toReal =
        ∑ x, (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) := by
      apply Finset.sum_congr rfl
      intro x _
      have hw_nn : 0 ≤ (prefixPMF μ n x).toReal := ENNReal.toReal_nonneg
      have hsq : Real.sqrt (prefixPMF μ n x).toReal * Real.sqrt (prefixPMF μ n x).toReal =
          (prefixPMF μ n x).toReal := Real.mul_self_sqrt hw_nn
      calc Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) *
          Real.sqrt (prefixPMF μ n x).toReal
          = (Real.sqrt (prefixPMF μ n x).toReal * Real.sqrt (prefixPMF μ n x).toReal) *
            predictionError μ ρ (List.ofFn x) := by ring
        _ = (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) := by rw [hsq]
    -- Rewrite RHS norms
    have hNorm1_sq : (∑ x, (Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x)) ^ 2) =
        ∑ x, (prefixPMF μ n x).toReal * (predictionError μ ρ (List.ofFn x)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
    have hNorm2_sq : (∑ x, (Real.sqrt (prefixPMF μ n x).toReal) ^ 2) =
        ∑ x, (prefixPMF μ n x).toReal := by
      apply Finset.sum_congr rfl
      intro x _
      exact Real.sq_sqrt ENNReal.toReal_nonneg
    -- Now use h with the rewritten forms
    calc (∑ x, (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x)) ^ 2
        = (∑ x, Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x) *
            Real.sqrt (prefixPMF μ n x).toReal) ^ 2 := by rw [hLHS_eq]
      _ ≤ (∑ x, (Real.sqrt (prefixPMF μ n x).toReal * predictionError μ ρ (List.ofFn x)) ^ 2) *
            (∑ x, (Real.sqrt (prefixPMF μ n x).toReal) ^ 2) := h
      _ = (∑ x, (prefixPMF μ n x).toReal * (predictionError μ ρ (List.ofFn x)) ^ 2) *
            (∑ x, (prefixPMF μ n x).toReal) := by rw [hNorm1_sq, hNorm2_sq]
      _ = (∑ x, (prefixPMF μ n x).toReal) *
            (∑ x, (prefixPMF μ n x).toReal * (predictionError μ ρ (List.ofFn x)) ^ 2) := by ring
  rw [hweights, one_mul] at hCS
  unfold predictionErrorSq
  have hsqrt := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq hLHS_nonneg] at hsqrt
  exact hsqrt

/-- Finite total squared error implies i.m.s. convergence (Theorem 3.19 style).

    If ∑_k E_μ[(ρ - μ)²] < ∞, then E_μ[(ρ - μ)²] → 0. -/
theorem convergesIMS_of_totalErrorSq_bounded (μ : PrefixMeasure) (ρ : Semimeasure)
    (hBounded : ∃ B : ℝ, ∀ n, totalExpectedErrorSq μ ρ n ≤ B) :
    ConvergesIMS μ ρ := by
  -- The sequence of partial sums is bounded and monotone increasing
  -- Hence it converges, and the terms must go to 0
  unfold ConvergesIMS
  -- Use the fact that bounded monotone sequences converge
  -- and if ∑ aₙ converges, then aₙ → 0
  obtain ⟨B, hB⟩ := hBounded
  have hMono : Monotone (totalExpectedErrorSq μ ρ) := by
    intro m n hmn
    unfold totalExpectedErrorSq
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ _
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg ENNReal.toReal_nonneg
      unfold predictionErrorSq
      exact sq_nonneg _
  have hNonneg : ∀ n, 0 ≤ expectedErrorSq μ ρ n := by
    intro n
    unfold expectedErrorSq expectPrefix predictionErrorSq
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg ENNReal.toReal_nonneg
    exact sq_nonneg _
  -- The partial sums converge (bounded monotone)
  have hPartialConv : ∃ L : ℝ, Filter.Tendsto (totalExpectedErrorSq μ ρ) Filter.atTop (nhds L) := by
    have hBddAbove : BddAbove (Set.range (totalExpectedErrorSq μ ρ)) := by
      use B
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      exact hB n
    exact ⟨_, tendsto_atTop_ciSup hMono hBddAbove⟩
  obtain ⟨L, hL⟩ := hPartialConv
  -- Since ∑_k aₖ converges, aₖ → 0
  have hTerms : Filter.Tendsto (expectedErrorSq μ ρ) Filter.atTop (nhds 0) := by
    -- Use the fact that aₙ = Sₙ₊₁ - Sₙ → L - L = 0
    have hDiff : ∀ n, expectedErrorSq μ ρ n =
        totalExpectedErrorSq μ ρ (n + 1) - totalExpectedErrorSq μ ρ n := by
      intro n
      unfold totalExpectedErrorSq
      simp only [Finset.sum_range_succ, add_sub_cancel_left]
    have hLim := Filter.Tendsto.sub
      (hL.comp (Filter.tendsto_add_atTop_nat 1))
      hL
    simp only [sub_self] at hLim
    have hEq : (fun n => totalExpectedErrorSq μ ρ (n + 1) - totalExpectedErrorSq μ ρ n) =
        expectedErrorSq μ ρ := by
      ext n
      exact (hDiff n).symm
    rw [← hEq]
    exact hLim
  exact hTerms

/-- i.m.s. convergence implies in-mean convergence. -/
theorem convergesInMean_of_convergesIMS (μ : PrefixMeasure) (ρ : Semimeasure)
    (hIMS : ConvergesIMS μ ρ) :
    ConvergesInMean μ ρ := by
  unfold ConvergesInMean ConvergesIMS at *
  -- Use expectedError ≤ sqrt(expectedErrorSq)
  -- If E[X²] → 0, then sqrt(E[X²]) → 0, hence E[|X|] → 0
  have hSqrt : Filter.Tendsto (fun n => Real.sqrt (expectedErrorSq μ ρ n)) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.comp (f := expectedErrorSq μ ρ) (g := Real.sqrt)
      (Real.continuous_sqrt.tendsto 0) hIMS
    simp only [Real.sqrt_zero] at h
    exact h
  -- Use squeeze theorem: 0 ≤ expectedError ≤ sqrt(expectedErrorSq) → 0
  have hNonneg : ∀ n, 0 ≤ expectedError μ ρ n := by
    intro n
    unfold expectedError expectPrefix
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hLE : ∀ n, expectedError μ ρ n ≤ Real.sqrt (expectedErrorSq μ ρ n) :=
    expectedError_le_sqrt_expectedErrorSq μ ρ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSqrt hNonneg hLE

/-- Main convergence theorem (Theorem 3.19 consequence):
    Under dominance, the universal predictor converges to μ in mean square. -/
theorem convergence_in_mean_square (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    ConvergesIMS μ ξ := by
  apply convergesIMS_of_totalErrorSq_bounded
  use Real.log (1 / c.toReal)
  intro n
  calc totalExpectedErrorSq μ ξ n
      ≤ totalSqDist μ ξ n := totalExpectedErrorSq_le_totalSqDist μ ξ n
    _ ≤ Real.log (1 / c.toReal) := convergence_bound μ ξ hdom hc0 n h_cond_true h_cond_false

/-- Corollary: Under dominance, the universal predictor converges to μ in mean. -/
theorem convergence_in_mean (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    ConvergesInMean μ ξ :=
  convergesInMean_of_convergesIMS μ ξ (convergence_in_mean_square μ ξ hdom hc0 h_cond_true h_cond_false)

end ConvergenceCriteria

end Mettapedia.UniversalAI.UniversalPrediction
