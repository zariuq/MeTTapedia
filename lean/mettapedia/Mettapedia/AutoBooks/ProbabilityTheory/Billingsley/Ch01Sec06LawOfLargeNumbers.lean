/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Billingsley Chapter 1, Section 6: The Law of Large Numbers

This file formalizes Section 6 of Billingsley's "Probability and Measure" (3rd Edition),
which covers the strong and weak laws of large numbers.

## Main theorems

* Theorem 6.1: Strong Law of Large Numbers (SLLN)
  - If Xₙ are i.i.d. with E[Xₙ] = m, then n⁻¹Sₙ → m a.s.
* Weak Law of Large Numbers (WLLN)
  - Under same hypotheses, n⁻¹Sₙ → m in probability
* Theorem 6.2: Bernstein's approximation theorem
  - Bernstein polynomials approximate continuous functions uniformly

## Key ideas

The proof of SLLN uses:
1. Fourth moment bound: E[Sₙ⁴] ≤ Kn²
2. Markov's inequality for k=4: P[|Sₙ| ≥ nε] ≤ Kn²ε⁻⁴/n⁴
3. First Borel-Cantelli lemma

The WLLN is a direct consequence of Chebyshev's inequality and variance addition.

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 6][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec06

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-! ## Partial Sums -/

/-- Partial sum Sₙ = X₁ + ⋯ + Xₙ -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, X i ω

/-- Partial average n⁻¹Sₙ -/
def partialAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * partialSum X n ω

/-! ## Strong Law of Large Numbers -/

/-- Identically distributed: all Xₙ have the same distribution. -/
def IdenticallyDistributed (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n m, μ.map (X n) = μ.map (X m)

/-- Theorem 6.1: Strong Law of Large Numbers.
If Xₙ are i.i.d. with E[Xₙ] = m and finite fourth moment, then
P[lim n⁻¹Sₙ = m] = 1.

Mathlib's Etemadi-style `ProbabilityTheory.strong_law_ae_real` only needs integrability
plus pairwise independence and identical distribution, so the fourth-moment and pairwise
hypotheses given here are more than enough. -/
theorem strong_law_of_large_numbers {X : ℕ → Ω → ℝ}
    (h_meas : ∀ n, Measurable (X n))
    (h_int : ∀ n, Integrable (X n) μ)
    (_h_int4 : ∀ n, Integrable (fun ω => (X n ω)^4) μ)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_id : IdenticallyDistributed μ X)
    (m : ℝ) (hm : ∀ n, ∫ ω, X n ω ∂μ = m) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => partialAverage X n ω) Filter.atTop (nhds m) := by
  have hindep_pair : Pairwise (Function.onFun (α := ℕ) (fun Y Z : Ω → ℝ => IndepFun Y Z μ) X) :=
    fun i j hij => h_indep i j hij
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    { aemeasurable_fst := (h_meas i).aemeasurable
      aemeasurable_snd := (h_meas 0).aemeasurable
      map_eq := h_id i 0 }
  have hAE := ProbabilityTheory.strong_law_ae_real X (h_int 0) hindep_pair hident
  have hmeq : ∫ ω, X 0 ω ∂μ = m := hm 0
  filter_upwards [hAE] with ω hω
  have hfeq : (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
           = (fun n : ℕ => partialAverage X n ω) := by
    funext n
    simp [partialAverage, partialSum, div_eq_inv_mul]
  rw [hfeq, hmeq] at hω
  exact hω

/-! ## Weak Law of Large Numbers -/

/-- Weak Law of Large Numbers via Chebyshev's inequality.
If Xₙ are i.i.d. with E[Xₙ] = m and finite variance σ², then
n⁻¹Sₙ → m in probability.

The proof is direct: P[|n⁻¹Sₙ - m| ≥ ε] ≤ Var[Sₙ]/(n²ε²) = σ²/(nε²) → 0. -/
theorem weak_law_of_large_numbers {X : ℕ → Ω → ℝ}
    (h_meas : ∀ n, Measurable (X n))
    (h_int : ∀ n, Integrable (X n) μ)
    (h_int2 : ∀ n, Integrable (fun ω => (X n ω)^2) μ)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_id : IdenticallyDistributed μ X)
    (m : ℝ) (hm : ∀ n, ∫ ω, X n ω ∂μ = m) :
    ∀ ε > 0, Filter.Tendsto
      (fun n => μ {ω | ε ≤ |partialAverage X n ω - m|}) Filter.atTop (nhds 0) := by
  intro ε hε
  have hX_mlp : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (h_meas i).aestronglyMeasurable).mpr (h_int2 i)
  set σ2 : ℝ := ProbabilityTheory.variance (X 0) μ with hσ2_def
  have hσ2_nn : 0 ≤ σ2 := ProbabilityTheory.variance_nonneg _ _
  -- All variances equal σ² by identical distribution
  have hvar_eq : ∀ i, ProbabilityTheory.variance (X i) μ = σ2 := by
    intro i
    have hid : IdentDistrib (X i) (X 0) μ μ :=
      { aemeasurable_fst := (h_meas i).aemeasurable
        aemeasurable_snd := (h_meas 0).aemeasurable
        map_eq := h_id i 0 }
    exact hid.variance_eq
  -- Partial sum as a Finset sum
  have hSumEq : ∀ n, partialSum X n = ∑ i ∈ Finset.range n, X i := fun n => by
    funext ω; simp [partialSum, Finset.sum_apply]
  -- Variance of Sₙ = n · σ²
  have hVar_Sn : ∀ n, ProbabilityTheory.variance (partialSum X n) μ = (n : ℝ) * σ2 := by
    intro n
    have hpair : Set.Pairwise (↑(Finset.range n) : Set ℕ)
        (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) := by
      intro i _ j _ hij; exact h_indep i j hij
    rw [hSumEq n,
        ProbabilityTheory.IndepFun.variance_sum (fun i _ => hX_mlp i) hpair]
    simp [hvar_eq, Finset.sum_const, Finset.card_range]
  -- E[Sₙ] = n · m
  have hE_Sn : ∀ n, ∫ ω, partialSum X n ω ∂μ = (n : ℝ) * m := by
    intro n
    have heq : (fun ω => partialSum X n ω) = fun ω => ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [partialSum]
    rw [show (fun ω => partialSum X n ω) = fun ω => ∑ i ∈ Finset.range n, X i ω from heq]
    rw [integral_finset_sum (Finset.range n) (fun i _ => h_int i)]
    simp [hm, Finset.sum_const, Finset.card_range]
  -- Sₙ ∈ L² for each n
  have hSn_mlp : ∀ n, MemLp (partialSum X n) 2 μ := fun n => by
    rw [hSumEq n]; exact memLp_finset_sum' _ (fun i _ => hX_mlp i)
  -- Upper-bound sequence σ²/(n·ε²) → 0 in ℝ≥0∞
  have hub_tendsto : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (σ2 / ((n : ℝ) * ε^2)))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto (fun n : ℕ => σ2 / ((n : ℝ) * ε^2))
        Filter.atTop (nhds 0) := by
      have hfeq : (fun n : ℕ => σ2 / ((n : ℝ) * ε^2))
                = (fun n : ℕ => (σ2 / ε^2) / (n : ℝ)) := by
        funext n
        rw [mul_comm ((n : ℝ)) (ε^2), ← div_div]
      rw [hfeq]
      exact tendsto_const_div_atTop_nhds_zero_nat (σ2 / ε^2)
    have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := (ENNReal.ofReal_zero).symm
    rw [h0]; exact ENNReal.tendsto_ofReal hreal
  -- Chebyshev bound for n ≥ 1
  have hCheb_n : ∀ n : ℕ, 1 ≤ n →
      μ {ω | ε ≤ |partialAverage X n ω - m|}
        ≤ ENNReal.ofReal (σ2 / ((n : ℝ) * ε^2)) := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hn_inv_pos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
    have hnε_pos : (0 : ℝ) < (n : ℝ) * ε := mul_pos hn_pos hε
    -- Set equivalence: {ε ≤ |Sₙ/n - m|} = {n·ε ≤ |Sₙ - E[Sₙ]|}
    have hSet : {ω | ε ≤ |partialAverage X n ω - m|}
              = {ω | (n : ℝ) * ε
                       ≤ |partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ|} := by
      ext ω
      have habs_n : |((n : ℝ) * ((n : ℝ)⁻¹ * partialSum X n ω - m))|
                  = (n : ℝ) * |(n : ℝ)⁻¹ * partialSum X n ω - m| := by
        rw [abs_mul, abs_of_pos hn_pos]
      have habs_ninv : |((n : ℝ)⁻¹ * (partialSum X n ω - (n : ℝ) * m))|
                     = (n : ℝ)⁻¹ * |partialSum X n ω - (n : ℝ) * m| := by
        rw [abs_mul, abs_of_pos hn_inv_pos]
      have hrw1 : (n : ℝ) * |(n : ℝ)⁻¹ * partialSum X n ω - m|
                = |partialSum X n ω - (n : ℝ) * m| := by
        rw [← habs_n, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
      have hrw2 : (n : ℝ)⁻¹ * |partialSum X n ω - (n : ℝ) * m|
                = |(n : ℝ)⁻¹ * partialSum X n ω - m| := by
        rw [← habs_ninv, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]
      simp only [Set.mem_setOf_eq, partialAverage, hE_Sn]
      constructor
      · intro h
        have := mul_le_mul_of_nonneg_left h hn_pos.le
        rw [hrw1] at this; exact this
      · intro h
        have h' := mul_le_mul_of_nonneg_left h hn_inv_pos.le
        have hid1 : (n : ℝ)⁻¹ * ((n : ℝ) * ε) = ε := by
          rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]
        rw [hid1, hrw2] at h'; exact h'
    rw [hSet]
    have hCheb := ProbabilityTheory.meas_ge_le_variance_div_sq (hSn_mlp n) hnε_pos
    rw [hVar_Sn n] at hCheb
    refine hCheb.trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hpow_eq : ((n : ℝ) * ε)^2 = (n : ℝ) * ((n : ℝ) * ε^2) := by ring
    have hrw_div : (n : ℝ) * σ2 / ((n : ℝ) * ε)^2 = σ2 / ((n : ℝ) * ε^2) := by
      rw [hpow_eq, mul_div_mul_left _ _ hn_ne]
    rw [hrw_div]
  -- Squeeze between 0 and σ²/(n·ε²)
  have htail : ∀ᶠ n in Filter.atTop,
      μ {ω | ε ≤ |partialAverage X n ω - m|}
        ≤ ENNReal.ofReal (σ2 / ((n : ℝ) * ε^2)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hCheb_n n hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hub_tendsto
    (Filter.Eventually.of_forall (fun _ => by simp)) htail

/-! ## Example 6.1: Bernoulli Trials

For Bernoulli trials with P[Xₙ = 1] = p, P[Xₙ = 0] = 1-p:
- Sₙ is the number of successes
- n⁻¹Sₙ → p a.s. (strong law)
- This is the frequency interpretation of probability
-/

/-- Bernoulli random variable: X = 1 with probability p, X = 0 with probability 1-p. -/
def BernoulliRV (X : Ω → ℝ) (p : ℝ) : Prop :=
  (μ {ω | X ω = 1}).toReal = p ∧ (μ {ω | X ω = 0}).toReal = 1 - p ∧
  ∀ ω, X ω = 0 ∨ X ω = 1

/-- Strong law for Bernoulli trials: frequency converges to probability. -/
theorem bernoulli_strong_law {X : ℕ → Ω → ℝ} {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1)
    (h_bern : ∀ n, BernoulliRV μ (X n) p)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_meas : ∀ n, Measurable (X n)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => partialAverage X n ω) Filter.atTop (nhds p) := by
  -- Each X n is pointwise in {0,1}, hence bounded by 1.
  have h_bound : ∀ n ω, |X n ω| ≤ 1 := fun n ω => by
    rcases (h_bern n).2.2 ω with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  -- Integrability of X n and X n ^ 4.
  have h_int : ∀ n, Integrable (X n) μ := fun n => by
    refine (integrable_const (1 : ℝ)).mono' (h_meas n).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact h_bound n ω
  have h_bound4 : ∀ n ω, |(X n ω) ^ 4| ≤ 1 := fun n ω => by
    rw [abs_pow]
    calc |X n ω| ^ 4
        ≤ (1 : ℝ) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (h_bound n ω) 4
      _ = 1 := one_pow _
  have h_int4 : ∀ n, Integrable (fun ω => (X n ω) ^ 4) μ := fun n => by
    refine (integrable_const (1 : ℝ)).mono'
      ((h_meas n).pow_const 4).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact h_bound4 n ω
  -- Translate Bernoulli probabilities into ENNReal equalities.
  have hμ1 : ∀ n, μ {ω | X n ω = 1} = ENNReal.ofReal p := fun n => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), (h_bern n).1]
  have hμ0 : ∀ n, μ {ω | X n ω = 0} = ENNReal.ofReal (1 - p) := fun n => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), (h_bern n).2.1]
  -- Identically distributed: any measurable S ⊆ ℝ pulls back to univ, {X=0}, {X=1}, or ∅.
  have h_id : IdenticallyDistributed μ X := by
    intro n m
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply (h_meas n) hS, Measure.map_apply (h_meas m) hS]
    by_cases h0 : (0 : ℝ) ∈ S
    · by_cases h1 : (1 : ℝ) ∈ S
      · have heqUniv : ∀ i, (X i ⁻¹' S) = Set.univ := by
          intro i; ext ω
          simp only [Set.mem_preimage, Set.mem_univ, iff_true]
          rcases (h_bern i).2.2 ω with hω | hω
          · rw [hω]; exact h0
          · rw [hω]; exact h1
        rw [heqUniv n, heqUniv m]
      · have heq0 : ∀ i, (X i ⁻¹' S) = {ω | X i ω = 0} := by
          intro i; ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          refine ⟨fun hω => ?_, fun hω => ?_⟩
          · rcases (h_bern i).2.2 ω with hz | ho
            · exact hz
            · rw [ho] at hω; exact absurd hω h1
          · rw [hω]; exact h0
        rw [heq0 n, heq0 m, hμ0 n, hμ0 m]
    · by_cases h1 : (1 : ℝ) ∈ S
      · have heq1 : ∀ i, (X i ⁻¹' S) = {ω | X i ω = 1} := by
          intro i; ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          refine ⟨fun hω => ?_, fun hω => ?_⟩
          · rcases (h_bern i).2.2 ω with hz | ho
            · rw [hz] at hω; exact absurd hω h0
            · exact ho
          · rw [hω]; exact h1
        rw [heq1 n, heq1 m, hμ1 n, hμ1 m]
      · have heqEmpty : ∀ i, (X i ⁻¹' S) = ∅ := by
          intro i; ext ω
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hω
          rcases (h_bern i).2.2 ω with hz | ho
          · rw [hz] at hω; exact h0 hω
          · rw [ho] at hω; exact h1 hω
        rw [heqEmpty n, heqEmpty m]
  -- Mean of X n equals p: write X n as indicator of {X n = 1}.
  have h_mean : ∀ n, ∫ ω, X n ω ∂μ = p := by
    intro n
    have hSet1 : MeasurableSet {ω | X n ω = 1} :=
      (h_meas n) (measurableSet_singleton 1)
    have h_eq_indic : (fun ω => X n ω) =ᵐ[μ]
        ({ω' | X n ω' = 1}).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards with ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h_mem
      · exact h_mem
      · rcases (h_bern n).2.2 ω with h0 | h1
        · exact h0
        · exact absurd h1 h_mem
    rw [integral_congr_ae h_eq_indic, integral_indicator hSet1, integral_const,
        measureReal_restrict_apply_univ, measureReal_def, smul_eq_mul, mul_one]
    exact (h_bern n).1
  -- Apply the strong law proved above.
  exact strong_law_of_large_numbers μ h_meas h_int h_int4 h_indep h_id p h_mean

/-! ## Theorem 6.2: Bernstein's Approximation Theorem

Bernstein polynomials provide a constructive proof of Weierstrass approximation. Mathlib
states it for continuous functions on the unit interval, with
`bernsteinApproximation n f x = ∑ k, bernstein n k x • f (k / n)`.
-/

/-- Theorem 6.2: the Bernstein polynomials of a continuous function on `[0, 1]` converge
to it uniformly (Mathlib's `bernsteinApproximation_uniform`). -/
theorem bernstein_approximation (f : C(unitInterval, ℝ)) :
    Filter.Tendsto (fun n => bernsteinApproximation n f) Filter.atTop (nhds f) :=
  bernsteinApproximation_uniform f

/-! ## Variance of Partial Sums -/

/-- Variance addition for independent random variables:
Var[Sₙ] = Σᵢ Var[Xᵢ] when Xᵢ are independent.

This follows from mathlib's `IndepFun.variance_sum` after converting between
the Billingsley-style integral definition and mathlib's variance notation. -/
theorem variance_sum_independent {X : ℕ → Ω → ℝ} (n : ℕ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i, Integrable (X i) μ)
    (h_int2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ) :
    ∫ ω, (partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ)^2 ∂μ =
      ∑ i ∈ Finset.range n, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ)^2 ∂μ := by
  -- Key step: E[Sₙ] = ∑ᵢ E[Xᵢ]
  have hE_sum : ∫ ω', partialSum X n ω' ∂μ = ∑ i ∈ Finset.range n, ∫ ω', X i ω' ∂μ := by
    unfold partialSum
    rw [integral_finset_sum (Finset.range n) (fun i _ => h_int i)]
  -- Let Yᵢ = Xᵢ - E[Xᵢ] be the centered variables
  set Y := fun i ω => X i ω - ∫ ω', X i ω' ∂μ with hY_def
  -- Each Yᵢ is integrable
  have hY_int : ∀ i, Integrable (Y i) μ := fun i => (h_int i).sub (integrable_const _)
  -- E[Yᵢ] = 0
  have hY_mean_zero : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [hY_def, integral_sub (h_int i) (integrable_const _), integral_const]
    simp only [smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul, sub_self]
  -- Yᵢ and Yⱼ are independent for i ≠ j (follows from independence of Xᵢ, Xⱼ)
  have hY_indep : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) μ := by
    intro i j hij
    -- Y i = (fun x => x - c_i) ∘ X i where c_i = ∫ X i
    have h : ((fun x => x - ∫ ω', X i ω' ∂μ) ∘ X i) ⟂ᵢ[μ] ((fun x => x - ∫ ω', X j ω' ∂μ) ∘ X j) :=
      (h_indep i j hij).comp (measurable_id.sub measurable_const) (measurable_id.sub measurable_const)
    exact h
  -- Sₙ - E[Sₙ] = ∑ᵢ Yᵢ
  have hSum_centered : ∀ ω, partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ =
      ∑ i ∈ Finset.range n, Y i ω := by
    intro ω
    simp only [partialSum, hY_def]
    rw [integral_finset_sum (Finset.range n) (fun i _ => h_int i)]
    simp only [Finset.sum_sub_distrib]
  -- Rewrite the LHS
  conv_lhs =>
    arg 2
    ext ω
    rw [hSum_centered ω]
  -- Bridge to mathlib's IndepFun.variance_sum via variance_eq_integral
  have hSumEq : partialSum X n = ∑ i ∈ Finset.range n, X i := by
    funext ω
    simp [partialSum, Finset.sum_apply]
  have hXlp : ∀ i ∈ Finset.range n, MemLp (X i) 2 μ := fun i _ =>
    (memLp_two_iff_integrable_sq (h_meas i).aestronglyMeasurable).mpr (h_int2 i)
  have hpair : Set.Pairwise (↑(Finset.range n) : Set ℕ)
      (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) := by
    intro i _ j _ hij
    exact h_indep i j hij
  have hSumMeas : AEMeasurable (partialSum X n) μ := by
    rw [hSumEq]
    exact Finset.aemeasurable_sum _ (fun i _ => (h_meas i).aemeasurable)
  have hVarSum : ProbabilityTheory.variance (partialSum X n) μ =
      ∑ i ∈ Finset.range n, ProbabilityTheory.variance (X i) μ := by
    rw [hSumEq]
    exact ProbabilityTheory.IndepFun.variance_sum hXlp hpair
  have hLHS : ∫ ω, (partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ)^2 ∂μ
      = ProbabilityTheory.variance (partialSum X n) μ :=
    (ProbabilityTheory.variance_eq_integral hSumMeas).symm
  have hRHS : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ)^2 ∂μ =
      ProbabilityTheory.variance (X i) μ :=
    fun i => (ProbabilityTheory.variance_eq_integral (h_meas i).aemeasurable).symm
  -- The conv_lhs earlier rewrote to ∫ (∑ Yᵢ)² ∂μ. Convert back.
  have hSumY : (fun ω => ∑ i ∈ Finset.range n, Y i ω) =
      fun ω => partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ := by
    funext ω; exact (hSum_centered ω).symm
  rw [show (∫ ω, (∑ i ∈ Finset.range n, Y i ω)^2 ∂μ) =
        (∫ ω, (partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ)^2 ∂μ) by
        congr 1; funext ω; rw [hSum_centered ω]]
  rw [hLHS, hVarSum]
  exact Finset.sum_congr rfl (fun i _ => (hRHS i).symm)

/-- For i.i.d. random variables with variance σ², Var[Sₙ] = nσ². -/
theorem variance_iid_sum {X : ℕ → Ω → ℝ} (n : ℕ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i, Integrable (X i) μ)
    (h_int2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (sigma2 : ℝ) (hσ : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ)^2 ∂μ = sigma2) :
    ∫ ω, (partialSum X n ω - ∫ ω', partialSum X n ω' ∂μ)^2 ∂μ = n * sigma2 := by
  rw [variance_sum_independent μ n h_meas h_int h_int2 h_indep]
  simp only [hσ]
  simp [Finset.sum_const, Finset.card_range]

end Mettapedia.AutoBooks.Billingsley.Ch01Sec06

end
