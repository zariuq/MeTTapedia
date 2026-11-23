/-
Copyright (c) 2026 Mettapedia Authors. All rights reserved.
SPDX-License-Identifier: MIT
Authors: Mettapedia Project
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.SubGaussian

/-!
# Billingsley Chapter 1, Section 9: Large Deviations

Moment and cumulant generating functions from Section 9 of Billingsley's "Probability
and Measure" (3rd Edition), with Hoeffding's inequality.

## Main theorems

* `moment_from_mgf`: moments are the derivatives of the moment generating function at 0
* `first_cumulant_is_mean`, `second_cumulant_is_variance`
* `bernoulli_variance_from_mgf`: Example 9.1
* `hoeffding_inequality`: P[Sₙ - E[Sₙ] ≥ t] ≤ exp(-2t²/Σᵢ(bᵢ-aᵢ)²) for independent bounded summands

## References

* [Billingsley, *Probability and Measure* (3rd ed.), Section 9][billingsley1995]
-/

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Mettapedia.AutoBooks.Billingsley.Ch01Sec09

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-! ## Moment Generating Functions -/

/-- Moment generating function: M(t) = E[e^{tX}].
Formula (9.1). -/
def momentGeneratingFunction (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * X ω) ∂μ

notation "MGF[" X "|" μ "]" => momentGeneratingFunction μ X

/-- M(0) = 1 for any moment generating function. -/
theorem mgf_zero (X : Ω → ℝ) : MGF[X|μ] 0 = 1 := by
  unfold momentGeneratingFunction
  simp only [zero_mul, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  -- μ.real univ = 1 for probability measures
  rw [measureReal_def, measure_univ, ENNReal.toReal_one]

/-- Moments can be obtained by differentiating MGF at 0.
E[X^k] = M^(k)(0). Formula (9.3). -/
theorem moment_from_mgf (X : Ω → ℝ) (k : ℕ)
    (hX : ∀ t, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    ∫ ω, (X ω)^k ∂μ = (deriv^[k] (MGF[X|μ])) 0 := by
  have h_set : ProbabilityTheory.integrableExpSet X μ = Set.univ := by
    ext t
    simp [ProbabilityTheory.integrableExpSet, hX t]
  have h_mem : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet X μ) := by
    rw [h_set]; simp
  have h_mgf_eq : MGF[X|μ] = ProbabilityTheory.mgf X μ := rfl
  have h_iter : deriv^[k] (MGF[X|μ]) = iteratedDeriv k (ProbabilityTheory.mgf X μ) := by
    rw [h_mgf_eq, iteratedDeriv_eq_iterate]
  rw [h_iter, ProbabilityTheory.iteratedDeriv_mgf_zero h_mem]
  simp [Pi.pow_apply]

/-! ## Cumulant Generating Function -/

/-- Cumulant generating function: K(t) = log M(t). -/
def cumulantGeneratingFunction (X : Ω → ℝ) (t : ℝ) : ℝ :=
  Real.log (MGF[X|μ] t)

/-- First cumulant is the mean: K'(0) = E[X].
We use the stronger hypothesis that the MGF exists in a neighborhood of `0`; this is the
natural hypothesis for differentiability of the CGF at zero. -/
theorem first_cumulant_is_mean (X : Ω → ℝ)
    (hX : ∀ t, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    deriv (cumulantGeneratingFunction μ X) 0 = ∫ ω, X ω ∂μ := by
  have h_set : ProbabilityTheory.integrableExpSet X μ = Set.univ := by
    ext t; simp [ProbabilityTheory.integrableExpSet, hX t]
  have h_mem : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet X μ) := by
    rw [h_set]; simp
  have h_cgf_eq : cumulantGeneratingFunction μ X = ProbabilityTheory.cgf X μ := rfl
  rw [h_cgf_eq, ProbabilityTheory.deriv_cgf_zero h_mem]
  simp

/-- Second cumulant is the variance: K''(0) = Var[X].
We use the stronger hypothesis that the MGF exists for all `t`; this is the natural
hypothesis for twice-differentiability of the CGF at zero. -/
theorem second_cumulant_is_variance (X : Ω → ℝ)
    (hX : ∀ t, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    (deriv^[2] (cumulantGeneratingFunction μ X)) 0 =
      ∫ ω, (X ω - ∫ ω', X ω' ∂μ)^2 ∂μ := by
  have h_set : ProbabilityTheory.integrableExpSet X μ = Set.univ := by
    ext t; simp [ProbabilityTheory.integrableExpSet, hX t]
  have h_mem : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet X μ) := by
    rw [h_set]; simp
  have h_cgf_eq : cumulantGeneratingFunction μ X = ProbabilityTheory.cgf X μ := rfl
  have h_iter : deriv^[2] (cumulantGeneratingFunction μ X)
      = iteratedDeriv 2 (ProbabilityTheory.cgf X μ) := by
    rw [h_cgf_eq, iteratedDeriv_eq_iterate]
  rw [h_iter, ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral h_mem]
  -- mgf X μ 0 = 1, exp(0 * _) = 1, deriv (cgf) 0 = μ[X].
  have h_deriv_cgf : deriv (ProbabilityTheory.cgf X μ) 0 = ∫ ω, X ω ∂μ := by
    rw [ProbabilityTheory.deriv_cgf_zero h_mem]; simp
  have h_mgf_zero : ProbabilityTheory.mgf X μ 0 = 1 := by
    simp [ProbabilityTheory.mgf]
  rw [h_deriv_cgf, h_mgf_zero, div_one]
  simp

/-! ## Example 9.1: Bernoulli MGF -/

/-- MGF for Bernoulli(p): M(t) = pe^t + (1-p). -/
def bernoulliMGF (p : ℝ) (t : ℝ) : ℝ := p * Real.exp t + (1 - p)

/-- Bernoulli variance from MGF: M''(0) - M'(0)² = p(1-p). -/
theorem bernoulli_variance_from_mgf (p : ℝ) (_hp : 0 ≤ p ∧ p ≤ 1) :
    (deriv^[2] (bernoulliMGF p)) 0 - (deriv (bernoulliMGF p) 0)^2 = p * (1 - p) := by
  -- bernoulliMGF p t = p * exp(t) + (1-p)
  -- M'(t) = p * exp(t), M'(0) = p
  -- M''(t) = p * exp(t), M''(0) = p
  -- So M''(0) - M'(0)² = p - p² = p(1-p)
  have h1 : deriv (bernoulliMGF p) = fun t => p * Real.exp t := by
    funext t
    have hderiv : HasDerivAt (bernoulliMGF p) (p * Real.exp t) t := by
      have h := ((Real.hasDerivAt_exp t).const_mul p).add_const (1 - p)
      exact h
    exact hderiv.deriv
  have h2 : deriv^[2] (bernoulliMGF p) = fun t => p * Real.exp t := by
    have := h1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, this]
    funext t
    rw [deriv_const_mul _ (Real.differentiable_exp.differentiableAt)]
    simp only [Real.deriv_exp]
  rw [h1, h2]
  simp only [Real.exp_zero, mul_one]
  ring

/-! ## Hoeffding's Inequality (a useful large deviation bound) -/

/-- Hoeffding's inequality for bounded random variables.
P[Sₙ - E[Sₙ] ≥ t] ≤ exp(-2t²/Σᵢ(bᵢ-aᵢ)²)
where aᵢ ≤ Xᵢ ≤ bᵢ.

Note: We use joint independence (`iIndepFun`) which is strictly stronger than pairwise
independence (and is the natural hypothesis under which Hoeffding holds). -/
theorem hoeffding_inequality {X : ℕ → Ω → ℝ} (n : ℕ)
    (a b : ℕ → ℝ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (h_indep : iIndepFun X μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | (∑ i ∈ Finset.range n, X i ω) -
      (∑ i ∈ Finset.range n, ∫ ω', X i ω' ∂μ) ≥ t}).toReal ≤
    Real.exp (-2 * t^2 / ∑ i ∈ Finset.range n, (b i - a i)^2) := by
  -- Shifted variables Y i = X i - μ[X i] are sub-gaussian with parameter ((b-a)/2)^2.
  set Y : ℕ → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂μ with hY_def
  have h_subG : ∀ i, ProbabilityTheory.HasSubgaussianMGF (Y i)
      ((‖b i - a i‖₊ / 2) ^ 2) μ :=
    fun i => ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bounded i)
  -- Joint independence transfers to the shifted variables via composition with x ↦ x - c.
  have h_indep_Y : ProbabilityTheory.iIndepFun Y μ := by
    have := h_indep.comp (g := fun i x => x - ∫ ω', X i ω' ∂μ)
      (fun _ => (measurable_id.sub_const _))
    exact this
  -- Rewrite the sum and apply mathlib's Hoeffding for joint-independent sub-gaussian.
  have h_set_eq : {ω | (∑ i ∈ Finset.range n, X i ω) -
        (∑ i ∈ Finset.range n, ∫ ω', X i ω' ∂μ) ≥ t}
      = {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} := by
    ext ω
    have : ∑ i ∈ Finset.range n, Y i ω
        = (∑ i ∈ Finset.range n, X i ω) - ∑ i ∈ Finset.range n, ∫ ω', X i ω' ∂μ := by
      simp [Y, Finset.sum_sub_distrib]
    simp [Set.mem_setOf_eq, this, ge_iff_le]
  rw [h_set_eq]
  have hMain := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (X := Y) h_indep_Y (s := Finset.range n) (fun i _ => h_subG i) ht
  rw [MeasureTheory.measureReal_def] at hMain
  -- Convert the ℝ≥0 parameter sum to the ℝ expression.
  have h_cast : (2 * ((∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2)) : ℝ≥0) : ℝ)
      = (∑ i ∈ Finset.range n, (b i - a i)^2) / 2 := by
    push_cast
    simp_rw [Real.norm_eq_abs, div_pow, sq_abs]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _; ring
  -- Transform bound: exp(-t² / (2·Σ c)) = exp(-2 t² / Σ (b-a)²).
  refine hMain.trans_eq ?_
  rw [h_cast]
  by_cases hs : (∑ i ∈ Finset.range n, (b i - a i)^2) = 0
  · simp [hs]
  · congr 1
    field_simp

end Mettapedia.AutoBooks.Billingsley.Ch01Sec09

end
