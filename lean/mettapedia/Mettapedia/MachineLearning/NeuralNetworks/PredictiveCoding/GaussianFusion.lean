import Mathlib.Tactic

/-!
# Scalar Gaussian fusion for predictive coding

This file contains the scalar Gaussian fusion primitive and its energy
minimization theorem for the predictive-coding development. The PLN-specific
truth-value bridge lives separately under `Mettapedia.PLN.Bridges`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## P1: scalar Gaussian fusion -/

/-- A scalar Gaussian source whose mean is also a valid PLN strength. -/
structure GaussianSource where
  mean : ℝ
  precision : ℝ
  mean_nonneg : 0 ≤ mean
  mean_le_one : mean ≤ 1
  precision_pos : 0 < precision

/-- Precision-weighted fusion of two scalar Gaussian observations. -/
noncomputable def gaussianFusion (mean₁ mean₂ precision₁ precision₂ : ℝ) : ℝ :=
  (precision₁ * mean₁ + precision₂ * mean₂) / (precision₁ + precision₂)

/-- Two-source scalar Gaussian energy with diagonal precisions. -/
noncomputable def twoSourceGaussianEnergy
    (mean₁ mean₂ precision₁ precision₂ z : ℝ) : ℝ :=
  precision₁ * (z - mean₁)^2 + precision₂ * (z - mean₂)^2

theorem twoSourceGaussianEnergy_sub_fusion_eq_square
    (mean₁ mean₂ precision₁ precision₂ z : ℝ)
    (hprecision_sum : precision₁ + precision₂ ≠ 0) :
    twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂ z -
        twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂
          (gaussianFusion mean₁ mean₂ precision₁ precision₂) =
      (precision₁ + precision₂) *
        (z - gaussianFusion mean₁ mean₂ precision₁ precision₂)^2 := by
  unfold twoSourceGaussianEnergy gaussianFusion
  field_simp [hprecision_sum]
  ring

/-- Gaussian fusion minimizes the two-source scalar Gaussian energy. -/
theorem gaussianFusion_isMinOn_twoSourceGaussianEnergy
    (mean₁ mean₂ precision₁ precision₂ : ℝ)
    (hprecision₁ : 0 < precision₁) (hprecision₂ : 0 < precision₂) :
    IsMinOn (twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂) Set.univ
      (gaussianFusion mean₁ mean₂ precision₁ precision₂) := by
  intro z _hz
  have hsum_pos : 0 < precision₁ + precision₂ := by linarith
  have hsum_ne : precision₁ + precision₂ ≠ 0 := ne_of_gt hsum_pos
  have hdiff :=
    twoSourceGaussianEnergy_sub_fusion_eq_square
      mean₁ mean₂ precision₁ precision₂ z hsum_ne
  have hnonneg :
      0 ≤ twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂ z -
        twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂
          (gaussianFusion mean₁ mean₂ precision₁ precision₂) := by
    rw [hdiff]
    exact mul_nonneg (le_of_lt hsum_pos) (sq_nonneg _)
  exact sub_nonneg.mp hnonneg

/-- Equality at the Gaussian minimum forces equality of the point. -/
theorem gaussianFusion_unique_of_min_energy
    (mean₁ mean₂ precision₁ precision₂ z : ℝ)
    (hprecision₁ : 0 < precision₁) (hprecision₂ : 0 < precision₂)
    (henergy :
      twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂ z =
        twoSourceGaussianEnergy mean₁ mean₂ precision₁ precision₂
          (gaussianFusion mean₁ mean₂ precision₁ precision₂)) :
    z = gaussianFusion mean₁ mean₂ precision₁ precision₂ := by
  have hsum_pos : 0 < precision₁ + precision₂ := by linarith
  have hsum_ne : precision₁ + precision₂ ≠ 0 := ne_of_gt hsum_pos
  have hdiff :=
    twoSourceGaussianEnergy_sub_fusion_eq_square
      mean₁ mean₂ precision₁ precision₂ z hsum_ne
  have hprod :
      (precision₁ + precision₂) *
          (z - gaussianFusion mean₁ mean₂ precision₁ precision₂)^2 = 0 := by
    rw [← hdiff, henergy]
    ring
  have hsquare : (z - gaussianFusion mean₁ mean₂ precision₁ precision₂)^2 = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_left hsum_ne
  have hsub : z - gaussianFusion mean₁ mean₂ precision₁ precision₂ = 0 :=
    sq_eq_zero_iff.mp hsquare
  exact sub_eq_zero.mp hsub

/-! ## P1 canaries -/

noncomputable def gaussianRevisionPositiveSource1 : GaussianSource where
  mean := (8 / 10 : ℝ)
  precision := 9
  mean_nonneg := by norm_num
  mean_le_one := by norm_num
  precision_pos := by norm_num

noncomputable def gaussianRevisionPositiveSource2 : GaussianSource where
  mean := (5 / 10 : ℝ)
  precision := 1
  mean_nonneg := by norm_num
  mean_le_one := by norm_num
  precision_pos := by norm_num

theorem gaussianFusion_positive_example :
    gaussianFusion gaussianRevisionPositiveSource1.mean gaussianRevisionPositiveSource2.mean
      gaussianRevisionPositiveSource1.precision gaussianRevisionPositiveSource2.precision =
        (77 / 100 : ℝ) := by
  norm_num [gaussianFusion, gaussianRevisionPositiveSource1, gaussianRevisionPositiveSource2]

theorem gaussianFusion_weighted_not_unweighted_example :
    ((gaussianRevisionPositiveSource1.mean + gaussianRevisionPositiveSource2.mean) / 2) ≠
      gaussianFusion gaussianRevisionPositiveSource1.mean gaussianRevisionPositiveSource2.mean
        gaussianRevisionPositiveSource1.precision gaussianRevisionPositiveSource2.precision := by
  norm_num [gaussianFusion, gaussianRevisionPositiveSource1, gaussianRevisionPositiveSource2]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
