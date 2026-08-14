import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.GaussianFusion
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
import Mettapedia.PLN.TruthValues.PLNWeightTV
import Mettapedia.PLN.TruthValues.PLNTruthTower

/-!
# Scalar Gaussian revision bridge

This file is the PLN-side bridge for predictive coding: precision-weighted
scalar Gaussian fusion agrees with existing PLN weighted revision on the shared
unit-strength evidence interface. Pure predictive-coding theory lives under
`Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding`.
-/

namespace Mettapedia.PLN.Bridges.PredictiveCoding

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNWeightTV

/-! ## Scalar Gaussian fusion to PLN revision -/

/-- Gaussian precision is the PLN evidence weight in this bridge. -/
noncomputable def evidenceWeightOfPrecision (precision : ℝ) : ℝ := precision

/-- The displayed PLN confidence corresponding to a Gaussian precision. -/
noncomputable def confidenceOfPrecision (precision : ℝ) : ℝ := w2c precision

theorem c2w_w2c_eq_self_of_nonneg (weight : ℝ) (hweight : 0 ≤ weight) :
    c2w (w2c weight) = weight := by
  unfold c2w w2c
  have hden : 0 < weight + 1 := by linarith
  have hlt : weight / (weight + 1) < 1 := by
    rw [div_lt_one hden]
    linarith
  simp [hlt]
  field_simp [ne_of_gt hden]
  ring

/-- STV view reached by the precision-to-confidence map. -/
noncomputable def stvOfPrecision
    (mean precision : ℝ) (hmean0 : 0 ≤ mean) (hmean1 : mean ≤ 1)
    (hprecision0 : 0 ≤ precision) : STV where
  strength := mean
  confidence := confidenceOfPrecision precision
  strength_nonneg := hmean0
  strength_le_one := hmean1
  confidence_nonneg := (WTV.w2c_bounds precision hprecision0).1
  confidence_le_one := (WTV.w2c_bounds precision hprecision0).2

/-- WTV recovered from the displayed precision confidence. -/
noncomputable def wtvOfPrecision
    (mean precision : ℝ) (hmean0 : 0 ≤ mean) (hmean1 : mean ≤ 1)
    (hprecision0 : 0 ≤ precision) : WTV :=
  WTV.ofCTV (stvOfPrecision mean precision hmean0 hmean1 hprecision0)

@[simp] theorem wtvOfPrecision_strength
    (mean precision : ℝ) (hmean0 : 0 ≤ mean) (hmean1 : mean ≤ 1)
    (hprecision0 : 0 ≤ precision) :
    (wtvOfPrecision mean precision hmean0 hmean1 hprecision0).strength = mean := by
  simp [wtvOfPrecision, stvOfPrecision, WTV.ofCTV]

@[simp] theorem wtvOfPrecision_weight
    (mean precision : ℝ) (hmean0 : 0 ≤ mean) (hmean1 : mean ≤ 1)
    (hprecision0 : 0 ≤ precision) :
    (wtvOfPrecision mean precision hmean0 hmean1 hprecision0).weight = precision := by
  simp [wtvOfPrecision, stvOfPrecision, confidenceOfPrecision, WTV.ofCTV,
    c2w_w2c_eq_self_of_nonneg precision hprecision0]

/-- P1 crown: Gaussian fusion agrees with existing PLN `revisionWTV` after
the precision-to-confidence display map and the `c2w ∘ w2c` round trip. -/
theorem gaussianFusion_eq_plnRevisionWTV
    (source₁ source₂ : GaussianSource) :
    gaussianFusion source₁.mean source₂.mean source₁.precision source₂.precision =
      (revisionWTV
        (wtvOfPrecision source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos))
        (wtvOfPrecision source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos))).strength := by
  have hsum : source₁.precision + source₂.precision ≠ 0 :=
    ne_of_gt (by
      linarith [source₁.precision_pos, source₂.precision_pos] :
        0 < source₁.precision + source₂.precision)
  simp [gaussianFusion, revisionWTV, hsum]

/-! ## Count-level PLN evidence corollary -/

/-- Real-valued binary counts with given unit strength and evidence weight. -/
def binaryCountsOfStrengthWeight
    (strength weight : ℝ) (hstrength0 : 0 ≤ strength) (hstrength1 : strength ≤ 1)
    (hweight0 : 0 ≤ weight) : BinaryCounts where
  nPlus := strength * weight
  nMinus := (1 - strength) * weight
  nPlus_nonneg := mul_nonneg hstrength0 hweight0
  nMinus_nonneg := mul_nonneg (by linarith) hweight0

@[simp] theorem binaryCountsOfStrengthWeight_total
    (strength weight : ℝ) (hstrength0 : 0 ≤ strength) (hstrength1 : strength ≤ 1)
    (hweight0 : 0 ≤ weight) :
    (binaryCountsOfStrengthWeight strength weight hstrength0 hstrength1 hweight0).total =
      weight := by
  simp [binaryCountsOfStrengthWeight, BinaryCounts.total]
  ring

theorem binaryCountsOfStrengthWeight_strength
    (strength weight : ℝ) (hstrength0 : 0 ≤ strength) (hstrength1 : strength ≤ 1)
    (hweight : 0 < weight) :
    (binaryCountsOfStrengthWeight strength weight hstrength0 hstrength1
      (le_of_lt hweight)).strength = strength := by
  unfold BinaryCounts.strength
  rw [binaryCountsOfStrengthWeight_total]
  unfold binaryCountsOfStrengthWeight
  simp
  field_simp [ne_of_gt hweight]

/-- Count-level PLN evidence corollary on the shared unit-strength domain. -/
theorem gaussianFusion_eq_binaryCounts_revision_strength
    (source₁ source₂ : GaussianSource) :
    gaussianFusion source₁.mean source₂.mean source₁.precision source₂.precision =
      ((binaryCountsOfStrengthWeight source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos)).add
        (binaryCountsOfStrengthWeight source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos))).strength := by
  let evidence₁ :=
    binaryCountsOfStrengthWeight source₁.mean source₁.precision
      source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos)
  let evidence₂ :=
    binaryCountsOfStrengthWeight source₂.mean source₂.precision
      source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos)
  have hevidence₁_total : evidence₁.total = source₁.precision :=
    binaryCountsOfStrengthWeight_total source₁.mean source₁.precision
      source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos)
  have hevidence₂_total : evidence₂.total = source₂.precision :=
    binaryCountsOfStrengthWeight_total source₂.mean source₂.precision
      source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos)
  have hevidence₁_strength : evidence₁.strength = source₁.mean := by
    simpa [evidence₁] using
      binaryCountsOfStrengthWeight_strength source₁.mean source₁.precision
        source₁.mean_nonneg source₁.mean_le_one source₁.precision_pos
  have hevidence₂_strength : evidence₂.strength = source₂.mean := by
    simpa [evidence₂] using
      binaryCountsOfStrengthWeight_strength source₂.mean source₂.precision
        source₂.mean_nonneg source₂.mean_le_one source₂.precision_pos
  have hevidence₁_ne : evidence₁.total ≠ 0 := by
    rw [hevidence₁_total]
    exact ne_of_gt source₁.precision_pos
  have hevidence₂_ne : evidence₂.total ≠ 0 := by
    rw [hevidence₂_total]
    exact ne_of_gt source₂.precision_pos
  have hevidence_sum_ne : evidence₁.total + evidence₂.total ≠ 0 := by
    rw [hevidence₁_total, hevidence₂_total]
    exact ne_of_gt (by
      linarith [source₁.precision_pos, source₂.precision_pos] :
        0 < source₁.precision + source₂.precision)
  have hmix :=
    BinaryCounts.add_strength_eq_weighted_mixture
      evidence₁ evidence₂ hevidence₁_ne hevidence₂_ne hevidence_sum_ne
  rw [hmix]
  rw [hevidence₁_strength, hevidence₂_strength, hevidence₁_total, hevidence₂_total]
  unfold gaussianFusion
  ring

/-! ## P1 bridge canary -/

theorem gaussianFusion_positive_example_matches_revisionWTV :
    (revisionWTV
        (wtvOfPrecision gaussianRevisionPositiveSource1.mean
          gaussianRevisionPositiveSource1.precision
          gaussianRevisionPositiveSource1.mean_nonneg
          gaussianRevisionPositiveSource1.mean_le_one
          (le_of_lt gaussianRevisionPositiveSource1.precision_pos))
        (wtvOfPrecision gaussianRevisionPositiveSource2.mean
          gaussianRevisionPositiveSource2.precision
          gaussianRevisionPositiveSource2.mean_nonneg
          gaussianRevisionPositiveSource2.mean_le_one
          (le_of_lt gaussianRevisionPositiveSource2.precision_pos))).strength =
      (77 / 100 : ℝ) := by
  rw [← gaussianFusion_eq_plnRevisionWTV]
  exact gaussianFusion_positive_example

end Mettapedia.PLN.Bridges.PredictiveCoding
