import Mettapedia.Logic.PLNRegimeMixtureTheorems
import Mathlib.Data.Real.Basic

/-!
# Certified Higher-Order Estimates

This module packages theorem-facing contracts for estimated 2nd/3rd-order
quantities.

The point is not to formalize particular ML models.  The point is to formalize
what their outputs must certify in order to be consumable by higher-order PLN
chaining theorems.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNRegimeMixtureTheorems

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Certified interval for a 2nd-order admissibility quantity, together with a
coverage/confidence level and a certified step-error bound. -/
structure CertifiedAdmissibilityEstimate where
  lower : ℝ
  upper : ℝ
  coverage : ℝ
  errorBound : ℝ := 0
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1
  lower_le_upper : lower ≤ upper
  coverage_nonneg : 0 ≤ coverage
  coverage_le_one : coverage ≤ 1
  errorBound_nonneg : 0 ≤ errorBound

/-- Certified interval for a 3rd-order trust quantity, together with optional
disagreement and fragility penalties used to widen conservative bounds. -/
structure CertifiedTrustEstimate where
  lower : ℝ
  upper : ℝ
  coverage : ℝ
  disagreementPenalty : ℝ := 0
  fragilityPenalty : ℝ := 0
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1
  lower_le_upper : lower ≤ upper
  coverage_nonneg : 0 ≤ coverage
  coverage_le_one : coverage ≤ 1
  disagreementPenalty_nonneg : 0 ≤ disagreementPenalty
  fragilityPenalty_nonneg : 0 ≤ fragilityPenalty

/-- Certified finite posterior over latent regimes, together with an optional
posterior uncertainty radius. -/
structure CertifiedRegimePosterior (R : Type*) [Fintype R] [DecidableEq R] where
  weights : R → ℝ
  valid : ValidRegimeWeights weights
  uncertaintyRadius : ℝ := 0
  uncertaintyRadius_nonneg : 0 ≤ uncertaintyRadius

/-- Conservative lower bound on step admissibility after discounting by trust. -/
def trustAdjustedLowerBound
    (admissibility : CertifiedAdmissibilityEstimate)
    (trust : CertifiedTrustEstimate) : ℝ :=
  admissibility.lower * trust.lower

theorem CertifiedAdmissibilityEstimate.lower_le_one
    (estimate : CertifiedAdmissibilityEstimate) :
    estimate.lower ≤ 1 := by
  exact le_trans estimate.lower_le_upper estimate.upper_le_one

theorem CertifiedTrustEstimate.lower_le_one
    (estimate : CertifiedTrustEstimate) :
    estimate.lower ≤ 1 := by
  exact le_trans estimate.lower_le_upper estimate.upper_le_one

theorem CertifiedRegimePosterior.weights_nonneg
    (posterior : CertifiedRegimePosterior R) (r : R) :
    0 ≤ posterior.weights r := by
  exact posterior.valid.1 r

theorem CertifiedRegimePosterior.weights_sum_eq_one
    (posterior : CertifiedRegimePosterior R) :
    ∑ r, posterior.weights r = 1 := by
  exact posterior.valid.2

theorem CertifiedRegimePosterior.mixtureValue_nonneg_of_unit_interval
    (posterior : CertifiedRegimePosterior R)
    {q : R → ℝ}
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    0 ≤ mixtureValue posterior.weights q := by
  exact PLNRegimeMixtureTheorems.mixtureValue_nonneg_of_unit_interval
    (w := posterior.weights) (q := q) posterior.valid hq

theorem CertifiedRegimePosterior.mixtureValue_le_one_of_unit_interval
    (posterior : CertifiedRegimePosterior R)
    {q : R → ℝ}
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    mixtureValue posterior.weights q ≤ 1 := by
  exact PLNRegimeMixtureTheorems.mixtureValue_le_one_of_unit_interval
    (w := posterior.weights) (q := q) posterior.valid hq

theorem trustAdjustedLowerBound_nonneg
    (admissibility : CertifiedAdmissibilityEstimate)
    (trust : CertifiedTrustEstimate) :
    0 ≤ trustAdjustedLowerBound admissibility trust := by
  unfold trustAdjustedLowerBound
  exact mul_nonneg admissibility.lower_nonneg trust.lower_nonneg

theorem trustAdjustedLowerBound_le_admissibilityLower
    (admissibility : CertifiedAdmissibilityEstimate)
    (trust : CertifiedTrustEstimate) :
    trustAdjustedLowerBound admissibility trust ≤ admissibility.lower := by
  unfold trustAdjustedLowerBound
  have htrust : trust.lower ≤ 1 := trust.lower_le_one
  calc
    admissibility.lower * trust.lower ≤ admissibility.lower * 1 := by
      exact mul_le_mul_of_nonneg_left htrust admissibility.lower_nonneg
    _ = admissibility.lower := by ring

theorem trustAdjustedLowerBound_mono
    {a₁ a₂ : CertifiedAdmissibilityEstimate}
    {t₁ t₂ : CertifiedTrustEstimate}
    (ha : a₁.lower ≤ a₂.lower)
    (ht : t₁.lower ≤ t₂.lower) :
    trustAdjustedLowerBound a₁ t₁ ≤ trustAdjustedLowerBound a₂ t₂ := by
  unfold trustAdjustedLowerBound
  calc
    a₁.lower * t₁.lower ≤ a₂.lower * t₁.lower := by
      exact mul_le_mul_of_nonneg_right ha t₁.lower_nonneg
    _ ≤ a₂.lower * t₂.lower := by
      exact mul_le_mul_of_nonneg_left ht a₂.lower_nonneg

theorem CertifiedTrustEstimate.penalties_nonneg
    (trust : CertifiedTrustEstimate) :
    0 ≤ trust.disagreementPenalty + trust.fragilityPenalty := by
  exact add_nonneg trust.disagreementPenalty_nonneg trust.fragilityPenalty_nonneg

end Mettapedia.Logic
