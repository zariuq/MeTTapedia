import Mettapedia.Logic.PLNHigherOrderCertifiedEstimates
import Mathlib.Data.Real.Basic

/-!
# Higher-Order Calibration Contracts

This module formalizes theorem-facing calibration/certification wrappers for
learned higher-order estimates.  It does not formalize any particular learner;
it formalizes the contract required for learned outputs to feed certified
chaining theorems.
-/

namespace Mettapedia.Logic

/-- Minimal conformal-style certificate for a scalar prediction. -/
structure ConformalCertificate where
  alpha : ℝ
  quantile : ℝ
  alpha_nonneg : 0 ≤ alpha
  alpha_lt_one : alpha < 1
  quantile_nonneg : 0 ≤ quantile

def conformalCoverage (cert : ConformalCertificate) : ℝ :=
  1 - cert.alpha

noncomputable def conformalToAdmissibility
    (modelOutput : ℝ)
    (hmodel : 0 ≤ modelOutput ∧ modelOutput ≤ 1)
    (cert : ConformalCertificate) :
    CertifiedAdmissibilityEstimate where
  lower := max 0 (modelOutput - cert.quantile)
  upper := min 1 (modelOutput + cert.quantile)
  coverage := conformalCoverage cert
  errorBound := cert.quantile
  lower_nonneg := by
    exact le_max_left _ _
  upper_le_one := by
    exact min_le_left _ _
  lower_le_upper := by
    have hmain : modelOutput - cert.quantile ≤ modelOutput + cert.quantile := by
      linarith [cert.quantile_nonneg]
    refine le_min ?_ ?_
    · refine max_le ?_ ?_
      · norm_num
      · linarith [hmodel.2, cert.quantile_nonneg]
    · refine max_le ?_ ?_
      · linarith [hmodel.1, cert.quantile_nonneg]
      · exact hmain
  coverage_nonneg := by
    unfold conformalCoverage
    linarith [cert.alpha_lt_one]
  coverage_le_one := by
    unfold conformalCoverage
    linarith [cert.alpha_nonneg]
  errorBound_nonneg := cert.quantile_nonneg

theorem conformal_interval_valid
    (modelOutput : ℝ)
    (hmodel : 0 ≤ modelOutput ∧ modelOutput ≤ 1)
    (cert : ConformalCertificate) :
    0 ≤ (conformalToAdmissibility modelOutput hmodel cert).lower ∧
    (conformalToAdmissibility modelOutput hmodel cert).lower ≤
      (conformalToAdmissibility modelOutput hmodel cert).upper ∧
    (conformalToAdmissibility modelOutput hmodel cert).upper ≤ 1 := by
  exact ⟨(conformalToAdmissibility modelOutput hmodel cert).lower_nonneg,
    (conformalToAdmissibility modelOutput hmodel cert).lower_le_upper,
    (conformalToAdmissibility modelOutput hmodel cert).upper_le_one⟩

theorem conformalCoverage_eq_one_sub_alpha
    (cert : ConformalCertificate) :
    conformalCoverage cert = 1 - cert.alpha := by
  rfl

theorem conformalToAdmissibility_coverage_eq_one_sub_alpha
    (modelOutput : ℝ)
    (hmodel : 0 ≤ modelOutput ∧ modelOutput ≤ 1)
    (cert : ConformalCertificate) :
    (conformalToAdmissibility modelOutput hmodel cert).coverage = 1 - cert.alpha := by
  rfl

theorem conformalToAdmissibility_errorBound_eq_quantile
    (modelOutput : ℝ)
    (hmodel : 0 ≤ modelOutput ∧ modelOutput ≤ 1)
    (cert : ConformalCertificate) :
    (conformalToAdmissibility modelOutput hmodel cert).errorBound = cert.quantile := by
  rfl

theorem conformalToAdmissibility_errorBound_mono
    (modelOutput : ℝ)
    (hmodel : 0 ≤ modelOutput ∧ modelOutput ≤ 1)
    {c₁ c₂ : ConformalCertificate}
    (hquant : c₁.quantile ≤ c₂.quantile) :
    (conformalToAdmissibility modelOutput hmodel c₁).errorBound ≤
      (conformalToAdmissibility modelOutput hmodel c₂).errorBound := by
  simpa [conformalToAdmissibility] using hquant

end Mettapedia.Logic
