import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# Bayesian reduction by a change of prior

The likelihood stays fixed. The new prior is required to be supported by the
old prior. Under those hypotheses, the evidence ratio and the new posterior
can be recovered from the old posterior using the prior density ratio.

Reference: Friston, Parr and Zeidman, *Bayesian model reduction* (2018).
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory

variable {S : Type*} [Fintype S]

/-- The finite Radon--Nikodym ratio for changing a prior. -/
noncomputable def priorRatio (old new : Prob S) (s : S) : ℝ := new.1 s / old.1 s

theorem priorRatio_nonneg (old new : Prob S) (s : S) : 0 ≤ priorRatio old new s :=
  div_nonneg (new.2.1 s) (old.2.1 s)

theorem mul_priorRatio (old new : Prob S)
    (support : ∀ s, 0 < new.1 s → 0 < old.1 s) (s : S) :
    old.1 s * priorRatio old new s = new.1 s := by
  unfold priorRatio
  by_cases hs : new.1 s = 0
  · simp [hs]
  · have hp : 0 < old.1 s := support s
      (lt_of_le_of_ne (new.2.1 s) (Ne.symm hs))
    field_simp

/-- The ratio of model evidences is an expectation under the old posterior. -/
theorem evidence_ratio_eq_posterior_expectation (old new : Prob S)
    (likelihood : S → ℝ) (nonneg : ∀ s, 0 ≤ likelihood s)
    (possible : 0 < evidence old likelihood)
    (support : ∀ s, 0 < new.1 s → 0 < old.1 s) :
    evidence (posterior old likelihood nonneg possible) (priorRatio old new) =
      evidence new likelihood / evidence old likelihood := by
  rw [evidence_posterior]
  congr 1
  unfold evidence
  apply Finset.sum_congr rfl
  intro s _
  calc old.1 s * (likelihood s * priorRatio old new s) =
      (old.1 s * priorRatio old new s) * likelihood s := by ring
    _ = new.1 s * likelihood s := by rw [mul_priorRatio old new support]

/-- Reweighting the old posterior recovers the independently defined new posterior. -/
theorem posterior_prior_reduction (old new : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s)
    (old_possible : 0 < evidence old likelihood)
    (new_possible : 0 < evidence new likelihood)
    (support : ∀ s, 0 < new.1 s → 0 < old.1 s) :
    posterior (posterior old likelihood nonneg old_possible) (priorRatio old new)
      (priorRatio_nonneg old new)
      (by
        rw [evidence_ratio_eq_posterior_expectation old new likelihood nonneg old_possible support]
        exact div_pos new_possible old_possible) =
    posterior new likelihood nonneg new_possible := by
  apply Subtype.ext
  funext s
  simp only [posterior_apply,
    evidence_ratio_eq_posterior_expectation old new likelihood nonneg old_possible support]
  calc (old.1 s * likelihood s / evidence old likelihood) * priorRatio old new s /
        (evidence new likelihood / evidence old likelihood) =
      (old.1 s * priorRatio old new s) * likelihood s / evidence new likelihood := by
        field_simp
    _ = new.1 s * likelihood s / evidence new likelihood := by
        rw [mul_priorRatio old new support]

/-- Prior changes compose as density ratios on the support of the final prior. -/
theorem priorRatio_comp (first second third : Prob S)
    (support : ∀ s, 0 < third.1 s → 0 < second.1 s) (s : S) :
    priorRatio first second s * priorRatio second third s = priorRatio first third s := by
  unfold priorRatio
  by_cases hs : third.1 s = 0
  · simp [hs]
  · have hsecond : second.1 s ≠ 0 := ne_of_gt
      (support s (lt_of_le_of_ne (third.2.1 s) (Ne.symm hs)))
    field_simp

/-- Sequential prior reductions recover the same posterior as the direct reduction. -/
theorem posterior_prior_reduction_comp (first second third : Prob S)
    (likelihood : S → ℝ) (nonneg : ∀ s, 0 ≤ likelihood s)
    (first_possible : 0 < evidence first likelihood)
    (second_possible : 0 < evidence second likelihood)
    (third_possible : 0 < evidence third likelihood)
    (second_support : ∀ s, 0 < second.1 s → 0 < first.1 s)
    (third_support : ∀ s, 0 < third.1 s → 0 < second.1 s) :
    posterior
      (posterior (posterior first likelihood nonneg first_possible) (priorRatio first second)
        (priorRatio_nonneg first second)
        (by
          rw [evidence_ratio_eq_posterior_expectation first second likelihood nonneg
            first_possible second_support]
          exact div_pos second_possible first_possible))
      (priorRatio second third) (priorRatio_nonneg second third)
      (by
        rw [posterior_prior_reduction first second likelihood nonneg first_possible
          second_possible second_support,
          evidence_ratio_eq_posterior_expectation second third likelihood nonneg
            second_possible third_support]
        exact div_pos third_possible second_possible) =
    posterior third likelihood nonneg third_possible := by
  simp only [posterior_prior_reduction first second likelihood nonneg first_possible
    second_possible second_support]
  exact posterior_prior_reduction second third likelihood nonneg second_possible
    third_possible third_support

/-- Supported reduction preserves the independently defined new posterior's
predictive law for every stochastic consumer kernel. -/
theorem posterior_predictive_reduction {O : Type*} [Fintype O]
    (old new : Prob S) (likelihood : S → ℝ) (consumer : S → Prob O)
    (nonneg : ∀ s, 0 ≤ likelihood s)
    (old_possible : 0 < evidence old likelihood)
    (new_possible : 0 < evidence new likelihood)
    (support : ∀ s, 0 < new.1 s → 0 < old.1 s) :
    observationLaw
      (posterior (posterior old likelihood nonneg old_possible) (priorRatio old new)
        (priorRatio_nonneg old new)
        (by
          rw [evidence_ratio_eq_posterior_expectation old new likelihood nonneg old_possible support]
          exact div_pos new_possible old_possible)) consumer =
      observationLaw (posterior new likelihood nonneg new_possible) consumer := by
  rw [posterior_prior_reduction old new likelihood nonneg old_possible new_possible support]

end Mettapedia.ProbabilityTheory.BayesianInference
