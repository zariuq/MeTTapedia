import Mettapedia.InformationTheory.FiniteProbability
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite Bayesian conditioning

Conditioning is normalization of the independently given prior and likelihood.
Positive evidence is required: an impossible observation does not define a
posterior probability distribution. Likelihoods need not sum to one; they can
also express successive observations or a change of prior.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory

variable {S O : Type*} [Fintype S] [Fintype O]

/-- The normalizing constant of a likelihood under a prior. -/
noncomputable def evidence (prior : Prob S) (likelihood : S → ℝ) : ℝ :=
  ∑ s, prior.1 s * likelihood s

theorem evidence_nonneg (prior : Prob S) (likelihood : S → ℝ)
    (h : ∀ s, 0 ≤ likelihood s) : 0 ≤ evidence prior likelihood :=
  Finset.sum_nonneg fun s _ => mul_nonneg (prior.2.1 s) (h s)

@[simp] theorem evidence_one (prior : Prob S) : evidence prior (fun _ => 1) = 1 := by
  simp [evidence, prior.2.2]

theorem evidence_scale (prior : Prob S) (likelihood : S → ℝ) (c : ℝ) :
    evidence prior (fun s => c * likelihood s) = c * evidence prior likelihood := by
  unfold evidence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Bayesian conditioning, defined only when the observation has positive evidence. -/
noncomputable def posterior (prior : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood) : Prob S :=
  ⟨fun s => prior.1 s * likelihood s / evidence prior likelihood,
    (fun s => div_nonneg (mul_nonneg (prior.2.1 s) (nonneg s)) possible.le), by
      rw [← Finset.sum_div, ← evidence, div_self (ne_of_gt possible)]⟩

@[simp] theorem posterior_apply (prior : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood) (s : S) :
    (posterior prior likelihood nonneg possible).1 s =
      prior.1 s * likelihood s / evidence prior likelihood := rfl

theorem posterior_pos_iff (prior : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood) (s : S) :
    0 < (posterior prior likelihood nonneg possible).1 s ↔
      0 < prior.1 s ∧ 0 < likelihood s := by
  rw [posterior_apply, div_pos_iff_of_pos_right possible]
  constructor
  · intro h
    constructor
    · exact lt_of_le_of_ne (prior.2.1 s) (by
        intro heq
        rw [← heq, zero_mul] at h
        exact (lt_irrefl 0) h)
    · exact lt_of_le_of_ne (nonneg s) (by
        intro heq
        rw [← heq, mul_zero] at h
        exact (lt_irrefl 0) h)
  · rintro ⟨hp, hl⟩
    exact mul_pos hp hl

@[simp] theorem posterior_one (prior : Prob S) :
    posterior prior (fun _ => 1) (fun _ => by norm_num)
      (by rw [evidence_one]; norm_num) = prior := by
  apply Subtype.ext
  funext s
  simp

theorem posterior_scale (prior : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (c : ℝ) (hc : 0 < c) :
    posterior prior (fun s => c * likelihood s)
      (fun s => mul_nonneg hc.le (nonneg s))
      (by rw [evidence_scale]; exact mul_pos hc possible) =
    posterior prior likelihood nonneg possible := by
  apply Subtype.ext
  funext s
  simp only [posterior_apply, evidence_scale]
  field_simp

theorem evidence_posterior (prior : Prob S) (first second : S → ℝ)
    (nonneg : ∀ s, 0 ≤ first s) (possible : 0 < evidence prior first) :
    evidence (posterior prior first nonneg possible) second =
      evidence prior (fun s => first s * second s) / evidence prior first := by
  simp only [evidence, posterior_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Sequential conditioning equals conditioning on the product likelihood. -/
theorem posterior_posterior (prior : Prob S) (first second : S → ℝ)
    (first_nonneg : ∀ s, 0 ≤ first s) (second_nonneg : ∀ s, 0 ≤ second s)
    (first_possible : 0 < evidence prior first)
    (second_possible : 0 < evidence (posterior prior first first_nonneg first_possible) second) :
    posterior (posterior prior first first_nonneg first_possible) second
      second_nonneg second_possible =
    posterior prior (fun s => first s * second s)
      (fun s => mul_nonneg (first_nonneg s) (second_nonneg s))
      (by
        have h := second_possible
        rw [evidence_posterior] at h
        exact (div_pos_iff_of_pos_right first_possible).mp h) := by
  apply Subtype.ext
  funext s
  simp only [posterior_apply, evidence_posterior]
  have hne : evidence prior first ≠ 0 := ne_of_gt first_possible
  field_simp

/-- The joint law of a latent state and an observation kernel. -/
noncomputable def joint (prior : Prob S) (likelihood : S → Prob O) : Prob (S × O) :=
  ⟨fun so => prior.1 so.1 * (likelihood so.1).1 so.2,
    (fun so => mul_nonneg (prior.2.1 so.1) ((likelihood so.1).2.1 so.2)), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, fun s => (likelihood s).2.2, mul_one]
      exact prior.2.2⟩

@[simp] theorem joint_apply (prior : Prob S) (likelihood : S → Prob O) (s : S) (o : O) :
    (joint prior likelihood).1 (s, o) = prior.1 s * (likelihood s).1 o := rfl

/-- The observation marginal of the joint law. -/
noncomputable def observationLaw (prior : Prob S) (likelihood : S → Prob O) : Prob O :=
  Prob.bind prior likelihood

@[simp] theorem observationLaw_apply (prior : Prob S) (likelihood : S → Prob O) (o : O) :
    (observationLaw prior likelihood).1 o = evidence prior (fun s => (likelihood s).1 o) := rfl

theorem joint_latent_marginal (prior : Prob S) (likelihood : S → Prob O) (s : S) :
    ∑ o, (joint prior likelihood).1 (s, o) = prior.1 s := by
  simp only [joint_apply, ← Finset.mul_sum, (likelihood s).2.2, mul_one]

theorem joint_observation_marginal (prior : Prob S) (likelihood : S → Prob O) (o : O) :
    ∑ s, (joint prior likelihood).1 (s, o) = (observationLaw prior likelihood).1 o := rfl

end Mettapedia.ProbabilityTheory.BayesianInference
