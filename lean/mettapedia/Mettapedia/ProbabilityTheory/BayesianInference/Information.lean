import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mettapedia.InformationTheory.ShannonEntropy.Shannon1948

/-!
# Bayesian information gain

The expected change from prior to posterior is mutual information and the
expected decrease in Shannon entropy. Null observations contribute zero mass;
the conditional mass on such an observation is not a posterior distribution.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

variable {S O : Type*} [Fintype S] [Fintype O]

/-- Conditional mass. Only positive-evidence observations yield a distribution. -/
noncomputable def conditionalMass (prior : Prob S) (likelihood : S → Prob O)
    (o : O) (s : S) : ℝ :=
  (joint prior likelihood).1 (s, o) / (observationLaw prior likelihood).1 o

theorem conditionalMass_eq_posterior (prior : Prob S) (likelihood : S → Prob O)
    (o : O) (possible : 0 < evidence prior (fun s => (likelihood s).1 o)) (s : S) :
    conditionalMass prior likelihood o s =
      (posterior prior (fun s => (likelihood s).1 o)
        (fun s => (likelihood s).2.1 o) possible).1 s := rfl

/-- Expected divergence of the posterior from the prior, weighted by the joint law. -/
noncomputable def expectedInformationGain (prior : Prob S) (likelihood : S → Prob O) : ℝ :=
  ∑ o, ∑ s, (joint prior likelihood).1 (s, o) *
    Real.log (conditionalMass prior likelihood o s / prior.1 s)

/-- Posterior entropy averaged over observations, without conditioning on null events. -/
noncomputable def expectedPosteriorEntropy (prior : Prob S) (likelihood : S → Prob O) : ℝ :=
  -∑ o, ∑ s, (joint prior likelihood).1 (s, o) *
    Real.log (conditionalMass prior likelihood o s)

theorem joint_pos_prior_pos (prior : Prob S) (likelihood : S → Prob O) (s : S) (o : O)
    (h : 0 < (joint prior likelihood).1 (s, o)) : 0 < prior.1 s := by
  apply lt_of_le_of_ne (prior.2.1 s)
  intro heq
  simp only [joint_apply, ← heq, zero_mul] at h
  exact (lt_irrefl 0) h

theorem joint_pos_observation_pos (prior : Prob S) (likelihood : S → Prob O) (s : S) (o : O)
    (h : 0 < (joint prior likelihood).1 (s, o)) :
    0 < (observationLaw prior likelihood).1 o := by
  apply lt_of_lt_of_le h
  rw [← joint_observation_marginal]
  exact Finset.single_le_sum (fun t _ => (joint prior likelihood).2.1 (t, o)) (mem_univ s)

theorem expectedInformationGain_eq_joint_divergence (prior : Prob S)
    (likelihood : S → Prob O) :
    expectedInformationGain prior likelihood =
      klSum (joint prior likelihood).1
        (fun so => prior.1 so.1 * (observationLaw prior likelihood).1 so.2) := by
  rw [expectedInformationGain, klSum_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro s _
  unfold conditionalMass
  congr 2
  ring

section Laws

variable [DecidableEq S] [DecidableEq O]

omit [DecidableEq O] in
theorem joint_pushforward_fst (prior : Prob S) (likelihood : S → Prob O) :
    pushforward (joint prior likelihood).1 Prod.fst = prior.1 := by
  funext s
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [joint_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact joint_latent_marginal prior likelihood s

omit [DecidableEq S] in
theorem joint_pushforward_snd (prior : Prob S) (likelihood : S → Prob O) :
    pushforward (joint prior likelihood).1 Prod.snd = (observationLaw prior likelihood).1 := by
  funext o
  rw [pushforward_eq_sum_ite, Fintype.sum_prod_type]
  simp only [joint_apply]
  simp [observationLaw]

theorem joint_law2 (prior : Prob S) (likelihood : S → Prob O) :
    law2 (joint prior likelihood).1 Prod.fst Prod.snd = (joint prior likelihood).1 := by
  funext so
  exact pushforward_of_injective _ (fun so : S × O => (so.1, so.2))
    (fun _ _ h => h) so

/-- Bayesian information gain is the existing finite mutual-information quantity. -/
theorem expectedInformationGain_eq_mutualInfo (prior : Prob S) (likelihood : S → Prob O) :
    expectedInformationGain prior likelihood =
      mutualInfo (joint prior likelihood).1 Prod.fst Prod.snd := by
  rw [expectedInformationGain_eq_joint_divergence, mutualInfo,
    joint_law2, joint_pushforward_fst, joint_pushforward_snd]

theorem expectedInformationGain_nonneg (prior : Prob S) (likelihood : S → Prob O) :
    0 ≤ expectedInformationGain prior likelihood := by
  rw [expectedInformationGain_eq_mutualInfo]
  exact mutualInfo_nonneg _ (joint prior likelihood).2.1 (joint prior likelihood).2.2 _ _

end Laws

/-- On possible observations, the joint-weighted formula is expected posterior KL. -/
theorem expectedInformationGain_eq_expected_posterior_kl (prior : Prob S)
    (likelihood : S → Prob O)
    (possible : ∀ o, 0 < evidence prior (fun s => (likelihood s).1 o)) :
    expectedInformationGain prior likelihood = ∑ o,
      (observationLaw prior likelihood).1 o *
        klSum (posterior prior (fun s => (likelihood s).1 o)
          (fun s => (likelihood s).2.1 o) (possible o)).1 prior.1 := by
  unfold expectedInformationGain
  apply Finset.sum_congr rfl
  intro o _
  rw [klSum_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [conditionalMass_eq_posterior prior likelihood o (possible o)]
  rw [← mul_assoc]
  congr 1
  simp only [posterior_apply, observationLaw_apply, joint_apply]
  field_simp [(possible o).ne']

/-- Information gain is prior entropy minus expected posterior entropy. -/
theorem expectedInformationGain_eq_entropy_sub (prior : Prob S) (likelihood : S → Prob O) :
    expectedInformationGain prior likelihood =
      shannonEntropyFin S prior - expectedPosteriorEntropy prior likelihood := by
  have hterm : ∀ o s,
      (joint prior likelihood).1 (s, o) * Real.log (conditionalMass prior likelihood o s / prior.1 s) =
      (joint prior likelihood).1 (s, o) * Real.log (conditionalMass prior likelihood o s) -
        (joint prior likelihood).1 (s, o) * Real.log (prior.1 s) := by
    intro o s
    rcases ((joint prior likelihood).2.1 (s, o)).lt_or_eq with hpos | hzero
    · have hp := joint_pos_prior_pos prior likelihood s o hpos
      have ho := joint_pos_observation_pos prior likelihood s o hpos
      have hc : 0 < conditionalMass prior likelihood o s := div_pos hpos ho
      rw [Real.log_div hc.ne' hp.ne', mul_sub]
    · rw [← hzero]
      simp
  have hprior : (∑ o, ∑ s, (joint prior likelihood).1 (s, o) * Real.log (prior.1 s)) =
      ∑ s, prior.1 s * Real.log (prior.1 s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, joint_latent_marginal]
  unfold expectedInformationGain
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hprior]
  unfold shannonEntropyFin expectedPosteriorEntropy
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The posterior-entropy formula agrees with the entropy of each normalized posterior. -/
theorem expectedPosteriorEntropy_eq (prior : Prob S) (likelihood : S → Prob O)
    (possible : ∀ o, 0 < evidence prior (fun s => (likelihood s).1 o)) :
    expectedPosteriorEntropy prior likelihood = ∑ o,
      (observationLaw prior likelihood).1 o *
        shannonEntropyFin S (posterior prior (fun s => (likelihood s).1 o)
          (fun s => (likelihood s).2.1 o) (possible o)) := by
  unfold expectedPosteriorEntropy shannonEntropyFin
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [conditionalMass_eq_posterior prior likelihood o (possible o), ← mul_assoc]
  congr 1
  simp only [posterior_apply, observationLaw_apply, joint_apply]
  field_simp [(possible o).ne']

end Mettapedia.ProbabilityTheory.BayesianInference
