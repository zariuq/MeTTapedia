import Mettapedia.ProbabilityTheory.BayesianInference.Information

/-!
# Expected free energy from joint densities

A predictive model and a preferred model are independent inputs. The objective
is defined from their densities; outcome risk, posterior mismatch and information
gain are derived as a decomposition. Posterior mismatch can be removed only
when the preferred conditional model agrees with the predictive posterior.

References: Da Costa et al. (2020), *Active inference on discrete state-spaces:
a synthesis*, equations (13)--(16); Millidge, Tschantz and Buckley (2021),
*Whence the expected free energy?*
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

variable {S O : Type*} [Fintype S] [Fintype O]

/-- Expected free energy evaluated from the predictive prior and preferred joint density. -/
noncomputable def expectedFreeEnergy (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O) : ℝ :=
  ∑ o, ∑ s, (joint prior likelihood).1 (s, o) *
    (Real.log (prior.1 s) - Real.log ((joint preferredPrior preferredLikelihood).1 (s, o)))

/-- Expected negative log mass assigned to outcomes by the preferred model. -/
noncomputable def outcomeSurprise (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O) : ℝ :=
  -∑ o, (observationLaw prior likelihood).1 o *
    Real.log ((observationLaw preferredPrior preferredLikelihood).1 o)

/-- Expected mismatch between predictive and preferred posteriors. -/
noncomputable def expectedPosteriorMismatch (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O) : ℝ :=
  ∑ o, ∑ s, (joint prior likelihood).1 (s, o) *
    Real.log (conditionalMass prior likelihood o s /
      conditionalMass preferredPrior preferredLikelihood o s)

/-- Support compatibility is required for the finite density decomposition. -/
theorem expectedFreeEnergy_decomposition (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O)
    (support : ∀ s o, 0 < (joint prior likelihood).1 (s, o) →
      0 < (joint preferredPrior preferredLikelihood).1 (s, o)) :
    expectedFreeEnergy prior likelihood preferredPrior preferredLikelihood =
      outcomeSurprise prior likelihood preferredPrior preferredLikelihood +
        expectedPosteriorMismatch prior likelihood preferredPrior preferredLikelihood -
        expectedInformationGain prior likelihood := by
  have hterm : ∀ o s,
      (joint prior likelihood).1 (s, o) *
        (Real.log (prior.1 s) - Real.log ((joint preferredPrior preferredLikelihood).1 (s, o))) =
      -(joint prior likelihood).1 (s, o) *
          Real.log ((observationLaw preferredPrior preferredLikelihood).1 o) +
        (joint prior likelihood).1 (s, o) *
          Real.log (conditionalMass prior likelihood o s /
            conditionalMass preferredPrior preferredLikelihood o s) -
        (joint prior likelihood).1 (s, o) *
          Real.log (conditionalMass prior likelihood o s / prior.1 s) := by
    intro o s
    rcases ((joint prior likelihood).2.1 (s, o)).lt_or_eq with hpos | hzero
    · have hp := joint_pos_prior_pos prior likelihood s o hpos
      have ho := joint_pos_observation_pos prior likelihood s o hpos
      have hpreferred := support s o hpos
      have hpo := joint_pos_observation_pos preferredPrior preferredLikelihood s o hpreferred
      have hc : 0 < conditionalMass prior likelihood o s := div_pos hpos ho
      have hpc : 0 < conditionalMass preferredPrior preferredLikelihood o s :=
        div_pos hpreferred hpo
      rw [Real.log_div hc.ne' hpc.ne', Real.log_div hc.ne' hp.ne']
      unfold conditionalMass
      rw [Real.log_div hpos.ne' ho.ne', Real.log_div hpreferred.ne' hpo.ne']
      ring
    · rw [← hzero]
      simp
  have hrisk : (∑ o, ∑ s, -(joint prior likelihood).1 (s, o) *
      Real.log ((observationLaw preferredPrior preferredLikelihood).1 o)) =
      outcomeSurprise prior likelihood preferredPrior preferredLikelihood := by
    simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.sum_mul,
      joint_observation_marginal, outcomeSurprise]
  unfold expectedFreeEnergy
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hrisk]
  rfl

/-- Mismatch vanishes when the two posterior models agree on positive-mass events. -/
theorem expectedPosteriorMismatch_eq_zero (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O)
    (same : ∀ s o, 0 < (joint prior likelihood).1 (s, o) →
      conditionalMass prior likelihood o s = conditionalMass preferredPrior preferredLikelihood o s) :
    expectedPosteriorMismatch prior likelihood preferredPrior preferredLikelihood = 0 := by
  unfold expectedPosteriorMismatch
  apply Finset.sum_eq_zero
  intro o _
  apply Finset.sum_eq_zero
  intro s _
  rcases ((joint prior likelihood).2.1 (s, o)).lt_or_eq with hpos | hzero
  · have ho := joint_pos_observation_pos prior likelihood s o hpos
    have hc : 0 < conditionalMass prior likelihood o s := div_pos hpos ho
    rw [← same s o hpos, div_self hc.ne', Real.log_one, mul_zero]
  · rw [← hzero]
    simp

/-- Ambiguity is expected entropy of the observation likelihood. -/
noncomputable def ambiguity (prior : Prob S) (likelihood : S → Prob O) : ℝ :=
  ∑ s, prior.1 s * shannonEntropyFin O (likelihood s)

theorem expectedInformationGain_eq_outcome_entropy_sub (prior : Prob S)
    (likelihood : S → Prob O) :
    expectedInformationGain prior likelihood =
      shannonEntropyFin O (observationLaw prior likelihood) - ambiguity prior likelihood := by
  have hterm : ∀ s o,
      (joint prior likelihood).1 (s, o) *
        Real.log ((joint prior likelihood).1 (s, o) /
          (prior.1 s * (observationLaw prior likelihood).1 o)) =
      (joint prior likelihood).1 (s, o) * Real.log ((likelihood s).1 o) -
        (joint prior likelihood).1 (s, o) * Real.log ((observationLaw prior likelihood).1 o) := by
    intro s o
    rcases ((joint prior likelihood).2.1 (s, o)).lt_or_eq with hpos | hzero
    · have hp := joint_pos_prior_pos prior likelihood s o hpos
      have ho := joint_pos_observation_pos prior likelihood s o hpos
      have hl : (likelihood s).1 o ≠ 0 := by
        intro heq
        simp only [joint_apply, heq, mul_zero] at hpos
        exact (lt_irrefl 0) hpos
      rw [joint_apply, Real.log_div (mul_pos hp (lt_of_le_of_ne
        ((likelihood s).2.1 o) (Ne.symm hl))).ne' (mul_pos hp ho).ne',
        Real.log_mul hp.ne' hl, Real.log_mul hp.ne' ho.ne']
      ring
    · rw [← hzero]
      simp
  have hobs : (∑ s, ∑ o, (joint prior likelihood).1 (s, o) *
      Real.log ((observationLaw prior likelihood).1 o)) =
      ∑ o, (observationLaw prior likelihood).1 o *
        Real.log ((observationLaw prior likelihood).1 o) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, joint_observation_marginal]
  rw [expectedInformationGain_eq_joint_divergence, klSum_eq_sum, Fintype.sum_prod_type]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hobs]
  unfold ambiguity shannonEntropyFin
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg, joint_apply,
    ← Finset.mul_sum, mul_assoc]
  ring

/-- When the conditional model is shared, risk plus ambiguity equals the density objective. -/
theorem expectedFreeEnergy_risk_ambiguity (prior : Prob S) (likelihood : S → Prob O)
    (preferredPrior : Prob S) (preferredLikelihood : S → Prob O)
    (support : ∀ s o, 0 < (joint prior likelihood).1 (s, o) →
      0 < (joint preferredPrior preferredLikelihood).1 (s, o))
    (same : ∀ s o, 0 < (joint prior likelihood).1 (s, o) →
      conditionalMass prior likelihood o s = conditionalMass preferredPrior preferredLikelihood o s) :
    expectedFreeEnergy prior likelihood preferredPrior preferredLikelihood =
      klSum (observationLaw prior likelihood).1 (observationLaw preferredPrior preferredLikelihood).1 +
        ambiguity prior likelihood := by
  have hs : ∀ o, 0 < (observationLaw prior likelihood).1 o →
      0 < (observationLaw preferredPrior preferredLikelihood).1 o := by
    intro o ho
    rw [← joint_observation_marginal] at ho
    obtain ⟨s, _, hpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun s _ => (joint prior likelihood).2.1 (s, o))).mp ho
    exact joint_pos_observation_pos preferredPrior preferredLikelihood s o (support s o hpos)
  have hterm : ∀ o,
      (observationLaw prior likelihood).1 o * Real.log
        ((observationLaw prior likelihood).1 o / (observationLaw preferredPrior preferredLikelihood).1 o) =
      (observationLaw prior likelihood).1 o * Real.log ((observationLaw prior likelihood).1 o) -
        (observationLaw prior likelihood).1 o * Real.log ((observationLaw preferredPrior preferredLikelihood).1 o) := by
    intro o
    rcases ((observationLaw prior likelihood).2.1 o).lt_or_eq with ho | ho
    · rw [Real.log_div ho.ne' (hs o ho).ne', mul_sub]
    · rw [← ho]
      simp
  rw [expectedFreeEnergy_decomposition prior likelihood preferredPrior preferredLikelihood support,
    expectedPosteriorMismatch_eq_zero prior likelihood preferredPrior preferredLikelihood same,
    expectedInformationGain_eq_outcome_entropy_sub, add_zero, klSum_eq_sum]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  unfold outcomeSurprise shannonEntropyFin
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

end Mettapedia.ProbabilityTheory.BayesianInference
