import Mettapedia.ProbabilityTheory.BayesianInference.Information
import Mettapedia.ProbabilityTheory.BayesianInference.InformationLaws
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.DecisionValueOfInformation
import Mathlib.Data.Finset.Max

/-!
# Bayesian experiments and downstream decision value

The joint law is built from the same prior and observation kernel used for
information gain. A policy may ignore its observation. Finite optimal selection
therefore gives nonnegative gross decision value, while acquisition cost and
the declared loss can make an informative experiment worthless.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Mettapedia.InformationTheory
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.DecisionValueOfInformation

variable {S O A : Type*} [Fintype S] [Fintype O]

noncomputable def decisionExperiment (prior : Prob S) (likelihood : S → Prob O)
    (loss : S → A → ℝ) : DecisionExperiment S O A :=
  ⟨fun s o => (joint prior likelihood).1 (s, o), loss⟩

theorem staticRisk_eq_prior_risk (prior : Prob S) (likelihood : S → Prob O)
    (loss : S → A → ℝ) (action : A) :
    staticRisk (decisionExperiment prior likelihood loss) action =
      ∑ s, prior.1 s * loss s action := by
  simp only [staticRisk, decisionExperiment, joint_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_mul, ← Finset.mul_sum, (likelihood s).2.2, mul_one]

/-- An optimum is constructed from the actual finite policy family. -/
theorem finite_optimal_signal_policy [Fintype A] [Nonempty A]
    (prior : Prob S) (likelihood : S → Prob O) (loss : S → A → ℝ) :
    ∃ policy : O → A, IsRiskMinimizing (decisionExperiment prior likelihood loss) policy := by
  classical
  have inhabited : (Finset.univ : Finset (O → A)).Nonempty :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty A), Finset.mem_univ _⟩
  obtain ⟨policy, _, optimal⟩ := Finset.exists_min_image Finset.univ
    (signalRisk (decisionExperiment prior likelihood loss)) inhabited
  exact ⟨policy, fun alternative => optimal alternative (Finset.mem_univ _)⟩

theorem optimal_experiment_gross_nonnegative (prior : Prob S) (likelihood : S → Prob O)
    (loss : S → A → ℝ) (baseline : A) (policy : O → A)
    (optimal : IsRiskMinimizing (decisionExperiment prior likelihood loss) policy) :
    0 ≤ grossDecisionValue (decisionExperiment prior likelihood loss) baseline policy :=
  grossDecisionValue_nonneg_of_optimal _ baseline policy optimal

/-- Information gain does not help a task whose loss is identically zero. -/
theorem zero_loss_acquisition_has_negative_value (prior : Prob S) (likelihood : S → Prob O)
    (baseline : A) (policy : O → A) (cost : ℝ) (positive : 0 < cost) :
    netDecisionValue (decisionExperiment prior likelihood (fun _ _ => 0))
      baseline policy cost < 0 := by
  simpa [netDecisionValue, grossDecisionValue, staticRisk, signalRisk, decisionExperiment] using
    neg_neg_of_pos positive

/-- A perfectly informative fair-bit experiment is harmful for the zero-loss
task once its positive acquisition cost is charged. -/
theorem positive_information_negative_task_value :
    0 < expectedInformationGain binaryUniform Prob.dirac ∧
      netDecisionValue (decisionExperiment binaryUniform Prob.dirac
        (fun _ (_ : Unit) => 0)) () (fun _ => ()) 1 < 0 := by
  constructor
  · rw [reveal_information_eq_log_two]
    exact Real.log_pos (by norm_num)
  · exact zero_loss_acquisition_has_negative_value _ _ _ _ _ (by norm_num)

end Mettapedia.ProbabilityTheory.BayesianInference
