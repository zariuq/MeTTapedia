import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds
import Mettapedia.Cybernetics.ApproximateAdequacy.ControllerCoupling
import Mettapedia.ProbabilityTheory.BayesianInference.ExpectationBounds

/-!
# Bayesian adaptive decisions with independently certified errors

The posterior is determined by a statistical prior and a supplied likelihood. The
world has its own initial law, transition kernel and rewards. A prior coupling
and observation-compatible successor couplings relate the two processes. The
trial posterior and numerical evaluator introduce two further errors.

The resulting decision theorem derives its score bound from these three
certificates. It does not assume the final model-versus-world score estimate.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy.BayesianDecision

open Finset
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Enactive.Razor

variable {S T O A : Type*} [Fintype S] [Fintype T] [Fintype O]

/-- Statistical inference, predictive coupling and numerical errors bound the
actual score of every finite observation-contingent policy. -/
theorem score_error
    (prior trial : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy trial (fun s => prior.1 s * likelihood s))
    (worldPrior : Prob T)
    (model : A → S → Prob (S × O)) (world : A → T → Prob (T × O))
    (modelReward : S → ℝ) (worldReward : T → ℝ) (metric : S → T → ℝ)
    (reward_bound : ∀ s t, |modelReward s - worldReward t| ≤ metric s t)
    (step : ∀ a s t, ∃ coupling : Coupling (model a s).1 (world a t).1,
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t)
    (priorCoupling : Coupling (posterior prior likelihood nonneg possible).1 worldPrior.1)
    (M : ℝ) (M_nonneg : 0 ≤ M) (bounded : ∀ s, |modelReward s| ≤ M)
    {n : ℕ} (policy : ObservationPolicy O A n) (computed numericalError : ℝ)
    (numerical : |expect trial.1 (adaptiveValue model modelReward policy) - computed| ≤
      numericalError) :
    |expect worldPrior.1 (adaptiveValue world worldReward policy) - computed| ≤
      priorCoupling.cost metric +
        M * Real.sqrt (2 * (variationalFreeEnergy prior likelihood trial +
          Real.log (evidence prior likelihood))) + numericalError := by
  have prediction := abs_expected_adaptiveValue_sub_le model world modelReward worldReward
    metric reward_bound step (posterior prior likelihood nonneg possible) worldPrior
    priorCoupling policy
  rw [abs_sub_comm] at prediction
  have inference := abs_variational_expectation_sub_le prior trial likelihood
    (adaptiveValue model modelReward policy) nonneg possible support M_nonneg
    (adaptiveValue_abs_le model modelReward M bounded policy)
  rw [abs_sub_comm] at inference
  exact DecisionBounds.score_error_chain _ _ _ _ _ _ _ prediction inference numerical

/-- Choosing an approximately best admissible computed policy gives an actual
world regret bound derived from the lower-level certificates. -/
theorem regret
    (prior trial : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy trial (fun s => prior.1 s * likelihood s))
    (worldPrior : Prob T)
    (model : A → S → Prob (S × O)) (world : A → T → Prob (T × O))
    (modelReward : S → ℝ) (worldReward : T → ℝ) (metric : S → T → ℝ)
    (reward_bound : ∀ s t, |modelReward s - worldReward t| ≤ metric s t)
    (step : ∀ a s t, ∃ coupling : Coupling (model a s).1 (world a t).1,
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t)
    (priorCoupling : Coupling (posterior prior likelihood nonneg possible).1 worldPrior.1)
    (M : ℝ) (M_nonneg : 0 ≤ M) (bounded : ∀ s, |modelReward s| ≤ M)
    {n : ℕ} (admissible : ObservationPolicy O A n → Prop)
    (computed : ObservationPolicy O A n → ℝ) (numericalError η : ℝ)
    (numerical : ∀ p, admissible p →
      |expect trial.1 (adaptiveValue model modelReward p) - computed p| ≤ numericalError)
    (selected : ObservationPolicy O A n) (selected_admissible : admissible selected)
    (best : ∀ p, admissible p → computed p ≤ computed selected + η)
    (alternative : ObservationPolicy O A n) (alternative_admissible : admissible alternative) :
    expect worldPrior.1 (adaptiveValue world worldReward alternative) -
      expect worldPrior.1 (adaptiveValue world worldReward selected) ≤
      2 * (priorCoupling.cost metric +
        M * Real.sqrt (2 * (variationalFreeEnergy prior likelihood trial +
          Real.log (evidence prior likelihood))) + numericalError) + η := by
  apply DecisionBounds.regret_le_of_score_error
    (fun p => expect worldPrior.1 (adaptiveValue world worldReward p)) computed admissible
    selected _ η _ selected_admissible best alternative alternative_admissible
  intro p hp
  exact score_error prior trial likelihood nonneg possible support worldPrior model world
    modelReward worldReward metric reward_bound step priorCoupling M M_nonneg bounded p
    (computed p) numericalError (numerical p hp)

section DifferentControllers

variable {U B Candidate : Type*} [Fintype U]

/-- Controller changes enter the decision chain through their actual coupled
executions, including different actions and observations. -/
theorem controller_score_error
    (prior trial : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy trial (fun s => prior.1 s * likelihood s))
    (worldPrior : Prob T)
    (model : A → S → Prob (S × O)) (world : B → T → Prob (T × U))
    (modelReward : S → ℝ) (worldReward : T → ℝ) (metric : S → T → ℝ)
    (initial : Coupling (posterior prior likelihood nonneg possible).1 worldPrior.1)
    (M : ℝ) (M_nonneg : 0 ≤ M) (bounded : ∀ s, |modelReward s| ≤ M)
    {n : ℕ} (first : ObservationPolicy O A n) (second : ObservationPolicy U B n)
    (executions : ∀ s t, 0 < initial.weight s t →
      CoupledExecution model world modelReward worldReward metric first second s t)
    (computed numericalError : ℝ)
    (numerical : |expect trial.1 (adaptiveValue model modelReward first) - computed| ≤
      numericalError) :
    |expect worldPrior.1 (adaptiveValue world worldReward second) - computed| ≤
      initial.cost metric +
        M * Real.sqrt (2 * (variationalFreeEnergy prior likelihood trial +
          Real.log (evidence prior likelihood))) + numericalError := by
  have prediction := CoupledExecution.expected_bound first second
    (posterior prior likelihood nonneg possible) worldPrior initial executions
  rw [abs_sub_comm] at prediction
  have inference := abs_variational_expectation_sub_le prior trial likelihood
    (adaptiveValue model modelReward first) nonneg possible support M_nonneg
    (adaptiveValue_abs_le model modelReward M bounded first)
  rw [abs_sub_comm] at inference
  exact DecisionBounds.score_error_chain _ _ _ _ _ _ _ prediction inference numerical

/-- Candidate policies may be implemented by different observation/action
interfaces while retaining a decision guarantee for the actual world score. -/
theorem controller_regret
    (prior trial : Prob S) (likelihood : S → ℝ)
    (nonneg : ∀ s, 0 ≤ likelihood s) (possible : 0 < evidence prior likelihood)
    (support : SupportedBy trial (fun s => prior.1 s * likelihood s))
    (worldPrior : Prob T)
    (model : A → S → Prob (S × O)) (world : B → T → Prob (T × U))
    (modelReward : S → ℝ) (worldReward : T → ℝ) (metric : S → T → ℝ)
    (initial : Coupling (posterior prior likelihood nonneg possible).1 worldPrior.1)
    (M : ℝ) (M_nonneg : 0 ≤ M) (bounded : ∀ s, |modelReward s| ≤ M)
    {n : ℕ} (first : Candidate → ObservationPolicy O A n)
    (second : Candidate → ObservationPolicy U B n) (admissible : Candidate → Prop)
    (executions : ∀ c, admissible c → ∀ s t, 0 < initial.weight s t →
      CoupledExecution model world modelReward worldReward metric (first c) (second c) s t)
    (computed : Candidate → ℝ) (numericalError η : ℝ)
    (numerical : ∀ c, admissible c →
      |expect trial.1 (adaptiveValue model modelReward (first c)) - computed c| ≤ numericalError)
    (selected : Candidate) (selected_admissible : admissible selected)
    (best : ∀ c, admissible c → computed c ≤ computed selected + η)
    (alternative : Candidate) (alternative_admissible : admissible alternative) :
    expect worldPrior.1 (adaptiveValue world worldReward (second alternative)) -
      expect worldPrior.1 (adaptiveValue world worldReward (second selected)) ≤
      2 * (initial.cost metric +
        M * Real.sqrt (2 * (variationalFreeEnergy prior likelihood trial +
          Real.log (evidence prior likelihood))) + numericalError) + η := by
  apply DecisionBounds.regret_le_of_score_error
    (fun c => expect worldPrior.1 (adaptiveValue world worldReward (second c)))
    computed admissible selected _ η _ selected_admissible best alternative alternative_admissible
  intro c hc
  exact controller_score_error prior trial likelihood nonneg possible support worldPrior model world
    modelReward worldReward metric initial M M_nonneg bounded (first c) (second c)
    (executions c hc) (computed c) numericalError (numerical c hc)

end DifferentControllers

end Mettapedia.Cybernetics.ApproximateAdequacy.BayesianDecision
