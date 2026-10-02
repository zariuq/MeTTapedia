import Mettapedia.Algorithms.FiniteKLCertificate
import Mettapedia.Algorithms.FiniteExecutionCoupling
import Mettapedia.Algorithms.FiniteAdaptivePolicy
import Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

/-!
# Checking an inference-to-action certificate

Independent rational inputs describe conditioning, approximate inference, the
model, the world and their controllers. The checker validates those inputs and
the tables connecting them. Acceptance implies a score interval for each
admissible candidate and a world-regret bound for the selected candidate.
-/

namespace Mettapedia.Algorithms.FiniteBayesianDecision

open Mettapedia.InformationTheory
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Algorithms.FiniteBayes

variable {S T O U A B C : Type*}
  [Fintype S] [Fintype T] [Fintype O] [Fintype U]

def checkPosterior (prior likelihood output : S → ℚ) : Bool :=
  match update prior likelihood with
  | none => false
  | some computed => decide (∀ s, computed s = output s)

theorem checkPosterior_sound (prior likelihood output : S → ℚ)
    (accepted : checkPosterior prior likelihood output = true) :
    update prior likelihood = some output := by
  cases result : update prior likelihood with
  | none => simp [checkPosterior, result] at accepted
  | some computed =>
      have same : computed = output := by
        apply funext
        simpa only [checkPosterior, result, decide_eq_true_eq] using accepted
      exact congrArg some same

def policyScore (prior : S → ℚ) (kernel : A → S → S × O → ℚ) (reward : S → ℚ)
    {n : ℕ} (policy : ObservationPolicy O A n) : ℚ :=
  ∑ s, prior s * FiniteAdaptivePolicy.value kernel reward policy s

theorem policyScore_cast (prior : S → ℚ) (kernel : A → S → S × O → ℚ) (reward : S → ℚ)
    (priorValid : IsDistribution prior) (kernelValid : ∀ a s, IsDistribution (kernel a s))
    {n : ℕ} (policy : ObservationPolicy O A n) :
    (policyScore prior kernel reward policy : ℝ) =
      expect (realDistribution prior priorValid).1
        (adaptiveValue (fun a s => realDistribution (kernel a s) (kernelValid a s))
          (fun s => (reward s : ℝ)) policy) := by
  simp only [policyScore, Rat.cast_sum, Rat.cast_mul, expect, realDistribution]
  apply Finset.sum_congr rfl
  intro s _
  rw [FiniteAdaptivePolicy.value_cast kernel reward kernelValid policy s]
  rfl

/-- All certificate fields are ordinary data, including normalization and error budgets. -/
structure Instance (S T O U A B C : Type*) (horizon : ℕ) where
  prior : S → ℚ
  likelihood : S → ℚ
  posterior : S → ℚ
  trial : S → ℚ
  worldPrior : T → ℚ
  model : A → S → S × O → ℚ
  world : B → T → T × U → ℚ
  modelReward : S → ℚ
  worldReward : T → ℚ
  metric : S → T → ℚ
  modelPolicy : C → ObservationPolicy O A horizon
  worldPolicy : C → ObservationPolicy U B horizon
  initial : S → T → ℚ
  execution : C → S → T → FiniteExecutionCoupling.Tables S T O U horizon
  magnitude : ℚ
  terms : ℕ
  predictionError : C → ℚ
  inferenceError : C → ℚ
  numericalError : C → ℚ
  computed : C → ℚ
  uniformError : ℚ
  slack : ℚ
  candidates : List C
  admissible : C → Bool
  selected : C

namespace Instance

variable {n : ℕ}

def radius (d : Instance S T O U A B C n) (c : C) : ℚ :=
  d.predictionError c + d.inferenceError c + d.numericalError c

def worldScore (d : Instance S T O U A B C n) (c : C) : ℚ :=
  policyScore d.worldPrior d.world d.worldReward (d.worldPolicy c)

def predictedScore (d : Instance S T O U A B C n) (c : C) : ℚ :=
  policyScore d.posterior d.model d.modelReward (d.modelPolicy c)

def trialScore (d : Instance S T O U A B C n) (c : C) : ℚ :=
  policyScore d.trial d.model d.modelReward (d.modelPolicy c)

variable [Fintype A] [Fintype B] [DecidableEq C]

/-- The acceptance conditions refer to raw checks, not to the final score bound. -/
def Conditions (d : Instance S T O U A B C n) : Prop :=
  checkPosterior d.prior d.likelihood d.posterior = true ∧
  checkDistribution d.worldPrior = true ∧
  FiniteExecutionCoupling.checkKernels d.model d.world = true ∧
  (∀ s, |d.modelReward s| ≤ d.magnitude) ∧
  FiniteCoupling.check d.posterior d.worldPrior d.initial = true ∧
  d.selected ∈ d.candidates ∧ 0 ≤ d.slack ∧
  ∀ c ∈ d.candidates,
    d.admissible c = true ∧
    FiniteKLCertificate.check d.trial d.posterior d.magnitude (d.inferenceError c) d.terms = true ∧
    0 ≤ d.predictionError c ∧ 0 ≤ d.numericalError c ∧
    (∑ s, ∑ t, d.initial s t * d.metric s t) ≤ d.predictionError c ∧
    (∀ s t, 0 < d.initial s t →
      FiniteExecutionCoupling.check d.model d.world d.modelReward d.worldReward d.metric
        (d.modelPolicy c) (d.worldPolicy c) s t (d.execution c s t) = true) ∧
    |d.trialScore c - d.computed c| ≤ d.numericalError c ∧
    d.radius c ≤ d.uniformError ∧ d.computed c ≤ d.computed d.selected + d.slack

instance (d : Instance S T O U A B C n) : Decidable d.Conditions := by
  unfold Conditions
  infer_instance

def check (d : Instance S T O U A B C n) : Bool := decide d.Conditions

theorem accepted_conditions (d : Instance S T O U A B C n)
    (accepted : d.check = true) : d.Conditions := of_decide_eq_true accepted

/-- Raw coupled tables bound prediction error for the controllers actually selected. -/
theorem prediction_bound (d : Instance S T O U A B C n)
    (accepted : d.check = true) (c : C) (member : c ∈ d.candidates) :
    |(d.worldScore c : ℝ) - (d.predictedScore c : ℝ)| ≤ (d.predictionError c : ℝ) := by
  obtain ⟨posteriorChecked, worldChecked, kernelsChecked, _, initialChecked, _, _, all⟩ :=
    d.accepted_conditions accepted
  obtain ⟨_, _, _, _, initialBound, executionChecked, _, _, _⟩ := all c member
  have posteriorValid := update_sound d.prior d.likelihood d.posterior
    (checkPosterior_sound _ _ _ posteriorChecked)
  have worldValid := (checkDistribution_iff d.worldPrior).mp worldChecked
  obtain ⟨modelValid, worldKernelValid⟩ :=
    (FiniteExecutionCoupling.checkKernels_iff d.model d.world).mp kernelsChecked
  let coupling := FiniteCoupling.realCoupling _ _ _ initialChecked
  have executions : ∀ s t, 0 < coupling.weight s t →
      CoupledExecution
        (fun a s => realDistribution (d.model a s) (modelValid a s))
        (fun b t => realDistribution (d.world b t) (worldKernelValid b t))
        (fun s => (d.modelReward s : ℝ)) (fun t => (d.worldReward t : ℝ))
        (fun s t => (d.metric s t : ℝ)) (d.modelPolicy c) (d.worldPolicy c) s t := by
    intro s t positive
    apply FiniteExecutionCoupling.check_sound d.model d.world modelValid worldKernelValid
      d.modelReward d.worldReward d.metric (d.modelPolicy c) (d.worldPolicy c)
      s t (d.execution c s t)
    apply executionChecked s t
    change 0 < (d.initial s t : ℝ) at positive
    exact_mod_cast positive
  have bound := CoupledExecution.expected_bound (d.modelPolicy c) (d.worldPolicy c)
    (realDistribution d.posterior posteriorValid) (realDistribution d.worldPrior worldValid)
    coupling executions
  rw [← policyScore_cast d.posterior d.model d.modelReward posteriorValid modelValid,
    ← policyScore_cast d.worldPrior d.world d.worldReward worldValid worldKernelValid] at bound
  have costBound : coupling.cost (fun s t => (d.metric s t : ℝ)) ≤
      (d.predictionError c : ℝ) := by
    change (∑ s, ∑ t, (d.initial s t : ℝ) * (d.metric s t : ℝ)) ≤ _
    exact_mod_cast initialBound
  rw [abs_sub_comm] at bound
  exact bound.trans costBound

/-- Inference, predictive adequacy and numerical evaluation compose without a score oracle. -/
theorem score_error (d : Instance S T O U A B C n)
    (accepted : d.check = true) (c : C) (member : c ∈ d.candidates) :
    |(d.worldScore c : ℝ) - (d.computed c : ℝ)| ≤ (d.radius c : ℝ) := by
  obtain ⟨_, _, kernelsChecked, rewardBound, _, _, _, all⟩ := d.accepted_conditions accepted
  obtain ⟨_, inferenceChecked, _, _, _, _, numericalBound, _, _⟩ := all c member
  obtain ⟨trialValid, posteriorValid, _, _, _, _⟩ :=
    FiniteKLCertificate.accepted_data _ _ _ _ _ inferenceChecked
  have modelValid := ((FiniteExecutionCoupling.checkKernels_iff d.model d.world).mp
    kernelsChecked).1
  have bounded : ∀ s, |adaptiveValue
      (fun a s => realDistribution (d.model a s) (modelValid a s))
      (fun s => (d.modelReward s : ℝ)) (d.modelPolicy c) s| ≤ (d.magnitude : ℝ) :=
    adaptiveValue_abs_le _ _ _ (fun s => by exact_mod_cast rewardBound s) _
  have inference := FiniteKLCertificate.expectation_error d.trial d.posterior trialValid
    posteriorValid d.magnitude (d.inferenceError c) d.terms inferenceChecked _ bounded
  change |expect (realDistribution d.trial trialValid).1 _ -
    expect (realDistribution d.posterior posteriorValid).1 _| ≤ _ at inference
  rw [← policyScore_cast d.trial d.model d.modelReward trialValid modelValid,
    ← policyScore_cast d.posterior d.model d.modelReward posteriorValid modelValid] at inference
  have numericalR : |(d.trialScore c : ℝ) - (d.computed c : ℝ)| ≤
      (d.numericalError c : ℝ) := by exact_mod_cast numericalBound
  simpa only [radius, Rat.cast_add] using DecisionBounds.score_error_chain
    (d.worldScore c) (d.predictedScore c) (d.trialScore c) (d.computed c)
    (d.predictionError c) (d.inferenceError c) (d.numericalError c)
    (d.prediction_bound accepted c member)
    (by simpa only [predictedScore, trialScore, abs_sub_comm] using inference) numericalR

/-- Every candidate has its own certified world-score interval. -/
theorem score_interval (d : Instance S T O U A B C n)
    (accepted : d.check = true) (c : C) (member : c ∈ d.candidates) :
    ((d.computed c - d.radius c : ℚ) : ℝ) ≤ (d.worldScore c : ℝ) ∧
      (d.worldScore c : ℝ) ≤ ((d.computed c + d.radius c : ℚ) : ℝ) := by
  have bound := abs_le.mp (d.score_error accepted c member)
  push_cast
  constructor <;> linarith

/-- Checked approximate maximization loses at most `2ε + η` in the independent world. -/
theorem regret (d : Instance S T O U A B C n) (accepted : d.check = true)
    (alternative : C) (member : alternative ∈ d.candidates) :
    d.admissible d.selected = true ∧
      (d.worldScore alternative : ℝ) - (d.worldScore d.selected : ℝ) ≤
        2 * (d.uniformError : ℝ) + (d.slack : ℝ) := by
  obtain ⟨_, _, _, _, _, selectedMember, _, all⟩ := d.accepted_conditions accepted
  refine ⟨(all d.selected selectedMember).1, ?_⟩
  apply DecisionBounds.regret_le_of_score_error
    (fun c => (d.worldScore c : ℝ)) (fun c => (d.computed c : ℝ))
    (fun c => c ∈ d.candidates) d.selected (d.uniformError : ℝ) (d.slack : ℝ)
    _ selectedMember _ alternative member
  · intro c member
    exact (d.score_error accepted c member).trans (by exact_mod_cast (all c member).2.2.2.2.2.2.2.1)
  · intro c member
    exact_mod_cast (all c member).2.2.2.2.2.2.2.2

end Instance
end Mettapedia.Algorithms.FiniteBayesianDecision
