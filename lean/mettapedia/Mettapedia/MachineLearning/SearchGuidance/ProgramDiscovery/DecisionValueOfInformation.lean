import Mathlib.Tactic

/-!
# Decision value of information

An observation has operational value only through the reduction in downstream
decision loss that it enables.  This file isolates the finite decision-theory
boundary.  A policy receiving a signal can always ignore it, so an optimal
signal-conditioned policy is no worse than any fixed action.  Acquisition is
strictly worthwhile exactly when that gross loss reduction exceeds its cost.

Prediction residual is not a substitute for this quantity.  An explicit pair
of candidates reverses residual and net-value rankings: the larger residual
has negative acquisition value while the smaller residual has positive value.
Thus residual-, entropy-, or surprise-based queues require a separate bridge
to the safety-relevant loss they are intended to reduce.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace DecisionValueOfInformation

open scoped BigOperators

noncomputable section

/-- Finite joint observation model together with a downstream decision loss. -/
structure DecisionExperiment (World Signal Action : Type*) where
  jointWeight : World → Signal → ℝ
  loss : World → Action → ℝ

variable {World Signal Action : Type*}
  [Fintype World] [Fintype Signal]

/-- Risk of committing to one action before observing the signal. -/
def staticRisk (experiment : DecisionExperiment World Signal Action)
    (action : Action) : ℝ :=
  ∑ world, ∑ signal,
    experiment.jointWeight world signal * experiment.loss world action

/-- Risk of a policy that may condition its action on the observed signal. -/
def signalRisk (experiment : DecisionExperiment World Signal Action)
    (policy : Signal → Action) : ℝ :=
  ∑ world, ∑ signal,
    experiment.jointWeight world signal *
      experiment.loss world (policy signal)

/-- A signal-conditioned policy is risk minimizing when it is no worse than
every other signal-conditioned policy. -/
def IsRiskMinimizing (experiment : DecisionExperiment World Signal Action)
    (policy : Signal → Action) : Prop :=
  ∀ alternative, signalRisk experiment policy ≤ signalRisk experiment alternative

/-- A policy that ignores its signal has exactly the corresponding static
risk. -/
theorem signalRisk_constant
    (experiment : DecisionExperiment World Signal Action)
    (action : Action) :
    signalRisk experiment (fun _ => action) = staticRisk experiment action := by
  rfl

/-- An optimal signal-conditioned policy cannot have greater risk than any
fixed action, because ignoring the signal remains available. -/
theorem optimalSignalRisk_le_staticRisk
    (experiment : DecisionExperiment World Signal Action)
    (policy : Signal → Action)
    (optimal : IsRiskMinimizing experiment policy)
    (baseline : Action) :
    signalRisk experiment policy ≤ staticRisk experiment baseline := by
  rw [← signalRisk_constant experiment baseline]
  exact optimal (fun _ => baseline)

/-- Gross decision value supplied by a signal-conditioned policy relative to
a fixed baseline action. -/
def grossDecisionValue
    (experiment : DecisionExperiment World Signal Action)
    (baseline : Action) (policy : Signal → Action) : ℝ :=
  staticRisk experiment baseline - signalRisk experiment policy

/-- The gross decision value of an optimal signal-conditioned policy is
nonnegative relative to every fixed baseline. -/
theorem grossDecisionValue_nonneg_of_optimal
    (experiment : DecisionExperiment World Signal Action)
    (baseline : Action) (policy : Signal → Action)
    (optimal : IsRiskMinimizing experiment policy) :
    0 ≤ grossDecisionValue experiment baseline policy := by
  unfold grossDecisionValue
  linarith [optimalSignalRisk_le_staticRisk experiment policy optimal baseline]

/-- Net decision value after charging acquisition cost. -/
def netDecisionValue
    (experiment : DecisionExperiment World Signal Action)
    (baseline : Action) (policy : Signal → Action) (cost : ℝ) : ℝ :=
  grossDecisionValue experiment baseline policy - cost

/-- Acquisition is strictly worthwhile exactly when cost is below the gross
decision-loss reduction. -/
theorem netDecisionValue_pos_iff_cost_lt_gross
    (experiment : DecisionExperiment World Signal Action)
    (baseline : Action) (policy : Signal → Action) (cost : ℝ) :
  0 < netDecisionValue experiment baseline policy cost ↔
      cost < grossDecisionValue experiment baseline policy := by
  unfold netDecisionValue
  constructor <;> intro h <;> linarith

/-- An optimal policy has nonnegative net value whenever acquisition cost is
nonpositive.  At positive cost, optimal use of the signal alone is not enough:
the loss reduction must also pay for observing it. -/
theorem netDecisionValue_nonneg_of_optimal_of_cost_nonpos
    (experiment : DecisionExperiment World Signal Action)
    (baseline : Action) (policy : Signal → Action) (cost : ℝ)
    (optimal : IsRiskMinimizing experiment policy) (cost_nonpos : cost ≤ 0) :
    0 ≤ netDecisionValue experiment baseline policy cost := by
  unfold netDecisionValue
  have gross_nonneg :=
    grossDecisionValue_nonneg_of_optimal experiment baseline policy optimal
  linarith

/-! ## Residual ranking is not value ranking -/

/-- Summary statistics exposed to an acquisition rule.  The decision-loss
fields are expectations supplied by a declared decision model; the residual
score is merely a model diagnostic. -/
structure AcquisitionSummary where
  residualScore : ℝ
  currentDecisionLoss : ℝ
  expectedPostAcquisitionLoss : ℝ
  acquisitionCost : ℝ

def summaryNetValue (candidate : AcquisitionSummary) : ℝ :=
  candidate.currentDecisionLoss -
    candidate.expectedPostAcquisitionLoss - candidate.acquisitionCost

/-- Large surprise whose acquisition cannot improve the decision. -/
def highResidualNoDecisionGain : AcquisitionSummary where
  residualScore := 10
  currentDecisionLoss := 5
  expectedPostAcquisitionLoss := 5
  acquisitionCost := 1

/-- Smaller surprise whose acquisition resolves a costly decision. -/
def lowResidualLargeDecisionGain : AcquisitionSummary where
  residualScore := 1
  currentDecisionLoss := 10
  expectedPostAcquisitionLoss := 0
  acquisitionCost := 1

/-- Raw residual ranking can be exactly opposite to safety-relevant net-value
ranking. -/
theorem residualRanking_can_reverse_decisionValueRanking :
    highResidualNoDecisionGain.residualScore >
        lowResidualLargeDecisionGain.residualScore ∧
      summaryNetValue highResidualNoDecisionGain < 0 ∧
      0 < summaryNetValue lowResidualLargeDecisionGain ∧
      summaryNetValue highResidualNoDecisionGain <
        summaryNetValue lowResidualLargeDecisionGain := by
  norm_num [highResidualNoDecisionGain, lowResidualLargeDecisionGain,
    summaryNetValue]

/-- Zero acquisition cost is not enough to make a useless signal strictly
valuable: if expected decision loss is unchanged, net value is exactly zero. -/
theorem unchangedDecisionLoss_has_zeroValue
    (currentLoss : ℝ) :
    summaryNetValue
      { residualScore := 100
        currentDecisionLoss := currentLoss
        expectedPostAcquisitionLoss := currentLoss
        acquisitionCost := 0 } = 0 := by
  simp [summaryNetValue]

#print axioms signalRisk_constant
#print axioms optimalSignalRisk_le_staticRisk
#print axioms grossDecisionValue_nonneg_of_optimal
#print axioms netDecisionValue_pos_iff_cost_lt_gross
#print axioms netDecisionValue_nonneg_of_optimal_of_cost_nonpos
#print axioms residualRanking_can_reverse_decisionValueRanking
#print axioms unchangedDecisionLoss_has_zeroValue

end


end DecisionValueOfInformation

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
