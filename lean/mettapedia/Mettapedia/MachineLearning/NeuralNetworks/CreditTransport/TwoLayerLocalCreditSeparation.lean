import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ProspectiveResidualSemantics

/-!
# A two-layer predictive-credit boundary for dependent-proof ranking

The dependent-proof pointer ranker uses a hidden nonlinear representation and
a scalar score per candidate.  This module isolates the local-credit algebra
after fixing one scalar input and one differentiable task residual.

Prospective output settling recovers both backpropagated parameter credits up
to the same first-step scale.  Hidden error-coordinate settling recovers the
first-layer credit at that scale, while the second layer is evaluated at the
settled hidden state and can therefore define a genuinely different update.
The final fixture proves that this distinction is non-vacuous.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace TwoLayerLocalCreditSeparation

/-- Hidden prediction of the scalar two-layer fixture. -/
def hiddenPrediction (firstWeight input : ℝ) : ℝ :=
  firstWeight * input

/-- Output prediction of the scalar two-layer fixture. -/
def outputPrediction (firstWeight secondWeight input : ℝ) : ℝ :=
  secondWeight * hiddenPrediction firstWeight input

/-- Residual of the half-squared task loss. -/
def taskResidual
    (firstWeight secondWeight input target : ℝ) : ℝ :=
  outputPrediction firstWeight secondWeight input - target

/-- Backpropagated first-layer credit. -/
def bpFirstCredit
    (firstWeight secondWeight input target : ℝ) : ℝ :=
  taskResidual firstWeight secondWeight input target * secondWeight * input

/-- Backpropagated second-layer credit. -/
def bpSecondCredit
    (firstWeight secondWeight input target : ℝ) : ℝ :=
  taskResidual firstWeight secondWeight input target *
    hiddenPrediction firstWeight input

/-- One hidden-state inference step from the feed-forward prediction. -/
def hiddenAfterOneStep
    (rate firstWeight secondWeight input target : ℝ) : ℝ :=
  hiddenPrediction firstWeight input -
    rate * taskResidual firstWeight secondWeight input target * secondWeight

/-- Local first-layer prediction-error credit at the settled hidden state. -/
def hiddenPCFirstCredit
    (precision rate firstWeight secondWeight input target : ℝ) : ℝ :=
  precision *
    (hiddenPrediction firstWeight input -
      hiddenAfterOneStep rate firstWeight secondWeight input target) *
    input

/-- Local second-layer task credit evaluated at the settled hidden state. -/
def hiddenPCSecondCredit
    (rate firstWeight secondWeight input target : ℝ) : ℝ :=
  let hidden :=
    hiddenAfterOneStep rate firstWeight secondWeight input target
  (secondWeight * hidden - target) * hidden

/-- Hidden-state PC recovers the first-layer BP credit at the common
rate-times-precision scale. -/
theorem hiddenPCFirstCredit_eq_scaledBP
    (precision rate firstWeight secondWeight input target : ℝ) :
    hiddenPCFirstCredit
        precision rate firstWeight secondWeight input target =
      (precision * rate) *
        bpFirstCredit firstWeight secondWeight input target := by
  simp [hiddenPCFirstCredit, hiddenAfterOneStep, bpFirstCredit,
    taskResidual, outputPrediction, hiddenPrediction]
  ring

/-- One output-state inference step from the feed-forward prediction. -/
def outputAfterOneStep
    (rate firstWeight secondWeight input target : ℝ) : ℝ :=
  outputPrediction firstWeight secondWeight input -
    rate * taskResidual firstWeight secondWeight input target

/-- Prospective local first-layer credit through the output prediction. -/
def prospectiveFirstCredit
    (precision rate firstWeight secondWeight input target : ℝ) : ℝ :=
  precision *
    (outputPrediction firstWeight secondWeight input -
      outputAfterOneStep rate firstWeight secondWeight input target) *
    secondWeight * input

/-- Prospective local second-layer credit through the output prediction. -/
def prospectiveSecondCredit
    (precision rate firstWeight secondWeight input target : ℝ) : ℝ :=
  precision *
    (outputPrediction firstWeight secondWeight input -
      outputAfterOneStep rate firstWeight secondWeight input target) *
    hiddenPrediction firstWeight input

/-- Prospective first-layer credit is scaled BP at the first settle step. -/
theorem prospectiveFirstCredit_eq_scaledBP
    (precision rate firstWeight secondWeight input target : ℝ) :
    prospectiveFirstCredit
        precision rate firstWeight secondWeight input target =
      (precision * rate) *
        bpFirstCredit firstWeight secondWeight input target := by
  simp [prospectiveFirstCredit, outputAfterOneStep, bpFirstCredit,
    taskResidual, outputPrediction, hiddenPrediction]
  ring

/-- Prospective second-layer credit has the same scale as the first layer. -/
theorem prospectiveSecondCredit_eq_scaledBP
    (precision rate firstWeight secondWeight input target : ℝ) :
    prospectiveSecondCredit
        precision rate firstWeight secondWeight input target =
      (precision * rate) *
        bpSecondCredit firstWeight secondWeight input target := by
  simp [prospectiveSecondCredit, outputAfterOneStep, bpSecondCredit,
    taskResidual, outputPrediction, hiddenPrediction]
  ring

/-- With unit rate-times-precision, the prospective fixture recovers both BP
credits exactly. -/
theorem prospective_unitScale_recoversBP :
    prospectiveFirstCredit 2 (1 / 2) 1 1 1 0 = bpFirstCredit 1 1 1 0 ∧
      prospectiveSecondCredit 2 (1 / 2) 1 1 1 0 =
        bpSecondCredit 1 1 1 0 := by
  norm_num [prospectiveFirstCredit_eq_scaledBP,
    prospectiveSecondCredit_eq_scaledBP]

/--
Negative boundary: even when hidden PC exactly recovers the first-layer BP
credit, its two-layer credit pair need not be a common scalar multiple of BP.
-/
theorem hiddenPC_twoLayerCredit_not_commonScaledBP :
    hiddenPCFirstCredit 2 (1 / 2) 1 1 1 0 = 1 ∧
      hiddenPCSecondCredit (1 / 2) 1 1 1 0 = 1 / 4 ∧
      bpFirstCredit 1 1 1 0 = 1 ∧
      bpSecondCredit 1 1 1 0 = 1 ∧
      ¬ ∃ scale : ℝ,
        hiddenPCFirstCredit 2 (1 / 2) 1 1 1 0 =
            scale * bpFirstCredit 1 1 1 0 ∧
          hiddenPCSecondCredit (1 / 2) 1 1 1 0 =
            scale * bpSecondCredit 1 1 1 0 := by
  norm_num [hiddenPCFirstCredit, hiddenPCSecondCredit, hiddenAfterOneStep,
    bpFirstCredit, bpSecondCredit, taskResidual, outputPrediction,
    hiddenPrediction]

#print axioms hiddenPCFirstCredit_eq_scaledBP
#print axioms prospectiveFirstCredit_eq_scaledBP
#print axioms prospectiveSecondCredit_eq_scaledBP
#print axioms prospective_unitScale_recoversBP
#print axioms hiddenPC_twoLayerCredit_not_commonScaledBP

end TwoLayerLocalCreditSeparation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
