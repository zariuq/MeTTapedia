import Mathlib

/-!
# One-step meta-gradient and its first-order boundary

Finn, Abbeel, and Levine (2017), *Model-Agnostic Meta-Learning for Fast
Adaptation of Deep Networks*, adapt a parameter by

`theta' = theta - alpha * trainGradient(theta)`

and differentiate an evaluation loss through that update.  The exact
one-dimensional derivative contains the curvature transport factor

`1 - alpha * trainHessian(theta)`.

This file proves the chain-rule identity for arbitrary differentiable scalar
functions.  It then isolates when the first-order approximation is exact and
gives a quadratic fixture in which dropping the curvature factor reverses the
meta-gradient direction.

The theorem is local and scalar.  It does not establish multi-step
meta-learning convergence, stochastic-gradient validity, task-distribution
generalization, or an implementation correspondence.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

noncomputable section

/-- One gradient adaptation step. -/
def oneStepAdapt
    (rate : ℝ) (trainGradient : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  parameter - rate * trainGradient parameter

/-- Evaluation loss after one adaptation step. -/
def oneStepMetaObjective
    (rate : ℝ) (trainGradient evaluationLoss : ℝ → ℝ)
    (parameter : ℝ) : ℝ :=
  evaluationLoss (oneStepAdapt rate trainGradient parameter)

/-- The exact meta-gradient: evaluation gradient transported through the
Jacobian of the adaptation step. -/
def exactOneStepMetaGradient
    (rate trainCurvature evaluationGradient : ℝ) : ℝ :=
  evaluationGradient * (1 - rate * trainCurvature)

/-- The first-order approximation drops the adaptation Jacobian. -/
def firstOrderMetaGradient (evaluationGradient : ℝ) : ℝ :=
  evaluationGradient

/-- Derivative of the one-step adaptation map. -/
theorem oneStepAdapt_hasDerivAt
    (rate trainCurvature parameter : ℝ)
    (trainGradient : ℝ → ℝ)
    (hgradient :
      HasDerivAt trainGradient trainCurvature parameter) :
    HasDerivAt
      (oneStepAdapt rate trainGradient)
      (1 - rate * trainCurvature)
      parameter := by
  have h :=
    (hasDerivAt_id parameter).sub (hgradient.const_mul rate)
  convert h using 1 <;> rfl

/-- Source chain rule: differentiating through the inner gradient update
multiplies the evaluation gradient by `1 - rate * trainCurvature`. -/
theorem oneStepMetaObjective_hasDerivAt
    (rate trainCurvature evaluationGradient parameter : ℝ)
    (trainGradient evaluationLoss : ℝ → ℝ)
    (hgradient :
      HasDerivAt trainGradient trainCurvature parameter)
    (hevaluation :
      HasDerivAt evaluationLoss evaluationGradient
        (oneStepAdapt rate trainGradient parameter)) :
    HasDerivAt
      (oneStepMetaObjective rate trainGradient evaluationLoss)
      (exactOneStepMetaGradient rate trainCurvature evaluationGradient)
      parameter := by
  change HasDerivAt
    (fun x : ℝ => evaluationLoss (oneStepAdapt rate trainGradient x))
    (evaluationGradient * (1 - rate * trainCurvature))
    parameter
  exact hevaluation.comp parameter
    (oneStepAdapt_hasDerivAt rate trainCurvature parameter
      trainGradient hgradient)

/-- Zero adaptation rate makes the first-order approximation exact. -/
theorem exactOneStepMetaGradient_zeroRate
    (trainCurvature evaluationGradient : ℝ) :
    exactOneStepMetaGradient 0 trainCurvature evaluationGradient =
      firstOrderMetaGradient evaluationGradient := by
  simp [exactOneStepMetaGradient, firstOrderMetaGradient]

/-- Locally affine training loss also makes the first-order approximation
exact. -/
theorem exactOneStepMetaGradient_zeroCurvature
    (rate evaluationGradient : ℝ) :
    exactOneStepMetaGradient rate 0 evaluationGradient =
      firstOrderMetaGradient evaluationGradient := by
  simp [exactOneStepMetaGradient, firstOrderMetaGradient]

/-- If the rate-curvature product is one, the exact meta-gradient vanishes
even when the evaluation gradient does not. -/
theorem exactOneStepMetaGradient_eq_zero_of_rate_mul_curvature_eq_one
    (rate trainCurvature evaluationGradient : ℝ)
    (critical : rate * trainCurvature = 1) :
    exactOneStepMetaGradient rate trainCurvature evaluationGradient = 0 := by
  simp [exactOneStepMetaGradient, critical]

/-- The exact and first-order meta-gradients differ by precisely the omitted
curvature term. -/
theorem exact_sub_firstOrder
    (rate trainCurvature evaluationGradient : ℝ) :
    exactOneStepMetaGradient rate trainCurvature evaluationGradient -
        firstOrderMetaGradient evaluationGradient =
      -(rate * trainCurvature * evaluationGradient) := by
  simp [exactOneStepMetaGradient, firstOrderMetaGradient]
  ring

/-! ## Quadratic source fixture -/

def quadraticGradient
    (curvature center parameter : ℝ) : ℝ :=
  curvature * (parameter - center)

def quadraticLoss
    (curvature center parameter : ℝ) : ℝ :=
  curvature / 2 * (parameter - center) ^ 2

theorem quadraticGradient_hasDerivAt
    (curvature center parameter : ℝ) :
    HasDerivAt
      (quadraticGradient curvature center)
      curvature
      parameter := by
  have h :=
    ((hasDerivAt_id parameter).sub_const center).const_mul curvature
  convert h using 1 <;> first | rfl | simp

theorem quadraticLoss_hasDerivAt
    (curvature center parameter : ℝ) :
    HasDerivAt
      (quadraticLoss curvature center)
      (quadraticGradient curvature center parameter)
      parameter := by
  have h :=
    (((hasDerivAt_id parameter).sub_const center).pow 2).const_mul
      (curvature / 2)
  convert h using 1 <;>
    first | rfl | (simp [quadraticGradient]; ring)

/-- A modest rate preserves direction in this fixture: the exact gradient is
one quarter and the first-order approximation is one half. -/
theorem quadratic_same_direction :
    exactOneStepMetaGradient
        (1 / 4) 2
        (quadraticGradient 1 0
          (oneStepAdapt (1 / 4) (quadraticGradient 2 0) 1)) =
      1 / 4 ∧
    firstOrderMetaGradient
        (quadraticGradient 1 0
          (oneStepAdapt (1 / 4) (quadraticGradient 2 0) 1)) =
      1 / 2 := by
  norm_num [exactOneStepMetaGradient, firstOrderMetaGradient,
    oneStepAdapt, quadraticGradient]

/-- With rate one and training curvature two, the adaptation Jacobian is
negative. The exact meta-gradient is `1`, while the first-order approximation
is `-1`; their product is negative. -/
theorem firstOrder_metaGradient_reverses_direction :
    let adapted :=
      oneStepAdapt 1 (quadraticGradient 2 0) 1
    let exact :=
      exactOneStepMetaGradient 1 2
        (quadraticGradient 1 0 adapted)
    let approximate :=
      firstOrderMetaGradient (quadraticGradient 1 0 adapted)
    adapted = -1 ∧ exact = 1 ∧ approximate = -1 ∧ exact * approximate < 0 := by
  norm_num [oneStepAdapt, quadraticGradient, exactOneStepMetaGradient,
    firstOrderMetaGradient]

#print axioms oneStepAdapt_hasDerivAt
#print axioms oneStepMetaObjective_hasDerivAt
#print axioms exactOneStepMetaGradient_zeroRate
#print axioms exactOneStepMetaGradient_zeroCurvature
#print axioms exactOneStepMetaGradient_eq_zero_of_rate_mul_curvature_eq_one
#print axioms exact_sub_firstOrder
#print axioms quadraticGradient_hasDerivAt
#print axioms quadraticLoss_hasDerivAt
#print axioms quadratic_same_direction
#print axioms firstOrder_metaGradient_reverses_direction

end

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
