import Mathlib.Tactic

/-!
# Last-layer reset and relearning geometry

Frati et al., *Reset It and Forget It: Relearning Last-Layer Weights
Improves Continual and Transfer Learning* (arXiv:2310.07996), repeatedly
resample selected last-layer classifier weights before relearning a class.
The source emphasizes that changing the classifier also changes the
backpropagated signal seen by the representation.

This file isolates two exact mechanisms for a linear last layer with
half-squared loss.

First, the representation gradient is the prediction residual times the
head vector.  Its finite perturbation law has an exact quadratic remainder.
At a zero feature vector, opposite head vectors induce opposite upstream
gradients, and two heads can agree on the current prediction while inducing
different representation gradients.

Second, with the representation frozen to a scalar unit feature, repeated
head-gradient steps have a closed form.  Two initial heads' loss ordering is
preserved by the same nondegenerate relearning schedule.  Thus a reset that
starts farther from the fixed-feature target does not become beneficial merely
by applying the same head optimizer; any such benefit must use a changed
training path, changed representation, stochastic selection, or another
mechanism outside this restriction.

The source's image experiments, random resampling distribution, sequential
and batch schedule, meta-learning comparison, and transfer claims are not
formalized here.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace LastLayerResetGeometry

noncomputable section

open scoped BigOperators

/-! ## Representation-gradient geometry -/

/-- A finite representation or classifier vector. -/
abbrev Feature (dimension : ℕ) :=
  Fin dimension → ℝ

/-- Scalar prediction of a linear last-layer head. -/
def prediction {dimension : ℕ}
    (head feature : Feature dimension) : ℝ :=
  head ⬝ᵥ feature

/-- Half-squared loss at one feature/target pair. -/
def halfSquaredFeatureLoss {dimension : ℕ}
    (head feature : Feature dimension) (target : ℝ) : ℝ :=
  (prediction head feature - target) ^ 2 / 2

/-- Euclidean gradient of the one-example loss with respect to the feature. -/
def featureGradient {dimension : ℕ}
    (head feature : Feature dimension) (target : ℝ) :
    Feature dimension :=
  fun coordinate =>
    (prediction head feature - target) * head coordinate

/-- A linear head sends a feature perturbation to its dot product with the
head. -/
theorem prediction_add {dimension : ℕ}
    (head feature perturbation : Feature dimension) :
    prediction head (feature + perturbation) =
      prediction head feature + prediction head perturbation := by
  simp [prediction, dotProduct, mul_add, Finset.sum_add_distrib]

/-- Pairing the representation gradient with a perturbation gives residual
times the head's prediction change. -/
theorem featureGradient_dot {dimension : ℕ}
    (head feature perturbation : Feature dimension) (target : ℝ) :
    featureGradient head feature target ⬝ᵥ perturbation =
      (prediction head feature - target) *
        prediction head perturbation := by
  unfold featureGradient prediction dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Exact finite Taylor law for a feature perturbation. -/
theorem halfSquaredFeatureLoss_add_exact {dimension : ℕ}
    (head feature perturbation : Feature dimension) (target : ℝ) :
    halfSquaredFeatureLoss head (feature + perturbation) target -
        halfSquaredFeatureLoss head feature target =
      featureGradient head feature target ⬝ᵥ perturbation +
        (prediction head perturbation) ^ 2 / 2 := by
  change
    (prediction head (feature + perturbation) - target) ^ 2 / 2 -
          (prediction head feature - target) ^ 2 / 2 =
      featureGradient head feature target ⬝ᵥ perturbation +
        (prediction head perturbation) ^ 2 / 2
  rw [prediction_add, featureGradient_dot]
  ring

/-- A zero last-layer head supplies no upstream representation gradient. -/
theorem zeroHead_featureGradient {dimension : ℕ}
    (feature : Feature dimension) (target : ℝ) :
    featureGradient (0 : Feature dimension) feature target = 0 := by
  funext coordinate
  simp [featureGradient, prediction, dotProduct]

/-- At the zero feature vector, the upstream gradient is negative target
times the current head. -/
theorem featureGradient_zeroFeature {dimension : ℕ}
    (head : Feature dimension) (target : ℝ) :
    featureGradient head 0 target =
      fun coordinate => -target * head coordinate := by
  funext coordinate
  simp [featureGradient, prediction, dotProduct]

/-- Opposite reset heads induce opposite upstream gradients at a zero feature
vector. -/
theorem oppositeHead_reverses_zeroFeatureGradient {dimension : ℕ}
    (head : Feature dimension) (target : ℝ) :
    featureGradient (-head) 0 target =
      -featureGradient head 0 target := by
  rw [featureGradient_zeroFeature, featureGradient_zeroFeature]
  funext coordinate
  simp

def fixtureFeature : Feature 2 :=
  ![1, 0]

def fixtureHeadLeft : Feature 2 :=
  ![1, 1]

def fixtureHeadRight : Feature 2 :=
  ![1, -1]

/-- Equal current predictions do not determine equal representation
gradients: the unobserved head coordinate remains visible to upstream credit. -/
theorem equal_prediction_different_featureGradient :
    prediction fixtureHeadLeft fixtureFeature =
        prediction fixtureHeadRight fixtureFeature ∧
      featureGradient fixtureHeadLeft fixtureFeature 0 ≠
        featureGradient fixtureHeadRight fixtureFeature 0 := by
  constructor
  · norm_num [prediction, fixtureHeadLeft, fixtureHeadRight, fixtureFeature,
      dotProduct, Fin.sum_univ_two]
  · intro gradientsEqual
    have coordinateOne := congrFun gradientsEqual (1 : Fin 2)
    norm_num [featureGradient, prediction, fixtureHeadLeft, fixtureHeadRight,
      fixtureFeature, dotProduct, Fin.sum_univ_two] at coordinateOne

/-! ## Frozen-feature relearning boundary -/

/-- One gradient step for a scalar head on a unit feature and target. -/
def unitFeatureHeadStep
    (rate target weight : ℝ) : ℝ :=
  weight - rate * (weight - target)

/-- Repeated scalar-head relearning steps. -/
def runUnitFeatureHeadSteps
    (rate target : ℝ) : ℕ → ℝ → ℝ
  | 0, initial => initial
  | steps + 1, initial =>
      runUnitFeatureHeadSteps rate target steps
        (unitFeatureHeadStep rate target initial)

/-- Exact residual after any finite number of unit-feature head steps. -/
theorem runUnitFeatureHeadSteps_sub_target
    (rate target initial : ℝ) (steps : ℕ) :
    runUnitFeatureHeadSteps rate target steps initial - target =
      (1 - rate) ^ steps * (initial - target) := by
  induction steps generalizing initial with
  | zero =>
      simp [runUnitFeatureHeadSteps]
  | succ steps inductionHypothesis =>
      rw [runUnitFeatureHeadSteps, inductionHypothesis]
      simp only [unitFeatureHeadStep, pow_succ]
      ring

/-- Half-squared loss for the scalar unit-feature restriction. -/
def unitFeatureLoss
    (weight target : ℝ) : ℝ :=
  (weight - target) ^ 2 / 2

/-- The finite relearning loss is the initial loss times the squared
contraction factor. -/
theorem unitFeatureLoss_run_eq
    (rate target initial : ℝ) (steps : ℕ) :
    unitFeatureLoss
        (runUnitFeatureHeadSteps rate target steps initial) target =
      ((1 - rate) ^ steps) ^ 2 * unitFeatureLoss initial target := by
  rw [unitFeatureLoss, unitFeatureLoss,
    runUnitFeatureHeadSteps_sub_target]
  ring

/-- Under the same relearning schedule, the exact loss difference between two
initial heads is scaled by the same nonnegative factor. -/
theorem equalSchedule_lossDifference_eq
    (rate target first second : ℝ) (steps : ℕ) :
    unitFeatureLoss
          (runUnitFeatureHeadSteps rate target steps first) target -
        unitFeatureLoss
          (runUnitFeatureHeadSteps rate target steps second) target =
      ((1 - rate) ^ steps) ^ 2 *
        (unitFeatureLoss first target - unitFeatureLoss second target) := by
  rw [unitFeatureLoss_run_eq, unitFeatureLoss_run_eq]
  ring

/-- If the schedule has not annihilated all residuals, it preserves the strict
ordering of initial fixed-feature losses. -/
theorem equalSchedule_loss_lt_iff
    (rate target first second : ℝ) (steps : ℕ)
    (nonzeroFactor : (1 - rate) ^ steps ≠ 0) :
    unitFeatureLoss
          (runUnitFeatureHeadSteps rate target steps first) target <
        unitFeatureLoss
          (runUnitFeatureHeadSteps rate target steps second) target ↔
      unitFeatureLoss first target < unitFeatureLoss second target := by
  rw [unitFeatureLoss_run_eq, unitFeatureLoss_run_eq]
  have positiveFactor : 0 < ((1 - rate) ^ steps) ^ 2 :=
    sq_pos_of_ne_zero nonzeroFactor
  constructor <;> intro comparison <;> nlinarith

/-- Unit learning rate reaches the fixed-feature target in one or more
steps, independently of the reset value. -/
theorem unitRate_relearns_after_positive_steps
    (target initial : ℝ) (steps : ℕ) :
    runUnitFeatureHeadSteps 1 target (steps + 1) initial = target := by
  apply sub_eq_zero.mp
  rw [runUnitFeatureHeadSteps_sub_target]
  simp

/-- A zero learning rate never relearns anything. -/
theorem zeroRate_preserves_reset
    (target initial : ℝ) (steps : ℕ) :
    runUnitFeatureHeadSteps 0 target steps initial = initial := by
  have residualIdentity :=
    runUnitFeatureHeadSteps_sub_target 0 target initial steps
  simpa using residualIdentity

/-- Positive fixture: one half-rate step quarters the loss. -/
theorem halfRate_oneStep_quarters_loss :
    unitFeatureLoss (runUnitFeatureHeadSteps (1 / 2) 0 1 2) 0 =
      (1 / 4) * unitFeatureLoss 2 0 := by
  norm_num [runUnitFeatureHeadSteps, unitFeatureHeadStep, unitFeatureLoss]

/-- Negative fixture: a rate of three quadruples the loss in one step. -/
theorem largeRate_oneStep_quadruples_loss :
    unitFeatureLoss (runUnitFeatureHeadSteps 3 0 1 1) 0 =
      4 * unitFeatureLoss 1 0 := by
  norm_num [runUnitFeatureHeadSteps, unitFeatureHeadStep, unitFeatureLoss]

/-- Negative reset boundary: at finite non-unit rate, resetting an already
optimal head away from the target makes the fixed-feature loss strictly
worse. -/
theorem resetOptimalHead_is_worse :
    unitFeatureLoss (runUnitFeatureHeadSteps (1 / 2) 0 1 1) 0 >
      unitFeatureLoss (runUnitFeatureHeadSteps (1 / 2) 0 1 0) 0 := by
  norm_num [runUnitFeatureHeadSteps, unitFeatureHeadStep, unitFeatureLoss]

#print axioms prediction_add
#print axioms featureGradient_dot
#print axioms halfSquaredFeatureLoss_add_exact
#print axioms zeroHead_featureGradient
#print axioms featureGradient_zeroFeature
#print axioms oppositeHead_reverses_zeroFeatureGradient
#print axioms equal_prediction_different_featureGradient
#print axioms runUnitFeatureHeadSteps_sub_target
#print axioms unitFeatureLoss_run_eq
#print axioms equalSchedule_lossDifference_eq
#print axioms equalSchedule_loss_lt_iff
#print axioms unitRate_relearns_after_positive_steps
#print axioms zeroRate_preserves_reset
#print axioms halfRate_oneStep_quarters_loss
#print axioms largeRate_oneStep_quadruples_loss
#print axioms resetOptimalHead_is_worse

end

end LastLayerResetGeometry

end Mettapedia.MachineLearning.ContinualLearning
