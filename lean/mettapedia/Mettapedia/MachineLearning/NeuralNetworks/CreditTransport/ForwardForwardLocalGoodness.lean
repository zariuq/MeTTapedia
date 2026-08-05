import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ForwardForwardObjectiveDecomposition

/-!
# Forward-Forward local goodness

Hinton, *The Forward-Forward Algorithm: Some Preliminary Investigations*
(2022, arXiv:2212.13345), defines the local probability that an activation
vector is positive by

`sigmoid (‖activation‖² - threshold)`.

The positive pass raises local squared goodness, while the negative pass lowers
it.  Before an activation is passed to the next layer, normalization removes
its length so that the next layer cannot reuse the preceding layer's goodness.

This file isolates that scalar objective and its exact boundaries.

* Positive and negative probabilities are strict complements in `(0, 1)`.
* Their negative-log losses are the corresponding softplus expressions.
* The positive-loss derivative is strictly negative and the negative-loss
  derivative is strictly positive.
* Positive rescaling of a nonzero raw activation strictly raises its positive
  probability, whereas normalization fixes every nonzero activation's
  goodness at one.
* Zero activation is a necessary boundary: totalized normalization leaves its
  goodness at zero.
* The original binary local objective is not the later full-comparison
  multiclass objective when more than one negative class is present.

These identities do not establish task accuracy, convergence, biological
plausibility, memory superiority, or equivalence to backpropagation.

Source artifact SHA-256:
`059f700a44f78227bfd8f6219b5460484502985808ff1e23874be4f53b468e4f`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ForwardForwardLocalGoodness

noncomputable section

open ForwardForwardObjectiveDecomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Squared goodness and binary probabilities -/

/-- Local goodness is the squared norm of the pre-normalization activation. -/
def activationGoodness (activation : E) : ℝ :=
  ‖activation‖ ^ 2

/-- Scalar form of Hinton's local positive-data probability. -/
def positiveProbabilityOfGoodness
    (threshold goodness : ℝ) : ℝ :=
  Real.sigmoid (goodness - threshold)

/-- Scalar probability assigned to the negative-data class. -/
def negativeProbabilityOfGoodness
    (threshold goodness : ℝ) : ℝ :=
  Real.sigmoid (threshold - goodness)

/-- Positive-data probability of an activation vector. -/
def positiveProbability
    (threshold : ℝ) (activation : E) : ℝ :=
  positiveProbabilityOfGoodness threshold
    (activationGoodness activation)

/-- Negative-data probability of an activation vector. -/
def negativeProbability
    (threshold : ℝ) (activation : E) : ℝ :=
  negativeProbabilityOfGoodness threshold
    (activationGoodness activation)

omit [NormedSpace ℝ E] in
theorem activationGoodness_nonneg (activation : E) :
    0 ≤ activationGoodness activation :=
  sq_nonneg _

omit [NormedSpace ℝ E] in
@[simp]
theorem activationGoodness_eq_zero_iff (activation : E) :
    activationGoodness activation = 0 ↔ activation = 0 := by
  simp [activationGoodness]

theorem positiveProbabilityOfGoodness_pos
    (threshold goodness : ℝ) :
    0 < positiveProbabilityOfGoodness threshold goodness :=
  Real.sigmoid_pos _

theorem positiveProbabilityOfGoodness_lt_one
    (threshold goodness : ℝ) :
    positiveProbabilityOfGoodness threshold goodness < 1 :=
  Real.sigmoid_lt_one _

theorem negativeProbabilityOfGoodness_pos
    (threshold goodness : ℝ) :
    0 < negativeProbabilityOfGoodness threshold goodness :=
  Real.sigmoid_pos _

theorem negativeProbabilityOfGoodness_lt_one
    (threshold goodness : ℝ) :
    negativeProbabilityOfGoodness threshold goodness < 1 :=
  Real.sigmoid_lt_one _

/-- The two local class probabilities are exact complements. -/
theorem negativeProbabilityOfGoodness_eq_one_sub
    (threshold goodness : ℝ) :
    negativeProbabilityOfGoodness threshold goodness =
      1 - positiveProbabilityOfGoodness threshold goodness := by
  simpa only [negativeProbabilityOfGoodness,
    positiveProbabilityOfGoodness, neg_sub] using
    Real.sigmoid_neg (goodness - threshold)

omit [NormedSpace ℝ E] in
theorem positive_add_negative_probability
    (threshold : ℝ) (activation : E) :
    positiveProbability threshold activation +
        negativeProbability threshold activation =
      1 := by
  rw [negativeProbability, positiveProbability,
    negativeProbabilityOfGoodness_eq_one_sub]
  ring

/-- Increasing scalar goodness strictly increases the positive probability. -/
theorem positiveProbabilityOfGoodness_strictMono
    (threshold : ℝ) :
    StrictMono (positiveProbabilityOfGoodness threshold) := by
  intro first second h
  apply Real.sigmoid_strictMono
  linarith

/-- Increasing scalar goodness strictly decreases the negative probability. -/
theorem negativeProbabilityOfGoodness_strictAnti
    (threshold : ℝ) :
    StrictAnti (negativeProbabilityOfGoodness threshold) := by
  intro first second h
  apply Real.sigmoid_strictMono
  linarith

/-- At the threshold the two local classes each receive probability one half. -/
theorem probabilities_at_threshold (threshold : ℝ) :
    positiveProbabilityOfGoodness threshold threshold = (2 : ℝ)⁻¹ ∧
      negativeProbabilityOfGoodness threshold threshold = (2 : ℝ)⁻¹ := by
  simp [positiveProbabilityOfGoodness, negativeProbabilityOfGoodness]

/-! ## Exact local negative-log losses -/

/-- Positive-data negative-log loss, written as a softplus. -/
def positiveLoss (threshold goodness : ℝ) : ℝ :=
  Real.log (1 + Real.exp (threshold - goodness))

/-- Negative-data negative-log loss, written as a softplus. -/
def negativeLoss (threshold goodness : ℝ) : ℝ :=
  Real.log (1 + Real.exp (goodness - threshold))

theorem positiveLoss_eq_neg_log_probability
    (threshold goodness : ℝ) :
    positiveLoss threshold goodness =
      -Real.log (positiveProbabilityOfGoodness threshold goodness) := by
  simp only [positiveLoss, positiveProbabilityOfGoodness,
    Real.sigmoid_def, neg_sub]
  rw [Real.log_inv]
  ring

theorem negativeLoss_eq_neg_log_probability
    (threshold goodness : ℝ) :
    negativeLoss threshold goodness =
      -Real.log (negativeProbabilityOfGoodness threshold goodness) := by
  simp only [negativeLoss, negativeProbabilityOfGoodness,
    Real.sigmoid_def, neg_sub]
  rw [Real.log_inv]
  ring

/-- Exact derivative of the positive-pass local loss. -/
theorem hasDerivAt_positiveLoss
    (threshold goodness : ℝ) :
    HasDerivAt (positiveLoss threshold)
      (-Real.exp (threshold - goodness) /
        (1 + Real.exp (threshold - goodness)))
      goodness := by
  have hinner :
      HasDerivAt (fun value : ℝ => threshold - value) (-1) goodness :=
    (hasDerivAt_id goodness).const_sub threshold
  have hsum :
      HasDerivAt
        (fun value : ℝ => 1 + Real.exp (threshold - value))
        (-Real.exp (threshold - goodness)) goodness := by
    simpa only [mul_neg, mul_one] using hinner.exp.const_add 1
  change
    HasDerivAt
      (fun value : ℝ => Real.log
        (1 + Real.exp (threshold - value)))
      (-Real.exp (threshold - goodness) /
        (1 + Real.exp (threshold - goodness)))
      goodness
  exact hsum.log (by positivity)

/-- Exact derivative of the negative-pass local loss. -/
theorem hasDerivAt_negativeLoss
    (threshold goodness : ℝ) :
    HasDerivAt (negativeLoss threshold)
      (Real.exp (goodness - threshold) /
        (1 + Real.exp (goodness - threshold)))
      goodness := by
  have hinner :
      HasDerivAt (fun value : ℝ => value - threshold) 1 goodness :=
    (hasDerivAt_id goodness).sub_const threshold
  have hsum :
      HasDerivAt
        (fun value : ℝ => 1 + Real.exp (value - threshold))
        (Real.exp (goodness - threshold)) goodness := by
    simpa only [mul_one] using hinner.exp.const_add 1
  change
    HasDerivAt
      (fun value : ℝ => Real.log
        (1 + Real.exp (value - threshold)))
      (Real.exp (goodness - threshold) /
        (1 + Real.exp (goodness - threshold)))
      goodness
  exact hsum.log (by positivity)

/-- Raising goodness is a strict descent direction for the positive loss. -/
theorem positiveLoss_derivative_neg
  (threshold goodness : ℝ) :
    deriv (positiveLoss threshold) goodness < 0 := by
  rw [(hasDerivAt_positiveLoss threshold goodness).deriv]
  rw [neg_div]
  exact neg_lt_zero.mpr (div_pos (Real.exp_pos _) (by positivity))

/-- Raising goodness is a strict ascent direction for the negative loss. -/
theorem negativeLoss_derivative_pos
    (threshold goodness : ℝ) :
    0 < deriv (negativeLoss threshold) goodness := by
  rw [(hasDerivAt_negativeLoss threshold goodness).deriv]
  exact div_pos (Real.exp_pos _) (by positivity)

theorem losses_at_threshold (threshold : ℝ) :
    positiveLoss threshold threshold = Real.log 2 ∧
      negativeLoss threshold threshold = Real.log 2 := by
  constructor <;> norm_num [positiveLoss, negativeLoss]

/-! ## Length removal and its zero boundary -/

/-- Raw squared goodness scales quadratically. -/
theorem activationGoodness_smul
    (scale : ℝ) (activation : E) :
    activationGoodness (scale • activation) =
      scale ^ 2 * activationGoodness activation := by
  simp [activationGoodness, norm_smul, Real.norm_eq_abs, mul_pow]

/-- A raw positive rescaling above one strictly raises positive probability
for every nonzero activation. -/
theorem positiveProbability_strictly_increases_under_raw_scale
    (threshold scale : ℝ) (activation : E)
    (hscale : 1 < scale)
    (hactivation : activation ≠ 0) :
    positiveProbability threshold activation <
      positiveProbability threshold (scale • activation) := by
  apply positiveProbabilityOfGoodness_strictMono threshold
  rw [activationGoodness_smul]
  have hgoodness :
      0 < activationGoodness activation := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hactivation)
  have hscaleSq : (1 : ℝ) < scale ^ 2 := by
    nlinarith [sq_nonneg (scale - 1)]
  nlinarith

/-- Normalization makes every nonzero activation's squared goodness exactly
one. -/
theorem activationGoodness_l2Normalize_eq_one
    (activation : E)
    (hactivation : activation ≠ 0) :
    activationGoodness (l2Normalize activation) = 1 := by
  have hnorm : ‖activation‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hactivation
  simp [activationGoodness, l2Normalize, norm_smul, hnorm]

/-- Hence every nonzero normalized activation has the same local positive
probability, independent of its incoming length. -/
theorem positiveProbability_l2Normalize
    (threshold : ℝ) (activation : E)
    (hactivation : activation ≠ 0) :
    positiveProbability threshold (l2Normalize activation) =
      Real.sigmoid (1 - threshold) := by
  simp [positiveProbability, positiveProbabilityOfGoodness,
    activationGoodness_l2Normalize_eq_one activation hactivation]

/-- Zero is a genuine boundary of totalized normalization. -/
theorem activationGoodness_l2Normalize_zero :
    activationGoodness (l2Normalize (0 : E)) = 0 := by
  simp [activationGoodness, l2Normalize]

/-- At zero, normalization cannot manufacture unit goodness. -/
theorem positiveProbability_l2Normalize_zero
    (threshold : ℝ) :
    positiveProbability threshold (l2Normalize (0 : E)) =
      Real.sigmoid (-threshold) := by
  simp [positiveProbability, positiveProbabilityOfGoodness,
    activationGoodness_l2Normalize_zero]

/-- The raw local objective is sensitive to length even when direction is
unchanged. -/
theorem sameDirection_differentLength_changes_probability :
    positiveProbability (E := ℝ) 0 (1 : ℝ) <
      positiveProbability (E := ℝ) 0 (2 : ℝ) := by
  simpa [smul_eq_mul] using
    positiveProbability_strictly_increases_under_raw_scale
      (E := ℝ) 0 2 (1 : ℝ) (by norm_num) (by norm_num)

/-- Squared goodness alone cannot distinguish a direction reversal. -/
theorem activationGoodness_negativeScale :
    activationGoodness ((-1 : ℝ) • (1 : ℝ)) =
      activationGoodness (1 : ℝ) := by
  norm_num [activationGoodness, Real.norm_eq_abs]

/-! ## Separation from later full-comparison objectives -/

/-- The original one-negative binary objective is not pointwise equal to a
full comparison against two negative classes. -/
theorem originalBinaryObjective_ne_twoNegativeFullComparison :
    let negatives : Bool → ℝ := fun _ => 0
    singleNegativeLoss 0 (negatives false) ≠
      fullComparisonLoss 0 negatives :=
  oneSampledNegative_ne_fullComparison

end

end ForwardForwardLocalGoodness

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
