import Mathlib.Tactic

/-!
# Continual-backpropagation utility and replacement boundaries

Dohare et al., *Maintaining Plasticity in Deep Continual Learning*
(arXiv:2306.13812), define exponentially averaged activation and utility
statistics and selectively reinitialize mature low-utility units.  When a
unit is removed, its mean outgoing contribution is transferred to the
consumer bias and its outgoing weight is set to zero.

This file isolates two exact finite mechanisms.

First, an exponential average initialized at zero is
`(1 - decay^age) * signal` on a constant signal.  Dividing the current
accumulator by `1 - decay^age` therefore recovers the signal whenever that
denominator is nonzero.  Equation (4) as printed instead uses the previous
accumulator in the numerator.  The lagged expression is zero at age one and,
at decay one half and age two, returns two thirds of a unit signal.  Both
formulas are represented so the index boundary remains explicit.

Second, moving `mean * outgoingWeight` into the consumer bias before zeroing
the outgoing weight preserves the consumer preactivation exactly at the mean
activation.  Away from that anchor, the exact drift is
`outgoingWeight * (mean - activation)`.  Zeroing without bias transfer fails
at the anchor whenever the mean contribution is nonzero.

The paper's low-utility ranking, stochastic replacement process, optimizer
interaction, effective-rank diagnostics, and empirical plasticity claims are
not formalized here.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ContinualBackpropUtility

noncomputable section

/-! ## Exponential activation statistics -/

/-- One exponential-moving-average update. -/
def emaStep (decay previous observation : ℝ) : ℝ :=
  decay * previous + (1 - decay) * observation

/-- Repeated EMA updates on a constant signal, initialized at zero. -/
def constantEmaRun (decay signal : ℝ) : ℕ → ℝ
  | 0 => 0
  | age + 1 => emaStep decay (constantEmaRun decay signal age) signal

/-- Exact finite-age closed form for the constant-signal accumulator. -/
theorem constantEmaRun_eq
    (decay signal : ℝ) (age : ℕ) :
    constantEmaRun decay signal age =
      (1 - decay ^ age) * signal := by
  induction age with
  | zero =>
      simp [constantEmaRun]
  | succ age ih =>
      simp only [constantEmaRun, emaStep, ih, pow_succ]
      ring

/-- Standard bias correction uses the current accumulator. -/
def currentBiasCorrection
    (decay accumulator : ℝ) (age : ℕ) : ℝ :=
  accumulator / (1 - decay ^ age)

/-- Equation (4) as typeset uses the previous accumulator with the current
age denominator. -/
def printedLaggedBiasCorrection
    (decay signal : ℝ) (age : ℕ) : ℝ :=
  constantEmaRun decay signal (age - 1) / (1 - decay ^ age)

/-- Current-accumulator bias correction exactly recovers a constant signal. -/
theorem currentBiasCorrection_constantEmaRun
    (decay signal : ℝ) (age : ℕ)
    (hdenominator : 1 - decay ^ age ≠ 0) :
    currentBiasCorrection decay (constantEmaRun decay signal age) age =
      signal := by
  rw [currentBiasCorrection, constantEmaRun_eq]
  exact mul_div_cancel_left₀ signal hdenominator

/-- Exact form of the printed lagged correction at every positive age. -/
theorem printedLaggedBiasCorrection_succ_eq
    (decay signal : ℝ) (age : ℕ) :
    printedLaggedBiasCorrection decay signal (age + 1) =
      ((1 - decay ^ age) * signal) /
        (1 - decay ^ (age + 1)) := by
  simp [printedLaggedBiasCorrection, constantEmaRun_eq]

/-- Positive boundary for the corrected formula: a unit signal is recovered
at age two for decay one half. -/
theorem currentBiasCorrection_half_age_two :
    currentBiasCorrection (1 / 2) (constantEmaRun (1 / 2) 1 2) 2 = 1 := by
  norm_num [currentBiasCorrection, constantEmaRun, emaStep]

/-- Negative boundary for the printed index: at age one the lagged numerator
is still the zero initialization. -/
theorem printedLaggedBiasCorrection_age_one :
    printedLaggedBiasCorrection (1 / 2) 1 1 = 0 ∧
      printedLaggedBiasCorrection (1 / 2) 1 1 ≠ 1 := by
  norm_num [printedLaggedBiasCorrection, constantEmaRun]

/-- At age two the same printed expression remains biased: it returns two
thirds of a unit constant signal. -/
theorem printedLaggedBiasCorrection_half_age_two :
    printedLaggedBiasCorrection (1 / 2) 1 2 = 2 / 3 ∧
      printedLaggedBiasCorrection (1 / 2) 1 2 ≠ 1 := by
  norm_num [printedLaggedBiasCorrection, constantEmaRun, emaStep]

/-! ## Function-preserving mean transfer -/

/-- One consumer's scalar preactivation contribution. -/
def consumerPreactivation
    (bias outgoingWeight activation : ℝ) : ℝ :=
  bias + outgoingWeight * activation

/-- Bias after transferring a removed unit's mean outgoing contribution. -/
def transferredBias
    (bias outgoingWeight meanActivation : ℝ) : ℝ :=
  bias + meanActivation * outgoingWeight

/-- Mean transfer followed by a zero outgoing weight preserves the consumer
preactivation exactly at the declared mean activation. -/
theorem transferMean_zeroWeight_preserves_at_mean
    (bias outgoingWeight meanActivation : ℝ) :
    consumerPreactivation
        (transferredBias bias outgoingWeight meanActivation) 0
        meanActivation =
      consumerPreactivation bias outgoingWeight meanActivation := by
  simp [consumerPreactivation, transferredBias]
  ring

/-- Exact off-anchor drift after mean transfer and outgoing-weight reset. -/
theorem transferMean_zeroWeight_change_exact
    (bias outgoingWeight meanActivation activation : ℝ) :
    consumerPreactivation
        (transferredBias bias outgoingWeight meanActivation) 0 activation -
        consumerPreactivation bias outgoingWeight activation =
      outgoingWeight * (meanActivation - activation) := by
  simp [consumerPreactivation, transferredBias]
  ring

/-- A freshly initialized unit with zero outgoing weight has no immediate
effect on a consumer, regardless of its activation. -/
theorem zeroOutgoingWeight_no_effect
    (bias activation : ℝ) :
    consumerPreactivation bias 0 activation = bias := by
  simp [consumerPreactivation]

/-- Negative boundary: simply zeroing the outgoing weight without transferring
the mean contribution changes the consumer at the mean whenever that
contribution is nonzero. -/
theorem zeroWeight_without_transfer_changes_mean_iff
    (bias outgoingWeight meanActivation : ℝ) :
    consumerPreactivation bias 0 meanActivation ≠
        consumerPreactivation bias outgoingWeight meanActivation ↔
      outgoingWeight * meanActivation ≠ 0 := by
  simp [consumerPreactivation]

/-! ## Maturity boundary -/

/-- Algorithm-1 eligibility: a unit's age must exceed the maturity threshold. -/
def replacementEligible (maturity age : ℕ) : Prop :=
  maturity < age

/-- Resetting a unit's age to zero prevents immediate replacement for every
maturity threshold. -/
theorem resetAge_not_replacementEligible (maturity : ℕ) :
    ¬ replacementEligible maturity 0 := by
  simp [replacementEligible]

/-- The first age that is eligible is the successor of the maturity
threshold. -/
theorem firstEligibleAge (maturity : ℕ) :
    replacementEligible maturity (maturity + 1) := by
  simp [replacementEligible]

#print axioms constantEmaRun_eq
#print axioms currentBiasCorrection_constantEmaRun
#print axioms printedLaggedBiasCorrection_succ_eq
#print axioms currentBiasCorrection_half_age_two
#print axioms printedLaggedBiasCorrection_age_one
#print axioms printedLaggedBiasCorrection_half_age_two
#print axioms transferMean_zeroWeight_preserves_at_mean
#print axioms transferMean_zeroWeight_change_exact
#print axioms zeroOutgoingWeight_no_effect
#print axioms zeroWeight_without_transfer_changes_mean_iff
#print axioms resetAge_not_replacementEligible
#print axioms firstEligibleAge

end

end ContinualBackpropUtility

end Mettapedia.MachineLearning.ContinualLearning
