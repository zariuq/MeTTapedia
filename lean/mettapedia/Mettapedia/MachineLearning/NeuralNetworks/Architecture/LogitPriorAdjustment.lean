import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention

/-!
# Logit adjustment under changing class priors

Huang et al., *Online Continual Learning via Logit Adjusted Softmax*
(arXiv:2311.06460), add a temperature-scaled log class prior to each logit.
At temperature one this converts log class-conditionals into a Bayes posterior;
at temperature zero it recovers the unadjusted classifier.

This file proves that finite-class algebra exactly.  It also records two
boundaries needed by a growing action vocabulary.  A uniform prior changes
every score by one common offset and therefore cannot change softmax
probabilities.  In contrast, a zero prior is outside the logarithmic theorem:
Lean's totalized real logarithm maps zero to zero, so blindly applying the
formula can assign positive softmax mass to an impossible class.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Class : Type*}

/-- A logit with the source paper's temperature-scaled log-prior correction. -/
def logitAdjustedScore
    (logit prior : Class → ℝ) (temperature : ℝ) (label : Class) : ℝ :=
  logit label + temperature * Real.log (prior label)

/-- A finite categorical softmax probability, reusing the exact attention
softmax semantics. -/
def categoricalSoftmaxProbability [Fintype Class]
    (score : Class → ℝ) (label : Class) : ℝ :=
  attentionWeight score label

/-- Evidence for a finite Bayes classifier. -/
def bayesEvidence [Fintype Class]
    (prior likelihood : Class → ℝ) : ℝ :=
  ∑ label, prior label * likelihood label

/-- Posterior mass of one class under a finite prior and likelihood family. -/
def bayesPosterior [Fintype Class]
    (prior likelihood : Class → ℝ) (label : Class) : ℝ :=
  prior label * likelihood label / bayesEvidence prior likelihood

/-- Likelihood normalized under a uniform class prior. -/
def balancedLikelihoodProbability [Fintype Class]
    (likelihood : Class → ℝ) (label : Class) : ℝ :=
  likelihood label / ∑ item, likelihood item

@[simp] theorem logitAdjustedScore_zero
    (logit prior : Class → ℝ) (label : Class) :
    logitAdjustedScore logit prior 0 label = logit label := by
  simp [logitAdjustedScore]

@[simp] theorem categoricalSoftmaxProbability_adjustment_zero
    [Fintype Class]
    (logit prior : Class → ℝ) (label : Class) :
    categoricalSoftmaxProbability
        (logitAdjustedScore logit prior 0) label =
      categoricalSoftmaxProbability logit label := by
  congr 1
  funext item
  exact logitAdjustedScore_zero logit prior item

/-- Equation (6)'s unnormalized-mass factorization. -/
theorem exp_logitAdjustedScore
    (logit prior : Class → ℝ) (temperature : ℝ) (label : Class)
    (priorPositive : 0 < prior label) :
    Real.exp (logitAdjustedScore logit prior temperature label) =
      Real.exp (logit label) * prior label ^ temperature := by
  rw [logitAdjustedScore, Real.exp_add,
    Real.rpow_def_of_pos priorPositive]
  congr 1
  ring_nf

/-- Softmax odds eliminate the common normalizing mass exactly. -/
theorem categoricalSoftmaxProbability_div
    [Fintype Class] [Nonempty Class]
    (score : Class → ℝ) (left right : Class) :
    categoricalSoftmaxProbability score left /
        categoricalSoftmaxProbability score right =
      Real.exp (score left - score right) := by
  have massNe : attentionMass score ≠ 0 :=
    ne_of_gt (attentionMass_pos score)
  have rightExpNe : Real.exp (score right) ≠ 0 :=
    Real.exp_ne_zero _
  simp only [categoricalSoftmaxProbability, attentionWeight]
  field_simp [massNe, rightExpNe]
  rw [Real.exp_sub]
  field_simp [rightExpNe]

/-- The source adjustment multiplies the unadjusted odds by the exact ratio of
temperature-powered priors. -/
theorem logitAdjustedSoftmax_odds
    [Fintype Class] [Nonempty Class]
    (logit prior : Class → ℝ) (temperature : ℝ) (left right : Class)
    (leftPriorPositive : 0 < prior left)
    (rightPriorPositive : 0 < prior right) :
    categoricalSoftmaxProbability
          (logitAdjustedScore logit prior temperature) left /
        categoricalSoftmaxProbability
          (logitAdjustedScore logit prior temperature) right =
      (Real.exp (logit left) * prior left ^ temperature) /
        (Real.exp (logit right) * prior right ^ temperature) := by
  rw [categoricalSoftmaxProbability_div, Real.exp_sub,
    exp_logitAdjustedScore logit prior temperature left
      leftPriorPositive,
    exp_logitAdjustedScore logit prior temperature right
      rightPriorPositive]

/-- A uniform class prior adds one common offset and hence leaves every
softmax probability unchanged. -/
theorem uniformPrior_adjustment_preserves_softmax
    [Fintype Class] [Nonempty Class]
    (logit : Class → ℝ) (prior temperature : ℝ) (label : Class) :
    categoricalSoftmaxProbability
        (logitAdjustedScore logit (fun _ => prior) temperature) label =
      categoricalSoftmaxProbability logit label := by
  change attentionWeight (fun item =>
      logit item + temperature * Real.log prior) label =
    attentionWeight logit label
  exact attentionWeight_add_const logit
    (temperature * Real.log prior) label

/-- Unadjusted softmax of log-likelihoods is the likelihood classifier induced
by a uniform class prior. -/
theorem softmax_logLikelihood_eq_balancedLikelihood
    [Fintype Class] [Nonempty Class]
    (likelihood : Class → ℝ)
    (likelihoodPositive : ∀ label, 0 < likelihood label)
    (label : Class) :
    categoricalSoftmaxProbability
        (fun item => Real.log (likelihood item)) label =
      balancedLikelihoodProbability likelihood label := by
  classical
  simp only [categoricalSoftmaxProbability, attentionWeight, attentionMass,
    balancedLikelihoodProbability]
  simp_rw [Real.exp_log (likelihoodPositive _)]

/-- With a positive uniform prior, the Bayes posterior is exactly the
normalized class-conditional likelihood. -/
theorem uniformPrior_bayesPosterior_eq_balancedLikelihood
    [Fintype Class] [Nonempty Class]
    (prior : ℝ) (likelihood : Class → ℝ) (label : Class)
    (priorPositive : 0 < prior)
    (likelihoodPositive : ∀ item, 0 < likelihood item) :
    bayesPosterior (fun _ => prior) likelihood label =
      balancedLikelihoodProbability likelihood label := by
  classical
  have sumPositive : 0 < ∑ item, likelihood item :=
    Finset.sum_pos (fun item _ => likelihoodPositive item)
      Finset.univ_nonempty
  simp only [bayesPosterior, bayesEvidence, balancedLikelihoodProbability]
  rw [show (∑ item, prior * likelihood item) =
      prior * ∑ item, likelihood item by rw [Finset.mul_sum]]
  field_simp [ne_of_gt priorPositive, ne_of_gt sumPositive]

/-- At temperature one, adjusted softmax of log-likelihoods is exactly the
finite Bayes posterior.  This is the reusable form of the source paper's
logit/prior identity. -/
theorem adjustedSoftmax_logLikelihood_eq_bayesPosterior
    [Fintype Class] [Nonempty Class]
    (prior likelihood : Class → ℝ)
    (priorPositive : ∀ label, 0 < prior label)
    (likelihoodPositive : ∀ label, 0 < likelihood label)
    (label : Class) :
    categoricalSoftmaxProbability
        (logitAdjustedScore
          (fun item => Real.log (likelihood item)) prior 1)
        label =
      bayesPosterior prior likelihood label := by
  classical
  simp only [categoricalSoftmaxProbability, attentionWeight, attentionMass,
    logitAdjustedScore, one_mul, Real.exp_add]
  simp_rw [Real.exp_log (likelihoodPositive _),
    Real.exp_log (priorPositive _)]
  simp only [bayesPosterior, bayesEvidence]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro item _
    ring

/-! ## Positive and negative finite fixtures -/

def equalBinaryLogits : Bool → ℝ := fun _ => 0

def threeToOnePrior : Bool → ℝ :=
  fun label => if label then 3 else 1

/-- With equal evidence, the prior adjustment changes an unadjusted tie into
the exact three-to-one posterior. -/
theorem threeToOnePrior_adjustment :
    categoricalSoftmaxProbability
        (logitAdjustedScore equalBinaryLogits threeToOnePrior 1) true =
        3 / 4 ∧
      categoricalSoftmaxProbability
        (logitAdjustedScore equalBinaryLogits threeToOnePrior 1) false =
        1 / 4 ∧
      categoricalSoftmaxProbability equalBinaryLogits true = 1 / 2 := by
  simp [categoricalSoftmaxProbability, attentionWeight, attentionMass,
    logitAdjustedScore, equalBinaryLogits, threeToOnePrior, Real.exp_log]
  norm_num

def zeroOnePrior : Bool → ℝ :=
  fun label => if label then 1 else 0

def unitLikelihood : Bool → ℝ := fun _ => 1

/-- Strict positivity is essential.  Because `Real.log` is totalized at zero,
blind logarithmic adjustment assigns probability one half where the Bayes
posterior assigns probability one. -/
theorem zeroPrior_breaks_logAdjustment :
    categoricalSoftmaxProbability
        (logitAdjustedScore equalBinaryLogits zeroOnePrior 1) true =
        1 / 2 ∧
      bayesPosterior zeroOnePrior unitLikelihood true = 1 ∧
      categoricalSoftmaxProbability
          (logitAdjustedScore equalBinaryLogits zeroOnePrior 1) true ≠
        bayesPosterior zeroOnePrior unitLikelihood true := by
  norm_num [categoricalSoftmaxProbability, attentionWeight, attentionMass,
    logitAdjustedScore, equalBinaryLogits, zeroOnePrior, unitLikelihood,
    bayesPosterior, bayesEvidence]

#print axioms categoricalSoftmaxProbability_adjustment_zero
#print axioms exp_logitAdjustedScore
#print axioms categoricalSoftmaxProbability_div
#print axioms logitAdjustedSoftmax_odds
#print axioms uniformPrior_adjustment_preserves_softmax
#print axioms softmax_logLikelihood_eq_balancedLikelihood
#print axioms uniformPrior_bayesPosterior_eq_balancedLikelihood
#print axioms adjustedSoftmax_logLikelihood_eq_bayesPosterior
#print axioms threeToOnePrior_adjustment
#print axioms zeroPrior_breaks_logAdjustment

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
