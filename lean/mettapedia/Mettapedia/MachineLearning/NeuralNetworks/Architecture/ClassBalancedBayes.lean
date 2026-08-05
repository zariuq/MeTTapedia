import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SlidingWindowPrior

/-!
# Finite class-balanced Bayes decision boundary

Huang et al., *Online Continual Learning via Logit Adjusted Softmax*
(arXiv:2311.06460), state that a classifier maximizing class-conditional
likelihood minimizes class-balanced misclassification error.

This file proves the finite theorem over arbitrary real score tables.  The
proof isolates one reusable identity: pointwise misclassification mass is total
score mass minus the score of the selected class.  Therefore every pointwise
score maximizer minimizes both total misclassification mass and, for a
nonempty class set, class-balanced error.

A normalized two-class fixture separates this objective from ordinary
prior-weighted sample error.  Under a three-to-one class prior, the
sample-optimal classifier is strictly worse for class-balanced error, while the
class-balanced classifier is strictly worse for prior-weighted sample error.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Class Observation : Type*}

/-- Misclassification mass at one observation. -/
def pointwiseMisclassificationMass [Fintype Class] [DecidableEq Class]
    (score : Class → Observation → ℝ)
    (predictor : Observation → Class) (observation : Observation) : ℝ :=
  ∑ label,
    if predictor observation = label then 0 else score label observation

/-- Total finite misclassification mass. -/
def misclassificationMass [Fintype Class] [DecidableEq Class]
    [Fintype Observation]
    (score : Class → Observation → ℝ)
    (predictor : Observation → Class) : ℝ :=
  ∑ observation,
    pointwiseMisclassificationMass score predictor observation

/-- Finite class-balanced error.  Each class-conditional row contributes with
the same `1 / |Class|` weight. -/
def classBalancedError [Fintype Class] [DecidableEq Class]
    [Fintype Observation]
    (likelihood : Class → Observation → ℝ)
    (predictor : Observation → Class) : ℝ :=
  misclassificationMass likelihood predictor / Fintype.card Class

/-- A predictor selects a pointwise maximum of a score table. -/
def IsPointwiseScoreMaximizer
    (score : Class → Observation → ℝ)
    (predictor : Observation → Class) : Prop :=
  ∀ observation label,
    score label observation ≤ score (predictor observation) observation

/-- A chosen finite likelihood maximizer. -/
def likelihoodMaximizer [Finite Class] [Nonempty Class]
    (likelihood : Class → Observation → ℝ)
    (observation : Observation) : Class :=
  Classical.choose
    (Finite.exists_max (fun label => likelihood label observation))

theorem likelihoodMaximizer_spec [Finite Class] [Nonempty Class]
    (likelihood : Class → Observation → ℝ)
    (observation : Observation) (label : Class) :
    likelihood label observation ≤
      likelihood (likelihoodMaximizer likelihood observation) observation :=
  Classical.choose_spec
    (Finite.exists_max (fun item => likelihood item observation)) label

theorem likelihoodMaximizer_isPointwiseScoreMaximizer
    [Finite Class] [Nonempty Class]
    (likelihood : Class → Observation → ℝ) :
    IsPointwiseScoreMaximizer likelihood
      (likelihoodMaximizer likelihood) :=
  fun observation label =>
    likelihoodMaximizer_spec likelihood observation label

/-- Pointwise error is total score mass minus the selected score. -/
theorem pointwiseMisclassificationMass_eq_total_sub_selected
    [Fintype Class] [DecidableEq Class]
    (score : Class → Observation → ℝ)
    (predictor : Observation → Class) (observation : Observation) :
    pointwiseMisclassificationMass score predictor observation =
      (∑ label, score label observation) -
        score (predictor observation) observation := by
  classical
  calc
    pointwiseMisclassificationMass score predictor observation =
        ∑ label, (score label observation -
          if predictor observation = label then
            score label observation else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      split <;> simp_all
    _ = (∑ label, score label observation) -
        ∑ label, if predictor observation = label then
          score label observation else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ label, score label observation) -
        score (predictor observation) observation := by
      rw [Finset.sum_ite_eq Finset.univ (predictor observation)]
      simp

/-- Any pointwise maximizer has no larger pointwise error than any competing
predictor. -/
theorem pointwiseMisclassificationMass_le_of_maximizer
    [Fintype Class] [DecidableEq Class]
    (score : Class → Observation → ℝ)
    (best predictor : Observation → Class)
    (bestMaximizes : IsPointwiseScoreMaximizer score best)
    (observation : Observation) :
    pointwiseMisclassificationMass score best observation ≤
      pointwiseMisclassificationMass score predictor observation := by
  rw [pointwiseMisclassificationMass_eq_total_sub_selected,
    pointwiseMisclassificationMass_eq_total_sub_selected]
  linarith [bestMaximizes observation (predictor observation)]

/-- Pointwise maximization minimizes total finite misclassification mass. -/
theorem misclassificationMass_le_of_maximizer
    [Fintype Class] [DecidableEq Class] [Fintype Observation]
    (score : Class → Observation → ℝ)
    (best predictor : Observation → Class)
    (bestMaximizes : IsPointwiseScoreMaximizer score best) :
    misclassificationMass score best ≤
      misclassificationMass score predictor := by
  apply Finset.sum_le_sum
  intro observation _
  exact pointwiseMisclassificationMass_le_of_maximizer
    score best predictor bestMaximizes observation

/-- The class-conditional likelihood maximizer minimizes finite
class-balanced error. -/
theorem likelihoodMaximizer_minimizes_classBalancedError
    [Fintype Class] [Nonempty Class] [DecidableEq Class]
    [Fintype Observation]
    (likelihood : Class → Observation → ℝ)
    (predictor : Observation → Class) :
    classBalancedError likelihood (likelihoodMaximizer likelihood) ≤
      classBalancedError likelihood predictor := by
  have cardPositive : 0 < (Fintype.card Class : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [classBalancedError, classBalancedError,
    div_le_div_iff_of_pos_right cardPositive]
  exact misclassificationMass_le_of_maximizer likelihood
    (likelihoodMaximizer likelihood) predictor
    (likelihoodMaximizer_isPointwiseScoreMaximizer likelihood)

/-- Prior-weighted likelihood table used by ordinary sample-risk
minimization. -/
def priorWeightedScore (prior : Class → ℝ)
    (likelihood : Class → Observation → ℝ) :
    Class → Observation → ℝ :=
  fun label observation => prior label * likelihood label observation

/-- Finite prior-weighted sample misclassification error. -/
def sampleMisclassificationError [Fintype Class] [DecidableEq Class]
    [Fintype Observation]
    (prior : Class → ℝ) (likelihood : Class → Observation → ℝ)
    (predictor : Observation → Class) : ℝ :=
  misclassificationMass (priorWeightedScore prior likelihood) predictor

/-- The pointwise prior-times-likelihood maximizer minimizes sample error. -/
theorem priorWeightedMaximizer_minimizes_sampleError
    [Fintype Class] [Nonempty Class] [DecidableEq Class]
    [Fintype Observation]
    (prior : Class → ℝ) (likelihood : Class → Observation → ℝ)
    (predictor : Observation → Class) :
    sampleMisclassificationError prior likelihood
        (likelihoodMaximizer (priorWeightedScore prior likelihood)) ≤
      sampleMisclassificationError prior likelihood predictor :=
  misclassificationMass_le_of_maximizer
    (priorWeightedScore prior likelihood)
    (likelihoodMaximizer (priorWeightedScore prior likelihood))
    predictor
    (likelihoodMaximizer_isPointwiseScoreMaximizer
      (priorWeightedScore prior likelihood))

/-! ## A normalized strict-separation fixture -/

/-- Both class-conditional rows are normalized.  Matching label/observation
pairs receive likelihood `1/3`; crossed pairs receive `2/3`. -/
def crossedLikelihood (label observation : Bool) : ℝ :=
  if label = observation then 1 / 3 else 2 / 3

def balancedBayesFixturePredictor (observation : Bool) : Bool :=
  !observation

def threeToOneClassPrior : Bool → ℝ :=
  fun label => if label then 3 / 4 else 1 / 4

def priorBayesFixturePredictor : Bool → Bool := fun _ => true

theorem crossedLikelihood_nonneg :
    ∀ label observation, 0 ≤ crossedLikelihood label observation := by
  intro label observation
  unfold crossedLikelihood
  split <;> norm_num

theorem crossedLikelihood_normalized :
    ∀ label, ∑ observation, crossedLikelihood label observation = 1 := by
  intro label
  cases label <;> norm_num [crossedLikelihood]

theorem balancedFixture_isPointwiseLikelihoodMaximizer :
    IsPointwiseScoreMaximizer crossedLikelihood
      balancedBayesFixturePredictor := by
  intro observation label
  cases observation <;> cases label <;>
    norm_num [crossedLikelihood, balancedBayesFixturePredictor]

theorem priorFixture_isPointwiseWeightedMaximizer :
    IsPointwiseScoreMaximizer
      (priorWeightedScore threeToOneClassPrior crossedLikelihood)
      priorBayesFixturePredictor := by
  intro observation label
  cases observation <;> cases label <;>
    norm_num [priorWeightedScore, threeToOneClassPrior,
      crossedLikelihood, priorBayesFixturePredictor]

/-- Imbalanced-prior sample risk and class-balanced risk have strict, opposite
preferences even though every class-conditional row is normalized. -/
theorem balanced_and_prior_optima_separate :
    classBalancedError crossedLikelihood balancedBayesFixturePredictor =
        1 / 3 ∧
      classBalancedError crossedLikelihood priorBayesFixturePredictor =
        1 / 2 ∧
      sampleMisclassificationError threeToOneClassPrior crossedLikelihood
          priorBayesFixturePredictor = 1 / 4 ∧
      sampleMisclassificationError threeToOneClassPrior crossedLikelihood
          balancedBayesFixturePredictor = 1 / 3 := by
  norm_num [classBalancedError, misclassificationMass,
    pointwiseMisclassificationMass, crossedLikelihood,
    balancedBayesFixturePredictor, priorBayesFixturePredictor,
    sampleMisclassificationError, priorWeightedScore, threeToOneClassPrior]

#print axioms likelihoodMaximizer_isPointwiseScoreMaximizer
#print axioms pointwiseMisclassificationMass_eq_total_sub_selected
#print axioms pointwiseMisclassificationMass_le_of_maximizer
#print axioms misclassificationMass_le_of_maximizer
#print axioms likelihoodMaximizer_minimizes_classBalancedError
#print axioms priorWeightedMaximizer_minimizes_sampleError
#print axioms crossedLikelihood_normalized
#print axioms balancedFixture_isPointwiseLikelihoodMaximizer
#print axioms priorFixture_isPointwiseWeightedMaximizer
#print axioms balanced_and_prior_optima_separate

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
