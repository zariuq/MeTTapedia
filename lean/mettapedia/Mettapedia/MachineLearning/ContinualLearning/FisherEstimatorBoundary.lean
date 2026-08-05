import Mathlib.Tactic

/-!
# Fisher-estimator boundaries for continual learning

Gido M. van de Ven, *On the Computation of the Fisher Information in
Continual Learning* (ICLR Blogpost, 2025, arXiv:2502.11756), distinguishes
four quantities that are often conflated in implementations of elastic
weight consolidation:

* the exact categorical expectation of the squared score;
* one label sampled from the model distribution for each input;
* the squared score of the observed ground-truth label;
* the square of a gradient aggregated across a minibatch.

This file isolates the exact finite algebra behind those distinctions.  A
model-distributed label gives an unbiased estimator of the exact categorical
Fisher contribution.  Sampling from another label distribution need not do
so, even when both distributions are normalized and the score has zero model
mean.  Squaring an aggregated batch gradient adds every pairwise cross term;
those terms can either cancel the individual squared mass or amplify it.

The results concern one scalar score coordinate and finite label spaces.
Coordinatewise application recovers a diagonal Fisher estimator, and an
outer finite average recovers the dataset formula.  No theorem here identifies
the empirical or batched quantity with the true Fisher, nor does it turn the
source's benchmark comparisons into universal performance claims.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace FisherEstimatorBoundary

open scoped BigOperators

noncomputable section

/-- A finite probability distribution used to state the sampling law
explicitly. -/
structure FiniteLabelDistribution (Label : Type*) [Fintype Label] where
  mass : Label → ℝ
  mass_nonneg : ∀ label, 0 ≤ mass label
  mass_sum_one : ∑ label, mass label = 1

/-- A scalar score coordinate over a finite model distribution.

The zero-mean field is the finite score identity
`E_{y ∼ p}[∂ log p(y)] = 0`.  Keeping it in the structure prevents arbitrary
numbers from being presented as a valid score model in the counterexamples.
-/
structure FiniteScoreModel (Label : Type*) [Fintype Label] where
  distribution : FiniteLabelDistribution Label
  score : Label → ℝ
  score_mean_zero :
    ∑ label, distribution.mass label * score label = 0

variable {Label : Type*} [Fintype Label]

/-- Expected squared score under an explicitly supplied label law. -/
def expectedSquaredScore
    (sampling : FiniteLabelDistribution Label)
    (score : Label → ℝ) : ℝ :=
  ∑ label, sampling.mass label * score label ^ 2

/-- Exact per-input categorical contribution to one diagonal Fisher
coordinate. -/
def exactClassFisher (model : FiniteScoreModel Label) : ℝ :=
  expectedSquaredScore model.distribution model.score

/-- Contribution produced after drawing one label. -/
def sampledLabelContribution
    (model : FiniteScoreModel Label) (label : Label) : ℝ :=
  model.score label ^ 2

/-- Expected one-label contribution under an explicit sampling law. -/
def expectedSampledContribution
    (sampling : FiniteLabelDistribution Label)
    (model : FiniteScoreModel Label) : ℝ :=
  ∑ label, sampling.mass label * sampledLabelContribution model label

/-- Sampling labels from the model distribution is unbiased for the exact
categorical Fisher contribution. -/
theorem expected_model_sample_eq_exact
    (model : FiniteScoreModel Label) :
    expectedSampledContribution model.distribution model =
      exactClassFisher model := by
  simp [expectedSampledContribution, sampledLabelContribution,
    exactClassFisher, expectedSquaredScore]

/-- The contribution obtained by using one observed ground-truth label.
Unlike model-distributed sampling, no expectation identity is assumed. -/
def empiricalLabelContribution
    (model : FiniteScoreModel Label) (observed : Label) : ℝ :=
  model.score observed ^ 2

theorem exactClassFisher_nonneg (model : FiniteScoreModel Label) :
    0 ≤ exactClassFisher model := by
  unfold exactClassFisher expectedSquaredScore
  exact Finset.sum_nonneg fun label _ =>
    mul_nonneg (model.distribution.mass_nonneg label)
      (sq_nonneg (model.score label))

/-- Exact finite-dataset diagonal Fisher contribution.  Empty datasets are
assigned zero by the field operations; applications should separately record
nonemptiness when interpreting this as an average. -/
def exactDatasetFisher (models : List (FiniteScoreModel Label)) : ℝ :=
  (models.map exactClassFisher).sum / models.length

/-- Expected finite-dataset contribution when each input draws one label
from its own model distribution. -/
def expectedSampledDatasetFisher
    (models : List (FiniteScoreModel Label)) : ℝ :=
  (models.map fun model =>
    expectedSampledContribution model.distribution model).sum /
      models.length

/-- Unbiasedness of model-distributed label sampling survives the outer
finite dataset average. -/
theorem expectedSampledDatasetFisher_eq_exact
    (models : List (FiniteScoreModel Label)) :
    expectedSampledDatasetFisher models = exactDatasetFisher models := by
  simp [expectedSampledDatasetFisher, exactDatasetFisher,
    expected_model_sample_eq_exact]

/-! ## A valid score model separating exact, empirical, and wrong-law sampling -/

def skewThreeMass : Fin 3 → ℝ :=
  fun label =>
    if label = 0 then (1 : ℝ) / 2
    else (1 : ℝ) / 4

def uniformThreeMass : Fin 3 → ℝ :=
  fun _ => (1 : ℝ) / 3

def balancedThreeScore : Fin 3 → ℝ :=
  fun label =>
    if label = 0 then 0
    else if label = 1 then 1
    else -1

@[simp] theorem skewThreeMass_zero :
    skewThreeMass 0 = 1 / 2 := by
  simp [skewThreeMass]

@[simp] theorem skewThreeMass_one :
    skewThreeMass 1 = 1 / 4 := by
  simp [skewThreeMass, show (1 : Fin 3) ≠ 0 by decide]

@[simp] theorem skewThreeMass_two :
    skewThreeMass 2 = 1 / 4 := by
  simp [skewThreeMass, show (2 : Fin 3) ≠ 0 by decide]

@[simp] theorem uniformThreeMass_value (label : Fin 3) :
    uniformThreeMass label = 1 / 3 := rfl

@[simp] theorem balancedThreeScore_zero :
    balancedThreeScore 0 = 0 := by
  simp [balancedThreeScore]

@[simp] theorem balancedThreeScore_one :
    balancedThreeScore 1 = 1 := by
  simp [balancedThreeScore, show (1 : Fin 3) ≠ 0 by decide]

@[simp] theorem balancedThreeScore_two :
    balancedThreeScore 2 = -1 := by
  simp [balancedThreeScore, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

def skewThreeDistribution : FiniteLabelDistribution (Fin 3) where
  mass := skewThreeMass
  mass_nonneg := by
    intro label
    fin_cases label <;> norm_num [skewThreeMass]
  mass_sum_one := by
    norm_num [Fin.sum_univ_three]

def uniformThreeDistribution : FiniteLabelDistribution (Fin 3) where
  mass := uniformThreeMass
  mass_nonneg := by
    intro label
    fin_cases label <;> norm_num [uniformThreeMass]
  mass_sum_one := by
    norm_num [uniformThreeMass, Fin.sum_univ_three]

/-- A nondegenerate three-label model whose score has exactly zero model
mean. -/
def balancedThreeScoreModel : FiniteScoreModel (Fin 3) where
  distribution := skewThreeDistribution
  score := balancedThreeScore
  score_mean_zero := by
    norm_num [skewThreeDistribution, Fin.sum_univ_three]

theorem balancedThreeScoreModel_exact_eq_half :
    exactClassFisher balancedThreeScoreModel = 1 / 2 := by
  norm_num [exactClassFisher, expectedSquaredScore,
    balancedThreeScoreModel, skewThreeDistribution, Fin.sum_univ_three]

/-- A perfectly fitted observed class can contribute zero empirical Fisher
even though the exact model Fisher is positive. -/
theorem empirical_zero_exact_positive :
    empiricalLabelContribution balancedThreeScoreModel 0 = 0 ∧
      0 < exactClassFisher balancedThreeScoreModel := by
  constructor
  · norm_num [empiricalLabelContribution, balancedThreeScoreModel,
      balancedThreeScore]
  · rw [balancedThreeScoreModel_exact_eq_half]
    norm_num

/-- A normalized but wrong label-sampling law is biased for this valid score
model. -/
theorem uniform_sampling_differs_from_exact :
    expectedSampledContribution uniformThreeDistribution
        balancedThreeScoreModel = 2 / 3 ∧
      expectedSampledContribution uniformThreeDistribution
        balancedThreeScoreModel ≠
          exactClassFisher balancedThreeScoreModel := by
  constructor
  · norm_num [expectedSampledContribution, sampledLabelContribution,
      uniformThreeDistribution, balancedThreeScoreModel,
      Fin.sum_univ_three]
  · rw [balancedThreeScoreModel_exact_eq_half]
    norm_num [expectedSampledContribution, sampledLabelContribution,
      uniformThreeDistribution, balancedThreeScoreModel,
      Fin.sum_univ_three]

/-! ## Squaring individual gradients versus an aggregated minibatch -/

/-- Sum of squares obtained by squaring each per-example scalar gradient
before aggregation. -/
def individualSquaredMass (gradients : List ℝ) : ℝ :=
  (gradients.map fun gradient => gradient ^ 2).sum

/-- Square obtained after first aggregating all scalar gradients in a batch. -/
def batchSquaredMass (gradients : List ℝ) : ℝ :=
  gradients.sum ^ 2

/-- Pairwise cross-term mass introduced by squaring an aggregated sum. -/
def batchCrossMass : List ℝ → ℝ
  | [] => 0
  | gradient :: gradients =>
      2 * gradient * gradients.sum + batchCrossMass gradients

/-- The batched approximation is exactly the individual squared mass plus
all pairwise cross terms. -/
theorem batchSquaredMass_eq_individual_add_cross
    (gradients : List ℝ) :
    batchSquaredMass gradients =
      individualSquaredMass gradients + batchCrossMass gradients := by
  induction gradients with
  | nil =>
      norm_num [batchSquaredMass, individualSquaredMass, batchCrossMass]
  | cons gradient gradients inductionHypothesis =>
      have tailIdentity :
          gradients.sum ^ 2 =
            individualSquaredMass gradients + batchCrossMass gradients := by
        simpa [batchSquaredMass] using inductionHypothesis
      simp only [batchSquaredMass, List.sum_cons, individualSquaredMass,
        List.map_cons, List.sum_cons, batchCrossMass]
      change (gradient + gradients.sum) ^ 2 =
        gradient ^ 2 +
          (gradients.map fun value => value ^ 2).sum +
          (2 * gradient * gradients.sum + batchCrossMass gradients)
      calc
        (gradient + gradients.sum) ^ 2 =
            gradient ^ 2 + 2 * gradient * gradients.sum +
              gradients.sum ^ 2 := by ring
        _ = gradient ^ 2 + 2 * gradient * gradients.sum +
              (individualSquaredMass gradients +
                batchCrossMass gradients) := by rw [tailIdentity]
        _ = gradient ^ 2 +
              (gradients.map fun value => value ^ 2).sum +
              (2 * gradient * gradients.sum +
                batchCrossMass gradients) := by
              simp only [individualSquaredMass]
              ring

/-- Per-example average of individual squared gradients. -/
def individualSquaredMean (gradients : List ℝ) : ℝ :=
  individualSquaredMass gradients / gradients.length

/-- Source-style batched approximation: square each aggregated minibatch
gradient, then average over minibatches rather than examples. -/
def batchedSquaredApproximation (batches : List (List ℝ)) : ℝ :=
  (batches.map batchSquaredMass).sum / batches.length

/-- Batch size one recovers the corresponding individual squared
contribution exactly. -/
theorem singleton_batch_recovers_individual (gradient : ℝ) :
    batchedSquaredApproximation [[gradient]] =
      individualSquaredMean [gradient] := by
  simp [batchedSquaredApproximation, batchSquaredMass,
    individualSquaredMean, individualSquaredMass]

/-- Opposing per-example gradients cancel after aggregation, although their
individual squared mean is positive. -/
theorem opposing_batch_cancels :
    individualSquaredMean [1, -1] = 1 ∧
      batchedSquaredApproximation [[1, -1]] = 0 ∧
      batchCrossMass [1, -1] = -2 := by
  norm_num [individualSquaredMean, individualSquaredMass,
    batchedSquaredApproximation, batchSquaredMass, batchCrossMass]

/-- Aligned per-example gradients amplify after aggregation: with the
source's per-batch normalization, one two-example batch gives four rather
than the individual squared mean of one. -/
theorem aligned_batch_amplifies :
    individualSquaredMean [1, 1] = 1 ∧
      batchedSquaredApproximation [[1, 1]] = 4 ∧
      batchCrossMass [1, 1] = 2 := by
  norm_num [individualSquaredMean, individualSquaredMass,
    batchedSquaredApproximation, batchSquaredMass, batchCrossMass]

end

end FisherEstimatorBoundary

end Mettapedia.MachineLearning.ContinualLearning
