import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.KalmanCorrespondence
import Mettapedia.PLN.Bridges.PredictiveCoding.WorldModelConnection
import Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore

/-!
# Scalar belief-state workspace cell

A scalar belief slot carries a mean and positive precision.  Conditioning by
one independent Gaussian observation adds precision and updates the mean by a
single precision-ratio gate.  The same interpolation is already present in
the predictive-coding Gaussian fusion theorem and in PLN weighted revision.

The generic interpolation algebra and belief-slot packaging are new.  The
Bayesian minimizer, scalar conditional-posterior, PLN revision, and conjugate
observation-count facts are transported from their sealed source modules.
Nothing here extends the result to nonlinear learned belief updates.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Set
open scoped ENNReal
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNWeightTV

/-! ## One precision-interpolation primitive -/

/-- Relative precision assigned to the new proposal. -/
noncomputable def precisionGain
    (priorPrecision observationPrecision : ℝ) : ℝ :=
  observationPrecision / (priorPrecision + observationPrecision)

/-- Interpolate an old mean toward a proposed mean using relative precision. -/
noncomputable def precisionInterpolate
    (oldMean proposedMean priorPrecision observationPrecision : ℝ) : ℝ :=
  oldMean + precisionGain priorPrecision observationPrecision *
    (proposedMean - oldMean)

/-- The gated form is exactly the precision-weighted mean. -/
theorem precisionInterpolate_eq_weightedMean
    (oldMean proposedMean priorPrecision observationPrecision : ℝ)
    (hsum : priorPrecision + observationPrecision ≠ 0) :
    precisionInterpolate oldMean proposedMean
        priorPrecision observationPrecision =
      (priorPrecision * oldMean + observationPrecision * proposedMean) /
        (priorPrecision + observationPrecision) := by
  unfold precisionInterpolate precisionGain
  field_simp [hsum]
  ring

/-- The common interpolation primitive is the existing scalar Gaussian fusion
operation. -/
theorem precisionInterpolate_eq_gaussianFusion
    (oldMean proposedMean priorPrecision observationPrecision : ℝ)
    (hsum : priorPrecision + observationPrecision ≠ 0) :
    precisionInterpolate oldMean proposedMean
        priorPrecision observationPrecision =
      gaussianFusion oldMean proposedMean priorPrecision observationPrecision := by
  rw [precisionInterpolate_eq_weightedMean _ _ _ _ hsum]
  rfl

/-- With unit observation gain, the common interpolation primitive is exactly
the sealed scalar Kalman update. -/
theorem precisionInterpolate_eq_scalarKalmanUpdate
    (oldMean observation priorPrecision observationPrecision : ℝ) :
    precisionInterpolate oldMean observation priorPrecision observationPrecision =
      scalarKalmanUpdate oldMean observation 1
        priorPrecision observationPrecision := by
  unfold precisionInterpolate precisionGain scalarKalmanUpdate scalarKalmanGain
  ring

/-- With one slot and unit observation gain, the same value is produced by the
generic workspace operator. -/
theorem precisionInterpolate_eq_workspaceStep
    (oldMean observation priorPrecision observationPrecision : ℝ) :
    precisionInterpolate oldMean observation priorPrecision observationPrecision =
      (scalarKalmanWorkspaceFamily observation 1
        priorPrecision observationPrecision).step (fun _ => oldMean) 0 := by
  rw [scalarKalmanWorkspaceStep_eq_update]
  exact precisionInterpolate_eq_scalarKalmanUpdate
    oldMean observation priorPrecision observationPrecision

/-! ## Belief slot and exact conditioning -/

/-- Scalar Gaussian belief state in mean/precision coordinates. -/
structure ScalarBeliefState where
  mean : ℝ
  precision : ℝ
  precision_pos : 0 < precision

namespace ScalarBeliefState

/-- Condition a belief slot by one independent scalar observation. -/
noncomputable def condition
    (prior : ScalarBeliefState) (observation observationPrecision : ℝ)
    (hobservation : 0 < observationPrecision) : ScalarBeliefState where
  mean := precisionInterpolate prior.mean observation
    prior.precision observationPrecision
  precision := prior.precision + observationPrecision
  precision_pos := add_pos prior.precision_pos hobservation

@[simp] theorem condition_precision
    (prior : ScalarBeliefState) (observation observationPrecision : ℝ)
    (hobservation : 0 < observationPrecision) :
    (prior.condition observation observationPrecision hobservation).precision =
      prior.precision + observationPrecision :=
  rfl

/-- The conditioned mean is the existing Gaussian fusion posterior. -/
theorem condition_mean_eq_gaussianFusion
    (prior : ScalarBeliefState) (observation observationPrecision : ℝ)
    (hobservation : 0 < observationPrecision) :
    (prior.condition observation observationPrecision hobservation).mean =
      gaussianFusion prior.mean observation prior.precision observationPrecision := by
  apply precisionInterpolate_eq_gaussianFusion
  exact ne_of_gt (add_pos prior.precision_pos hobservation)

/-- Exact-gain conditioning crown: the updated belief mean minimizes the
two-source Gaussian energy. -/
theorem condition_mean_isBayesian
    (prior : ScalarBeliefState) (observation observationPrecision : ℝ)
    (hobservation : 0 < observationPrecision) :
    IsMinOn
      (twoSourceGaussianEnergy prior.mean observation
        prior.precision observationPrecision) univ
      (prior.condition observation observationPrecision hobservation).mean := by
  rw [prior.condition_mean_eq_gaussianFusion observation observationPrecision
    hobservation]
  exact gaussianFusion_isMinOn_twoSourceGaussianEnergy
    prior.mean observation prior.precision observationPrecision
      prior.precision_pos hobservation

/-- The belief-slot update is the conditional posterior mean of the sealed
depth-two linear-Gaussian chain. -/
theorem condition_mean_eq_conditionalPosteriorMean
    (prior : ScalarBeliefState) (observation observationPrecision : ℝ)
    (hobservation : 0 < observationPrecision) :
    (prior.condition observation observationPrecision hobservation).mean =
      pcConditionalPosteriorMean
        (pcDepthTwoLinks 1 1 prior.precision observationPrecision
          prior.precision_pos hobservation)
        prior.mean observation 0 := by
  rw [pcConditionalPosteriorMean_depthTwo_eq_scalarKalmanUpdate]
  simpa [condition] using
    (precisionInterpolate_eq_scalarKalmanUpdate
      prior.mean observation prior.precision observationPrecision)

end ScalarBeliefState

/-! ## Conjugate-evidence and PLN revision transport -/

/-- On the Gaussian-to-binary evidence adapter, abstract conjugate observation
count is exactly the encoded source precision. -/
theorem conjugateObservationCount_gaussianSource_eq_precision
    (source : GaussianSource) :
    ConjugateEvidence.observationCount (pcGaussianEvidenceOfSource source) =
      ENNReal.ofReal source.precision := by
  change (pcGaussianEvidenceOfSource source).pos +
      (pcGaussianEvidenceOfSource source).neg = ENNReal.ofReal source.precision
  unfold pcGaussianEvidenceOfSource
  rw [← add_mul]
  have hmean_le : ENNReal.ofReal source.mean ≤ 1 := by
    simpa using ENNReal.ofReal_le_one.mpr source.mean_le_one
  rw [add_tsub_cancel_of_le hmean_le, one_mul]

/-- PLN weighted revision is the same precision interpolation after the
existing precision-to-confidence coordinate bridge. -/
theorem precisionInterpolate_eq_plnRevision
    (source₁ source₂ : GaussianSource) :
    precisionInterpolate source₁.mean source₂.mean
        source₁.precision source₂.precision =
      (revisionWTV
        (wtvOfPrecision source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one source₁.precision_pos.le)
        (wtvOfPrecision source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one source₂.precision_pos.le)).strength := by
  rw [precisionInterpolate_eq_gaussianFusion]
  · exact gaussianFusion_eq_plnRevisionWTV source₁ source₂
  · exact ne_of_gt (add_pos source₁.precision_pos source₂.precision_pos)

/-- Belief-state unification crown: one value is simultaneously the
precision-weighted mean, Gaussian posterior fusion, unit-gain Kalman update,
one-step workspace update, and PLN evidence revision; the abstract conjugate
counts recover the two precisions used by that common gate. -/
theorem beliefUpdate_unification
    (source₁ source₂ : GaussianSource) :
    let update := precisionInterpolate source₁.mean source₂.mean
      source₁.precision source₂.precision
    update = gaussianFusion source₁.mean source₂.mean
        source₁.precision source₂.precision ∧
      update = scalarKalmanUpdate source₁.mean source₂.mean 1
        source₁.precision source₂.precision ∧
      update = (scalarKalmanWorkspaceFamily source₂.mean 1
        source₁.precision source₂.precision).step (fun _ => source₁.mean) 0 ∧
      update = (revisionWTV
        (wtvOfPrecision source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one source₁.precision_pos.le)
        (wtvOfPrecision source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one source₂.precision_pos.le)).strength ∧
      ConjugateEvidence.observationCount (pcGaussianEvidenceOfSource source₁) =
        ENNReal.ofReal source₁.precision ∧
      ConjugateEvidence.observationCount (pcGaussianEvidenceOfSource source₂) =
        ENNReal.ofReal source₂.precision := by
  dsimp only
  have hsum : source₁.precision + source₂.precision ≠ 0 :=
    ne_of_gt (add_pos source₁.precision_pos source₂.precision_pos)
  exact ⟨precisionInterpolate_eq_gaussianFusion _ _ _ _ hsum,
    precisionInterpolate_eq_scalarKalmanUpdate _ _ _ _,
    precisionInterpolate_eq_workspaceStep _ _ _ _,
    precisionInterpolate_eq_plnRevision source₁ source₂,
    conjugateObservationCount_gaussianSource_eq_precision source₁,
    conjugateObservationCount_gaussianSource_eq_precision source₂⟩

/-! ## Positive and negative fixtures -/

/-- The existing unequal-precision sources condition to `77/100` through the
common belief update. -/
theorem beliefUpdate_positiveExample :
    precisionInterpolate gaussianRevisionPositiveSource1.mean
      gaussianRevisionPositiveSource2.mean
      gaussianRevisionPositiveSource1.precision
      gaussianRevisionPositiveSource2.precision = 77 / 100 := by
  rw [precisionInterpolate_eq_gaussianFusion]
  · exact gaussianFusion_positive_example
  · norm_num [gaussianRevisionPositiveSource1, gaussianRevisionPositiveSource2]

/-- Zero observation precision contributes no information and therefore
freezes the old mean; positive precision is substantive in the conditioning
crown. -/
theorem zeroObservationPrecision_freezes_negativeBoundary
    (oldMean proposedMean priorPrecision : ℝ) :
    precisionInterpolate oldMean proposedMean priorPrecision 0 = oldMean := by
  simp [precisionInterpolate, precisionGain]

#print axioms precisionInterpolate_eq_workspaceStep
#print axioms ScalarBeliefState.condition_mean_isBayesian
#print axioms ScalarBeliefState.condition_mean_eq_conditionalPosteriorMean
#print axioms conjugateObservationCount_gaussianSource_eq_precision
#print axioms precisionInterpolate_eq_plnRevision
#print axioms beliefUpdate_unification
#print axioms beliefUpdate_positiveExample
#print axioms zeroObservationPrecision_freezes_negativeBoundary

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
