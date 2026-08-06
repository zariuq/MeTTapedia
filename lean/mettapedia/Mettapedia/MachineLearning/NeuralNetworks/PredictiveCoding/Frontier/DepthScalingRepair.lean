import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.CoordinateRescue
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ResidualBoundary
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalityCeiling

/-!
# Depth-scaling repairs for predictive coding

This file formalizes the scalar linear-Gaussian core of Qi, Forasassi,
Lukasiewicz, and Salvatori, *Towards the Training of Deeper Predictive Coding
Neural Networks*, arXiv:2506.23800v3 (2025-10-10).  The authenticated source
artifact used for the current correspondence audit has SHA-256
`8fa1d245be3cf937fa2c4a961d0f8068ca2bfdf4dd753d9413030901c4942c79`.

The chain is genuinely arbitrary-depth: it has `depth + 1` scalar activities
and `depth` weighted Gaussian links.  We derive the activity and weight
gradients by exact finite-increment identities.  This exposes two convention
boundaries in the displayed source equations: with residual
`error = activity - prediction`, the source's displayed activity and weight
updates have the sign of the gradient rather than its negative, and its
activity equation uses the current-layer covariance in both terms.  We keep
the source formula, the covariance-corrected formula, and the mechanically
derived negative-gradient step separate and prove their relationships.

The remaining sections give exact models for four proposed depth repairs:

* a one-sweep inverse-covariance (precision) spike cancels first-arrival
  attenuation;
* a forward-reference error avoids a declared accumulated-prediction drift;
* one auxiliary buffer per skipped edge synchronizes residual-path arrivals;
* frozen batch statistics remain invariant during an inner inference loop.

Claims about nonlinear networks, optimization accuracy, VGG/ResNet
performance, and universal superiority over passive schedules remain
empirical reproduction targets.  The exact theorems below state the scalar
models and assumptions under which the repair mechanisms hold.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open scoped BigOperators

/-! ## T1: an arbitrary-depth scalar linear-Gaussian chain -/

/-- Scalar activities on the `depth + 1` vertices of a linear chain. -/
abbrev DepthActivity (depth : ℕ) := Fin (depth + 1) → ℝ

/-- Scalar link data indexed by the `depth` predictions in the chain. -/
abbrev DepthLinkData (depth : ℕ) := Fin depth → ℝ

/-- Source vertex of a link. -/
def depthSourceNode {depth : ℕ} (link : Fin depth) : Fin (depth + 1) :=
  Fin.castSucc link

/-- Target vertex of a link. -/
def depthTargetNode {depth : ℕ} (link : Fin depth) : Fin (depth + 1) :=
  link.succ

/-- Linear prediction `μⁿ = Wⁿ xⁿ⁻¹` for a scalar link. -/
noncomputable def depthPrediction {depth : ℕ}
    (weight : DepthLinkData depth) (activity : DepthActivity depth)
    (link : Fin depth) : ℝ :=
  weight link * activity (depthSourceNode link)

/-- Prediction error `εⁿ = xⁿ - μⁿ`. -/
noncomputable def depthPredictionError {depth : ℕ}
    (weight : DepthLinkData depth) (activity : DepthActivity depth)
    (link : Fin depth) : ℝ :=
  activity (depthTargetNode link) - depthPrediction weight activity link

/-- One covariance-weighted Gaussian energy term.  The division convention is
that of the cited Eq. 1; positivity is tracked separately. -/
noncomputable def depthLayerEnergy {depth : ℕ}
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (link : Fin depth) : ℝ :=
  (1 / 2 : ℝ) * depthPredictionError weight activity link ^ 2 /
    covariance link

/-- Eq. 1 in the arbitrary-depth scalar linear-Gaussian chain. -/
noncomputable def depthPredictiveCodingEnergy {depth : ℕ}
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) : ℝ :=
  ∑ link : Fin depth, depthLayerEnergy weight covariance activity link

/-- Every link covariance is strictly positive. -/
def PositiveDepthCovariance {depth : ℕ}
    (covariance : DepthLinkData depth) : Prop :=
  ∀ link, 0 < covariance link

/-- Incoming link for a hidden vertex numbered `hidden + 1`. -/
def hiddenIncomingLink {depth : ℕ} (hidden : Fin (depth - 1)) : Fin depth :=
  ⟨hidden.val, by omega⟩

/-- Outgoing link for a hidden vertex numbered `hidden + 1`. -/
def hiddenOutgoingLink {depth : ℕ} (hidden : Fin (depth - 1)) : Fin depth :=
  ⟨hidden.val + 1, by omega⟩

/-- The energy gradient with respect to hidden activity `xˡ`.  This is the
incoming residual force minus the transpose-weighted outgoing force. -/
noncomputable def depthActivityGradient {depth : ℕ}
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1)) : ℝ :=
  depthPredictionError weight activity (hiddenIncomingLink hidden) /
      covariance (hiddenIncomingLink hidden) -
    weight (hiddenOutgoingLink hidden) *
      depthPredictionError weight activity (hiddenOutgoingLink hidden) /
      covariance (hiddenOutgoingLink hidden)

/-- The mechanically derived negative-gradient activity step. -/
noncomputable def depthNegativeGradientActivityStep {depth : ℕ}
    (rate : ℝ) (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1)) : ℝ :=
  -rate * depthActivityGradient weight covariance activity hidden

/-- The source paper's displayed Eq. 2, specialized to scalars.  It uses the
incoming covariance in both terms. -/
noncomputable def paperDisplayedActivityStep {depth : ℕ}
    (rate : ℝ) (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1)) : ℝ :=
  rate *
    (depthPredictionError weight activity (hiddenIncomingLink hidden) /
        covariance (hiddenIncomingLink hidden) -
      weight (hiddenOutgoingLink hidden) *
        depthPredictionError weight activity (hiddenOutgoingLink hidden) /
        covariance (hiddenIncomingLink hidden))

/-- Covariance-corrected reading of the displayed activity formula.  It is
the positive gradient step under `error = activity - prediction`. -/
noncomputable def covarianceCorrectedDisplayedActivityStep {depth : ℕ}
    (rate : ℝ) (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1)) : ℝ :=
  rate * depthActivityGradient weight covariance activity hidden

/-- Exact local two-link energy before perturbing one hidden activity. -/
noncomputable def hiddenPairEnergy
    (incomingError outgoingError _outgoingWeight
      incomingCovariance outgoingCovariance : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (incomingError ^ 2 / incomingCovariance +
      outgoingError ^ 2 / outgoingCovariance)

/-- Exact local energy after adding `perturbation` to a hidden activity. -/
noncomputable def hiddenPairEnergyAfterActivityPerturbation
    (incomingError outgoingError outgoingWeight
      incomingCovariance outgoingCovariance perturbation : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((incomingError + perturbation) ^ 2 / incomingCovariance +
      (outgoingError - outgoingWeight * perturbation) ^ 2 /
        outgoingCovariance)

/-- Exact finite-increment derivation of the activity gradient.  The linear
coefficient is the gradient and the remaining term is quadratic. -/
theorem hiddenPairEnergy_activityIncrement_exact
    (incomingError outgoingError outgoingWeight
      incomingCovariance outgoingCovariance perturbation : ℝ) :
    hiddenPairEnergyAfterActivityPerturbation incomingError outgoingError
        outgoingWeight incomingCovariance outgoingCovariance perturbation -
      hiddenPairEnergy incomingError outgoingError outgoingWeight
        incomingCovariance outgoingCovariance =
      perturbation *
          (incomingError / incomingCovariance -
            outgoingWeight * outgoingError / outgoingCovariance) +
        perturbation ^ 2 / 2 *
          (1 / incomingCovariance +
            outgoingWeight ^ 2 / outgoingCovariance) := by
  unfold hiddenPairEnergyAfterActivityPerturbation hiddenPairEnergy
  ring

/-- The covariance-corrected displayed force is exactly the energy
gradient step, hence the negative-gradient step is its additive inverse. -/
theorem negativeGradientActivityStep_eq_neg_correctedDisplayed
    {depth : ℕ} (rate : ℝ)
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1)) :
    depthNegativeGradientActivityStep rate weight covariance activity hidden =
      -covarianceCorrectedDisplayedActivityStep rate weight covariance
        activity hidden := by
  simp [depthNegativeGradientActivityStep,
    covarianceCorrectedDisplayedActivityStep]

/-- The source's same-covariance formula agrees with the corrected displayed
formula exactly when the adjacent covariances agree. -/
theorem paperDisplayedActivityStep_eq_corrected_of_covariance_eq
    {depth : ℕ} (rate : ℝ)
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (hidden : Fin (depth - 1))
    (hcovariance : covariance (hiddenIncomingLink hidden) =
      covariance (hiddenOutgoingLink hidden)) :
    paperDisplayedActivityStep rate weight covariance activity hidden =
      covarianceCorrectedDisplayedActivityStep rate weight covariance
        activity hidden := by
  simp [paperDisplayedActivityStep,
    covarianceCorrectedDisplayedActivityStep, depthActivityGradient,
    hcovariance]

/-- Gradient of one link energy with respect to its scalar weight. -/
noncomputable def depthWeightGradient {depth : ℕ}
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (link : Fin depth) : ℝ :=
  -depthPredictionError weight activity link *
      activity (depthSourceNode link) / covariance link

/-- Mechanically derived negative-gradient weight step. -/
noncomputable def depthNegativeGradientWeightStep {depth : ℕ}
    (rate : ℝ) (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (link : Fin depth) : ℝ :=
  -rate * depthWeightGradient weight covariance activity link

/-- Source paper's displayed Eq. 3 under the stated residual convention. -/
noncomputable def paperDisplayedWeightStep {depth : ℕ}
    (rate : ℝ) (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (link : Fin depth) : ℝ :=
  -rate * depthPredictionError weight activity link *
    activity (depthSourceNode link) / covariance link

/-- Exact one-link energy before a weight perturbation. -/
noncomputable def oneLinkEnergy
    (predictionError covariance : ℝ) : ℝ :=
  (1 / 2 : ℝ) * predictionError ^ 2 / covariance

/-- Exact one-link energy after adding `perturbation` to the weight. -/
noncomputable def oneLinkEnergyAfterWeightPerturbation
    (predictionError sourceActivity covariance perturbation : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (predictionError - perturbation * sourceActivity) ^ 2 / covariance

/-- Exact finite-increment derivation of the weight gradient. -/
theorem oneLinkEnergy_weightIncrement_exact
    (predictionError sourceActivity covariance perturbation : ℝ) :
    oneLinkEnergyAfterWeightPerturbation predictionError sourceActivity
        covariance perturbation -
      oneLinkEnergy predictionError covariance =
      perturbation *
          (-predictionError * sourceActivity / covariance) +
        perturbation ^ 2 / 2 * sourceActivity ^ 2 / covariance := by
  unfold oneLinkEnergyAfterWeightPerturbation oneLinkEnergy
  ring

/-- Under the paper's residual convention, displayed Eq. 3 is the positive
gradient step; it is opposite to the negative-gradient step. -/
theorem paperDisplayedWeightStep_eq_neg_negativeGradient
    {depth : ℕ} (rate : ℝ)
    (weight covariance : DepthLinkData depth)
    (activity : DepthActivity depth) (link : Fin depth) :
    paperDisplayedWeightStep rate weight covariance activity link =
      -depthNegativeGradientWeightStep rate weight covariance activity link := by
  simp [paperDisplayedWeightStep, depthNegativeGradientWeightStep,
    depthWeightGradient]
  ring

/-- Unit weights. -/
noncomputable def unitDepthWeights (depth : ℕ) : DepthLinkData depth :=
  fun _ ↦ 1

/-- Unit covariances. -/
noncomputable def unitDepthCovariances (depth : ℕ) : DepthLinkData depth :=
  fun _ ↦ 1

/-- Constant activity profile. -/
noncomputable def constantDepthActivity (depth : ℕ) (value : ℝ) :
    DepthActivity depth :=
  fun _ ↦ value

/-- Zero weights. -/
noncomputable def zeroDepthWeights (depth : ℕ) : DepthLinkData depth :=
  fun _ ↦ 0

/-- Ramp activity profile `xˡ = l`. -/
noncomputable def rampDepthActivity (depth : ℕ) : DepthActivity depth :=
  fun node ↦ node.val

/-- Positive fixture: a constant profile is perfectly predicted by every
unit-weight link, at every depth. -/
theorem constant_unitChain_energy_zero (depth : ℕ) (value : ℝ) :
    depthPredictiveCodingEnergy (unitDepthWeights depth)
      (unitDepthCovariances depth) (constantDepthActivity depth value) = 0 := by
  simp [depthPredictiveCodingEnergy, depthLayerEnergy,
    depthPredictionError, depthPrediction, unitDepthWeights,
    unitDepthCovariances, constantDepthActivity]

/-- Positive covariance fixture. -/
theorem unitDepthCovariances_positive (depth : ℕ) :
    PositiveDepthCovariance (unitDepthCovariances depth) := by
  intro link
  norm_num [unitDepthCovariances]

/-- Negative fixture: a zero covariance schedule is outside the
linear-Gaussian domain as soon as a link exists. -/
theorem zeroCovariance_not_positive :
    ¬ PositiveDepthCovariance (fun _ : Fin 1 ↦ (0 : ℝ)) := by
  intro h
  have := h 0
  norm_num at this

/-- Nonzero-energy fixture at depth three. -/
theorem zeroWeight_ramp_depthThree_energy :
    depthPredictiveCodingEnergy (zeroDepthWeights 3)
      (unitDepthCovariances 3) (rampDepthActivity 3) = 7 := by
  norm_num [depthPredictiveCodingEnergy, depthLayerEnergy,
    depthPredictionError, depthPrediction, zeroDepthWeights,
    unitDepthCovariances, rampDepthActivity, depthSourceNode,
    depthTargetNode, Fin.sum_univ_succ]

/-- Concrete covariance-index mismatch: the paper's displayed current-layer
denominator and the corrected adjacent-layer denominator give different
steps. -/
theorem displayedActivity_covarianceMismatch :
    let weight : DepthLinkData 2 := fun _ ↦ 1
    let covariance : DepthLinkData 2 := fun link ↦ if link.val = 0 then 1 else 2
    let activity : DepthActivity 2 := fun node ↦ if node.val = 2 then 1 else 0
    paperDisplayedActivityStep 1 weight covariance activity (0 : Fin 1) = -1 ∧
      covarianceCorrectedDisplayedActivityStep 1 weight covariance activity
        (0 : Fin 1) = -(1 / 2 : ℝ) := by
  norm_num [paperDisplayedActivityStep,
    covarianceCorrectedDisplayedActivityStep, depthActivityGradient,
    depthPredictionError, depthPrediction, hiddenIncomingLink,
    hiddenOutgoingLink, depthSourceNode, depthTargetNode]

/-! ## T2: geometric energy imbalance and finite propagation speed -/

/-- First-arrival error after crossing `distance` state-coordinate links. -/
noncomputable def geometricArrivalError
    (inferenceRate outputError : ℝ) (distance : ℕ) : ℝ :=
  spcWavefrontSignal inferenceRate outputError distance

/-- Energy carried by the first-arrival error, at unit covariance. -/
noncomputable def geometricArrivalEnergy
    (inferenceRate outputError : ℝ) (distance : ℕ) : ℝ :=
  (1 / 2 : ℝ) * geometricArrivalError inferenceRate outputError distance ^ 2

theorem geometricArrivalError_closedForm
    (inferenceRate outputError : ℝ) (distance : ℕ) :
    geometricArrivalError inferenceRate outputError distance =
      inferenceRate ^ distance * outputError := by
  exact spcWavefrontSignal_closedForm inferenceRate outputError distance

/-- Every additional edge multiplies first-arrival energy by `rate²`. -/
theorem geometricArrivalEnergy_succ
    (inferenceRate outputError : ℝ) (distance : ℕ) :
    geometricArrivalEnergy inferenceRate outputError (distance + 1) =
      inferenceRate ^ 2 *
        geometricArrivalEnergy inferenceRate outputError distance := by
  simp [geometricArrivalEnergy, geometricArrivalError_closedForm, pow_succ]
  ring

/-- Exact input/output imbalance after `depth` links. -/
theorem geometricArrivalEnergy_depth_eq
    (inferenceRate outputError : ℝ) (depth : ℕ) :
    geometricArrivalEnergy inferenceRate outputError depth =
      (inferenceRate ^ depth) ^ 2 *
        geometricArrivalEnergy inferenceRate outputError 0 := by
  simp [geometricArrivalEnergy, geometricArrivalError_closedForm]
  ring

/-- In the strictly contractive nonnegative regime, every earlier layer has
strictly less first-arrival energy when the output error is nonzero. -/
theorem geometricArrivalEnergy_strictly_decreases_with_distance
    (inferenceRate outputError : ℝ) (distance : ℕ)
    (hratePositive : 0 < inferenceRate) (hrateContractive : inferenceRate < 1)
    (herror : outputError ≠ 0) :
    geometricArrivalEnergy inferenceRate outputError (distance + 1) <
      geometricArrivalEnergy inferenceRate outputError distance := by
  rw [geometricArrivalEnergy_succ]
  have henergy :
      0 < geometricArrivalEnergy inferenceRate outputError distance := by
    simp [geometricArrivalEnergy, geometricArrivalError_closedForm]
    positivity
  have hsquare : inferenceRate ^ 2 < 1 := by nlinarith
  nlinarith

/-- Negative boundary: a unit inference rate has no geometric depth
imbalance. -/
theorem unitRate_geometricArrivalEnergy_depthInvariant
    (outputError : ℝ) (distance : ℕ) :
    geometricArrivalEnergy 1 outputError distance =
      geometricArrivalEnergy 1 outputError 0 := by
  simp [geometricArrivalEnergy, geometricArrivalError_closedForm]

/-- Terminal vertex at distance `distance` from vertex zero. -/
def chainTerminalNode (distance : ℕ) : Fin (distance + 1) :=
  ⟨distance, by omega⟩

/-- A unit-bandwidth exact update cannot make an input-only distinction reach
layer `layer` in a depth-`depth` chain before `depth - layer` sweeps.  The
chain is reindexed from the output, so its terminal vertex has precisely that
distance. -/
theorem unitBandwidth_exactArrival_requires_depth_sub_layer
    {Value : Type*} (depth layer sweeps : ℕ)
    (step : ChainState Value (depth - layer) →
      ChainState Value (depth - layer))
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ target₀ target₁ : ChainState Value (depth - layer))
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (htarget : target₀ (chainTerminalNode (depth - layer)) ≠
      target₁ (chainTerminalNode (depth - layer)))
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    depth - layer ≤ sweeps := by
  have hreach := hasChainBandwidth_exact_settling_requires_reach
    step hbandwidth initial₀ initial₁ target₀ target₁ haway
    (chainTerminalNode (depth - layer)) htarget hsettle₀ hsettle₁
  simpa [chainTerminalNode] using hreach

/-- Coordinate-rescue bridge: the geometric profile is exactly the sealed
sPC state-coordinate wavefront, not a new recurrence. -/
theorem geometricArrivalError_eq_sealedWavefront
    (inferenceRate outputError : ℝ) (distance : ℕ) :
    geometricArrivalError inferenceRate outputError distance =
      spcWavefrontSignal inferenceRate outputError distance := by
  rfl

/-- Concrete contrast with the residual boundary: the half-rate state
wavefront has magnitude `1/16` after four links, whereas a half-strength
residual branch has multiplier `81/16`.  These are different recurrences,
so this theorem is a contrast rather than an identification. -/
theorem halfRate_wavefront_vs_residual_depthFour :
    |geometricArrivalError (1 / 2) 1 4| = 1 / 16 ∧
      residualStackMultiplier (1 / 2) 4 = 81 / 16 := by
  constructor
  · norm_num [geometricArrivalError, spcWavefrontSignal_closedForm]
  · norm_num [residualStackMultiplier]

/-! ## T3: spiking covariance and schedule separation -/

/-- Eq. 4, indexed by distance from the output: the covariance is `spike`
exactly when the error wavefront first arrives. -/
noncomputable def spikingCovariance
    (spike : ℝ) (time distance : ℕ) : ℝ :=
  if distance = time then spike else 1

/-- A local first-arrival update with propagation factor `rate`, incoming
signal `signal`, and covariance `covariance`. -/
noncomputable def covarianceWeightedArrivalUpdate
    (rate signal covariance : ℝ) : ℝ :=
  rate * signal / covariance

/-- At the wavefront, choosing covariance equal to the propagation rate
cancels one step of attenuation exactly. -/
theorem spikingCovariance_equalizes_firstArrival
    (rate signal : ℝ) (distance : ℕ) (hrate : rate ≠ 0) :
    covarianceWeightedArrivalUpdate rate signal
        (spikingCovariance rate distance distance) = signal := by
  simp [covarianceWeightedArrivalUpdate, spikingCovariance, hrate]

/-- Away from the wavefront, the same schedule leaves unit covariance. -/
theorem spikingCovariance_off_front
    (rate : ℝ) (time distance : ℕ) (hoff : distance ≠ time) :
    spikingCovariance rate time distance = 1 := by
  simp [spikingCovariance, hoff]

/-- Exact arbitrary-depth equalization: every layer's first-arrival update is
the same incoming signal when its own arrival time is used. -/
theorem spikingCovariance_equalizes_all_layers
    (rate signal : ℝ) (depth layer : ℕ) (hrate : rate ≠ 0) :
    covarianceWeightedArrivalUpdate rate signal
        (spikingCovariance rate (depth - layer) (depth - layer)) = signal := by
  exact spikingCovariance_equalizes_firstArrival rate signal
    (depth - layer) hrate

/-- Signal transported across successive first-arrival updates under an
arbitrary covariance schedule.  Index `step` is the distance already crossed
from the output. -/
noncomputable def scheduledFirstArrivalSignal
    (rate : ℝ) (covarianceAtArrival : ℕ → ℝ) (signal : ℝ) : ℕ → ℝ
  | 0 => signal
  | distance + 1 =>
      covarianceWeightedArrivalUpdate rate
        (scheduledFirstArrivalSignal rate covarianceAtArrival signal distance)
        (covarianceAtArrival distance)

/-- General schedule-level closed form: cumulative first-arrival transport is
the product of the local rate-to-covariance ratios. -/
theorem scheduledFirstArrivalSignal_closedForm
    (rate : ℝ) (covarianceAtArrival : ℕ → ℝ)
    (signal : ℝ) (distance : ℕ) :
    scheduledFirstArrivalSignal rate covarianceAtArrival signal distance =
      (∏ step ∈ Finset.range distance,
        rate / covarianceAtArrival step) * signal := by
  induction distance with
  | zero =>
      simp [scheduledFirstArrivalSignal]
  | succ distance ih =>
      rw [scheduledFirstArrivalSignal, ih]
      simp only [covarianceWeightedArrivalUpdate, Finset.prod_range_succ]
      ring

/-- Unit covariance recovers the ordinary geometric wavefront at every
depth. -/
theorem scheduledFirstArrivalSignal_unitCovariance
    (rate signal : ℝ) (distance : ℕ) :
    scheduledFirstArrivalSignal rate (fun _ ↦ 1) signal distance =
      rate ^ distance * signal := by
  rw [scheduledFirstArrivalSignal_closedForm]
  simp

/-- Applying the source spike at every layer's own first-arrival time removes
the entire depth product, not merely one isolated local attenuation. -/
theorem scheduledFirstArrivalSignal_spikingCovariance
    (rate signal : ℝ) (distance : ℕ) (hrate : rate ≠ 0) :
    scheduledFirstArrivalSignal rate
        (fun step ↦ spikingCovariance rate step step) signal distance =
      signal := by
  rw [scheduledFirstArrivalSignal_closedForm]
  simp [spikingCovariance, hrate]

/-- The unit-covariance schedule is definitionally the previously sealed sPC
wavefront recurrence. -/
theorem scheduledFirstArrivalSignal_unit_eq_geometricArrivalError
    (rate signal : ℝ) (distance : ℕ) :
    scheduledFirstArrivalSignal rate (fun _ ↦ 1) signal distance =
      geometricArrivalError rate signal distance := by
  rw [scheduledFirstArrivalSignal_unitCovariance,
    geometricArrivalError_closedForm]

/-- In the positive contractive regime and at nonzero depth, the complete
spiking schedule transports strictly more positive first-arrival signal than
the unit-covariance schedule.  This is a signal theorem, not an accuracy
claim. -/
theorem scheduledSpiking_strictly_exceeds_unitCovariance
    (rate signal : ℝ) (distance : ℕ)
    (hratePositive : 0 < rate) (hrateContractive : rate < 1)
    (hsignal : 0 < signal) (hdistance : 0 < distance) :
    scheduledFirstArrivalSignal rate (fun _ ↦ 1) signal distance <
      scheduledFirstArrivalSignal rate
        (fun step ↦ spikingCovariance rate step step) signal distance := by
  rw [scheduledFirstArrivalSignal_unitCovariance,
    scheduledFirstArrivalSignal_spikingCovariance rate signal distance
      (ne_of_gt hratePositive)]
  have hpower : rate ^ distance < 1 :=
    pow_lt_one₀ (le_of_lt hratePositive) hrateContractive
      (Nat.ne_of_gt hdistance)
  nlinarith

/-- Negative fixture: a zero propagation rate cannot be rescued by choosing
zero covariance, because division by zero remains zero in the field
convention.  The nonzero-rate premise is substantive. -/
theorem zeroRate_spike_does_not_equalize_unitSignal (distance : ℕ) :
    covarianceWeightedArrivalUpdate 0 1
      (spikingCovariance 0 distance distance) = 0 := by
  simp [covarianceWeightedArrivalUpdate, spikingCovariance]

/-- Any positive covariance strictly larger than the propagation rate
under-propagates a positive incoming signal relative to the spike. -/
theorem passiveCovariance_underpropagates
    (rate signal passiveCovariance : ℝ)
    (hrate : 0 < rate) (hsignal : 0 < signal)
    (hpassive : rate < passiveCovariance) :
    covarianceWeightedArrivalUpdate rate signal passiveCovariance < signal := by
  have hcovariance : 0 < passiveCovariance := lt_trans hrate hpassive
  rw [covarianceWeightedArrivalUpdate, div_lt_iff₀ hcovariance]
  nlinarith

/-- A simple passive linear-decay covariance approaching `rate` from above. -/
noncomputable def passiveLinearCovariance
    (rate : ℝ) (time : ℕ) : ℝ :=
  rate + (1 - rate) / (time + 2 : ℕ)

/-- A simple passive exponential-decay covariance approaching `rate` from
above. -/
noncomputable def passiveExponentialCovariance
    (rate decay : ℝ) (time : ℕ) : ℝ :=
  rate + (1 - rate) * decay ^ time

theorem rate_lt_passiveLinearCovariance
    (rate : ℝ) (time : ℕ) (hrate : rate < 1) :
    rate < passiveLinearCovariance rate time := by
  unfold passiveLinearCovariance
  have hdenominator : (0 : ℝ) < (time + 2 : ℕ) := by positivity
  have hnumerator : 0 < 1 - rate := sub_pos.mpr hrate
  have : 0 < (1 - rate) / (time + 2 : ℕ) :=
    div_pos hnumerator hdenominator
  linarith

theorem rate_lt_passiveExponentialCovariance
    (rate decay : ℝ) (time : ℕ)
    (hrate : rate < 1) (hdecay : 0 < decay) :
    rate < passiveExponentialCovariance rate decay time := by
  unfold passiveExponentialCovariance
  have : 0 < (1 - rate) * decay ^ time := by positivity
  linarith

/-- Linear-decay separation at first arrival. -/
theorem passiveLinear_underpropagates_at_arrival
    (rate signal : ℝ) (time : ℕ)
    (hratePositive : 0 < rate) (hrateContractive : rate < 1)
    (hsignal : 0 < signal) :
    covarianceWeightedArrivalUpdate rate signal
        (passiveLinearCovariance rate time) < signal := by
  exact passiveCovariance_underpropagates rate signal
    (passiveLinearCovariance rate time) hratePositive hsignal
    (rate_lt_passiveLinearCovariance rate time hrateContractive)

/-- Exponential-decay separation at first arrival. -/
theorem passiveExponential_underpropagates_at_arrival
    (rate decay signal : ℝ) (time : ℕ)
    (hratePositive : 0 < rate) (hrateContractive : rate < 1)
    (hdecay : 0 < decay) (hsignal : 0 < signal) :
    covarianceWeightedArrivalUpdate rate signal
        (passiveExponentialCovariance rate decay time) < signal := by
  exact passiveCovariance_underpropagates rate signal
    (passiveExponentialCovariance rate decay time) hratePositive hsignal
    (rate_lt_passiveExponentialCovariance rate decay time
      hrateContractive hdecay)

/-! ## T4: forward-reference errors and accumulated prediction drift -/

/-- Prediction displacement accumulated through all preceding layers. -/
noncomputable def cumulativePredictionDrift
    (drift : ℕ → ℝ) (layer : ℕ) : ℝ :=
  ∑ index ∈ Finset.range layer, drift index

/-- Standard settled prediction error in a declared additive-drift model. -/
noncomputable def standardSettledPredictionError
    (initialPrediction finalActivity drift : ℕ → ℝ)
    (layer : ℕ) : ℝ :=
  finalActivity layer -
    (initialPrediction layer + cumulativePredictionDrift drift layer)

/-- Eq. 5 forward-reference error: final activity minus the stored initial
feed-forward prediction. -/
noncomputable def forwardReferencePredictionError
    (initialPrediction finalActivity : ℕ → ℝ) (layer : ℕ) : ℝ :=
  finalActivity layer - initialPrediction layer

/-- The standard and forward-reference errors differ exactly by accumulated
prediction drift. -/
theorem standardSettledError_eq_forward_sub_cumulativeDrift
    (initialPrediction finalActivity drift : ℕ → ℝ)
    (layer : ℕ) :
    standardSettledPredictionError initialPrediction finalActivity drift layer =
      forwardReferencePredictionError initialPrediction finalActivity layer -
        cumulativePredictionDrift drift layer := by
  simp [standardSettledPredictionError, forwardReferencePredictionError]
  ring

/-- Constant per-layer drift accumulates linearly with depth. -/
theorem cumulativePredictionDrift_const (drift : ℝ) (layer : ℕ) :
    cumulativePredictionDrift (fun _ ↦ drift) layer = (layer : ℝ) * drift := by
  simp [cumulativePredictionDrift]

/-- Exact constant-drift profile: the forward error stays equal to `signal`,
while the settled-prediction error includes the depth-linear drift. -/
theorem constantDrift_standard_vs_forward
    (signal drift : ℝ) (layer : ℕ) :
    standardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ signal)
        (fun _ ↦ drift) layer = signal - (layer : ℝ) * drift ∧
      forwardReferencePredictionError (fun _ ↦ 0) (fun _ ↦ signal)
        layer = signal := by
  constructor
  · simp [standardSettledPredictionError, cumulativePredictionDrift]
  · simp [forwardReferencePredictionError]

/-- Positive fixture: with zero forward error and unit per-layer prediction
drift, the standard error magnitude is exactly the layer index. -/
theorem unitDrift_standardError_abs_eq_layer (layer : ℕ) :
    |standardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ 0)
      (fun _ ↦ 1) layer| = (layer : ℝ) := by
  simp [standardSettledPredictionError, cumulativePredictionDrift,
    abs_of_nonneg]

/-- The same fixture has identically zero forward-reference error. -/
theorem unitDrift_forwardError_zero (layer : ℕ) :
    forwardReferencePredictionError (fun _ ↦ 0) (fun _ ↦ 0) layer = 0 := by
  simp [forwardReferencePredictionError]

/-- Consequently the standard error is unbounded over depth in this declared
accumulated-drift model, while the forward error remains zero. -/
theorem unitDrift_standardError_unbounded (bound : ℝ) :
    ∃ layer : ℕ,
      bound < |standardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ 0)
        (fun _ ↦ 1) layer| := by
  obtain ⟨layer, hlayer⟩ := exists_nat_gt bound
  refine ⟨layer, ?_⟩
  rw [unitDrift_standardError_abs_eq_layer]
  exact hlayer

/-- Negative boundary: without prediction drift, standard and
forward-reference errors coincide.  Forward updates are not universally
different from standard updates. -/
theorem zeroDrift_standard_eq_forward
    (initialPrediction finalActivity : ℕ → ℝ) (layer : ℕ) :
    standardSettledPredictionError initialPrediction finalActivity
        (fun _ ↦ 0) layer =
      forwardReferencePredictionError initialPrediction finalActivity layer := by
  simp [standardSettledPredictionError, forwardReferencePredictionError,
    cumulativePredictionDrift]

/-- Scalar local weight credit before application of its learning rate and
sign convention. -/
noncomputable def scalarPredictionWeightCredit
    (predictionError presynapticActivity : ℝ) : ℝ :=
  predictionError * presynapticActivity

/-- The forward-reference weight credit is the settled-prediction credit plus
an exact accumulated-drift correction.  This lifts the error identity to the
quantity that actually updates a scalar weight. -/
theorem forwardReferenceWeightCredit_eq_standard_add_drift
    (initialPrediction finalActivity drift : ℕ → ℝ)
    (layer : ℕ) (presynapticActivity : ℝ) :
    scalarPredictionWeightCredit
        (forwardReferencePredictionError initialPrediction finalActivity layer)
        presynapticActivity =
      scalarPredictionWeightCredit
          (standardSettledPredictionError initialPrediction finalActivity
            drift layer)
          presynapticActivity +
        cumulativePredictionDrift drift layer * presynapticActivity := by
  rw [standardSettledError_eq_forward_sub_cumulativeDrift]
  simp [scalarPredictionWeightCredit]
  ring

/-- Mechanism-separation fixture: prediction drift can make forward-reference
and settled-prediction weight credits point in opposite directions. -/
theorem forwardReferenceWeightCredit_can_reverse_standard :
    scalarPredictionWeightCredit
        (standardSettledPredictionError (fun _ ↦ 0) (fun _ ↦ 1)
          (fun _ ↦ 2) 1) 1 = -1 ∧
      scalarPredictionWeightCredit
        (forwardReferencePredictionError (fun _ ↦ 0) (fun _ ↦ 1) 1) 1 = 1 := by
  norm_num [scalarPredictionWeightCredit, standardSettledPredictionError,
    forwardReferencePredictionError, cumulativePredictionDrift]

/-- Negative boundary: a zero presynaptic activity erases the distinction
between the two error references at that weight. -/
theorem zeroPresynapticActivity_erases_forwardCreditDifference
    (initialPrediction finalActivity drift : ℕ → ℝ) (layer : ℕ) :
    scalarPredictionWeightCredit
        (forwardReferencePredictionError initialPrediction finalActivity layer)
        0 =
      scalarPredictionWeightCredit
        (standardSettledPredictionError initialPrediction finalActivity drift
          layer)
        0 := by
  simp [scalarPredictionWeightCredit]

/-! ## T5: residual timing and auxiliary buffers -/

/-- Arrival time through a main path containing `skipped + 1` local edges. -/
def residualMainPathArrivalTime (skipped : ℕ) : ℕ := skipped + 1

/-- Arrival time through an unbuffered one-edge residual skip. -/
def residualSkipArrivalTime : ℕ := 1

/-- A residual skip and its main path are temporally mismatched whenever the
skip bypasses at least one intermediate layer. -/
theorem residualSkip_arrives_early
    (skipped : ℕ) (hskipped : 0 < skipped) :
    residualSkipArrivalTime < residualMainPathArrivalTime skipped := by
  simp [residualSkipArrivalTime, residualMainPathArrivalTime]
  omega

/-- Number of unit-delay auxiliary buffers prescribed for a skip. -/
def residualAuxiliaryBufferCount (skipped : ℕ) : ℕ := skipped

/-- Arrival time of the buffered residual path. -/
def bufferedResidualArrivalTime (skipped : ℕ) : ℕ :=
  residualSkipArrivalTime + residualAuxiliaryBufferCount skipped

/-- One auxiliary buffer per skipped layer synchronizes the two paths
exactly. -/
theorem auxiliaryBuffers_synchronize_residual_paths (skipped : ℕ) :
    bufferedResidualArrivalTime skipped = residualMainPathArrivalTime skipped := by
  simp [bufferedResidualArrivalTime, residualSkipArrivalTime,
    residualAuxiliaryBufferCount, residualMainPathArrivalTime]
  omega

/-- Negative fixture: one fewer buffer still arrives one sweep early. -/
theorem insufficientAuxiliaryBuffers_arrive_early
    (skipped : ℕ) (hskipped : 0 < skipped) :
    residualSkipArrivalTime + (skipped - 1) <
      residualMainPathArrivalTime skipped := by
  simp [residualSkipArrivalTime, residualMainPathArrivalTime]
  omega

/-- Finite-speed bridge: an exact unit-bandwidth signal along the main path
requires at least `skipped + 1` sweeps.  Thus the timing model above is the
tight lower-bound clock supplied by the generic locality theorem. -/
theorem residualMainPath_exactSignal_requires_sweeps
    {Value : Type*} (skipped sweeps : ℕ)
    (step : ChainState Value (skipped + 1) → ChainState Value (skipped + 1))
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ target₀ target₁ : ChainState Value (skipped + 1))
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (htarget : target₀ (chainTerminalNode (skipped + 1)) ≠
      target₁ (chainTerminalNode (skipped + 1)))
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    skipped + 1 ≤ sweeps := by
  simpa using
    (unitBandwidth_exactArrival_requires_depth_sub_layer
      (depth := skipped + 1) (layer := 0) (sweeps := sweeps)
      step hbandwidth initial₀ initial₁ target₀ target₁ haway
      htarget hsettle₀ hsettle₁)

/-! ## T6: frozen batch statistics during the inner loop -/

/-- One live exponential-moving-average update of a batch statistic. -/
noncomputable def liveBatchStatisticStep
    (momentum batch statistic : ℝ) : ℝ :=
  momentum * statistic + (1 - momentum) * batch

/-- A frozen statistic is unchanged during an inference step. -/
noncomputable def frozenBatchStatisticStep (statistic : ℝ) : ℝ :=
  statistic

/-- Frozen statistics remain exactly invariant for every number of inner
inference steps. -/
theorem frozenBatchStatistic_iterate_exact (statistic : ℝ) (steps : ℕ) :
    Nat.iterate frozenBatchStatisticStep steps statistic = statistic := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [Function.iterate_succ_apply', frozenBatchStatisticStep, ih]

/-- Closed form of repeated live statistic updates. -/
theorem liveBatchStatistic_iterate_exact
    (momentum batch statistic : ℝ) (steps : ℕ) :
    Nat.iterate (liveBatchStatisticStep momentum batch) steps statistic =
      batch + momentum ^ steps * (statistic - batch) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [liveBatchStatisticStep, pow_succ]
      ring

/-- With nonunit momentum, the unique live-statistic fixed point is the
current batch statistic. -/
theorem liveBatchStatistic_fixedPoint_iff
    (momentum batch statistic : ℝ) (hmomentum : momentum ≠ 1) :
    liveBatchStatisticStep momentum batch statistic = statistic ↔
      statistic = batch := by
  constructor
  · intro hfixed
    have hfactor : (1 - momentum) * (batch - statistic) = 0 := by
      calc
        (1 - momentum) * (batch - statistic) =
            liveBatchStatisticStep momentum batch statistic - statistic := by
          simp [liveBatchStatisticStep]
          ring
        _ = 0 := by rw [hfixed]; ring
    rcases mul_eq_zero.mp hfactor with hmomentumZero | hstatistic
    · exfalso
      apply hmomentum
      linarith
    · linarith
  · intro hstatistic
    simp [liveBatchStatisticStep, hstatistic]
    ring

/-- Every value is a fixed point of the frozen inner-loop statistic map. -/
theorem frozenBatchStatistic_fixedPoint (statistic : ℝ) :
    frozenBatchStatisticStep statistic = statistic := by
  rfl

/-- Scalar form of Eq. 6.  Mean and variance are explicit state variables so
the effect of freezing them can be stated independently of network accuracy. -/
noncomputable def scalarBatchNormalize
    (scale bias epsilon mean variance input : ℝ) : ℝ :=
  scale * ((input - mean) / Real.sqrt (variance + epsilon)) + bias

/-- Frozen statistics make the normalization map invariant throughout the
inner inference loop. -/
theorem scalarBatchNormalize_frozen_invariant
    (scale bias epsilon mean variance input : ℝ) (steps : ℕ) :
    scalarBatchNormalize scale bias epsilon
        (Nat.iterate frozenBatchStatisticStep steps mean) variance input =
      scalarBatchNormalize scale bias epsilon mean variance input := by
  rw [frozenBatchStatistic_iterate_exact]

/-- Freezing both mean and variance makes the full scalar normalization map
invariant throughout the inner loop. -/
theorem scalarBatchNormalize_bothStatistics_frozen_invariant
    (scale bias epsilon mean variance input : ℝ) (steps : ℕ) :
    scalarBatchNormalize scale bias epsilon
        (Nat.iterate frozenBatchStatisticStep steps mean)
        (Nat.iterate frozenBatchStatisticStep steps variance) input =
      scalarBatchNormalize scale bias epsilon mean variance input := by
  rw [frozenBatchStatistic_iterate_exact,
    frozenBatchStatistic_iterate_exact]

/-- Distance of a running statistic from a fixed reference statistic. -/
noncomputable def statisticReferenceError
    (reference statistic : ℝ) : ℝ := |statistic - reference|

/-- Concrete statistic-overfitting fixture: starting at the reference zero,
a live zero-momentum step on batch one moves distance one away, whereas a
frozen step stays at the reference. -/
theorem liveStatistic_can_move_away_from_reference :
    statisticReferenceError 0 (frozenBatchStatisticStep 0) = 0 ∧
      statisticReferenceError 0 (liveBatchStatisticStep 0 1 0) = 1 := by
  norm_num [statisticReferenceError, frozenBatchStatisticStep,
    liveBatchStatisticStep]

/-- The same fixture changes the normalized activation from zero to minus
one when the live mean is reused, while freezing preserves zero. -/
theorem liveStatistic_changes_normalization :
    scalarBatchNormalize 1 0 1 0 0 0 = 0 ∧
      scalarBatchNormalize 1 0 1 (liveBatchStatisticStep 0 1 0) 0 0 = -1 := by
  norm_num [scalarBatchNormalize, liveBatchStatisticStep]

/-- Negative boundary: if the live batch equals the current statistic, live
and frozen updates coincide. -/
theorem liveStatistic_eq_frozen_of_batch_eq
    (momentum statistic : ℝ) :
    liveBatchStatisticStep momentum statistic statistic =
      frozenBatchStatisticStep statistic := by
  simp [liveBatchStatisticStep, frozenBatchStatisticStep]
  ring

/-! ## T7: integrated certificate and empirical boundary -/

/-- Exact theorem fields shared by the four repair mechanisms. -/
structure DepthScalingRepairCertificate : Prop where
  activityConvention :
    ∀ {depth : ℕ} (rate : ℝ)
      (weight covariance : DepthLinkData depth)
      (activity : DepthActivity depth) (hidden : Fin (depth - 1)),
      depthNegativeGradientActivityStep rate weight covariance activity hidden =
        -covarianceCorrectedDisplayedActivityStep rate weight covariance
          activity hidden
  weightConvention :
    ∀ {depth : ℕ} (rate : ℝ)
      (weight covariance : DepthLinkData depth)
      (activity : DepthActivity depth) (link : Fin depth),
      paperDisplayedWeightStep rate weight covariance activity link =
        -depthNegativeGradientWeightStep rate weight covariance activity link
  spikingEqualization :
    ∀ (rate signal : ℝ) (distance : ℕ), rate ≠ 0 →
      covarianceWeightedArrivalUpdate rate signal
        (spikingCovariance rate distance distance) = signal
  scheduleSpikingEqualization :
    ∀ (rate signal : ℝ) (distance : ℕ), rate ≠ 0 →
      scheduledFirstArrivalSignal rate
        (fun step ↦ spikingCovariance rate step step) signal distance = signal
  forwardZeroDrift :
    ∀ (initialPrediction finalActivity : ℕ → ℝ) (layer : ℕ),
      standardSettledPredictionError initialPrediction finalActivity
          (fun _ ↦ 0) layer =
        forwardReferencePredictionError initialPrediction finalActivity layer
  forwardWeightCreditDecomposition :
    ∀ (initialPrediction finalActivity drift : ℕ → ℝ)
      (layer : ℕ) (presynapticActivity : ℝ),
      scalarPredictionWeightCredit
          (forwardReferencePredictionError initialPrediction finalActivity
            layer)
          presynapticActivity =
        scalarPredictionWeightCredit
            (standardSettledPredictionError initialPrediction finalActivity
              drift layer)
            presynapticActivity +
          cumulativePredictionDrift drift layer * presynapticActivity
  residualSynchronization :
    ∀ skipped : ℕ,
      bufferedResidualArrivalTime skipped = residualMainPathArrivalTime skipped
  frozenStatistic :
    ∀ (statistic : ℝ) (steps : ℕ),
      Nat.iterate frozenBatchStatisticStep steps statistic = statistic

/-- Composition crown: the sign/covariance boundary and all four repair
mechanisms are assembled from the independently proved arbitrary-depth
theorems. -/
theorem depthScalingRepair : DepthScalingRepairCertificate where
  activityConvention := negativeGradientActivityStep_eq_neg_correctedDisplayed
  weightConvention := paperDisplayedWeightStep_eq_neg_negativeGradient
  spikingEqualization := spikingCovariance_equalizes_firstArrival
  scheduleSpikingEqualization :=
    scheduledFirstArrivalSignal_spikingCovariance
  forwardZeroDrift := zeroDrift_standard_eq_forward
  forwardWeightCreditDecomposition :=
    forwardReferenceWeightCredit_eq_standard_add_drift
  residualSynchronization := auxiliaryBuffers_synchronize_residual_paths
  frozenStatistic := frozenBatchStatistic_iterate_exact

inductive DepthScalingClaimStatus
  | exactScalarTheorem
  | empiricalReproductionTarget
  deriving DecidableEq, Repr

structure DepthScalingBoundaryClaim where
  description : String
  status : DepthScalingClaimStatus
  deriving DecidableEq, Repr

/-- The cited deep-network performance result is recorded as an empirical
target, not inferred from the scalar repair certificate. -/
def deepResNetPerformanceBoundary : DepthScalingBoundaryClaim where
  description :=
    "nonlinear VGG/ResNet accuracy and optimization improvements from integrated repairs"
  status := .empiricalReproductionTarget

/-- Universal dominance over all passive schedules is likewise outside the
exact separation proved for the explicit linear and exponential fixtures. -/
def passiveScheduleDominanceBoundary : DepthScalingBoundaryClaim where
  description :=
    "universal accuracy dominance of spiking covariance over every passive schedule"
  status := .empiricalReproductionTarget

/-- The observed cross-layer energy profile and its causal connection to
accuracy are experimental measurements, not consequences of the geometric
first-arrival model alone. -/
def observedEnergyImbalanceBoundary : DepthScalingBoundaryClaim where
  description :=
    "measured layer-energy imbalance and its causal relation to deep-network accuracy"
  status := .empiricalReproductionTarget

/-- Frozen statistics are exactly invariant above, but convergence and
generalization of a nonlinear normalized PC network remain empirical. -/
def batchFreezingNetworkStabilityBoundary : DepthScalingBoundaryClaim where
  description :=
    "nonlinear network convergence and generalization under BatchNorm Freezing"
  status := .empiricalReproductionTarget

theorem deepResNetPerformanceBoundary_not_exact :
    deepResNetPerformanceBoundary.status ≠ .exactScalarTheorem := by
  decide

theorem passiveScheduleDominanceBoundary_not_exact :
    passiveScheduleDominanceBoundary.status ≠ .exactScalarTheorem := by
  decide

theorem observedEnergyImbalanceBoundary_not_exact :
    observedEnergyImbalanceBoundary.status ≠ .exactScalarTheorem := by
  decide

theorem batchFreezingNetworkStabilityBoundary_not_exact :
    batchFreezingNetworkStabilityBoundary.status ≠ .exactScalarTheorem := by
  decide

#print axioms hiddenPairEnergy_activityIncrement_exact
#print axioms oneLinkEnergy_weightIncrement_exact
#print axioms unitBandwidth_exactArrival_requires_depth_sub_layer
#print axioms spikingCovariance_equalizes_all_layers
#print axioms scheduledFirstArrivalSignal_spikingCovariance
#print axioms forwardReferenceWeightCredit_eq_standard_add_drift
#print axioms forwardReferenceWeightCredit_can_reverse_standard
#print axioms residualMainPath_exactSignal_requires_sweeps
#print axioms depthScalingRepair

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
