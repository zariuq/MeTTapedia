import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.PCInference
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ErrorStateReparameterization
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.TrustRegion
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ProspectiveInterference
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.FrozenAdapterConditionalAdvantage

/-!
# Predictive-coding plasticity frontier

Predictive coding is licensed here as a learning rule only under explicit
update conditions.  Unit-rate error-coordinate plasticity is exactly the
backpropagation product.  Curvature-normalized scalar PC is loss-decreasing
precisely for preconditioners in `(0,2)`, while identity is the unique
one-step optimum.  Prospective activity can strictly preserve an old output
when the old path is live and the hidden repair moves.  Trust-region algebra
is exact only inside its quadratic model, and the unrestricted strict-saddle
claim has a counterexample.

The new result is a sharp anti-overshoot analysis.  Scalar gradient endpoints
remain on the same target-residual branch exactly when their residual step
factors have nonnegative product.  Unit trust bounds imply this H5 condition,
so the frozen-adapter source-forgetting comparison follows from a step bound
rather than being imposed as an unexplained premise.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

/-! ## BP-equivalent and preconditioned regimes -/

/-- Proof-bearing equality between a PC plasticity update and its BP target. -/
structure BPEquivalentPlasticityLicense
    (pcUpdate bpUpdate : ℝ) : Prop where
  updatesEqual : pcUpdate = bpUpdate

/-- Unit-rate one-step error-coordinate PC is exactly the scalar BP product. -/
theorem epcOneStep_bpEquivalentLicense
    (predictionJacobian lossGradient : ℝ) :
    BPEquivalentPlasticityLicense
      (pcLocalParameterUpdate predictionJacobian
        (epcOneStepError 1 lossGradient))
      (predictionJacobian * lossGradient) :=
  ⟨epcOneStepParameterUpdate_unitRate_eq_backprop _ _⟩

/-- Curvature-normalized BP update, before a PC preconditioner is applied. -/
noncomputable def chainLinkNormalizedBPUpdate
    (sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  weight - chainLinkNormalizedBackpropDirection
    sourceActivation downstreamGain target weight

/-- Identity-preconditioned PC is definitionally the curvature-normalized BP
update. -/
theorem identityPreconditionedPC_bpEquivalentLicense
    (sourceActivation downstreamGain target weight : ℝ) :
    BPEquivalentPlasticityLicense
      (chainLinkPreconditionedPCUpdate 1 sourceActivation downstreamGain
        target weight)
      (chainLinkNormalizedBPUpdate sourceActivation downstreamGain
        target weight) := by
  constructor
  simp [chainLinkPreconditionedPCUpdate, chainLinkNormalizedBPUpdate]

/-! ## Sharp trust and anti-overshoot bounds -/

/-- Endpoint of a scalar quadratic gradient step with dimensionless step
factor `step`. -/
noncomputable def scalarGradientEndpoint
    (targetCenter initial step : ℝ) : ℝ :=
  initial - step * (initial - targetCenter)

theorem scalarGradientEndpoint_residual_exact
    (targetCenter initial step : ℝ) :
    scalarGradientEndpoint targetCenter initial step - targetCenter =
      (1 - step) * (initial - targetCenter) := by
  unfold scalarGradientEndpoint
  ring

/-- A scalar step does not cross the target relative to its initial point. -/
def DoesNotOvershoot
    (targetCenter initial endpoint : ℝ) : Prop :=
  0 ≤ (endpoint - targetCenter) * (initial - targetCenter)

/-- Sharp one-step anti-overshoot boundary away from the optimum: no target
crossing holds exactly for `step ≤ 1`. -/
theorem scalarGradientEndpoint_doesNotOvershoot_iff
    (targetCenter initial step : ℝ) (hnontrivial : initial ≠ targetCenter) :
    DoesNotOvershoot targetCenter initial
        (scalarGradientEndpoint targetCenter initial step) ↔
      step ≤ 1 := by
  have hsquare : 0 < (initial - targetCenter) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hnontrivial)
  unfold DoesNotOvershoot
  rw [scalarGradientEndpoint_residual_exact]
  have hfactor :
      (1 - step) * (initial - targetCenter) *
          (initial - targetCenter) =
        (1 - step) * (initial - targetCenter) ^ 2 := by ring
  rw [hfactor]
  exact (mul_nonneg_iff_of_pos_right hsquare).trans sub_nonneg

/-- Exact paired-H5 boundary: two scalar gradient endpoints lie on the same
target-residual branch iff their two residual step factors have nonnegative
product. -/
theorem sameTargetResidualBranch_gradientEndpoints_iff
    (targetCenter initial pcStep bpStep : ℝ)
    (hnontrivial : initial ≠ targetCenter) :
    SameTargetResidualBranch targetCenter
        (scalarGradientEndpoint targetCenter initial pcStep)
        (scalarGradientEndpoint targetCenter initial bpStep) ↔
      0 ≤ (1 - pcStep) * (1 - bpStep) := by
  have hsquare : 0 < (initial - targetCenter) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hnontrivial)
  unfold SameTargetResidualBranch
  rw [scalarGradientEndpoint_residual_exact,
    scalarGradientEndpoint_residual_exact]
  have hfactor :
      (1 - pcStep) * (initial - targetCenter) *
          ((1 - bpStep) * (initial - targetCenter)) =
        ((1 - pcStep) * (1 - bpStep)) *
          (initial - targetCenter) ^ 2 := by ring
  rw [hfactor, mul_nonneg_iff_of_pos_right hsquare]

/-- The unit trust interval is the no-overshoot half of the larger strict
descent interval `(0,2)`. -/
def UnitTrustBound (step : ℝ) : Prop :=
  0 ≤ step ∧ step ≤ 1

/-- Two unit-trust-bounded updates automatically satisfy frozen-adapter H5. -/
theorem unitTrustBounds_imply_sameTargetResidualBranch
    (targetCenter initial pcStep bpStep : ℝ)
    (hpc : UnitTrustBound pcStep) (hbp : UnitTrustBound bpStep) :
    SameTargetResidualBranch targetCenter
      (scalarGradientEndpoint targetCenter initial pcStep)
      (scalarGradientEndpoint targetCenter initial bpStep) := by
  unfold SameTargetResidualBranch
  rw [scalarGradientEndpoint_residual_exact,
    scalarGradientEndpoint_residual_exact]
  have hfactor :
      (1 - pcStep) * (initial - targetCenter) *
          ((1 - bpStep) * (initial - targetCenter)) =
        ((1 - pcStep) * (1 - bpStep)) *
          (initial - targetCenter) ^ 2 := by ring
  rw [hfactor]
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hpc.2) (sub_nonneg.mpr hbp.2))
    (sq_nonneg (initial - targetCenter))

/-- H5 derived from the trust bound closes the scalar frozen-adapter
forgetting comparison whenever target progress is matched. -/
theorem matchedProgress_unitTrustBounds_restore_sourceForgetting
    (sourceCenter targetCenter initial pcStep bpStep : ℝ)
    (hprogress : MatchedTargetProgress targetCenter initial
      (scalarGradientEndpoint targetCenter initial pcStep)
      (scalarGradientEndpoint targetCenter initial bpStep))
    (hpc : UnitTrustBound pcStep) (hbp : UnitTrustBound bpStep) :
    sourceForgetting sourceCenter initial
        (scalarGradientEndpoint targetCenter initial pcStep) ≤
      sourceForgetting sourceCenter initial
        (scalarGradientEndpoint targetCenter initial bpStep) := by
  exact sameTargetResidualBranch_restores_sourceForgetting_bound
    sourceCenter targetCenter initial _ _ hprogress
    (unitTrustBounds_imply_sameTargetResidualBranch
      targetCenter initial pcStep bpStep hpc hbp)

/-! ## Substantive properties carried by the plasticity license -/

/-- Exact Figure-1 prospective repair property. -/
def ProspectiveInterferenceGuarantee : Prop :=
  ∀ input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ,
    errorReadout * input ≠ 0 →
    bpRepairedHidden errorReadout input errorTarget ≠ 0 →
      sharedHiddenOutput errorReadout
          (bpRepairedHidden errorReadout input errorTarget) input = errorTarget ∧
        (halfSquaredOutputError
            (sharedHiddenOutput oldCorrectReadout oldHidden input)
            (sharedHiddenOutput oldCorrectReadout
              (bpRepairedHidden errorReadout input errorTarget) input) >
          halfSquaredOutputError
            (sharedHiddenOutput oldCorrectReadout oldHidden input)
            (sharedHiddenOutput
              (prospectiveCorrectReadout oldHidden oldCorrectReadout
                (bpRepairedHidden errorReadout input errorTarget))
              (bpRepairedHidden errorReadout input errorTarget) input) ↔
          oldCorrectReadout * input ≠ 0 ∧
            bpRepairedHidden errorReadout input errorTarget ≠ oldHidden)

/-- The prospective example is classified as metric/optimum mismatch, not
curvature commutator or connection remainder. -/
def ProspectiveGeometryGuarantee : Prop :=
  ∀ oldOptimum newOptimum : ℝ, newOptimum ≠ oldOptimum →
    pairwiseInterferenceEnergy
        (scalarOptimumTask oldOptimum).curvature
        (scalarOptimumTask newOptimum).curvature = 0 ∧
      quadraticConnectionRemainder
        (scalarOptimumTask oldOptimum)
        (scalarOptimumTask newOptimum) 1
        (scalarParameter oldOptimum) = 0 ∧
      quadraticMetricMismatchAgainstReference
        (scalarOptimumTask oldOptimum)
        (scalarOptimumTask newOptimum) 1
        (scalarParameter oldOptimum) (scalarParameter oldOptimum) ≠ 0

/-- Exact scalar preconditioner boundary: strict descent iff the
dimensionless preconditioner lies in `(0,2)`. -/
def SharpPreconditionerGuarantee : Prop :=
  ∀ preconditioner sourceActivation downstreamGain target weight : ℝ,
    downstreamGain * sourceActivation ≠ 0 →
    chainLinkResidual sourceActivation downstreamGain target weight ≠ 0 →
      (chainLinkHalfSquaredLoss sourceActivation downstreamGain target
          (chainLinkPreconditionedPCUpdate preconditioner sourceActivation
            downstreamGain target weight) <
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight ↔
        0 < preconditioner ∧ preconditioner < 2)

/-- Exact local trust-region correction together with its declared Taylor
boundary. -/
def TrustRegionGuarantee : Prop :=
  (∀ backpropGradient stateJacobian fisher stateLossGradient : ℝ,
    linearizedPCWeightGradient backpropGradient stateJacobian
        (quadraticStateShift fisher stateLossGradient) =
      backpropGradient + stateJacobian * (stateLossGradient / fisher)) ∧
    equationSevenTaylorBoundary.status ≠ .exactQuadraticIdentity

/-- Canonical counterexample to an unrestricted strict-saddle advantage. -/
def UnrestrictedStrictSaddleCounterexample : Prop :=
  IsCriticalPoint orthogonalDatasetEquilibratedEnergy (1, 0) ∧
    HasTwoSidedSaddleCurves orthogonalDatasetEquilibratedEnergy (1, 0)
      (fun step => (1 - step, step))
      (fun step => (1 + step, step)) ∧
    (∀ direction,
      HasSecondDirectionalCurvatureAt orthogonalDatasetEquilibratedEnergy
        (1, 0) direction 0) ∧
    ¬ HasStrictSaddleCertificate orthogonalDatasetEquilibratedEnergy (1, 0)

/-- Full proof-bearing PC plasticity license for the modeled family. -/
structure PCPlasticityLicense : Prop where
  bpEquivalent : ∀ predictionJacobian lossGradient : ℝ,
    pcLocalParameterUpdate predictionJacobian
        (epcOneStepError 1 lossGradient) =
      predictionJacobian * lossGradient
  prospectiveInterference : ProspectiveInterferenceGuarantee
  prospectiveGeometry : ProspectiveGeometryGuarantee
  sharpPreconditioner : SharpPreconditionerGuarantee
  trustRegion : TrustRegionGuarantee
  unrestrictedStrictSaddleCounterexample :
    UnrestrictedStrictSaddleCounterexample
  antiOvershootH5 : ∀ targetCenter initial pcStep bpStep : ℝ,
    UnitTrustBound pcStep → UnitTrustBound bpStep →
      SameTargetResidualBranch targetCenter
        (scalarGradientEndpoint targetCenter initial pcStep)
        (scalarGradientEndpoint targetCenter initial bpStep)
  frozenAdapterRestriction : ∀ backboneSegments adapterSegments : ℕ,
    1 < adapterSegments → ∀ rate : ℝ,
      IsFrozenAdapterSlowModeRate backboneSegments adapterSegments rate ↔
        rate = pathRelaxationRate adapterSegments
  frozenFourInsufficient :
    ∃ initial pcEndpoint bpEndpoint : ℝ,
      FrozenAdapterFourHypotheses initial pcEndpoint bpEndpoint ∧
        ¬ sourceForgetting 0 initial pcEndpoint ≤
          sourceForgetting 0 initial bpEndpoint
  frozenFiveRestores : ∀ initial pcEndpoint bpEndpoint : ℝ,
    FrozenAdapterFourHypotheses initial pcEndpoint bpEndpoint →
      SameTargetResidualBranch 1 pcEndpoint bpEndpoint →
        sourceForgetting 0 initial pcEndpoint ≤
          sourceForgetting 0 initial bpEndpoint

/-- T4 crown: all plasticity permissions and counter-boundaries are carried
by one checked license. -/
theorem pcPlasticity_frontier : PCPlasticityLicense := by
  refine
    { bpEquivalent := epcOneStepParameterUpdate_unitRate_eq_backprop
      prospectiveInterference := ?_
      prospectiveGeometry := prospectiveInterference_metric_not_connection
      sharpPreconditioner := ?_
      trustRegion := ⟨linearizedPCWeightGradient_eq_inverseFisherCorrection,
        equationSevenTaylorBoundary_not_exact⟩
      unrestrictedStrictSaddleCounterexample :=
        frontier_universalStrictSaddle_counterexample
      antiOvershootH5 := unitTrustBounds_imply_sameTargetResidualBranch
      frozenAdapterRestriction := fun backboneSegments adapterSegments hadapter rate =>
        isFrozenAdapterSlowModeRate_iff
          backboneSegments adapterSegments hadapter rate
      frozenFourInsufficient := frozenAdapter_four_hypotheses_insufficient
      frozenFiveRestores :=
        frozenAdapter_five_hypotheses_restore_sourceForgetting_bound }
  · intro input oldHidden oldCorrectReadout errorReadout errorTarget
      hpath hnew
    exact prospectiveRepair_target_and_advantage
      input oldHidden oldCorrectReadout errorReadout errorTarget hpath hnew
  · intro preconditioner sourceActivation downstreamGain target weight
      heffective hresidual
    exact chainLink_preconditionedUpdate_strictDescent_iff
      preconditioner sourceActivation downstreamGain target weight
      heffective hresidual

#print axioms epcOneStep_bpEquivalentLicense
#print axioms scalarGradientEndpoint_doesNotOvershoot_iff
#print axioms sameTargetResidualBranch_gradientEndpoints_iff
#print axioms matchedProgress_unitTrustBounds_restore_sourceForgetting
#print axioms pcPlasticity_frontier

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
