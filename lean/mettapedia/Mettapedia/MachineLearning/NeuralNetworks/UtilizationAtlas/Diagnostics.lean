import MeTTailCore.Crypto.SHA256
import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.Recommendations

/-!
# Operational diagnostics for the utilization atlas

Each exported diagnostic is a quantity already identified by one of the
frontier theorems.  Its zero, equality, sign, or saturation boundary is proved
here before the quantities are exposed to an experiment record.  The fields
are deliberately scalar summaries: they do not replace the full certificates
carried by the corresponding utilization licenses.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
open MeTTailCore.Crypto.SHA256

/-! ## Statistical-regime diagnostics -/

/-- Declared process-noise variance `Q`; zero is the stationary boundary. -/
noncomputable def processVarianceQDiagnostic (processVariance : ℝ) : ℝ :=
  processVariance

theorem processVarianceQDiagnostic_eq_zero_iff (processVariance : ℝ) :
    processVarianceQDiagnostic processVariance = 0 ↔ processVariance = 0 := by
  rfl

/-- Precision overstatement caused by treating overlapping packets as fresh. -/
noncomputable def overlapDiagnostic
    (priorPrecision firstPrecision secondPrecision overlap : ℝ) : ℝ :=
  naiveOverlappingPrecision priorPrecision firstPrecision secondPrecision -
    overlapCalibratedPrecision priorPrecision firstPrecision
      secondPrecision overlap

theorem overlapDiagnostic_eq_overlap
    (priorPrecision firstPrecision secondPrecision overlap : ℝ) :
    overlapDiagnostic priorPrecision firstPrecision secondPrecision overlap =
      overlap := by
  exact naivePrecision_sub_calibrated_eq_overlap _ _ _ _

theorem overlapDiagnostic_eq_zero_iff
    (priorPrecision firstPrecision secondPrecision overlap : ℝ) :
    overlapDiagnostic priorPrecision firstPrecision secondPrecision overlap = 0 ↔
      overlap = 0 := by
  rw [overlapDiagnostic_eq_overlap]

/-- Algebraic residual of the false-unit distortion equality boundary. -/
noncomputable def distortionResidualDiagnostic
    (priorVariance noiseVariance distortion : ℝ) : ℝ :=
  (distortion - 1) * (priorVariance * distortion - noiseVariance)

theorem distortionResidualDiagnostic_eq_zero_iff_hardwired_optimal
    (priorVariance noiseVariance distortion : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    distortionResidualDiagnostic priorVariance noiseVariance distortion = 0 ↔
      unitModelHardwiredMix priorVariance noiseVariance =
        distortedOptimalMix priorVariance noiseVariance distortion := by
  exact (unitModelHardwiredMix_eq_distortedOptimalMix_iff
    priorVariance noiseVariance distortion hprior hnoise).symm

/-- Difference between the two noise-conditioned scalar Kalman gains. -/
noncomputable def gainVariationDiagnostic
    (priorVariance firstNoise secondNoise : ℝ) : ℝ :=
  varianceKalmanGain priorVariance firstNoise -
    varianceKalmanGain priorVariance secondNoise

theorem gainVariationDiagnostic_eq_zero_iff_noise_eq
    (priorVariance firstNoise secondNoise : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise) :
    gainVariationDiagnostic priorVariance firstNoise secondNoise = 0 ↔
      firstNoise = secondNoise := by
  constructor
  · intro hzero
    by_contra hnoise
    exact varianceKalmanGain_ne_of_noise_ne priorVariance firstNoise secondNoise
      hprior hfirst hsecond hnoise (sub_eq_zero.mp hzero)
  · rintro rfl
    simp [gainVariationDiagnostic]

/-! ## Plasticity and finite-inference diagnostics -/

/-- Product of the two signed residuals about a shared target.  Its sign is
the exact H5 branch diagnostic. -/
noncomputable def branchProductDiagnostic
    (targetCenter firstEndpoint secondEndpoint : ℝ) : ℝ :=
  (firstEndpoint - targetCenter) * (secondEndpoint - targetCenter)

theorem branchProductDiagnostic_nonnegative_iff
    (targetCenter firstEndpoint secondEndpoint : ℝ) :
    0 ≤ branchProductDiagnostic targetCenter firstEndpoint secondEndpoint ↔
      SameTargetResidualBranch targetCenter firstEndpoint secondEndpoint := by
  rfl

theorem branchProductDiagnostic_eq_zero_iff
    (targetCenter firstEndpoint secondEndpoint : ℝ) :
    branchProductDiagnostic targetCenter firstEndpoint secondEndpoint = 0 ↔
      firstEndpoint = targetCenter ∨ secondEndpoint = targetCenter := by
  simp [branchProductDiagnostic, sub_eq_zero]

/-- Exact scalar spectral envelope for the half-relaxation PC fixture. -/
noncomputable def spectralEnvelopeDiagnostic
    (target initial : ℝ) (sweeps : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ sweeps * |initial - target|

theorem spectralEnvelopeDiagnostic_eq_residual
    (target initial : ℝ) (sweeps : ℕ) :
    spectralEnvelopeDiagnostic target initial sweeps =
      halfRelaxationResidual target initial sweeps := by
  exact (halfRelaxationResidual_exact target initial sweeps).symm

theorem spectralEnvelopeDiagnostic_eq_zero_iff
    (target initial : ℝ) (sweeps : ℕ) :
    spectralEnvelopeDiagnostic target initial sweeps = 0 ↔ initial = target := by
  unfold spectralEnvelopeDiagnostic
  constructor
  · intro hzero
    have hpower : (1 / 2 : ℝ) ^ sweeps ≠ 0 := by norm_num
    have habs : |initial - target| = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hpower
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · rintro rfl
    simp

/-- Fraction of the finite-speed dependency radius consumed by a target
distance.  It is defined when the denominator is positive. -/
noncomputable def propagationRatioDiagnostic
    (distance bandwidth sweeps : ℕ) : ℝ :=
  (distance : ℝ) / (sweeps * bandwidth : ℕ)

theorem propagationRatioDiagnostic_le_one
    (distance bandwidth sweeps : ℕ)
    (hpositive : 0 < sweeps * bandwidth)
    (hreach : distance ≤ sweeps * bandwidth) :
    propagationRatioDiagnostic distance bandwidth sweeps ≤ 1 := by
  unfold propagationRatioDiagnostic
  rw [div_le_one (by exact_mod_cast hpositive)]
  exact_mod_cast hreach

theorem propagationRatioDiagnostic_eq_one_iff
    (distance bandwidth sweeps : ℕ)
    (hpositive : 0 < sweeps * bandwidth) :
    propagationRatioDiagnostic distance bandwidth sweeps = 1 ↔
      distance = sweeps * bandwidth := by
  have hden : ((sweeps * bandwidth : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpositive)
  unfold propagationRatioDiagnostic
  constructor
  · intro hratio
    field_simp [hden] at hratio
    exact_mod_cast hratio
  · rintro rfl
    exact div_self hden

/-- Exact finite-speed PC inference can only populate records whose
propagation ratio is at most one. -/
theorem pcFiniteSpeed_propagationRatioDiagnostic_le_one
    (distance bandwidth sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step bandwidth)
    (hsettleZero :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettleOne :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0))
    (hpositive : 0 < sweeps * bandwidth) :
    propagationRatioDiagnostic distance bandwidth sweeps ≤ 1 := by
  apply propagationRatioDiagnostic_le_one distance bandwidth sweeps hpositive
  exact pcFiniteSpeed_distance_le_sweeps_mul_bandwidth
    distance bandwidth sweeps step hbandwidth hsettleZero hsettleOne

/-! ## Workspace, routing, and stability diagnostics -/

/-- Squared Frobenius magnitude of the task-curvature commutator. -/
noncomputable def commutatorDiagnostic
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) : ℝ :=
  pairwiseInterferenceEnergy first second

theorem commutatorDiagnostic_eq_zero_iff
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    commutatorDiagnostic first second = 0 ↔ Commute first second := by
  exact pairwiseInterferenceEnergy_eq_zero_iff_commute first second

/-- Off-diagonal Hessian diagnostic for a two-hole quadratic. -/
noncomputable def crossSlotHessianDiagnostic
    (firstCurvature secondCurvature coupling : ℝ) : ℝ :=
  crossSlotHessianBlock firstCurvature secondCurvature coupling

theorem crossSlotHessianDiagnostic_eq_coupling
    (firstCurvature secondCurvature coupling : ℝ) :
    crossSlotHessianDiagnostic firstCurvature secondCurvature coupling =
      coupling := by
  exact crossSlotHessianBlock_eq_coupling _ _ _

theorem crossSlotHessianDiagnostic_eq_zero_iff_independent
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ) :
    crossSlotHessianDiagnostic firstCurvature secondCurvature coupling = 0 ↔
      SlotwiseIndependentSettling firstCurvature secondCurvature coupling
        firstForce secondForce := by
  exact (slotwiseIndependentSettling_iff_crossSlotHessianBlock_zero
    firstCurvature secondCurvature coupling firstForce secondForce).symm

/-- One-step excess over a proposed geometric Lyapunov contraction. -/
noncomputable def lyapunovResidualDiagnostic
    (currentEnergy nextEnergy rate : ℝ) : ℝ :=
  nextEnergy - rate * currentEnergy

theorem lyapunovResidualDiagnostic_eq_zero_iff
    (currentEnergy nextEnergy rate : ℝ) :
    lyapunovResidualDiagnostic currentEnergy nextEnergy rate = 0 ↔
      nextEnergy = rate * currentEnergy := by
  exact sub_eq_zero

theorem certifiedLyapunovResidualDiagnostic_nonpositive
    {Command Index : Type*} [Fintype Index]
    {transition : Command → Matrix Index Index ℝ}
    (certificate : CommonQuadraticLyapunov transition)
    (command : Command) (state : Index → ℝ) :
    lyapunovResidualDiagnostic
        (quadraticEnergy certificate.metric state)
        (quadraticEnergy certificate.metric
          (Matrix.mulVec (transition command) state))
        certificate.rate ≤ 0 := by
  exact sub_nonpos.mpr (certificate.contracts command state)

/-- Decision-probability advantage of the exact two-mode representation over
nearest-mean selection by the moment-matched single Gaussian fixture. -/
noncomputable def multimodalDecisionGapDiagnostic : ℝ :=
  bimodalDecisionGap

theorem multimodalDecisionGapDiagnostic_eq_half :
    multimodalDecisionGapDiagnostic = 1 / 2 := by
  exact bimodalDecisionGap_eq_half

/-! ## Formal experiment record and T7 crown -/

/-- Scalar wire record for one utilization-atlas diagnostic observation. -/
structure UtilizationDiagnosticRecord where
  processVarianceQ : ℝ
  overlap : ℝ
  distortionResidual : ℝ
  gainVariation : ℝ
  branchProduct : ℝ
  spectralEnvelope : ℝ
  propagationRatio : ℝ
  commutatorEnergy : ℝ
  crossSlotHessian : ℝ
  lyapunovResidual : ℝ
  multimodalDecisionGap : ℝ

/-- T7 license: every diagnostic has its exact interpretation or certified
sign boundary. -/
structure DiagnosticsFrontierLicense : Prop where
  processStationaryBoundary : ∀ processVariance : ℝ,
    processVarianceQDiagnostic processVariance = 0 ↔ processVariance = 0
  overlapExact : ∀ priorPrecision firstPrecision secondPrecision overlap : ℝ,
    overlapDiagnostic priorPrecision firstPrecision secondPrecision overlap =
      overlap
  distortionBoundary : ∀ priorVariance noiseVariance distortion : ℝ,
    0 < priorVariance → 0 < noiseVariance →
      (distortionResidualDiagnostic priorVariance noiseVariance distortion = 0 ↔
        unitModelHardwiredMix priorVariance noiseVariance =
          distortedOptimalMix priorVariance noiseVariance distortion)
  gainBoundary : ∀ priorVariance firstNoise secondNoise : ℝ,
    0 < priorVariance → 0 < firstNoise → 0 < secondNoise →
      (gainVariationDiagnostic priorVariance firstNoise secondNoise = 0 ↔
        firstNoise = secondNoise)
  branchBoundary : ∀ targetCenter firstEndpoint secondEndpoint : ℝ,
    branchProductDiagnostic targetCenter firstEndpoint secondEndpoint = 0 ↔
      firstEndpoint = targetCenter ∨ secondEndpoint = targetCenter
  spectralEnvelopeExact : ∀ target initial : ℝ, ∀ sweeps : ℕ,
    spectralEnvelopeDiagnostic target initial sweeps =
      halfRelaxationResidual target initial sweeps
  propagationSaturation : ∀ distance bandwidth sweeps : ℕ,
    0 < sweeps * bandwidth →
      (propagationRatioDiagnostic distance bandwidth sweeps = 1 ↔
        distance = sweeps * bandwidth)
  commutatorBoundary : ∀ {Index : Type} [Fintype Index],
    ∀ first second : Matrix Index Index ℝ,
      commutatorDiagnostic first second = 0 ↔ Commute first second
  crossSlotBoundary : ∀ firstCurvature secondCurvature coupling
      firstForce secondForce : ℝ,
    crossSlotHessianDiagnostic firstCurvature secondCurvature coupling = 0 ↔
      SlotwiseIndependentSettling firstCurvature secondCurvature coupling
        firstForce secondForce
  lyapunovCertified : ∀ {Command Index : Type} [Fintype Index],
    ∀ {transition : Command → Matrix Index Index ℝ},
      ∀ certificate : CommonQuadraticLyapunov transition,
        ∀ command state,
          lyapunovResidualDiagnostic
              (quadraticEnergy certificate.metric state)
              (quadraticEnergy certificate.metric
                (Matrix.mulVec (transition command) state))
              certificate.rate ≤ 0
  multimodalGapExact : multimodalDecisionGapDiagnostic = 1 / 2

theorem diagnostics_frontier_crown : DiagnosticsFrontierLicense where
  processStationaryBoundary := processVarianceQDiagnostic_eq_zero_iff
  overlapExact := overlapDiagnostic_eq_overlap
  distortionBoundary :=
    distortionResidualDiagnostic_eq_zero_iff_hardwired_optimal
  gainBoundary := gainVariationDiagnostic_eq_zero_iff_noise_eq
  branchBoundary := branchProductDiagnostic_eq_zero_iff
  spectralEnvelopeExact := spectralEnvelopeDiagnostic_eq_residual
  propagationSaturation := propagationRatioDiagnostic_eq_one_iff
  commutatorBoundary := commutatorDiagnostic_eq_zero_iff
  crossSlotBoundary := crossSlotHessianDiagnostic_eq_zero_iff_independent
  lyapunovCertified := certifiedLyapunovResidualDiagnostic_nonpositive
  multimodalGapExact := multimodalDecisionGapDiagnostic_eq_half

/-! ## Hash-pinned v3 experiment schema

Version two remains immutable.  Version three adds the eleven diagnostics
only after their semantics and boundaries above have been checked. -/

/-- Canonical minified JSON Schema payload for diagnostic depth-probe rows. -/
def utilizationAtlasDepthProbeSchemaPayload : String :=
  "{" ++
  "\"$schema\":\"https://json-schema.org/draft/2020-12/schema\"," ++
  "\"$id\":\"workspace_decoder.depth_probe.v3\"," ++
  "\"title\":\"Three-lineage utilization-atlas depth probe record\"," ++
  "\"type\":\"object\"," ++
  "\"additionalProperties\":false," ++
  "\"required\":[\"schema_version\",\"run_id\",\"lineage\",\"seed\"," ++
    "\"generation\",\"split\",\"example_id\",\"recurrence_depth\"," ++
    "\"target_action_id\",\"held_out_loss\",\"settling_residual_norm\"," ++
    "\"read_attention_entropy\",\"legal_action_count\",\"accepted\"," ++
    "\"confidence_kappa\",\"slot_evidence_trajectories\"," ++
    "\"utilization_diagnostics\"]," ++
  "\"properties\":{" ++
    "\"schema_version\":{\"const\":\"workspace_decoder.depth_probe.v3\"}," ++
    "\"run_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"lineage\":{\"enum\":[\"gru\",\"workspace\",\"selective_belief\"]}," ++
    "\"seed\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"generation\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"split\":{\"enum\":[\"calibration\",\"held_out\"]}," ++
    "\"example_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"recurrence_depth\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"target_action_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"held_out_loss\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"settling_residual_norm\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"read_attention_entropy\":{\"type\":\"number\",\"minimum\":0}," ++
    "\"legal_action_count\":{\"type\":\"integer\",\"minimum\":0}," ++
    "\"accepted\":{\"type\":\"boolean\"}," ++
    "\"confidence_kappa\":{\"type\":\"number\",\"exclusiveMinimum\":0}," ++
    "\"slot_evidence_trajectories\":{\"type\":\"array\",\"items\":{" ++
      "\"type\":\"object\",\"additionalProperties\":false," ++
      "\"required\":[\"slot_id\",\"steps\"]," ++
      "\"properties\":{" ++
        "\"slot_id\":{\"type\":\"string\",\"minLength\":1}," ++
        "\"steps\":{\"type\":\"array\",\"items\":{" ++
          "\"type\":\"object\",\"additionalProperties\":false," ++
          "\"required\":[\"recurrence_depth\",\"n_plus\",\"n_minus\"," ++
            "\"effective_evidence\",\"decay_retention\"," ++
            "\"derived_decay_default\",\"natural_parameter\"," ++
            "\"precision\",\"strength\",\"confidence\",\"mean\",\"gain\"]," ++
          "\"properties\":{" ++
            "\"recurrence_depth\":{\"type\":\"integer\",\"minimum\":0}," ++
            "\"n_plus\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"n_minus\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"effective_evidence\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"decay_retention\":{\"type\":\"number\",\"minimum\":0," ++
              "\"maximum\":1}," ++
            "\"derived_decay_default\":{\"type\":\"number\",\"minimum\":0," ++
              "\"maximum\":1}," ++
            "\"natural_parameter\":{\"type\":\"number\"}," ++
            "\"precision\":{\"type\":\"number\",\"minimum\":0}," ++
            "\"strength\":{\"type\":\"number\",\"minimum\":0,\"maximum\":1}," ++
            "\"confidence\":{\"type\":\"number\",\"minimum\":0,\"maximum\":1}," ++
            "\"mean\":{\"type\":\"number\"}," ++
            "\"gain\":{\"type\":\"number\"}" ++
          "}}" ++
      "}}}}," ++
    "\"utilization_diagnostics\":{\"type\":\"object\"," ++
      "\"additionalProperties\":false," ++
      "\"required\":[\"process_variance_q\",\"overlap\"," ++
        "\"distortion_residual\",\"gain_variation\",\"branch_product\"," ++
        "\"spectral_envelope\",\"propagation_ratio\"," ++
        "\"commutator_energy\",\"cross_slot_hessian\"," ++
        "\"lyapunov_residual\",\"multimodal_decision_gap\"]," ++
      "\"properties\":{" ++
        "\"process_variance_q\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"overlap\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"distortion_residual\":{\"type\":\"number\"}," ++
        "\"gain_variation\":{\"type\":\"number\"}," ++
        "\"branch_product\":{\"type\":\"number\"}," ++
        "\"spectral_envelope\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"propagation_ratio\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"commutator_energy\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"cross_slot_hessian\":{\"type\":\"number\"}," ++
        "\"lyapunov_residual\":{\"type\":\"number\"}," ++
        "\"multimodal_decision_gap\":{\"type\":\"number\"}" ++
      "}}" ++
  "}," ++
  "\"formal_scope\":{" ++
    "\"belief_coordinates\":\"weighted_n_plus_n_minus\"," ++
    "\"gaussian_coordinates\":\"natural_information_eta_lambda\"," ++
    "\"diagnostic_semantics\":\"utilization_atlas_t7_exact_boundaries\"," ++
    "\"diagnostic_columns\":[\"process_variance_q\",\"overlap\"," ++
      "\"distortion_residual\",\"gain_variation\",\"branch_product\"," ++
      "\"spectral_envelope\",\"propagation_ratio\",\"commutator_energy\"," ++
      "\"cross_slot_hessian\",\"lyapunov_residual\"," ++
      "\"multimodal_decision_gap\"]," ++
    "\"nonlinear_trajectory\":\"registered_empirical_question\"}" ++
  "}"

/-- Digest computed by the repository's Lean SHA-256 implementation. -/
def utilizationAtlasDepthProbeSchemaComputedSha256 : String :=
  sha256Hex utilizationAtlasDepthProbeSchemaPayload

/-- Immutable digest of the canonical v3 schema payload. -/
def utilizationAtlasDepthProbeSchemaSha256 : String :=
  "32d10597a6da115a6462cff46126faef8cfbc9d7e8856cdff2084c923ad39da9"

/- The build fails if the kernel computation and literal digest disagree. -/
#guard utilizationAtlasDepthProbeSchemaComputedSha256 ==
  utilizationAtlasDepthProbeSchemaSha256

/-- Export envelope; the digest covers the nested `schema` payload. -/
def renderUtilizationAtlasDepthProbeSchemaFixture : String :=
  "{\"schema_sha256\":\"" ++ utilizationAtlasDepthProbeSchemaSha256 ++
    "\",\"schema\":" ++ utilizationAtlasDepthProbeSchemaPayload ++ "}\n"

#print axioms overlapDiagnostic_eq_overlap
#print axioms distortionResidualDiagnostic_eq_zero_iff_hardwired_optimal
#print axioms gainVariationDiagnostic_eq_zero_iff_noise_eq
#print axioms spectralEnvelopeDiagnostic_eq_residual
#print axioms propagationRatioDiagnostic_eq_one_iff
#print axioms pcFiniteSpeed_propagationRatioDiagnostic_le_one
#print axioms commutatorDiagnostic_eq_zero_iff
#print axioms crossSlotHessianDiagnostic_eq_zero_iff_independent
#print axioms certifiedLyapunovResidualDiagnostic_nonpositive
#print axioms diagnostics_frontier_crown

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
