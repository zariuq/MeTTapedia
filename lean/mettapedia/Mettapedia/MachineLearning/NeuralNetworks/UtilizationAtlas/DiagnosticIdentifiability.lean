import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.Diagnostics

/-!
# Diagnostic identifiability from deployed-cell telemetry

The v3 depth-probe row contains two logically different layers.  Primitive
telemetry is emitted by the deployed cell: loss, settling residual, read
entropy, counts, retention, natural coordinates, moment coordinates, and the
gain trajectory.  The nested `utilization_diagnostics` object is a derived
analysis output.  It is not admitted as an input here, because recovering a
diagnostic by reading its answer column would be circular.

The scalar/quadratic model below proves that gain variation and the exact
half-relaxation spectral envelope are recoverable from primitive telemetry.
Each other diagnostic receives an explicit admissible confound: two regimes
emit identical primitive telemetry but have different diagnostic values.
Matrix-valued statistical identification and trained-nonlinear identification
remain outside this file's declared scope.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## T1: primitive telemetry and scalar regime parameters -/

/-- Exact registry of the primitive v3 fields used by the observable model.
The two gain observations are positions in the single `gain` trajectory. -/
inductive PrimitiveTelemetryField where
  | recurrenceDepth
  | targetActionId
  | heldOutLoss
  | settlingResidualNorm
  | readAttentionEntropy
  | legalActionCount
  | accepted
  | confidenceKappa
  | slotId
  | nPlus
  | nMinus
  | effectiveEvidence
  | decayRetention
  | derivedDecayDefault
  | naturalParameter
  | precision
  | strength
  | confidence
  | mean
  | gain
  deriving DecidableEq, Fintype, Repr

/-- The JSON key assigned to a primitive observable. -/
def primitiveTelemetryFieldName : PrimitiveTelemetryField → String
  | .recurrenceDepth => "recurrence_depth"
  | .targetActionId => "target_action_id"
  | .heldOutLoss => "held_out_loss"
  | .settlingResidualNorm => "settling_residual_norm"
  | .readAttentionEntropy => "read_attention_entropy"
  | .legalActionCount => "legal_action_count"
  | .accepted => "accepted"
  | .confidenceKappa => "confidence_kappa"
  | .slotId => "slot_id"
  | .nPlus => "n_plus"
  | .nMinus => "n_minus"
  | .effectiveEvidence => "effective_evidence"
  | .decayRetention => "decay_retention"
  | .derivedDecayDefault => "derived_decay_default"
  | .naturalParameter => "natural_parameter"
  | .precision => "precision"
  | .strength => "strength"
  | .confidence => "confidence"
  | .mean => "mean"
  | .gain => "gain"

/-- Iterable primitive-field registry for schema audits. -/
def primitiveTelemetryFields : List PrimitiveTelemetryField :=
  [ .recurrenceDepth
  , .targetActionId
  , .heldOutLoss
  , .settlingResidualNorm
  , .readAttentionEntropy
  , .legalActionCount
  , .accepted
  , .confidenceKappa
  , .slotId
  , .nPlus
  , .nMinus
  , .effectiveEvidence
  , .decayRetention
  , .derivedDecayDefault
  , .naturalParameter
  , .precision
  , .strength
  , .confidence
  , .mean
  , .gain ]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- Every modeled observable key occurs in the hash-pinned v3 schema payload. -/
theorem primitiveTelemetryRegistry_grounded :
    primitiveTelemetryFields.all (fun field =>
      utilizationAtlasDepthProbeSchemaPayload.contains
        ("\"" ++ primitiveTelemetryFieldName field ++ "\"")) = true := by
  norm_num [primitiveTelemetryFields, primitiveTelemetryFieldName,
    utilizationAtlasDepthProbeSchemaPayload]
  all_goals decide

/-- The registry cannot circularly import the v3 derived answer block. -/
theorem primitiveTelemetryRegistry_excludes_derivedDiagnostics
    (field : PrimitiveTelemetryField) :
    primitiveTelemetryFieldName field ≠ "utilization_diagnostics" := by
  cases field <;> decide

/-- A two-step slice of one slot's primitive v3 telemetry.  Campaign metadata
such as run identifiers and the derived diagnostic annotation block are not
cell observables and therefore do not occur in this type. -/
structure RegimeObservables where
  recurrenceDepth : ℕ
  targetActionId : String
  heldOutLoss : ℝ
  settlingResidualNorm : ℝ
  readAttentionEntropy : ℝ
  legalActionCount : ℕ
  accepted : Bool
  confidenceKappa : ℝ
  slotId : String
  nPlus : ℝ
  nMinus : ℝ
  effectiveEvidence : ℝ
  decayRetention : ℝ
  derivedDecayDefault : ℝ
  naturalParameter : ℝ
  precision : ℝ
  strength : ℝ
  confidence : ℝ
  mean : ℝ
  earlierGain : ℝ
  laterGain : ℝ

/-- Numeric constraints imposed by the primitive part of the v3 schema. -/
def RegimeObservables.SchemaValid (observables : RegimeObservables) : Prop :=
  0 ≤ observables.heldOutLoss ∧
  0 ≤ observables.settlingResidualNorm ∧
  0 ≤ observables.readAttentionEntropy ∧
  0 < observables.confidenceKappa ∧
  0 ≤ observables.nPlus ∧
  0 ≤ observables.nMinus ∧
  0 ≤ observables.effectiveEvidence ∧
  observables.decayRetention ∈ Set.Icc (0 : ℝ) 1 ∧
  observables.derivedDecayDefault ∈ Set.Icc (0 : ℝ) 1 ∧
  0 ≤ observables.precision ∧
  observables.strength ∈ Set.Icc (0 : ℝ) 1 ∧
  observables.confidence ∈ Set.Icc (0 : ℝ) 1

/-- Scalar/quadratic regime parameters and the primitive log values not fixed
by the two proved recovery laws. -/
structure ScalarDiagnosticRegime where
  processVarianceQ : ℝ
  priorPrecision : ℝ
  firstPrecision : ℝ
  secondPrecision : ℝ
  overlap : ℝ
  priorVariance : ℝ
  noiseVariance : ℝ
  distortion : ℝ
  firstNoise : ℝ
  secondNoise : ℝ
  branchTarget : ℝ
  firstEndpoint : ℝ
  secondEndpoint : ℝ
  spectralTarget : ℝ
  spectralInitial : ℝ
  sweeps : ℕ
  propagationDistance : ℕ
  propagationBandwidth : ℕ
  firstCurvatureOperator : Matrix (Fin 2) (Fin 2) ℝ
  secondCurvatureOperator : Matrix (Fin 2) (Fin 2) ℝ
  firstSlotCurvature : ℝ
  secondSlotCurvature : ℝ
  slotCoupling : ℝ
  currentEnergy : ℝ
  nextEnergy : ℝ
  lyapunovRate : ℝ
  mixtureChoiceMass : ℝ
  gaussianChoiceMass : ℝ
  targetActionId : String
  heldOutLoss : ℝ
  readAttentionEntropy : ℝ
  legalActionCount : ℕ
  accepted : Bool
  confidenceKappa : ℝ
  slotId : String
  nPlus : ℝ
  nMinus : ℝ
  effectiveEvidence : ℝ
  decayRetention : ℝ
  derivedDecayDefault : ℝ
  naturalParameter : ℝ
  precision : ℝ
  strength : ℝ
  confidence : ℝ
  mean : ℝ

/-- Primitive telemetry generated by a regime.  The two gain fields are two
entries of the logged per-step `gain` trajectory, and settling residual is the
existing v3 `settling_residual_norm` field. -/
noncomputable def observeRegime
    (regime : ScalarDiagnosticRegime) : RegimeObservables where
  recurrenceDepth := regime.sweeps
  targetActionId := regime.targetActionId
  heldOutLoss := regime.heldOutLoss
  settlingResidualNorm :=
    spectralEnvelopeDiagnostic regime.spectralTarget regime.spectralInitial
      regime.sweeps
  readAttentionEntropy := regime.readAttentionEntropy
  legalActionCount := regime.legalActionCount
  accepted := regime.accepted
  confidenceKappa := regime.confidenceKappa
  slotId := regime.slotId
  nPlus := regime.nPlus
  nMinus := regime.nMinus
  effectiveEvidence := regime.effectiveEvidence
  decayRetention := regime.decayRetention
  derivedDecayDefault := regime.derivedDecayDefault
  naturalParameter := regime.naturalParameter
  precision := regime.precision
  strength := regime.strength
  confidence := regime.confidence
  mean := regime.mean
  earlierGain := varianceKalmanGain regime.priorVariance regime.firstNoise
  laterGain := varianceKalmanGain regime.priorVariance regime.secondNoise

/-- Admissibility of both the modeled regime and its emitted v3 telemetry. -/
def ScalarDiagnosticRegime.Admissible
    (regime : ScalarDiagnosticRegime) : Prop :=
  0 ≤ regime.processVarianceQ ∧
  0 < regime.priorPrecision ∧
  ValidPrecisionOverlap regime.firstPrecision regime.secondPrecision
    regime.overlap ∧
  0 < regime.priorVariance ∧
  0 < regime.noiseVariance ∧
  0 < regime.firstNoise ∧
  0 < regime.secondNoise ∧
  0 < regime.sweeps * regime.propagationBandwidth ∧
  0 ≤ regime.currentEnergy ∧
  0 ≤ regime.nextEnergy ∧
  0 ≤ regime.lyapunovRate ∧
  0 ≤ regime.mixtureChoiceMass ∧
  0 ≤ regime.gaussianChoiceMass ∧
  (observeRegime regime).SchemaValid

/-! ## The eleven regime diagnostics -/

/-- Generalized multimodal decision gap; the earlier fixed two-mode fixture is
its specialization at masses `1/2` and `0`. -/
noncomputable def regimeMultimodalDecisionGap
    (regime : ScalarDiagnosticRegime) : ℝ :=
  regime.mixtureChoiceMass - regime.gaussianChoiceMass

/-- Registry of the eleven diagnostics already exposed by v3. -/
inductive DiagnosticKind where
  | processVarianceQ
  | overlap
  | distortionResidual
  | gainVariation
  | branchProduct
  | spectralEnvelope
  | propagationRatio
  | commutatorEnergy
  | crossSlotHessian
  | lyapunovResidual
  | multimodalDecisionGap
  deriving DecidableEq, Fintype, Repr

/-- Diagnostic value in the scalar/quadratic regime model. -/
noncomputable def diagnosticValue
    (kind : DiagnosticKind) (regime : ScalarDiagnosticRegime) : ℝ :=
  match kind with
  | .processVarianceQ =>
      processVarianceQDiagnostic regime.processVarianceQ
  | .overlap =>
      overlapDiagnostic regime.priorPrecision regime.firstPrecision
        regime.secondPrecision regime.overlap
  | .distortionResidual =>
      distortionResidualDiagnostic regime.priorVariance regime.noiseVariance
        regime.distortion
  | .gainVariation =>
      gainVariationDiagnostic regime.priorVariance regime.firstNoise
        regime.secondNoise
  | .branchProduct =>
      branchProductDiagnostic regime.branchTarget regime.firstEndpoint
        regime.secondEndpoint
  | .spectralEnvelope =>
      spectralEnvelopeDiagnostic regime.spectralTarget regime.spectralInitial
        regime.sweeps
  | .propagationRatio =>
      propagationRatioDiagnostic regime.propagationDistance
        regime.propagationBandwidth regime.sweeps
  | .commutatorEnergy =>
      commutatorDiagnostic regime.firstCurvatureOperator
        regime.secondCurvatureOperator
  | .crossSlotHessian =>
      crossSlotHessianDiagnostic regime.firstSlotCurvature
        regime.secondSlotCurvature regime.slotCoupling
  | .lyapunovResidual =>
      lyapunovResidualDiagnostic regime.currentEnergy regime.nextEnergy
        regime.lyapunovRate
  | .multimodalDecisionGap => regimeMultimodalDecisionGap regime

/-- Identifiability means one function of primitive telemetry recovers the
diagnostic on every admissible scalar regime. -/
def IdentifiableFromTelemetry
    (diagnostic : ScalarDiagnosticRegime → ℝ) : Prop :=
  ∃ recover : RegimeObservables → ℝ,
    ∀ regime, regime.Admissible →
      recover (observeRegime regime) = diagnostic regime

/-- A confound is an admissible pair with identical primitive telemetry and
different diagnostic values. -/
def DiagnosticConfound
    (diagnostic : ScalarDiagnosticRegime → ℝ) : Prop :=
  ∃ first second,
    first.Admissible ∧ second.Admissible ∧
      observeRegime first = observeRegime second ∧
      diagnostic first ≠ diagnostic second

/-- A sealed confound rules out every telemetry-only recovery function. -/
theorem diagnosticConfound_not_identifiable
    {diagnostic : ScalarDiagnosticRegime → ℝ}
    (hconfound : DiagnosticConfound diagnostic) :
    ¬ IdentifiableFromTelemetry diagnostic := by
  rintro ⟨recover, hrecover⟩
  rcases hconfound with
    ⟨first, second, hfirst, hsecond, hobservables, hdifferent⟩
  apply hdifferent
  calc
    diagnostic first = recover (observeRegime first) :=
      (hrecover first hfirst).symm
    _ = recover (observeRegime second) := congrArg recover hobservables
    _ = diagnostic second := hrecover second hsecond

/-! ## T2 positive recoveries -/

/-- Gain variation is read directly from two entries of the logged gain
trajectory. -/
noncomputable def recoverGainVariation
    (observables : RegimeObservables) : ℝ :=
  observables.earlierGain - observables.laterGain

theorem recoverGainVariation_correct
    (regime : ScalarDiagnosticRegime) :
    recoverGainVariation (observeRegime regime) =
      diagnosticValue .gainVariation regime := by
  rfl

theorem gainVariation_identifiable :
    IdentifiableFromTelemetry (diagnosticValue .gainVariation) := by
  exact ⟨recoverGainVariation, fun regime _hadmissible =>
    recoverGainVariation_correct regime⟩

/-- The scalar spectral envelope is exactly the logged settling residual norm. -/
noncomputable def recoverSpectralEnvelope
    (observables : RegimeObservables) : ℝ :=
  observables.settlingResidualNorm

theorem recoverSpectralEnvelope_correct
    (regime : ScalarDiagnosticRegime) :
    recoverSpectralEnvelope (observeRegime regime) =
      diagnosticValue .spectralEnvelope regime := by
  rfl

theorem spectralEnvelope_identifiable :
    IdentifiableFromTelemetry (diagnosticValue .spectralEnvelope) := by
  exact ⟨recoverSpectralEnvelope, fun regime _hadmissible =>
    recoverSpectralEnvelope_correct regime⟩

/-! ## T2 negative confounding fixtures -/

/-- Common admissible regime from which every confounding pair differs only
in the latent parameter under test. -/
noncomputable def identifiabilityBaseline : ScalarDiagnosticRegime where
  processVarianceQ := 0
  priorPrecision := 1
  firstPrecision := 1
  secondPrecision := 1
  overlap := 0
  priorVariance := 1
  noiseVariance := 1
  distortion := 1
  firstNoise := 1
  secondNoise := 2
  branchTarget := 0
  firstEndpoint := 0
  secondEndpoint := 1
  spectralTarget := 0
  spectralInitial := 1
  sweeps := 1
  propagationDistance := 1
  propagationBandwidth := 1
  firstCurvatureOperator := 0
  secondCurvatureOperator := 0
  firstSlotCurvature := 1
  secondSlotCurvature := 1
  slotCoupling := 0
  currentEnergy := 0
  nextEnergy := 0
  lyapunovRate := 0
  mixtureChoiceMass := 0
  gaussianChoiceMass := 0
  targetActionId := "target-0"
  heldOutLoss := 0
  readAttentionEntropy := 0
  legalActionCount := 1
  accepted := true
  confidenceKappa := 1
  slotId := "slot-0"
  nPlus := 0
  nMinus := 0
  effectiveEvidence := 0
  decayRetention := 1
  derivedDecayDefault := 1
  naturalParameter := 0
  precision := 1
  strength := 0
  confidence := 0
  mean := 0

theorem identifiabilityBaseline_admissible :
    identifiabilityBaseline.Admissible := by
  norm_num [ScalarDiagnosticRegime.Admissible,
    RegimeObservables.SchemaValid, observeRegime,
    spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
    identifiabilityBaseline]

theorem processVarianceQ_confound :
    DiagnosticConfound (diagnosticValue .processVarianceQ) := by
  let changed := { identifiabilityBaseline with processVarianceQ := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, processVarianceQDiagnostic, changed,
      identifiabilityBaseline]

theorem overlap_confound :
    DiagnosticConfound (diagnosticValue .overlap) := by
  let changed := { identifiabilityBaseline with overlap := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, overlapDiagnostic,
      naiveOverlappingPrecision, overlapCalibratedPrecision, changed,
      identifiabilityBaseline]

theorem distortionResidual_confound :
    DiagnosticConfound (diagnosticValue .distortionResidual) := by
  let changed := { identifiabilityBaseline with distortion := 2 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, distortionResidualDiagnostic, changed,
      identifiabilityBaseline]

theorem branchProduct_confound :
    DiagnosticConfound (diagnosticValue .branchProduct) := by
  let changed := { identifiabilityBaseline with firstEndpoint := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, branchProductDiagnostic, changed,
      identifiabilityBaseline]

theorem propagationRatio_confound :
    DiagnosticConfound (diagnosticValue .propagationRatio) := by
  let changed := { identifiabilityBaseline with propagationDistance := 2 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, propagationRatioDiagnostic, changed,
      identifiabilityBaseline]

theorem commutatorEnergy_confound :
    DiagnosticConfound (diagnosticValue .commutatorEnergy) := by
  let changed :=
    { identifiabilityBaseline with
      firstCurvatureOperator := axisRankOneCurvature
      secondCurvatureOperator := directionRankOneCurvature 1 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · rw [show diagnosticValue .commutatorEnergy identifiabilityBaseline = 0 by
      norm_num [diagnosticValue, commutatorDiagnostic,
        pairwiseInterferenceEnergy, interferenceGramEntry,
        matrixCommutator, identifiabilityBaseline]]
    have hchanged : diagnosticValue .commutatorEnergy changed = 2 := by
      simpa [diagnosticValue, commutatorDiagnostic, changed] using
        unitOblique_interferenceEnergy_positive_negativeExample
    rw [hchanged]
    norm_num

theorem crossSlotHessian_confound :
    DiagnosticConfound (diagnosticValue .crossSlotHessian) := by
  let changed := { identifiabilityBaseline with slotCoupling := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, crossSlotHessianDiagnostic,
      crossSlotHessianBlock, twoSlotHessian, changed,
      identifiabilityBaseline]

theorem lyapunovResidual_confound :
    DiagnosticConfound (diagnosticValue .lyapunovResidual) := by
  let changed := { identifiabilityBaseline with nextEnergy := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, lyapunovResidualDiagnostic, changed,
      identifiabilityBaseline]

theorem multimodalDecisionGap_confound :
    DiagnosticConfound (diagnosticValue .multimodalDecisionGap) := by
  let changed := { identifiabilityBaseline with mixtureChoiceMass := 1 }
  refine ⟨identifiabilityBaseline, changed,
    identifiabilityBaseline_admissible, ?_, rfl, ?_⟩
  · norm_num [changed, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]
  · norm_num [diagnosticValue, regimeMultimodalDecisionGap, changed,
      identifiabilityBaseline]

theorem processVarianceQ_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .processVarianceQ) :=
  diagnosticConfound_not_identifiable processVarianceQ_confound

theorem overlap_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .overlap) :=
  diagnosticConfound_not_identifiable overlap_confound

theorem distortionResidual_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .distortionResidual) :=
  diagnosticConfound_not_identifiable distortionResidual_confound

theorem branchProduct_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .branchProduct) :=
  diagnosticConfound_not_identifiable branchProduct_confound

theorem propagationRatio_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .propagationRatio) :=
  diagnosticConfound_not_identifiable propagationRatio_confound

theorem commutatorEnergy_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .commutatorEnergy) :=
  diagnosticConfound_not_identifiable commutatorEnergy_confound

theorem crossSlotHessian_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .crossSlotHessian) :=
  diagnosticConfound_not_identifiable crossSlotHessian_confound

theorem lyapunovResidual_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .lyapunovResidual) :=
  diagnosticConfound_not_identifiable lyapunovResidual_confound

theorem multimodalDecisionGap_not_identifiable :
    ¬ IdentifiableFromTelemetry (diagnosticValue .multimodalDecisionGap) :=
  diagnosticConfound_not_identifiable multimodalDecisionGap_confound

/-! ## T3: probe checklist and instrument crown -/

/-- Additional intervention or metadata required to break one confound. -/
inductive NeededProbe where
  | innovationResidualSeries
  | sourceIdentityAndOverlap
  | latentMeasurementCalibrationPairs
  | pairedCounterfactualEndpointsAndTargetChart
  | topologyDistanceAndBandwidth
  | pairedOperatorJacobian
  | crossSlotPerturbation
  | lyapunovMetricEnergyAndRate
  | fullCompletionPosteriorOrMixtureComponents
  deriving DecidableEq, Fintype, Repr

/-- Result of the primitive-telemetry identifiability audit. -/
inductive IdentifiabilityStatus where
  | recovered
  | confounded (needs : NeededProbe)
  deriving DecidableEq, Repr

/-- Direct campaign checklist for all eleven diagnostics. -/
def diagnosticIdentifiabilityStatus :
    DiagnosticKind → IdentifiabilityStatus
  | .processVarianceQ => .confounded .innovationResidualSeries
  | .overlap => .confounded .sourceIdentityAndOverlap
  | .distortionResidual => .confounded .latentMeasurementCalibrationPairs
  | .gainVariation => .recovered
  | .branchProduct =>
      .confounded .pairedCounterfactualEndpointsAndTargetChart
  | .spectralEnvelope => .recovered
  | .propagationRatio => .confounded .topologyDistanceAndBandwidth
  | .commutatorEnergy => .confounded .pairedOperatorJacobian
  | .crossSlotHessian => .confounded .crossSlotPerturbation
  | .lyapunovResidual => .confounded .lyapunovMetricEnergyAndRate
  | .multimodalDecisionGap =>
      .confounded .fullCompletionPosteriorOrMixtureComponents

/-- The identifiable subset in a directly iterable form. -/
def identifiableDiagnosticSubset : List DiagnosticKind :=
  [.gainVariation, .spectralEnvelope]

/-- The nine required probes in a directly iterable campaign checklist. -/
def diagnosticProbeChecklist : List (DiagnosticKind × NeededProbe) :=
  [ (.processVarianceQ, .innovationResidualSeries)
  , (.overlap, .sourceIdentityAndOverlap)
  , (.distortionResidual, .latentMeasurementCalibrationPairs)
  , (.branchProduct, .pairedCounterfactualEndpointsAndTargetChart)
  , (.propagationRatio, .topologyDistanceAndBandwidth)
  , (.commutatorEnergy, .pairedOperatorJacobian)
  , (.crossSlotHessian, .crossSlotPerturbation)
  , (.lyapunovResidual, .lyapunovMetricEnergyAndRate)
  , (.multimodalDecisionGap,
      .fullCompletionPosteriorOrMixtureComponents) ]

/-- Mathematical obligation attached to one checklist entry. -/
def DiagnosticInstrumentSeal
    (kind : DiagnosticKind) : IdentifiabilityStatus → Prop
  | .recovered => IdentifiableFromTelemetry (diagnosticValue kind)
  | .confounded _probe => DiagnosticConfound (diagnosticValue kind)

theorem everyDiagnostic_instrumentSealed
    (kind : DiagnosticKind) :
    DiagnosticInstrumentSeal kind (diagnosticIdentifiabilityStatus kind) := by
  cases kind with
  | processVarianceQ => exact processVarianceQ_confound
  | overlap => exact overlap_confound
  | distortionResidual => exact distortionResidual_confound
  | gainVariation => exact gainVariation_identifiable
  | branchProduct => exact branchProduct_confound
  | spectralEnvelope => exact spectralEnvelope_identifiable
  | propagationRatio => exact propagationRatio_confound
  | commutatorEnergy => exact commutatorEnergy_confound
  | crossSlotHessian => exact crossSlotHessian_confound
  | lyapunovResidual => exact lyapunovResidual_confound
  | multimodalDecisionGap => exact multimodalDecisionGap_confound

/-- Exactly two of the current diagnostics are recoverable from primitive v3
telemetry in the declared scalar/quadratic model. -/
theorem diagnosticStatus_recovered_iff (kind : DiagnosticKind) :
    diagnosticIdentifiabilityStatus kind = .recovered ↔
      kind = .gainVariation ∨ kind = .spectralEnvelope := by
  cases kind <;> simp [diagnosticIdentifiabilityStatus]

/-- Extensional classification: primitive v3 telemetry identifies exactly
gain variation and the scalar spectral envelope. -/
theorem diagnostic_identifiable_iff (kind : DiagnosticKind) :
    IdentifiableFromTelemetry (diagnosticValue kind) ↔
      kind = .gainVariation ∨ kind = .spectralEnvelope := by
  cases kind <;>
    simp [processVarianceQ_not_identifiable, overlap_not_identifiable,
      distortionResidual_not_identifiable, gainVariation_identifiable,
      branchProduct_not_identifiable, spectralEnvelope_identifiable,
      propagationRatio_not_identifiable, commutatorEnergy_not_identifiable,
      crossSlotHessian_not_identifiable, lyapunovResidual_not_identifiable,
      multimodalDecisionGap_not_identifiable]

theorem mem_identifiableDiagnosticSubset_iff (kind : DiagnosticKind) :
    kind ∈ identifiableDiagnosticSubset ↔
      diagnosticIdentifiabilityStatus kind = .recovered := by
  cases kind <;> decide

theorem mem_identifiableDiagnosticSubset_iff_telemetry
    (kind : DiagnosticKind) :
    kind ∈ identifiableDiagnosticSubset ↔
      IdentifiableFromTelemetry (diagnosticValue kind) := by
  calc
    kind ∈ identifiableDiagnosticSubset ↔
        diagnosticIdentifiabilityStatus kind = .recovered :=
      mem_identifiableDiagnosticSubset_iff kind
    _ ↔ kind = .gainVariation ∨ kind = .spectralEnvelope :=
      diagnosticStatus_recovered_iff kind
    _ ↔ IdentifiableFromTelemetry (diagnosticValue kind) :=
      (diagnostic_identifiable_iff kind).symm

theorem mem_diagnosticProbeChecklist_iff
    (kind : DiagnosticKind) (probe : NeededProbe) :
    (kind, probe) ∈ diagnosticProbeChecklist ↔
      diagnosticIdentifiabilityStatus kind = .confounded probe := by
  cases kind <;> cases probe <;> decide

/-- The generalized multimodal quantity specializes to the earlier sealed
finite two-mode fixture without making the generalized quantity observable. -/
noncomputable def finiteBimodalIdentifiabilityRegime : ScalarDiagnosticRegime :=
  { identifiabilityBaseline with
    mixtureChoiceMass := 1 / 2
    gaussianChoiceMass := 0 }

theorem finiteBimodalDiagnostic_specializes :
    diagnosticValue .multimodalDecisionGap
        finiteBimodalIdentifiabilityRegime =
      multimodalDecisionGapDiagnostic := by
  rw [multimodalDecisionGapDiagnostic_eq_half]
  norm_num [diagnosticValue, regimeMultimodalDecisionGap,
    finiteBimodalIdentifiabilityRegime]

/-- Proof-bearing instrument checklist consumed by the empirical campaign. -/
structure DiagnosticInstrumentCrown : Prop where
  primitiveRegistryGrounded :
    primitiveTelemetryFields.all (fun field =>
      utilizationAtlasDepthProbeSchemaPayload.contains
        ("\"" ++ primitiveTelemetryFieldName field ++ "\"")) = true
  derivedDiagnosticsExcluded : ∀ field,
    primitiveTelemetryFieldName field ≠ "utilization_diagnostics"
  everyDiagnosticSealed : ∀ kind,
    DiagnosticInstrumentSeal kind (diagnosticIdentifiabilityStatus kind)
  recoveredExactly : ∀ kind,
    diagnosticIdentifiabilityStatus kind = .recovered ↔
      kind = .gainVariation ∨ kind = .spectralEnvelope
  identifiableSubsetExact : ∀ kind,
    kind ∈ identifiableDiagnosticSubset ↔
      IdentifiableFromTelemetry (diagnosticValue kind)
  probeChecklistExact : ∀ kind probe,
    (kind, probe) ∈ diagnosticProbeChecklist ↔
      diagnosticIdentifiabilityStatus kind = .confounded probe
  everyConfoundExcludesRecovery : ∀ kind probe,
    diagnosticIdentifiabilityStatus kind = .confounded probe →
      ¬ IdentifiableFromTelemetry (diagnosticValue kind)
  finiteBimodalSpecialization :
    diagnosticValue .multimodalDecisionGap
        finiteBimodalIdentifiabilityRegime =
      multimodalDecisionGapDiagnostic

theorem diagnostic_instrument_crown : DiagnosticInstrumentCrown where
  primitiveRegistryGrounded := primitiveTelemetryRegistry_grounded
  derivedDiagnosticsExcluded :=
    primitiveTelemetryRegistry_excludes_derivedDiagnostics
  everyDiagnosticSealed := everyDiagnostic_instrumentSealed
  recoveredExactly := diagnosticStatus_recovered_iff
  identifiableSubsetExact :=
    mem_identifiableDiagnosticSubset_iff_telemetry
  probeChecklistExact := mem_diagnosticProbeChecklist_iff
  everyConfoundExcludesRecovery := by
    intro kind probe hstatus
    have hseal := everyDiagnostic_instrumentSealed kind
    rw [hstatus] at hseal
    exact diagnosticConfound_not_identifiable hseal
  finiteBimodalSpecialization := finiteBimodalDiagnostic_specializes

#print axioms diagnosticConfound_not_identifiable
#print axioms primitiveTelemetryRegistry_grounded
#print axioms primitiveTelemetryRegistry_excludes_derivedDiagnostics
#print axioms gainVariation_identifiable
#print axioms spectralEnvelope_identifiable
#print axioms diagnostic_identifiable_iff
#print axioms processVarianceQ_confound
#print axioms overlap_confound
#print axioms distortionResidual_confound
#print axioms branchProduct_confound
#print axioms propagationRatio_confound
#print axioms commutatorEnergy_confound
#print axioms crossSlotHessian_confound
#print axioms lyapunovResidual_confound
#print axioms multimodalDecisionGap_confound
#print axioms diagnostic_instrument_crown

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
