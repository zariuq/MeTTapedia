import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.DiagnosticIdentifiability

/-!
# Decision-relevant active probing

This file turns the finite utilization atlas into a selector driven by
primitive v3 telemetry and explicitly selected interventions.  The deployed
selector never receives a regime constructor or the derived
`utilization_diagnostics` object.  A finite regime is used only on the
generative side, to state which transcript that regime emits and to prove
soundness for every modeled possibility.

The exact scalar model uses three primitive quantities already present in v3:
settling residual, gain variation, and effective evidence.  Selected probes
then reveal their named boundary predicates.  Two incomparable minimal probe
suites suffice for recommendations: routed-workspace evidence may be supplied
by either the commutator or Lyapunov intervention.  Probe completeness is not
claimed; only decision sufficiency for the declared finite regime family is.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open MeTTailCore.Crypto.SHA256

/-! ## T1: primitive observations, probe transcripts, and fibers -/

/-- A neutral admissible telemetry fixture: no settling residual, no gain
variation, and no accumulated effective evidence. -/
noncomputable def decisionTelemetryBaseline : ScalarDiagnosticRegime :=
  { identifiabilityBaseline with
    firstNoise := 1
    secondNoise := 1
    spectralTarget := 0
    spectralInitial := 0
    effectiveEvidence := 0
    nPlus := 0
    nMinus := 0
    strength := 0
    confidence := 0 }

/-- Count-bearing primitive telemetry used by all modeled belief regimes. -/
noncomputable def evidenceBearingTelemetry : ScalarDiagnosticRegime :=
  { decisionTelemetryBaseline with
    effectiveEvidence := 1
    nPlus := 1
    strength := 1
    confidence := 1 / 2 }

/-- A v3-grounded scalar telemetry fixture for every finite utilization
regime.  Only the generative model sees the regime constructor. -/
noncomputable def canonicalDecisionRegime :
    ModeledUtilizationRegime → ScalarDiagnosticRegime
  | .contractivePCInference =>
      { decisionTelemetryBaseline with spectralInitial := 1 }
  | .stationaryIndependentGaussian => evidenceBearingTelemetry
  | .positiveProcessDrift => evidenceBearingTelemetry
  | .knownObservationOverlap => evidenceBearingTelemetry
  | .fixedLinearDistortion => evidenceBearingTelemetry
  | .finiteBimodalDecision => evidenceBearingTelemetry
  | .varyingObservationNoise =>
      { decisionTelemetryBaseline with secondNoise := 2 }
  | _ => decisionTelemetryBaseline

/-- Primitive v3 telemetry emitted by the canonical finite regime model. -/
noncomputable def canonicalPrimitiveObservables
    (regime : ModeledUtilizationRegime) : RegimeObservables :=
  observeRegime (canonicalDecisionRegime regime)

theorem canonicalDecisionRegime_admissible
    (regime : ModeledUtilizationRegime) :
    (canonicalDecisionRegime regime).Admissible := by
  cases regime <;>
    norm_num [canonicalDecisionRegime, evidenceBearingTelemetry,
      decisionTelemetryBaseline, ScalarDiagnosticRegime.Admissible,
      RegimeObservables.SchemaValid, observeRegime,
      spectralEnvelopeDiagnostic, ValidPrecisionOverlap,
      identifiabilityBaseline]

/-- Finite classifier computed only from recoverable primitive v3 values. -/
inductive PrimitiveRecommendationOutcome where
  | plain
  | evidenceBearing
  | settlingDetected
  | gainVariationDetected
  deriving DecidableEq, Fintype, Repr

/-- Exact scalar classifier.  Empirical consumers may separately register a
tolerance policy, but no noisy or trained-nonlinear theorem is asserted here. -/
noncomputable def primitiveOutcomeFromObservables
    (observables : RegimeObservables) : PrimitiveRecommendationOutcome :=
  if recoverGainVariation observables ≠ 0 then
    .gainVariationDetected
  else if recoverSpectralEnvelope observables ≠ 0 then
    .settlingDetected
  else if observables.effectiveEvidence ≠ 0 then
    .evidenceBearing
  else
    .plain

/-- Executable finite shadow of the primitive classifier. -/
def primitiveOutcomeForRegime :
    ModeledUtilizationRegime → PrimitiveRecommendationOutcome
  | .contractivePCInference => .settlingDetected
  | .stationaryIndependentGaussian => .evidenceBearing
  | .positiveProcessDrift => .evidenceBearing
  | .knownObservationOverlap => .evidenceBearing
  | .fixedLinearDistortion => .evidenceBearing
  | .finiteBimodalDecision => .evidenceBearing
  | .varyingObservationNoise => .gainVariationDetected
  | _ => .plain

theorem primitiveOutcome_grounded_in_v3
    (regime : ModeledUtilizationRegime) :
    primitiveOutcomeFromObservables (canonicalPrimitiveObservables regime) =
      primitiveOutcomeForRegime regime := by
  cases regime <;>
    norm_num [primitiveOutcomeFromObservables, canonicalPrimitiveObservables,
      canonicalDecisionRegime, evidenceBearingTelemetry,
      decisionTelemetryBaseline, observeRegime, recoverGainVariation,
      recoverSpectralEnvelope, varianceKalmanGain,
      spectralEnvelopeDiagnostic, identifiabilityBaseline,
      primitiveOutcomeForRegime]

/-- The finite classifier reads only registered primitive fields. -/
theorem primitiveClassifier_fields_registered :
    PrimitiveTelemetryField.settlingResidualNorm ∈ primitiveTelemetryFields ∧
    PrimitiveTelemetryField.effectiveEvidence ∈ primitiveTelemetryFields ∧
    PrimitiveTelemetryField.gain ∈ primitiveTelemetryFields := by
  decide

/-- Boundary-triggering Boolean returned by one selected intervention. -/
def probeOutcome
    (regime : ModeledUtilizationRegime) : NeededProbe → Bool
  | .innovationResidualSeries => regime == .positiveProcessDrift
  | .sourceIdentityAndOverlap => regime == .knownObservationOverlap
  | .latentMeasurementCalibrationPairs => regime == .fixedLinearDistortion
  | .pairedCounterfactualEndpointsAndTargetChart =>
      regime == .prospectivePCPlasticity
  | .topologyDistanceAndBandwidth => regime == .contractivePCInference
  | .pairedOperatorJacobian => regime == .contextDependentRouting
  | .crossSlotPerturbation => regime == .separableTypedHoles
  | .lyapunovMetricEnergyAndRate => regime == .contextDependentRouting
  | .fullCompletionPosteriorOrMixtureComponents =>
      regime == .finiteBimodalDecision

theorem innovationProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .innovationResidualSeries = true ↔
      regime = .positiveProcessDrift := by
  cases regime <;> decide

theorem overlapProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .sourceIdentityAndOverlap = true ↔
      regime = .knownObservationOverlap := by
  cases regime <;> decide

theorem distortionProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .latentMeasurementCalibrationPairs = true ↔
      regime = .fixedLinearDistortion := by
  cases regime <;> decide

theorem plasticityProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .pairedCounterfactualEndpointsAndTargetChart = true ↔
      regime = .prospectivePCPlasticity := by
  cases regime <;> decide

theorem propagationProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .topologyDistanceAndBandwidth = true ↔
      regime = .contractivePCInference := by
  cases regime <;> decide

theorem commutatorProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .pairedOperatorJacobian = true ↔
      regime = .contextDependentRouting := by
  cases regime <;> decide

theorem crossSlotProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .crossSlotPerturbation = true ↔
      regime = .separableTypedHoles := by
  cases regime <;> decide

theorem lyapunovProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .lyapunovMetricEnergyAndRate = true ↔
      regime = .contextDependentRouting := by
  cases regime <;> decide

theorem multimodalProbe_positive_iff (regime : ModeledUtilizationRegime) :
    probeOutcome regime .fullCompletionPosteriorOrMixtureComponents = true ↔
      regime = .finiteBimodalDecision := by
  cases regime <;> decide

/-- Stable probe order for transcripts and campaign serialization. -/
def allNeededProbes : List NeededProbe :=
  [ .innovationResidualSeries
  , .sourceIdentityAndOverlap
  , .latentMeasurementCalibrationPairs
  , .pairedCounterfactualEndpointsAndTargetChart
  , .topologyDistanceAndBandwidth
  , .pairedOperatorJacobian
  , .crossSlotPerturbation
  , .lyapunovMetricEnergyAndRate
  , .fullCompletionPosteriorOrMixtureComponents ]

theorem mem_allNeededProbes (probe : NeededProbe) :
    probe ∈ allNeededProbes := by
  cases probe <;> decide

/-- Read selected probes in a canonical order; unselected probes are absent
rather than silently treated as negative. -/
def selectedProbeReadings
    (suite : Finset NeededProbe) (regime : ModeledUtilizationRegime) :
    List (NeededProbe × Bool) :=
  allNeededProbes.filterMap fun probe =>
    if probe ∈ suite then some (probe, probeOutcome regime probe) else none

/-- Complete selector input: a finite classification of primitive telemetry
and the readings of exactly the chosen interventions. -/
structure ProbeSignature where
  primitive : PrimitiveRecommendationOutcome
  readings : List (NeededProbe × Bool)
  deriving DecidableEq, Repr

def probeSignature
    (suite : Finset NeededProbe)
    (regime : ModeledUtilizationRegime) : ProbeSignature where
  primitive := primitiveOutcomeForRegime regime
  readings := selectedProbeReadings suite regime

/-- Regimes are observationally equivalent when the selector receives the
same primitive telemetry class and the same selected probe readings. -/
def ObservationallyEquivalent
    (suite : Finset NeededProbe)
    (first second : ModeledUtilizationRegime) : Prop :=
  probeSignature suite first = probeSignature suite second

theorem observationallyEquivalent_refl
    (suite : Finset NeededProbe) (regime : ModeledUtilizationRegime) :
    ObservationallyEquivalent suite regime regime := by
  rfl

theorem observationallyEquivalent_symm
    {suite : Finset NeededProbe} {first second : ModeledUtilizationRegime}
    (heq : ObservationallyEquivalent suite first second) :
    ObservationallyEquivalent suite second first :=
  heq.symm

theorem observationallyEquivalent_trans
    {suite : Finset NeededProbe}
    {first second third : ModeledUtilizationRegime}
    (hfirst : ObservationallyEquivalent suite first second)
    (hsecond : ObservationallyEquivalent suite second third) :
    ObservationallyEquivalent suite first third :=
  hfirst.trans hsecond

/-- Fiber of regimes consistent with one generated transcript. -/
def observationFiber
    (suite : Finset NeededProbe)
    (regime : ModeledUtilizationRegime) :
    Finset ModeledUtilizationRegime :=
  Finset.univ.filter fun candidate =>
    probeSignature suite candidate = probeSignature suite regime

/-! ## T2: generic decision-identifiability theorem -/

/-- A decision is constant on every observational fiber. -/
def FiberConstant
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision) : Prop :=
  ∀ first second, observe first = observe second →
    decideFor first = decideFor second

/-- A selector is sound when it reconstructs the declared decision from every
generated observation. -/
def SelectorSound
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision)
    (selector : Observation → Decision) : Prop :=
  ∀ regime, selector (observe regime) = decideFor regime

/-- Construct a selector from fiber constancy.  Off-image observations return
an explicit fallback; generated observations always take the witness branch. -/
noncomputable def selectorOfFiberConstancy
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision)
    (fallback : Decision)
    (_hconstant : FiberConstant observe decideFor) :
    Observation → Decision := by
  classical
  exact fun observation =>
    if hexists : ∃ regime, observe regime = observation then
      decideFor (Classical.choose hexists)
    else
      fallback

theorem selectorOfFiberConstancy_sound
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision)
    (fallback : Decision)
    (hconstant : FiberConstant observe decideFor) :
    SelectorSound observe decideFor
      (selectorOfFiberConstancy observe decideFor fallback hconstant) := by
  intro regime
  rw [selectorOfFiberConstancy, dif_pos ⟨regime, rfl⟩]
  apply hconstant (Classical.choose (show ∃ candidate,
    observe candidate = observe regime from ⟨regime, rfl⟩)) regime
  exact Classical.choose_spec (show ∃ candidate,
    observe candidate = observe regime from ⟨regime, rfl⟩)

/-- Constructive selector theorem: recovery exists exactly when the desired
decision is constant on observation fibers. -/
theorem soundSelector_exists_iff_fiberConstant
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision)
    (fallback : Decision) :
    (∃ selector, SelectorSound observe decideFor selector) ↔
      FiberConstant observe decideFor := by
  constructor
  · rintro ⟨selector, hsound⟩ first second heq
    calc
      decideFor first = selector (observe first) := (hsound first).symm
      _ = selector (observe second) := congrArg selector heq
      _ = decideFor second := hsound second
  · intro hconstant
    exact ⟨selectorOfFiberConstancy observe decideFor fallback hconstant,
      selectorOfFiberConstancy_sound observe decideFor fallback hconstant⟩

/-- A decision confound is a same-transcript pair requiring different
decisions. -/
def DecisionConfound
    {Regime Observation Decision : Type}
    (observe : Regime → Observation)
    (decideFor : Regime → Decision) : Prop :=
  ∃ first second, observe first = observe second ∧
    decideFor first ≠ decideFor second

theorem decisionConfound_not_fiberConstant
    {Regime Observation Decision : Type}
    {observe : Regime → Observation}
    {decideFor : Regime → Decision}
    (hconfound : DecisionConfound observe decideFor) :
    ¬ FiberConstant observe decideFor := by
  rintro hconstant
  rcases hconfound with ⟨first, second, heq, hne⟩
  exact hne (hconstant first second heq)

theorem decisionConfound_no_soundSelector
    {Regime Observation Decision : Type}
    {observe : Regime → Observation}
    {decideFor : Regime → Decision}
    (fallback : Decision)
    (hconfound : DecisionConfound observe decideFor) :
    ¬ ∃ selector, SelectorSound observe decideFor selector := by
  intro hexists
  exact decisionConfound_not_fiberConstant hconfound
    ((soundSelector_exists_iff_fiberConstant observe decideFor
      fallback).mp hexists)

/-- Decision-level sufficiency of a selected probe suite. -/
def ProbeSuiteSeparatesRecommendations
    (suite : Finset NeededProbe) : Prop :=
  FiberConstant (probeSignature suite) recommendationFor

/-- Recommendation-identifiability from one selected probe suite. -/
def RecommendationDecisionIdentifiable
    (suite : Finset NeededProbe) : Prop :=
  ∃ selector : ProbeSignature → Recommendation,
    SelectorSound (probeSignature suite) recommendationFor selector

theorem recommendationDecisionIdentifiable_iff
    (suite : Finset NeededProbe) :
    RecommendationDecisionIdentifiable suite ↔
      ProbeSuiteSeparatesRecommendations suite :=
  soundSelector_exists_iff_fiberConstant
    (probeSignature suite) recommendationFor .useBackprop

/-! ## T3: two incomparable inclusion-minimal probe suites -/

/-- Minimal suite using the operator-Jacobian route to identify routing. -/
def commutatorDecisionProbeSuite : Finset NeededProbe :=
  [ NeededProbe.innovationResidualSeries
  , .sourceIdentityAndOverlap
  , .latentMeasurementCalibrationPairs
  , .pairedCounterfactualEndpointsAndTargetChart
  , .pairedOperatorJacobian
  , .crossSlotPerturbation
  , .fullCompletionPosteriorOrMixtureComponents ].toFinset

/-- Minimal suite using the Lyapunov route to identify routing. -/
def lyapunovDecisionProbeSuite : Finset NeededProbe :=
  [ NeededProbe.innovationResidualSeries
  , .sourceIdentityAndOverlap
  , .latentMeasurementCalibrationPairs
  , .pairedCounterfactualEndpointsAndTargetChart
  , .crossSlotPerturbation
  , .lyapunovMetricEnergyAndRate
  , .fullCompletionPosteriorOrMixtureComponents ].toFinset

/-- Both minimal suites identify the finite regime itself; recommendation
identification is the weaker consequence consumed by the selector. -/
def expectedRecommendationFiber
    (regime : ModeledUtilizationRegime) :
    Finset ModeledUtilizationRegime :=
  { regime }

theorem commutatorSuite_fiber_exact
    (regime : ModeledUtilizationRegime) :
    observationFiber commutatorDecisionProbeSuite regime =
      expectedRecommendationFiber regime := by
  ext candidate
  cases regime <;> cases candidate <;> decide

theorem lyapunovSuite_fiber_exact
    (regime : ModeledUtilizationRegime) :
    observationFiber lyapunovDecisionProbeSuite regime =
      expectedRecommendationFiber regime := by
  ext candidate
  cases regime <;> cases candidate <;> decide

theorem commutatorDecisionProbeSuite_separates :
    ProbeSuiteSeparatesRecommendations commutatorDecisionProbeSuite := by
  unfold ProbeSuiteSeparatesRecommendations FiberConstant
  intro first second heq
  have hmem : first ∈ observationFiber commutatorDecisionProbeSuite second := by
    simp [observationFiber, heq]
  rw [commutatorSuite_fiber_exact second] at hmem
  simp [expectedRecommendationFiber] at hmem
  subst first
  rfl

theorem lyapunovDecisionProbeSuite_separates :
    ProbeSuiteSeparatesRecommendations lyapunovDecisionProbeSuite := by
  unfold ProbeSuiteSeparatesRecommendations FiberConstant
  intro first second heq
  have hmem : first ∈ observationFiber lyapunovDecisionProbeSuite second := by
    simp [observationFiber, heq]
  rw [lyapunovSuite_fiber_exact second] at hmem
  simp [expectedRecommendationFiber] at hmem
  subst first
  rfl

/-- Concrete recovered selector for the commutator-minimal suite. -/
noncomputable def commutatorDecisionSelector :
    ProbeSignature → Recommendation :=
  selectorOfFiberConstancy
    (probeSignature commutatorDecisionProbeSuite)
    recommendationFor .useBackprop
    commutatorDecisionProbeSuite_separates

theorem commutatorDecisionSelector_sound :
    SelectorSound (probeSignature commutatorDecisionProbeSuite)
      recommendationFor commutatorDecisionSelector :=
  selectorOfFiberConstancy_sound
    (probeSignature commutatorDecisionProbeSuite)
    recommendationFor .useBackprop
    commutatorDecisionProbeSuite_separates

/-- Concrete recovered selector for the Lyapunov-minimal suite. -/
noncomputable def lyapunovDecisionSelector :
    ProbeSignature → Recommendation :=
  selectorOfFiberConstancy
    (probeSignature lyapunovDecisionProbeSuite)
    recommendationFor .useBackprop
    lyapunovDecisionProbeSuite_separates

theorem lyapunovDecisionSelector_sound :
    SelectorSound (probeSignature lyapunovDecisionProbeSuite)
      recommendationFor lyapunovDecisionSelector :=
  selectorOfFiberConstancy_sound
    (probeSignature lyapunovDecisionProbeSuite)
    recommendationFor .useBackprop
    lyapunovDecisionProbeSuite_separates

/-- Removing a probe from a suite is the precise lower-bound test. -/
def InclusionMinimalDecisionSuite (suite : Finset NeededProbe) : Prop :=
  ProbeSuiteSeparatesRecommendations suite ∧
    ∀ probe ∈ suite,
      ¬ ProbeSuiteSeparatesRecommendations (suite.erase probe)

/-- Canonical pair exposed when a required probe is deleted. -/
def deletionConfoundPair :
    NeededProbe → ModeledUtilizationRegime × ModeledUtilizationRegime
  | .innovationResidualSeries =>
      (.stationaryIndependentGaussian, .positiveProcessDrift)
  | .sourceIdentityAndOverlap =>
      (.stationaryIndependentGaussian, .knownObservationOverlap)
  | .latentMeasurementCalibrationPairs =>
      (.stationaryIndependentGaussian, .fixedLinearDistortion)
  | .pairedCounterfactualEndpointsAndTargetChart =>
      (.wellSpecifiedScalarQuadratic, .prospectivePCPlasticity)
  | .topologyDistanceAndBandwidth =>
      (.wellSpecifiedScalarQuadratic, .contractivePCInference)
  | .pairedOperatorJacobian =>
      (.wellSpecifiedScalarQuadratic, .contextDependentRouting)
  | .crossSlotPerturbation =>
      (.wellSpecifiedScalarQuadratic, .separableTypedHoles)
  | .lyapunovMetricEnergyAndRate =>
      (.wellSpecifiedScalarQuadratic, .contextDependentRouting)
  | .fullCompletionPosteriorOrMixtureComponents =>
      (.stationaryIndependentGaussian, .finiteBimodalDecision)

theorem commutatorSuite_deletion_confound
    (probe : NeededProbe) (hmem : probe ∈ commutatorDecisionProbeSuite) :
    let pair := deletionConfoundPair probe
    probeSignature (commutatorDecisionProbeSuite.erase probe) pair.1 =
        probeSignature (commutatorDecisionProbeSuite.erase probe) pair.2 ∧
      recommendationFor pair.1 ≠ recommendationFor pair.2 := by
  cases probe with
  | innovationResidualSeries => decide
  | sourceIdentityAndOverlap => decide
  | latentMeasurementCalibrationPairs => decide
  | pairedCounterfactualEndpointsAndTargetChart => decide
  | topologyDistanceAndBandwidth =>
      simp [commutatorDecisionProbeSuite] at hmem
  | pairedOperatorJacobian => decide
  | crossSlotPerturbation => decide
  | lyapunovMetricEnergyAndRate =>
      simp [commutatorDecisionProbeSuite] at hmem
  | fullCompletionPosteriorOrMixtureComponents => decide

theorem lyapunovSuite_deletion_confound
    (probe : NeededProbe) (hmem : probe ∈ lyapunovDecisionProbeSuite) :
    let pair := deletionConfoundPair probe
    probeSignature (lyapunovDecisionProbeSuite.erase probe) pair.1 =
        probeSignature (lyapunovDecisionProbeSuite.erase probe) pair.2 ∧
      recommendationFor pair.1 ≠ recommendationFor pair.2 := by
  cases probe with
  | innovationResidualSeries => decide
  | sourceIdentityAndOverlap => decide
  | latentMeasurementCalibrationPairs => decide
  | pairedCounterfactualEndpointsAndTargetChart => decide
  | topologyDistanceAndBandwidth =>
      simp [lyapunovDecisionProbeSuite] at hmem
  | pairedOperatorJacobian =>
      simp [lyapunovDecisionProbeSuite] at hmem
  | crossSlotPerturbation => decide
  | lyapunovMetricEnergyAndRate => decide
  | fullCompletionPosteriorOrMixtureComponents => decide

theorem commutatorSuite_erased_decisionConfound
    (probe : NeededProbe) (hmem : probe ∈ commutatorDecisionProbeSuite) :
    DecisionConfound
      (probeSignature (commutatorDecisionProbeSuite.erase probe))
      recommendationFor := by
  let pair := deletionConfoundPair probe
  have hpair := commutatorSuite_deletion_confound probe hmem
  exact ⟨pair.1, pair.2, hpair.1, hpair.2⟩

theorem lyapunovSuite_erased_decisionConfound
    (probe : NeededProbe) (hmem : probe ∈ lyapunovDecisionProbeSuite) :
    DecisionConfound
      (probeSignature (lyapunovDecisionProbeSuite.erase probe))
      recommendationFor := by
  let pair := deletionConfoundPair probe
  have hpair := lyapunovSuite_deletion_confound probe hmem
  exact ⟨pair.1, pair.2, hpair.1, hpair.2⟩

theorem commutatorSuite_erased_noSelector
    (probe : NeededProbe) (hmem : probe ∈ commutatorDecisionProbeSuite) :
    ¬ RecommendationDecisionIdentifiable
      (commutatorDecisionProbeSuite.erase probe) :=
  decisionConfound_no_soundSelector .useBackprop
    (commutatorSuite_erased_decisionConfound probe hmem)

theorem lyapunovSuite_erased_noSelector
    (probe : NeededProbe) (hmem : probe ∈ lyapunovDecisionProbeSuite) :
    ¬ RecommendationDecisionIdentifiable
      (lyapunovDecisionProbeSuite.erase probe) :=
  decisionConfound_no_soundSelector .useBackprop
    (lyapunovSuite_erased_decisionConfound probe hmem)

theorem commutatorDecisionProbeSuite_minimal :
    InclusionMinimalDecisionSuite commutatorDecisionProbeSuite := by
  refine ⟨commutatorDecisionProbeSuite_separates, ?_⟩
  intro probe hmem hseparates
  have hpair := commutatorSuite_deletion_confound probe hmem
  exact hpair.2 (hseparates _ _ hpair.1)

theorem lyapunovDecisionProbeSuite_minimal :
    InclusionMinimalDecisionSuite lyapunovDecisionProbeSuite := by
  refine ⟨lyapunovDecisionProbeSuite_separates, ?_⟩
  intro probe hmem hseparates
  have hpair := lyapunovSuite_deletion_confound probe hmem
  exact hpair.2 (hseparates _ _ hpair.1)

theorem minimalDecisionSuites_incomparable :
    ¬ commutatorDecisionProbeSuite ⊆ lyapunovDecisionProbeSuite ∧
      ¬ lyapunovDecisionProbeSuite ⊆ commutatorDecisionProbeSuite := by
  decide

/-! ## T4: terminating adaptive probe tree and exact cost -/

/-- A finite binary probe program.  `negative` and `positive` branches are
selected by the corresponding Boolean intervention result. -/
inductive ProbeDecisionTree where
  | leaf (recommendation : Recommendation)
  | branch (probe : NeededProbe)
      (negative positive : ProbeDecisionTree)
  deriving Repr

namespace ProbeDecisionTree

/-- Run a finite tree in one modeled regime. -/
def run : ProbeDecisionTree → ModeledUtilizationRegime → Recommendation
  | .leaf recommendation, _ => recommendation
  | .branch probe negative positive, regime =>
      if probeOutcome regime probe then
        positive.run regime
      else
        negative.run regime

/-- Execute against supplied intervention readings.  Missing readings do not
default to negative; they stop with `none`. -/
def runWith
    (results : NeededProbe → Option Bool) :
    ProbeDecisionTree → Option Recommendation
  | .leaf recommendation => some recommendation
  | .branch probe negative positive =>
      match results probe with
      | none => none
      | some false => negative.runWith results
      | some true => positive.runWith results

/-- Number of interventions executed on one path. -/
def runCost : ProbeDecisionTree → ModeledUtilizationRegime → ℕ
  | .leaf _, _ => 0
  | .branch probe negative positive, regime =>
      if probeOutcome regime probe then
        1 + positive.runCost regime
      else
        1 + negative.runCost regime

/-- Ordered interventions actually executed on one path. -/
def runProbes : ProbeDecisionTree → ModeledUtilizationRegime → List NeededProbe
  | .leaf _, _ => []
  | .branch probe negative positive, regime =>
      probe :: if probeOutcome regime probe then
        positive.runProbes regime
      else
        negative.runProbes regime

/-- Static set of probes mentioned anywhere in the tree. -/
def usedProbes : ProbeDecisionTree → Finset NeededProbe
  | .leaf _ => ∅
  | .branch probe negative positive =>
      insert probe (negative.usedProbes ∪ positive.usedProbes)

end ProbeDecisionTree

/-- Lookup one explicitly selected probe result in a serialized signature. -/
def ProbeSignature.probeResult
    (signature : ProbeSignature) (probe : NeededProbe) : Option Bool :=
  match signature.readings.find? fun reading => reading.1 == probe with
  | none => none
  | some reading => some reading.2

/-- Evidence-bearing branch: fading, either calibration failure, multimodality,
or the stationary additive default. -/
def evidenceActiveTree : ProbeDecisionTree :=
  .branch .innovationResidualSeries
    (.branch .sourceIdentityAndOverlap
      (.branch .latentMeasurementCalibrationPairs
        (.branch .fullCompletionPosteriorOrMixtureComponents
          (.leaf .useAdditiveBelief)
          (.leaf (.useMixtureBelief 2)))
        (.leaf .useCalibratedBelief))
      (.leaf .useCalibratedBelief))
    (.leaf .useFadingBelief)

/-- Plain branch: prospective plasticity, typed separation, routed control, or
the well-specified backprop default. -/
def plainActiveTree : ProbeDecisionTree :=
  .branch .pairedCounterfactualEndpointsAndTargetChart
    (.branch .crossSlotPerturbation
      (.branch .pairedOperatorJacobian
        (.leaf .useBackprop)
        (.leaf .useRoutedWorkspace))
      (.leaf .useTypedWorkspace))
    (.leaf .usePCPlasticity)

/-- Adaptive forest selected by the primitive v3 outcome before interventions
begin. -/
def activeDecisionTree :
    PrimitiveRecommendationOutcome → ProbeDecisionTree
  | .plain => plainActiveTree
  | .evidenceBearing => evidenceActiveTree
  | .settlingDetected => .leaf .usePCInference
  | .gainVariationDetected => .leaf .useSelectiveWorkspace

/-- Executable architecture recommendation from the generated transcript. -/
def activeRecommendation
    (regime : ModeledUtilizationRegime) : Recommendation :=
  (activeDecisionTree (primitiveOutcomeForRegime regime)).run regime

/-- Empirical-harness selector: consumes only primitive classification and
serialized probe results, never a regime constructor. -/
def activeRecommendationFromSignature
    (signature : ProbeSignature) : Option Recommendation :=
  (activeDecisionTree signature.primitive).runWith signature.probeResult

/-- Exact number of selected interventions on one adaptive path. -/
def activeProbeCost (regime : ModeledUtilizationRegime) : ℕ :=
  (activeDecisionTree (primitiveOutcomeForRegime regime)).runCost regime

/-- Ordered adaptive transcript requested for one modeled regime. -/
def activeProbePath (regime : ModeledUtilizationRegime) : List NeededProbe :=
  (activeDecisionTree (primitiveOutcomeForRegime regime)).runProbes regime

/-- Set of interventions actually requested on one adaptive path. -/
def activeProbeSuite (regime : ModeledUtilizationRegime) : Finset NeededProbe :=
  (activeProbePath regime).toFinset

/-- The recommendation is already determined within one observation fiber. -/
def RecommendationResolvedAt
    (suite : Finset NeededProbe) (regime : ModeledUtilizationRegime) : Prop :=
  ∀ candidate,
    probeSignature suite candidate = probeSignature suite regime →
      recommendationFor candidate = recommendationFor regime

instance recommendationResolvedAtDecidable
    (suite : Finset NeededProbe) (regime : ModeledUtilizationRegime) :
    Decidable (RecommendationResolvedAt suite regime) := by
  unfold RecommendationResolvedAt
  exact Fintype.decidableForallFintype

/-- All strict prefix suites of one adaptive path, including the empty
prefix and excluding the complete path. -/
def activeProbeProperPrefixSuites
    (regime : ModeledUtilizationRegime) : List (Finset NeededProbe) :=
  (List.range (activeProbePath regime).length).map fun prefixLength =>
    ((activeProbePath regime).take prefixLength).toFinset

/-- The adaptive path resolves its recommendation, and no strict prefix does.
This is the exact finite-model meaning of stopping at first determination. -/
def StopsAtFirstRecommendation
    (regime : ModeledUtilizationRegime) : Prop :=
  RecommendationResolvedAt (activeProbeSuite regime) regime ∧
    (activeProbeProperPrefixSuites regime).Forall fun suite =>
      ¬ RecommendationResolvedAt suite regime

instance stopsAtFirstRecommendationDecidable
    (regime : ModeledUtilizationRegime) :
    Decidable (StopsAtFirstRecommendation regime) := by
  unfold StopsAtFirstRecommendation
  infer_instance

theorem activeRecommendation_correct
    (regime : ModeledUtilizationRegime) :
    activeRecommendation regime = recommendationFor regime := by
  cases regime <;> decide

theorem activeRecommendationFromSignature_correct
    (regime : ModeledUtilizationRegime) :
    activeRecommendationFromSignature
        (probeSignature commutatorDecisionProbeSuite regime) =
      some (recommendationFor regime) := by
  cases regime <;> decide

/-- The transcript runner needs exactly the adaptively requested probes, not
the unused remainder of the static minimal suite. -/
theorem activeRecommendationFromAdaptiveSignature_correct
    (regime : ModeledUtilizationRegime) :
    activeRecommendationFromSignature
        (probeSignature (activeProbeSuite regime) regime) =
      some (recommendationFor regime) := by
  cases regime <;> decide

/-- Every reached leaf carries the substantive theorem licensed by the finite
atlas, not merely the same enum tag. -/
theorem activeRecommendation_guaranteed
    (regime : ModeledUtilizationRegime) :
    RecommendationGuarantee regime (activeRecommendation regime) := by
  rw [activeRecommendation_correct regime]
  exact recommendationFor_guaranteed regime

/-- Every result reached by the transcript-only runner is the licensed atlas
recommendation for its generating regime. -/
theorem activeRecommendationFromSignature_guaranteed
    (regime : ModeledUtilizationRegime) :
    ∃ recommendation,
      activeRecommendationFromSignature
          (probeSignature commutatorDecisionProbeSuite regime) =
        some recommendation ∧
      RecommendationGuarantee regime recommendation := by
  exact ⟨recommendationFor regime,
    activeRecommendationFromSignature_correct regime,
    recommendationFor_guaranteed regime⟩

/-- The actually requested adaptive transcript reaches a licensed leaf. -/
theorem activeRecommendationFromAdaptiveSignature_guaranteed
    (regime : ModeledUtilizationRegime) :
    ∃ recommendation,
      activeRecommendationFromSignature
          (probeSignature (activeProbeSuite regime) regime) =
        some recommendation ∧
      RecommendationGuarantee regime recommendation := by
  exact ⟨recommendationFor regime,
    activeRecommendationFromAdaptiveSignature_correct regime,
    recommendationFor_guaranteed regime⟩

theorem activeProbePath_length_eq_cost
    (regime : ModeledUtilizationRegime) :
    (activeProbePath regime).length = activeProbeCost regime := by
  cases regime <;> decide

theorem activeProbeSuite_card_eq_cost
    (regime : ModeledUtilizationRegime) :
    (activeProbeSuite regime).card = activeProbeCost regime := by
  cases regime <;> decide

theorem activeProbePath_stopsAtFirstRecommendation
    (regime : ModeledUtilizationRegime) :
    StopsAtFirstRecommendation regime := by
  cases regime <;> decide

theorem activeProbeCost_le_four (regime : ModeledUtilizationRegime) :
    activeProbeCost regime ≤ 4 := by
  cases regime <;> decide

theorem activeProbeCost_worstCase_exact :
    (∀ regime, activeProbeCost regime ≤ 4) ∧
      ∃ regime, activeProbeCost regime = 4 := by
  exact ⟨activeProbeCost_le_four,
    ⟨.stationaryIndependentGaussian, by decide⟩⟩

/-- The adaptive tree never leaves the proved inclusion-minimal commutator
suite, although each path generally uses only a strict subset. -/
theorem activeDecisionTree_uses_minimalSuite
    (primitive : PrimitiveRecommendationOutcome) :
    (activeDecisionTree primitive).usedProbes ⊆
      commutatorDecisionProbeSuite := by
  cases primitive <;> decide

/-! ## T5: exact fiber hybrids, singleton compression, and abstention -/

/-- Stable enumeration of the finite recommendation model. -/
def allModeledUtilizationRegimes : List ModeledUtilizationRegime :=
  [ .wellSpecifiedScalarQuadratic
  , .contractivePCInference
  , .prospectivePCPlasticity
  , .stationaryIndependentGaussian
  , .positiveProcessDrift
  , .knownObservationOverlap
  , .fixedLinearDistortion
  , .finiteBimodalDecision
  , .separableTypedHoles
  , .varyingObservationNoise
  , .contextDependentRouting ]

theorem mem_allModeledUtilizationRegimes
    (regime : ModeledUtilizationRegime) :
    regime ∈ allModeledUtilizationRegimes := by
  cases regime <;> decide

/-! ### Exhaustive minimal-suite characterization -/

/-- Quotient-free nine-bit representation used only to exhaust the finite
probe-family search in the kernel. -/
structure ProbeMask where
  innovation : Bool
  overlap : Bool
  distortion : Bool
  plasticity : Bool
  propagation : Bool
  commutator : Bool
  crossSlot : Bool
  lyapunov : Bool
  multimodal : Bool
  deriving DecidableEq, Repr

def ProbeMask.toFinset (mask : ProbeMask) : Finset NeededProbe :=
  ([ (NeededProbe.innovationResidualSeries, mask.innovation)
   , (.sourceIdentityAndOverlap, mask.overlap)
   , (.latentMeasurementCalibrationPairs, mask.distortion)
   , (.pairedCounterfactualEndpointsAndTargetChart, mask.plasticity)
   , (.topologyDistanceAndBandwidth, mask.propagation)
   , (.pairedOperatorJacobian, mask.commutator)
   , (.crossSlotPerturbation, mask.crossSlot)
   , (.lyapunovMetricEnergyAndRate, mask.lyapunov)
   , (.fullCompletionPosteriorOrMixtureComponents, mask.multimodal) ].filterMap
      fun entry => if entry.2 then some entry.1 else none).toFinset

def ProbeMask.ofFinset (suite : Finset NeededProbe) : ProbeMask where
  innovation := decide (.innovationResidualSeries ∈ suite)
  overlap := decide (.sourceIdentityAndOverlap ∈ suite)
  distortion := decide (.latentMeasurementCalibrationPairs ∈ suite)
  plasticity := decide
    (.pairedCounterfactualEndpointsAndTargetChart ∈ suite)
  propagation := decide (.topologyDistanceAndBandwidth ∈ suite)
  commutator := decide (.pairedOperatorJacobian ∈ suite)
  crossSlot := decide (.crossSlotPerturbation ∈ suite)
  lyapunov := decide (.lyapunovMetricEnergyAndRate ∈ suite)
  multimodal := decide
    (.fullCompletionPosteriorOrMixtureComponents ∈ suite)

theorem ProbeMask.toFinset_ofFinset (suite : Finset NeededProbe) :
    (ProbeMask.ofFinset suite).toFinset = suite := by
  ext probe
  cases probe <;> simp [ProbeMask.ofFinset, ProbeMask.toFinset]

def commutatorDecisionProbeMask : ProbeMask where
  innovation := true
  overlap := true
  distortion := true
  plasticity := true
  propagation := false
  commutator := true
  crossSlot := true
  lyapunov := false
  multimodal := true

def lyapunovDecisionProbeMask : ProbeMask where
  innovation := true
  overlap := true
  distortion := true
  plasticity := true
  propagation := false
  commutator := false
  crossSlot := true
  lyapunov := true
  multimodal := true

theorem commutatorDecisionProbeMask_toFinset :
    commutatorDecisionProbeMask.toFinset =
      commutatorDecisionProbeSuite := by
  decide

theorem lyapunovDecisionProbeMask_toFinset :
    lyapunovDecisionProbeMask.toFinset = lyapunovDecisionProbeSuite := by
  decide

/-- Kernel-computable check of recommendation constancy on every finite pair. -/
def probeSuiteSeparatesBool (suite : Finset NeededProbe) : Bool :=
  allModeledUtilizationRegimes.all fun first =>
    allModeledUtilizationRegimes.all fun second =>
      if probeSignature suite first == probeSignature suite second then
        recommendationFor first == recommendationFor second
      else
        true

theorem probeSuiteSeparatesBool_eq_true_iff
    (suite : Finset NeededProbe) :
    probeSuiteSeparatesBool suite = true ↔
      ProbeSuiteSeparatesRecommendations suite := by
  constructor
  · intro hbool first second heq
    have hfirst := (List.all_eq_true.mp hbool) first
      (mem_allModeledUtilizationRegimes first)
    have hsecond := (List.all_eq_true.mp hfirst) second
      (mem_allModeledUtilizationRegimes second)
    simp [heq] at hsecond
    exact hsecond
  · intro hconstant
    apply List.all_eq_true.mpr
    intro first _hfirst
    apply List.all_eq_true.mpr
    intro second _hsecond
    by_cases heq : probeSignature suite first = probeSignature suite second
    · have hrecommendation := hconstant first second heq
      simp [heq, hrecommendation]
    · simp [heq]

/-- Boolean mirror of semantic inclusion-minimality. -/
def inclusionMinimalDecisionSuiteBool
    (suite : Finset NeededProbe) : Bool :=
  probeSuiteSeparatesBool suite &&
    allNeededProbes.all fun probe =>
      if probe ∈ suite then
        !probeSuiteSeparatesBool (suite.erase probe)
      else
        true

theorem inclusionMinimalDecisionSuiteBool_eq_true_iff
    (suite : Finset NeededProbe) :
    inclusionMinimalDecisionSuiteBool suite = true ↔
      InclusionMinimalDecisionSuite suite := by
  constructor
  · intro hbool
    rcases Bool.and_eq_true_iff.mp hbool with ⟨hseparates, hdeletions⟩
    refine ⟨(probeSuiteSeparatesBool_eq_true_iff suite).1 hseparates, ?_⟩
    intro probe hmem herased
    have hprobe := (List.all_eq_true.mp hdeletions) probe
      (mem_allNeededProbes probe)
    have herasedFalse :
        probeSuiteSeparatesBool (suite.erase probe) = false := by
      simpa [hmem] using hprobe
    have herasedTrue :=
      (probeSuiteSeparatesBool_eq_true_iff (suite.erase probe)).2 herased
    rw [herasedTrue] at herasedFalse
    contradiction
  · rintro ⟨hseparates, hdeletions⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨(probeSuiteSeparatesBool_eq_true_iff suite).2 hseparates, ?_⟩
    apply List.all_eq_true.mpr
    intro probe _hregistry
    by_cases hmem : probe ∈ suite
    · have hnot := hdeletions probe hmem
      have hfalse : probeSuiteSeparatesBool (suite.erase probe) = false := by
        cases hvalue : probeSuiteSeparatesBool (suite.erase probe) with
        | false => rfl
        | true =>
            exact False.elim (hnot
              ((probeSuiteSeparatesBool_eq_true_iff
                (suite.erase probe)).1 hvalue))
      simp [hmem, hfalse]
    · simp [hmem]

set_option maxHeartbeats 2000000 in
/-- Exhaustive nine-bit theorem: exactly two masks are inclusion-minimal. -/
theorem inclusionMinimalDecisionProbeMask_iff (mask : ProbeMask) :
    inclusionMinimalDecisionSuiteBool mask.toFinset = true ↔
      mask = commutatorDecisionProbeMask ∨
        mask = lyapunovDecisionProbeMask := by
  rcases mask with
    ⟨innovation, overlap, distortion, plasticity, propagation,
      commutator, crossSlot, lyapunov, multimodal⟩
  cases innovation <;> cases overlap <;> cases distortion <;>
    cases plasticity <;> cases propagation <;> cases commutator <;>
    cases crossSlot <;> cases lyapunov <;> cases multimodal <;> decide

/-- Exact semantic characterization for every finite probe set. -/
theorem inclusionMinimalDecisionSuite_iff
    (suite : Finset NeededProbe) :
    InclusionMinimalDecisionSuite suite ↔
      suite = commutatorDecisionProbeSuite ∨
        suite = lyapunovDecisionProbeSuite := by
  let mask := ProbeMask.ofFinset suite
  have hround : mask.toFinset = suite := ProbeMask.toFinset_ofFinset suite
  constructor
  · intro hminimal
    have hbool :=
      (inclusionMinimalDecisionSuiteBool_eq_true_iff suite).2 hminimal
    have hmask : inclusionMinimalDecisionSuiteBool mask.toFinset = true := by
      simpa [hround] using hbool
    rcases (inclusionMinimalDecisionProbeMask_iff mask).1 hmask with
      hcommutator | hlyapunov
    · left
      calc
        suite = mask.toFinset := hround.symm
        _ = commutatorDecisionProbeMask.toFinset := by rw [hcommutator]
        _ = commutatorDecisionProbeSuite :=
          commutatorDecisionProbeMask_toFinset
    · right
      calc
        suite = mask.toFinset := hround.symm
        _ = lyapunovDecisionProbeMask.toFinset := by rw [hlyapunov]
        _ = lyapunovDecisionProbeSuite := lyapunovDecisionProbeMask_toFinset
  · rintro (rfl | rfl)
    · exact commutatorDecisionProbeSuite_minimal
    · exact lyapunovDecisionProbeSuite_minimal

/-- Distinct recommendations supported by regimes consistent with a supplied
transcript. -/
def fiberRecommendationList
    (suite : Finset NeededProbe) (signature : ProbeSignature) :
    List Recommendation :=
  ((allModeledUtilizationRegimes.filter fun regime =>
      probeSignature suite regime = signature).map recommendationFor).eraseDups

theorem mem_fiberRecommendationList_iff
    {suite : Finset NeededProbe} {signature : ProbeSignature}
    {recommendation : Recommendation} :
    recommendation ∈ fiberRecommendationList suite signature ↔
      ∃ regime,
        probeSignature suite regime = signature ∧
          recommendationFor regime = recommendation := by
  simp only [fiberRecommendationList, List.mem_eraseDups, List.mem_map,
    List.mem_filter]
  constructor
  · rintro ⟨regime, ⟨_hregistry, hsignature⟩, rfl⟩
    exact ⟨regime, of_decide_eq_true hsignature, rfl⟩
  · rintro ⟨regime, hsignature, rfl⟩
    exact ⟨regime,
      ⟨mem_allModeledUtilizationRegimes regime, by simp [hsignature]⟩, rfl⟩

/-- Exact hybrid for a fiber; no unsupported component is inserted. -/
def fiberHybrid
    (suite : Finset NeededProbe) (signature : ProbeSignature) :
    HybridRecommendation where
  components := fiberRecommendationList suite signature

theorem fiberHybrid_licenses
    {suite : Finset NeededProbe} {signature : ProbeSignature}
    {regime : ModeledUtilizationRegime}
    (hconsistent : probeSignature suite regime = signature) :
    (fiberHybrid suite signature).Licenses regime := by
  refine ⟨recommendationFor regime, ?_, recommendationFor_guaranteed regime⟩
  exact (mem_fiberRecommendationList_iff).2 ⟨regime, hconsistent, rfl⟩

/-- Coverage by component identity, used to state hybrid minimality without
assuming any unproved uniqueness property of arbitrary guarantees. -/
def HybridCoversSignature
    (suite : Finset NeededProbe) (signature : ProbeSignature)
    (hybrid : HybridRecommendation) : Prop :=
  ∀ regime, probeSignature suite regime = signature →
    recommendationFor regime ∈ hybrid.components

theorem fiberHybrid_covers
    (suite : Finset NeededProbe) (signature : ProbeSignature) :
    HybridCoversSignature suite signature (fiberHybrid suite signature) := by
  intro regime hconsistent
  exact (mem_fiberRecommendationList_iff).2 ⟨regime, hconsistent, rfl⟩

/-- Minimality: every component of the exact fiber hybrid is required in any
other component-wise cover of the same observation fiber. -/
theorem fiberHybrid_component_minimal
    {suite : Finset NeededProbe} {signature : ProbeSignature}
    {hybrid : HybridRecommendation}
    (hcovers : HybridCoversSignature suite signature hybrid) :
    ∀ recommendation ∈ (fiberHybrid suite signature).components,
      recommendation ∈ hybrid.components := by
  intro recommendation hmem
  rcases (mem_fiberRecommendationList_iff).1 hmem with
    ⟨regime, hconsistent, hrecommendation⟩
  rw [← hrecommendation]
  exact hcovers regime hconsistent

/-- Runtime result for arbitrary transcripts. -/
inductive SafeArchitectureDecision where
  | abstain
  | singleton (recommendation : Recommendation)
  | hybrid (components : List Recommendation)
  deriving DecidableEq, Repr

def SafeArchitectureDecision.Licenses
    (decision : SafeArchitectureDecision)
    (regime : ModeledUtilizationRegime) : Prop :=
  match decision with
  | .abstain => False
  | .singleton recommendation =>
      RecommendationGuarantee regime recommendation
  | .hybrid components =>
      (HybridRecommendation.mk components).Licenses regime

/-- Empty fibers abstain, singleton recommendation fibers compress to one
answer, and ambiguous fibers return their exact minimal hybrid. -/
def safeDecisionFromSignature
    (suite : Finset NeededProbe) (signature : ProbeSignature) :
    SafeArchitectureDecision :=
  match fiberRecommendationList suite signature with
  | [] => .abstain
  | [recommendation] => .singleton recommendation
  | recommendations => .hybrid recommendations

theorem safeDecisionFromGeneratedSignature_sound
    (suite : Finset NeededProbe) (regime : ModeledUtilizationRegime) :
    (safeDecisionFromSignature suite (probeSignature suite regime)).Licenses
      regime := by
  have hmem : recommendationFor regime ∈
      fiberRecommendationList suite (probeSignature suite regime) :=
    (mem_fiberRecommendationList_iff).2 ⟨regime, rfl, rfl⟩
  generalize hlist :
    fiberRecommendationList suite (probeSignature suite regime) =
      recommendations at hmem ⊢
  cases recommendations with
  | nil => simp at hmem
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hmem
          subst first
          simpa [safeDecisionFromSignature, hlist,
            SafeArchitectureDecision.Licenses] using
            recommendationFor_guaranteed regime
      | cons second tail =>
          simp only [safeDecisionFromSignature, hlist,
            SafeArchitectureDecision.Licenses,
            HybridRecommendation.Licenses]
          exact ⟨recommendationFor regime, hmem,
            recommendationFor_guaranteed regime⟩

/-- Every modeled regime consistent with an arbitrary supplied transcript is
licensed by its singleton or exact-hybrid decision.  Empty fibers may
abstain, but cannot satisfy the consistency premise. -/
theorem safeDecisionFromSignature_sound_of_consistent
    {suite : Finset NeededProbe} {signature : ProbeSignature}
    {regime : ModeledUtilizationRegime}
    (hconsistent : probeSignature suite regime = signature) :
    (safeDecisionFromSignature suite signature).Licenses regime := by
  subst signature
  exact safeDecisionFromGeneratedSignature_sound suite regime

/-- Singleton output is permitted only when every consistent regime carries
that same recommendation. -/
theorem safeDecision_singleton_only_on_constantFiber
    {suite : Finset NeededProbe} {signature : ProbeSignature}
    {recommendation : Recommendation}
    (hsingleton : safeDecisionFromSignature suite signature =
      .singleton recommendation) :
    ∀ regime, probeSignature suite regime = signature →
      recommendationFor regime = recommendation := by
  have hlist : fiberRecommendationList suite signature = [recommendation] := by
    generalize hrecommendations :
      fiberRecommendationList suite signature = recommendations at hsingleton
    cases recommendations with
    | nil => simp [safeDecisionFromSignature, hrecommendations] at hsingleton
    | cons first rest =>
        cases rest with
        | nil =>
            simpa [safeDecisionFromSignature, hrecommendations] using hsingleton
        | cons second tail =>
            simp [safeDecisionFromSignature, hrecommendations] at hsingleton
  intro regime hconsistent
  have hmem : recommendationFor regime ∈
      fiberRecommendationList suite signature :=
    (mem_fiberRecommendationList_iff).2 ⟨regime, hconsistent, rfl⟩
  rw [hlist] at hmem
  simpa using hmem

/-- Positive ambiguity fixture: without interventions the plain primitive
class supports four distinct recommendations, so the safe result is a hybrid. -/
theorem noProbe_plain_returns_exactHybrid :
    safeDecisionFromSignature ∅
        (probeSignature ∅ .wellSpecifiedScalarQuadratic) =
      .hybrid
        [ .useBackprop
        , .usePCPlasticity
        , .useTypedWorkspace
        , .useRoutedWorkspace ] := by
  decide

/-- Negative fixture: a malformed supplement transcript matches no generated
regime and therefore produces explicit abstention. -/
def impossibleProbeSignature : ProbeSignature where
  primitive := .settlingDetected
  readings := []

theorem impossibleTranscript_abstains :
    safeDecisionFromSignature commutatorDecisionProbeSuite
        impossibleProbeSignature = .abstain := by
  decide

/-! ## T6: hash-pinned supplement and executable decision forest -/

/-- Stable wire key for each intervention. -/
def neededProbeKey : NeededProbe → String
  | .innovationResidualSeries => "innovation_residual_series"
  | .sourceIdentityAndOverlap => "source_identity_and_overlap"
  | .latentMeasurementCalibrationPairs =>
      "latent_measurement_calibration_pairs"
  | .pairedCounterfactualEndpointsAndTargetChart =>
      "paired_counterfactual_endpoints_and_target_chart"
  | .topologyDistanceAndBandwidth => "topology_distance_and_bandwidth"
  | .pairedOperatorJacobian => "paired_operator_jacobian"
  | .crossSlotPerturbation => "cross_slot_perturbation"
  | .lyapunovMetricEnergyAndRate => "lyapunov_metric_energy_and_rate"
  | .fullCompletionPosteriorOrMixtureComponents =>
      "full_completion_posterior_or_mixture_components"

/-- Stable wire key for the finite recommendation vocabulary. -/
def recommendationKey : Recommendation → String
  | .useBackprop => "backprop"
  | .usePCInference => "pc_inference"
  | .usePCPlasticity => "pc_plasticity"
  | .useAdditiveBelief => "additive_belief"
  | .useFadingBelief => "fading_belief"
  | .useCalibratedBelief => "calibrated_belief"
  | .useMixtureBelief width => "mixture_belief_" ++ toString width
  | .useTypedWorkspace => "typed_workspace"
  | .useSelectiveWorkspace => "selective_workspace"
  | .useRoutedWorkspace => "routed_workspace"

def primitiveRecommendationOutcomeKey :
    PrimitiveRecommendationOutcome → String
  | .plain => "plain"
  | .evidenceBearing => "evidence_bearing"
  | .settlingDetected => "settling_detected"
  | .gainVariationDetected => "gain_variation_detected"

/-- The only supplement fields admitted as selector inputs. -/
inductive SupplementSelectorInput where
  | primitiveInputs
  | selectedProbes
  | probeResults
  deriving DecidableEq, Fintype, Repr

def supplementSelectorInputKey : SupplementSelectorInput → String
  | .primitiveInputs => "primitive_inputs"
  | .selectedProbes => "selected_probes"
  | .probeResults => "probe_results"

theorem supplementSelectorInput_excludes_derivedAnswers
    (input : SupplementSelectorInput) :
    supplementSelectorInputKey input ≠ "utilization_diagnostics" ∧
      supplementSelectorInputKey input ≠ "regime" := by
  cases input <;> decide

namespace ProbeDecisionTree

/-- Canonical JSON rendering of the executable binary probe program. -/
def render : ProbeDecisionTree → String
  | .leaf recommendation =>
      "{\"leaf\":\"" ++ recommendationKey recommendation ++ "\"}"
  | .branch probe negative positive =>
      "{\"probe\":\"" ++ neededProbeKey probe ++ "\"," ++
        "\"false\":" ++ negative.render ++ "," ++
        "\"true\":" ++ positive.render ++ "}"

end ProbeDecisionTree

/-- Canonical executable decision forest indexed by primitive v3 outcome. -/
def activeProbeDecisionForestPayload : String :=
  "{" ++
    "\"plain\":" ++ (activeDecisionTree .plain).render ++ "," ++
    "\"evidence_bearing\":" ++
      (activeDecisionTree .evidenceBearing).render ++ "," ++
    "\"settling_detected\":" ++
      (activeDecisionTree .settlingDetected).render ++ "," ++
    "\"gain_variation_detected\":" ++
      (activeDecisionTree .gainVariationDetected).render ++
  "}"

def activeProbeDecisionForestComputedSha256 : String :=
  sha256Hex activeProbeDecisionForestPayload

/-- Immutable digest of the executable decision forest. -/
def activeProbeDecisionForestSha256 : String :=
  "6c601d5392350e42e7f9f60f297e456a9013ed422365bc7b96d49dbf128a2cab"

#guard activeProbeDecisionForestComputedSha256 ==
  activeProbeDecisionForestSha256

/-- Canonical minified JSON Schema for the probe supplement.  The existing v3
record remains immutable and is referenced by its pinned digest. -/
def activeProbeSupplementSchemaPayload : String :=
  "{" ++
  "\"$schema\":\"https://json-schema.org/draft/2020-12/schema\"," ++
  "\"$id\":\"workspace_decoder.active_probe_supplement.v1\"," ++
  "\"title\":\"Decision-relevant active-probe supplement\"," ++
  "\"type\":\"object\"," ++
  "\"additionalProperties\":false," ++
  "\"required\":[\"schema_version\",\"depth_probe_schema_sha256\"," ++
    "\"run_id\",\"example_id\",\"primitive_inputs\"," ++
    "\"selected_probes\",\"probe_results\",\"decision_output\"]," ++
  "\"properties\":{" ++
    "\"schema_version\":{" ++
      "\"const\":\"workspace_decoder.active_probe_supplement.v1\"}," ++
    "\"depth_probe_schema_sha256\":{" ++
      "\"const\":\"" ++ utilizationAtlasDepthProbeSchemaSha256 ++ "\"}," ++
    "\"run_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"example_id\":{\"type\":\"string\",\"minLength\":1}," ++
    "\"primitive_inputs\":{" ++
      "\"type\":\"object\",\"additionalProperties\":false," ++
      "\"required\":[\"settling_residual_norm\",\"effective_evidence\"," ++
        "\"earlier_gain\",\"later_gain\"]," ++
      "\"properties\":{" ++
        "\"settling_residual_norm\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"effective_evidence\":{\"type\":\"number\",\"minimum\":0}," ++
        "\"earlier_gain\":{\"type\":\"number\"}," ++
        "\"later_gain\":{\"type\":\"number\"}}}," ++
    "\"selected_probes\":{\"type\":\"array\",\"uniqueItems\":true," ++
      "\"items\":{\"enum\":[" ++
        "\"innovation_residual_series\",\"source_identity_and_overlap\"," ++
        "\"latent_measurement_calibration_pairs\"," ++
        "\"paired_counterfactual_endpoints_and_target_chart\"," ++
        "\"topology_distance_and_bandwidth\",\"paired_operator_jacobian\"," ++
        "\"cross_slot_perturbation\",\"lyapunov_metric_energy_and_rate\"," ++
        "\"full_completion_posterior_or_mixture_components\"]}}," ++
    "\"probe_results\":{\"type\":\"object\"," ++
      "\"additionalProperties\":false,\"properties\":{" ++
        "\"innovation_residual_series\":{\"type\":\"boolean\"}," ++
        "\"source_identity_and_overlap\":{\"type\":\"boolean\"}," ++
        "\"latent_measurement_calibration_pairs\":{\"type\":\"boolean\"}," ++
        "\"paired_counterfactual_endpoints_and_target_chart\":{" ++
          "\"type\":\"boolean\"}," ++
        "\"topology_distance_and_bandwidth\":{\"type\":\"boolean\"}," ++
        "\"paired_operator_jacobian\":{\"type\":\"boolean\"}," ++
        "\"cross_slot_perturbation\":{\"type\":\"boolean\"}," ++
        "\"lyapunov_metric_energy_and_rate\":{\"type\":\"boolean\"}," ++
        "\"full_completion_posterior_or_mixture_components\":{" ++
          "\"type\":\"boolean\"}}}," ++
    "\"decision_output\":{\"oneOf\":[" ++
      "{\"type\":\"object\",\"additionalProperties\":false," ++
        "\"required\":[\"kind\",\"recommendation\"]," ++
        "\"properties\":{\"kind\":{\"const\":\"singleton\"}," ++
          "\"recommendation\":{\"enum\":[" ++
            "\"backprop\",\"pc_inference\",\"pc_plasticity\"," ++
            "\"additive_belief\",\"fading_belief\",\"calibrated_belief\"," ++
            "\"mixture_belief_2\",\"typed_workspace\"," ++
            "\"selective_workspace\",\"routed_workspace\"]}}}," ++
      "{\"type\":\"object\",\"additionalProperties\":false," ++
        "\"required\":[\"kind\",\"recommendations\"]," ++
        "\"properties\":{\"kind\":{\"const\":\"hybrid\"}," ++
          "\"recommendations\":{\"type\":\"array\",\"uniqueItems\":true," ++
            "\"items\":{\"enum\":[" ++
              "\"backprop\",\"pc_inference\",\"pc_plasticity\"," ++
              "\"additive_belief\",\"fading_belief\"," ++
              "\"calibrated_belief\",\"mixture_belief_2\"," ++
              "\"typed_workspace\",\"selective_workspace\"," ++
              "\"routed_workspace\"]}}}}," ++
      "{\"type\":\"object\",\"additionalProperties\":false," ++
        "\"required\":[\"kind\"]," ++
        "\"properties\":{\"kind\":{\"const\":\"abstain\"}}}]}}," ++
  "\"formal_scope\":{" ++
    "\"selector_inputs\":[\"primitive_inputs\",\"selected_probes\"," ++
      "\"probe_results\"]," ++
    "\"selector_output\":\"decision_output\"," ++
    "\"derived_diagnostic_block\":\"excluded\"," ++
    "\"regime_label\":\"excluded\"," ++
    "\"decision_forest_sha256\":\"" ++
      activeProbeDecisionForestComputedSha256 ++ "\"," ++
    "\"formal_model\":\"finite_scalar_quadratic_exact\"," ++
    "\"matrix_and_trained_nonlinear\":\"open\"}}"

def activeProbeSupplementSchemaComputedSha256 : String :=
  sha256Hex activeProbeSupplementSchemaPayload

/-- Immutable digest of the v1 probe-supplement schema. -/
def activeProbeSupplementSchemaSha256 : String :=
  "06ba50bd19c3e40c7a01abfbc0cbda2e3944bb8f3c8b25ce543b32006474514d"

#guard activeProbeSupplementSchemaComputedSha256 ==
  activeProbeSupplementSchemaSha256

/-- Export envelope consumed by the empirical harness.  The nested schema and
decision forest are independently hash-pinned. -/
def renderActiveProbeSupplementFixture : String :=
  "{\"schema_sha256\":\"" ++ activeProbeSupplementSchemaSha256 ++
    "\",\"decision_forest_sha256\":\"" ++
    activeProbeDecisionForestSha256 ++
    "\",\"depth_probe_schema_sha256\":\"" ++
    utilizationAtlasDepthProbeSchemaSha256 ++
    "\",\"schema\":" ++ activeProbeSupplementSchemaPayload ++
    ",\"decision_forest\":" ++ activeProbeDecisionForestPayload ++ "}\n"

/-! ## Integrated active-probing crown -/

/-- Proof-bearing interface for observation quotients, decision recovery,
minimal interventions, adaptive selection, safe ambiguity, and selector-input
discipline.  The adjacent guards pin the schema and executable forest. -/
structure ActiveProbing : Prop where
  canonicalTelemetryAdmissible : ∀ regime,
    (canonicalDecisionRegime regime).Admissible
  primitiveClassifierGrounded : ∀ regime,
    primitiveOutcomeFromObservables (canonicalPrimitiveObservables regime) =
      primitiveOutcomeForRegime regime
  observationReflexive : ∀ suite regime,
    ObservationallyEquivalent suite regime regime
  observationSymmetric : ∀ suite first second,
    ObservationallyEquivalent suite first second →
      ObservationallyEquivalent suite second first
  observationTransitive : ∀ suite first second third,
    ObservationallyEquivalent suite first second →
      ObservationallyEquivalent suite second third →
        ObservationallyEquivalent suite first third
  selectorCriterion : ∀ suite,
    RecommendationDecisionIdentifiable suite ↔
      ProbeSuiteSeparatesRecommendations suite
  recoveredCommutatorSelector :
    SelectorSound (probeSignature commutatorDecisionProbeSuite)
      recommendationFor commutatorDecisionSelector
  recoveredLyapunovSelector :
    SelectorSound (probeSignature lyapunovDecisionProbeSuite)
      recommendationFor lyapunovDecisionSelector
  minimalSuitesExact : ∀ suite,
    InclusionMinimalDecisionSuite suite ↔
      suite = commutatorDecisionProbeSuite ∨
        suite = lyapunovDecisionProbeSuite
  commutatorDeletionWitness : ∀ probe,
    ∀ _hmem : probe ∈ commutatorDecisionProbeSuite,
      let pair := deletionConfoundPair probe
      probeSignature (commutatorDecisionProbeSuite.erase probe) pair.1 =
          probeSignature (commutatorDecisionProbeSuite.erase probe) pair.2 ∧
        recommendationFor pair.1 ≠ recommendationFor pair.2
  lyapunovDeletionWitness : ∀ probe,
    ∀ _hmem : probe ∈ lyapunovDecisionProbeSuite,
      let pair := deletionConfoundPair probe
      probeSignature (lyapunovDecisionProbeSuite.erase probe) pair.1 =
          probeSignature (lyapunovDecisionProbeSuite.erase probe) pair.2 ∧
        recommendationFor pair.1 ≠ recommendationFor pair.2
  adaptiveLeafCorrect : ∀ regime,
    activeRecommendation regime = recommendationFor regime
  adaptiveLeafGuaranteed : ∀ regime,
    RecommendationGuarantee regime (activeRecommendation regime)
  transcriptRunnerGuaranteed : ∀ regime,
    ∃ recommendation,
      activeRecommendationFromSignature
          (probeSignature (activeProbeSuite regime) regime) =
        some recommendation ∧
      RecommendationGuarantee regime recommendation
  adaptiveStopsAtFirstDetermination : ∀ regime,
    StopsAtFirstRecommendation regime
  adaptiveWorstCaseExact :
    (∀ regime, activeProbeCost regime ≤ 4) ∧
      ∃ regime, activeProbeCost regime = 4
  safeConsistentTranscript : ∀ suite signature regime,
    probeSignature suite regime = signature →
      (safeDecisionFromSignature suite signature).Licenses regime
  singletonOnlyOnConstantFiber : ∀ suite signature recommendation,
    safeDecisionFromSignature suite signature = .singleton recommendation →
      ∀ regime, probeSignature suite regime = signature →
        recommendationFor regime = recommendation
  exactHybridMinimal : ∀ suite signature hybrid,
    HybridCoversSignature suite signature hybrid →
      ∀ recommendation ∈ (fiberHybrid suite signature).components,
        recommendation ∈ hybrid.components
  selectorInputsExcludeAnswers : ∀ input,
    supplementSelectorInputKey input ≠ "utilization_diagnostics" ∧
      supplementSelectorInputKey input ≠ "regime"

theorem active_probing : ActiveProbing where
  canonicalTelemetryAdmissible := canonicalDecisionRegime_admissible
  primitiveClassifierGrounded := primitiveOutcome_grounded_in_v3
  observationReflexive := observationallyEquivalent_refl
  observationSymmetric := fun _suite _first _second =>
    observationallyEquivalent_symm
  observationTransitive := fun _suite _first _second _third =>
    observationallyEquivalent_trans
  selectorCriterion := recommendationDecisionIdentifiable_iff
  recoveredCommutatorSelector := commutatorDecisionSelector_sound
  recoveredLyapunovSelector := lyapunovDecisionSelector_sound
  minimalSuitesExact := inclusionMinimalDecisionSuite_iff
  commutatorDeletionWitness := commutatorSuite_deletion_confound
  lyapunovDeletionWitness := lyapunovSuite_deletion_confound
  adaptiveLeafCorrect := activeRecommendation_correct
  adaptiveLeafGuaranteed := activeRecommendation_guaranteed
  transcriptRunnerGuaranteed :=
    activeRecommendationFromAdaptiveSignature_guaranteed
  adaptiveStopsAtFirstDetermination :=
    activeProbePath_stopsAtFirstRecommendation
  adaptiveWorstCaseExact := activeProbeCost_worstCase_exact
  safeConsistentTranscript := fun _suite _signature _regime =>
    safeDecisionFromSignature_sound_of_consistent
  singletonOnlyOnConstantFiber := fun _suite _signature _recommendation =>
    safeDecision_singleton_only_on_constantFiber
  exactHybridMinimal := fun _suite _signature _hybrid =>
    fiberHybrid_component_minimal
  selectorInputsExcludeAnswers :=
    supplementSelectorInput_excludes_derivedAnswers

#print axioms primitiveOutcome_grounded_in_v3
#print axioms soundSelector_exists_iff_fiberConstant
#print axioms recommendationDecisionIdentifiable_iff
#print axioms commutatorDecisionProbeSuite_minimal
#print axioms lyapunovDecisionProbeSuite_minimal
#print axioms inclusionMinimalDecisionSuite_iff
#print axioms activeRecommendation_guaranteed
#print axioms activeRecommendationFromSignature_guaranteed
#print axioms activeRecommendationFromAdaptiveSignature_guaranteed
#print axioms activeProbePath_stopsAtFirstRecommendation
#print axioms activeProbeCost_worstCase_exact
#print axioms fiberHybrid_component_minimal
#print axioms safeDecisionFromGeneratedSignature_sound
#print axioms safeDecisionFromSignature_sound_of_consistent
#print axioms active_probing

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
