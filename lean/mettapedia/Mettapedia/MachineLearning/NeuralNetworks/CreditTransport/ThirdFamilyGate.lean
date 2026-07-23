import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OperatorSplitting

/-!
# Third-family admission gate

This module represents the evidence required before an update rule may be
treated as a training family distinct from BP, predictive coding, and known
optimizer or search families.  The registry is deliberately refusal-capable:
an unresolved or refuted requirement blocks naming, while mathematical
collapse and prior-art containment count as informative outcomes.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ThirdFamilyGate

/-- Three-valued state of one admission obligation. -/
inductive GateStatus where
  | confirmed
  | refuted
  | unresolved
  deriving DecidableEq, Repr

namespace GateStatus

def IsConfirmed (status : GateStatus) : Prop := status = .confirmed

end GateStatus

/-- Candidate mechanisms are kept unnamed until the full gate passes. -/
inductive Candidate where
  | precisionContinuation
  | dualRateAccumulation
  | amortizedDualInitializer
  | broadcastInitializerWithCorrection
  | stateDependentReliability
  | skewMonotoneTransport
  | localKKTOperatorSplitting
  | verifierFlowCredit
  deriving DecidableEq, Fintype, Repr

/-- The operational axis on which a candidate acts. -/
inductive MechanismAxis where
  | solverDynamics
  | initializer
  | optimizerTransport
  | searchAllocation
  deriving DecidableEq, Repr

/-- Conservative classification of the currently registered construction. -/
inductive CandidateClass where
  | collapse
  | publishedRecovery
  | finiteTimeExtensionWithoutEndpointSeparation
  | collapseOrAdditiveHybrid
  | fixedMetricSeparationVariableMetricCollapse
  | knownOperatorGeometry
  | knownFamilyPendingStrongerSeparation
  | orthogonalSearchAxis
  deriving DecidableEq, Repr

/-- Smallest already-characterized mathematical family containing the current
construction.  This is an intensional registry field, not a bibliographic
claim proved by Lean. -/
inductive KnownFamily where
  | regularizedAugmentedLagrangian
  | pcalmOrMethodOfMultipliers
  | amortizedContractiveSolver
  | broadcastWarmStartOrAdditiveHybrid
  | variableMetricOrMirrorGradient
  | gradientSkewOperatorSplitting
  | monotoneOperatorSplitting
  | verifierGuidedSearch
  deriving DecidableEq, Repr

/-- Ten independent obligations from mathematical nondegeneracy through the
matched-compute gate.  Combining several requirements into one field is
avoided so that a missing empirical certificate cannot be hidden by a
theoretical separation result. -/
structure GateProfile where
  nondegenerate : GateStatus
  updateFamilySeparation : GateStatus
  predictiveTrajectorySeparation : GateStatus
  mathematicalClassDeclared : GateStatus
  convergenceBoundaries : GateStatus
  localityAndOracleAudit : GateStatus
  empiricalMechanismGate : GateStatus
  matchedComputeValueGate : GateStatus
  alternativeAtlasComparison : GateStatus
  priorArtSeparation : GateStatus
  deriving DecidableEq, Repr

namespace GateProfile

/-- Naming is licensed only when every declared obligation is confirmed. -/
def NamingLicensed (profile : GateProfile) : Prop :=
  profile.nondegenerate.IsConfirmed ∧
    profile.updateFamilySeparation.IsConfirmed ∧
    profile.predictiveTrajectorySeparation.IsConfirmed ∧
    profile.mathematicalClassDeclared.IsConfirmed ∧
    profile.convergenceBoundaries.IsConfirmed ∧
    profile.localityAndOracleAudit.IsConfirmed ∧
    profile.empiricalMechanismGate.IsConfirmed ∧
    profile.matchedComputeValueGate.IsConfirmed ∧
    profile.alternativeAtlasComparison.IsConfirmed ∧
    profile.priorArtSeparation.IsConfirmed

theorem namingLicensed_requires_mechanismGate
    {profile : GateProfile} (licensed : profile.NamingLicensed) :
    profile.empiricalMechanismGate = .confirmed :=
  licensed.2.2.2.2.2.2.1

theorem namingLicensed_requires_matchedCompute
    {profile : GateProfile} (licensed : profile.NamingLicensed) :
    profile.matchedComputeValueGate = .confirmed :=
  licensed.2.2.2.2.2.2.2.1

theorem namingLicensed_requires_priorArtSeparation
    {profile : GateProfile} (licensed : profile.NamingLicensed) :
    profile.priorArtSeparation = .confirmed :=
  licensed.2.2.2.2.2.2.2.2.2

end GateProfile

/-- Auditable registry row.  `oracleAudit` says what the current construction
actually consumes; it does not infer locality from the candidate name. -/
structure CandidateAssessment where
  axis : MechanismAxis
  classification : CandidateClass
  smallestKnownFamily : KnownFamily
  oracleAudit : OracleAudit
  gate : GateProfile
  deriving Repr

/-- Current evidence registry.  `unresolved` means that the obligation has
not been established, not that it is false. -/
def assessment : Candidate → CandidateAssessment
  | .precisionContinuation => {
      axis := .solverDynamics
      classification := .collapse
      smallestKnownFamily := .regularizedAugmentedLagrangian
      oracleAudit := ⟨[.localJvpOrVjp], false⟩
      gate := ⟨.confirmed, .refuted, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }
  | .dualRateAccumulation => {
      axis := .solverDynamics
      classification := .publishedRecovery
      smallestKnownFamily := .pcalmOrMethodOfMultipliers
      oracleAudit := ⟨[.localJvpOrVjp], false⟩
      gate := ⟨.confirmed, .refuted, .refuted, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }
  | .amortizedDualInitializer => {
      axis := .initializer
      classification := .finiteTimeExtensionWithoutEndpointSeparation
      smallestKnownFamily := .amortizedContractiveSolver
      oracleAudit := ⟨[.learnedCreditProxy, .localJvpOrVjp], true⟩
      gate := ⟨.confirmed, .refuted, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }
  | .broadcastInitializerWithCorrection => {
      axis := .initializer
      classification := .collapseOrAdditiveHybrid
      smallestKnownFamily := .broadcastWarmStartOrAdditiveHybrid
      oracleAudit := ⟨[.broadcastOutputError, .localJvpOrVjp], false⟩
      gate := ⟨.confirmed, .unresolved, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .unresolved⟩ }
  | .stateDependentReliability => {
      axis := .optimizerTransport
      classification := .fixedMetricSeparationVariableMetricCollapse
      smallestKnownFamily := .variableMetricOrMirrorGradient
      oracleAudit := ⟨[.exactReverseVjp, .parameterUpdateTransform], false⟩
      gate := ⟨.confirmed, .refuted, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }
  | .skewMonotoneTransport => {
      axis := .optimizerTransport
      classification := .knownOperatorGeometry
      smallestKnownFamily := .gradientSkewOperatorSplitting
      oracleAudit := ⟨[.exactReverseVjp, .parameterUpdateTransform], false⟩
      gate := ⟨.confirmed, .confirmed, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }
  | .localKKTOperatorSplitting => {
      axis := .solverDynamics
      classification := .knownFamilyPendingStrongerSeparation
      smallestKnownFamily := .monotoneOperatorSplitting
      oracleAudit := ⟨[.localJvpOrVjp, .auxiliaryBlockSolve], false⟩
      gate := ⟨.confirmed, .unresolved, .unresolved, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .unresolved⟩ }
  | .verifierFlowCredit => {
      axis := .searchAllocation
      classification := .orthogonalSearchAxis
      smallestKnownFamily := .verifierGuidedSearch
      oracleAudit := ⟨[.terminalVerifierReward], false⟩
      gate := ⟨.confirmed, .refuted, .refuted, .confirmed, .confirmed,
        .confirmed, .unresolved, .unresolved, .confirmed, .refuted⟩ }

/-- None of the currently registered candidates clears every naming gate. -/
theorem no_registered_candidate_is_namingLicensed (candidate : Candidate) :
    ¬ (assessment candidate).gate.NamingLicensed := by
  fin_cases candidate <;>
    simp [assessment, GateProfile.NamingLicensed, GateStatus.IsConfirmed]

/-- The skew construction is explicitly an optimizer transform after exact
reverse credit, not a replacement source for that credit. -/
theorem skew_transport_is_optimizer_after_exact_credit :
    (assessment .skewMonotoneTransport).axis = .optimizerTransport ∧
      (assessment .skewMonotoneTransport).oracleAudit.Declares
        .exactReverseVjp ∧
      (assessment .skewMonotoneTransport).oracleAudit.Declares
        .parameterUpdateTransform := by
  simp [assessment, OracleAudit.Declares]

/-- Verifier-flow credit is registered on the orthogonal search-allocation
axis and consumes terminal checker reward. -/
theorem verifier_flow_is_search_axis :
    (assessment .verifierFlowCredit).axis = .searchAllocation ∧
      (assessment .verifierFlowCredit).oracleAudit.Declares
        .terminalVerifierReward := by
  simp [assessment, OracleAudit.Declares]

#print axioms GateProfile.namingLicensed_requires_mechanismGate
#print axioms GateProfile.namingLicensed_requires_matchedCompute
#print axioms no_registered_candidate_is_namingLicensed
#print axioms skew_transport_is_optimizer_after_exact_credit
#print axioms verifier_flow_is_search_axis

end ThirdFamilyGate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
