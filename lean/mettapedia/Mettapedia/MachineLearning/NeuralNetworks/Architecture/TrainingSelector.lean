import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.ActiveProbing

/-!
# Carrier-by-credit training selector

This file gives a set-valued selector for training regimes.  A method appears
exactly when its declared graph, dynamics, reachability, resource, and trust
premises hold.  The output is an eligibility set, not a ranking and not an
empirical superiority claim.  When no method is licensed, the selector returns
only `unresolved`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector

open Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

/-- Checker feedback available to a learning or search rule. -/
inductive CheckerFeedbackSupport where
  | noFeedback
  | terminalOnly
  | partialProgress
  | denseFeedback
  deriving DecidableEq, Fintype, Repr

/-- Training and adaptation regimes represented by the selector. -/
inductive TrainingMethod where
  | ordinaryBP
  | constrainedBP
  | errorCoordinatePC
  | prospectivePrimalDualPC
  | dfaDirectBroadcast
  | syntheticGradient
  | targetPropagation
  | forwardGradient
  | zerothOrderAdapterTuning
  | equilibriumMethod
  | fastStateBeliefCarom
  | searchLevelFlow
  | periodicConsolidation
  | unresolved
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and quantitative observations used by the selector.  Rational
fields are exact so boundary cases cannot be changed by floating-point noise. -/
structure Profile where
  graphDepth : ℕ
  sharedStateFanin : ℕ
  jacobianSpectralRadius : ℚ
  nonnormalGain : ℚ
  measuredContraction : ℚ
  initializerRelativeError : ℚ
  stateCarrierReachable : Bool
  adapterRankSufficient : Bool
  evidenceHeteroscedastic : Bool
  evidenceCalibrated : Bool
  operatorInterference : ℚ
  operatorsCommute : Bool
  replayFraction : ℚ
  driftRate : ℚ
  retentionCurvature : ℚ
  retentionPressure : ℚ
  retentionProbeAvailable : Bool
  maxWorkMultiplier : ℚ
  maxSpanRounds : ℕ
  maxMemoryMultiplier : ℚ
  localParallelHardware : Bool
  checkerFeedbackSupport : CheckerFeedbackSupport
  discoveryComplementarity : ℚ
  exactTaskGradient : Bool
  reverseModeAvailable : Bool
  residualEnergyAvailable : Bool
  errorCoordinatesAvailable : Bool
  latentConstraintRepair : Bool
  settlingBoundCertified : Bool
  dualStabilityCertified : Bool
  broadcastFeedbackAvailable : Bool
  broadcastRankSufficient : Bool
  sharedOccurrenceAggregationCertified : Bool
  syntheticGradientErrorBound : ℚ
  syntheticRefreshRate : ℚ
  inverseModelErrorBound : ℚ
  forwardJvpAvailable : Bool
  activeParameterDimension : ℕ
  perturbationBudget : ℕ
  smoothSurrogateAvailable : Bool
  checkerPlateauDetected : Bool
  freeNudgedPhasesAvailable : Bool
  fastStateReachable : Bool
  fastStateCalibrated : Bool
  slowWeightReachable : Bool
  longHorizonRecurringContext : Bool
  compositionalAcyclicSearch : Bool
  fairBaselineQueue : Bool
  consolidationPeriodIdentified : Bool
  deriving DecidableEq, Repr

/-- Work, critical-path span, and activation-memory demand. -/
structure ResourceDemand where
  workMultiplier : ℚ
  spanRounds : ℕ
  memoryMultiplier : ℚ
  deriving DecidableEq, Repr

/-- A profile can pay a method's complete declared resource demand. -/
def WithinResources (profile : Profile) (demand : ResourceDemand) : Prop :=
  demand.workMultiplier ≤ profile.maxWorkMultiplier ∧
    demand.spanRounds ≤ profile.maxSpanRounds ∧
    demand.memoryMultiplier ≤ profile.maxMemoryMultiplier

/-- Shared-state credit is safe only when sharing is absent or occurrence
aggregation has been certified. -/
def SharingAccountedFor (profile : Profile) : Prop :=
  profile.sharedStateFanin ≤ 1 ∨
    profile.sharedOccurrenceAggregationCertified = true

/-- Iterative local dynamics require more than spectral-radius telemetry. -/
def ContractiveAndControlled (profile : Profile) : Prop :=
  profile.jacobianSpectralRadius < 1 ∧
    profile.measuredContraction < 1 ∧
    profile.nonnormalGain ≤ 4 ∧
    profile.settlingBoundCertified = true

/-- Resource demand used by each candidate. -/
def resourceDemand (profile : Profile) : TrainingMethod → Option ResourceDemand
  | .ordinaryBP | .constrainedBP =>
      some ⟨2, max 1 profile.graphDepth, 2⟩
  | .errorCoordinatePC =>
      some ⟨3, if profile.localParallelHardware then 1
        else max 2 profile.graphDepth, 2⟩
  | .prospectivePrimalDualPC =>
      some ⟨4, if profile.localParallelHardware then 2
        else max 3 profile.graphDepth, 3⟩
  | .dfaDirectBroadcast => some ⟨1, 1, 1⟩
  | .syntheticGradient => some ⟨2, 1, 1⟩
  | .targetPropagation => some ⟨3, 2, 2⟩
  | .forwardGradient => some ⟨2, 1, 1⟩
  | .zerothOrderAdapterTuning => some ⟨2, 1, 1⟩
  | .equilibriumMethod => some ⟨4, 2, 2⟩
  | .fastStateBeliefCarom => some ⟨1, 1, 2⟩
  | .searchLevelFlow => some ⟨2, 1, 1⟩
  | .periodicConsolidation => some ⟨2, 1, 2⟩
  | .unresolved => none

/-- Premises shared by ordinary and retention-constrained reverse-mode
training. -/
def OrdinaryBPPremises (profile : Profile) : Prop :=
  profile.exactTaskGradient = true ∧
    profile.reverseModeAvailable = true ∧
    profile.stateCarrierReachable = true ∧
    profile.adapterRankSufficient = true ∧
    SharingAccountedFor profile ∧
    WithinResources profile ⟨2, max 1 profile.graphDepth, 2⟩

/-- Exact premise relation mirrored by the executable selector. -/
def MethodPremises (profile : Profile) : TrainingMethod → Prop
  | .ordinaryBP => OrdinaryBPPremises profile
  | .constrainedBP =>
      OrdinaryBPPremises profile ∧
      profile.retentionProbeAvailable = true ∧
      1 / 2 ≤ profile.retentionPressure ∧
      profile.retentionCurvature ≤ 2
  | .errorCoordinatePC =>
      profile.residualEnergyAvailable = true ∧
      profile.errorCoordinatesAvailable = true ∧
      profile.stateCarrierReachable = true ∧
      ContractiveAndControlled profile ∧
      SharingAccountedFor profile ∧
      WithinResources profile
        ⟨3, if profile.localParallelHardware then 1
          else max 2 profile.graphDepth, 2⟩
  | .prospectivePrimalDualPC =>
      profile.residualEnergyAvailable = true ∧
      profile.latentConstraintRepair = true ∧
      profile.dualStabilityCertified = true ∧
      profile.stateCarrierReachable = true ∧
      ContractiveAndControlled profile ∧
      profile.initializerRelativeError ≤ 1 ∧
      SharingAccountedFor profile ∧
      WithinResources profile
        ⟨4, if profile.localParallelHardware then 2
          else max 3 profile.graphDepth, 3⟩
  | .dfaDirectBroadcast =>
      profile.reverseModeAvailable = false ∧
      profile.broadcastFeedbackAvailable = true ∧
      profile.broadcastRankSufficient = true ∧
      profile.stateCarrierReachable = true ∧
      profile.adapterRankSufficient = true ∧
      SharingAccountedFor profile ∧
      WithinResources profile ⟨1, 1, 1⟩
  | .syntheticGradient =>
      profile.reverseModeAvailable = false ∧
      profile.localParallelHardware = true ∧
      profile.syntheticGradientErrorBound < 1 ∧
      profile.driftRate ≤ profile.syntheticRefreshRate ∧
      profile.stateCarrierReachable = true ∧
      WithinResources profile ⟨2, 1, 1⟩
  | .targetPropagation =>
      profile.reverseModeAvailable = false ∧
      profile.inverseModelErrorBound < 1 / 2 ∧
      profile.jacobianSpectralRadius < 1 ∧
      profile.stateCarrierReachable = true ∧
      profile.adapterRankSufficient = true ∧
      WithinResources profile ⟨3, 2, 2⟩
  | .forwardGradient =>
      profile.reverseModeAvailable = false ∧
      profile.forwardJvpAvailable = true ∧
      profile.smoothSurrogateAvailable = true ∧
      profile.checkerPlateauDetected = false ∧
      profile.activeParameterDimension ≤ profile.perturbationBudget ∧
      profile.adapterRankSufficient = true ∧
      WithinResources profile ⟨2, 1, 1⟩
  | .zerothOrderAdapterTuning =>
      profile.reverseModeAvailable = false ∧
      profile.forwardJvpAvailable = false ∧
      profile.smoothSurrogateAvailable = true ∧
      profile.checkerPlateauDetected = false ∧
      profile.activeParameterDimension ≤ 64 ∧
      2 * profile.activeParameterDimension ≤ profile.perturbationBudget ∧
      WithinResources profile ⟨2, 1, 1⟩
  | .equilibriumMethod =>
      profile.residualEnergyAvailable = true ∧
      profile.freeNudgedPhasesAvailable = true ∧
      profile.stateCarrierReachable = true ∧
      ContractiveAndControlled profile ∧
      SharingAccountedFor profile ∧
      WithinResources profile ⟨4, 2, 2⟩
  | .fastStateBeliefCarom =>
      profile.stateCarrierReachable = true ∧
      profile.fastStateReachable = true ∧
      profile.evidenceHeteroscedastic = true ∧
      profile.evidenceCalibrated = true ∧
      1 / 4 ≤ profile.driftRate ∧
      profile.operatorInterference ≤ 1 ∧
      WithinResources profile ⟨1, 1, 2⟩
  | .searchLevelFlow =>
      profile.checkerFeedbackSupport ≠ .noFeedback ∧
      profile.compositionalAcyclicSearch = true ∧
      profile.fairBaselineQueue = true ∧
      1 / 4 ≤ profile.discoveryComplementarity ∧
      WithinResources profile ⟨2, 1, 1⟩
  | .periodicConsolidation =>
      profile.fastStateReachable = true ∧
      profile.slowWeightReachable = true ∧
      profile.adapterRankSufficient = true ∧
      profile.longHorizonRecurringContext = true ∧
      profile.consolidationPeriodIdentified = true ∧
      profile.operatorsCommute = true ∧
      1 / 4 ≤ profile.replayFraction ∧
      WithinResources profile ⟨2, 1, 2⟩
  | .unresolved => False

/-- Fully computational resource check. -/
def withinResourcesBool (profile : Profile) (demand : ResourceDemand) : Bool :=
  decide (demand.workMultiplier ≤ profile.maxWorkMultiplier) &&
    decide (demand.spanRounds ≤ profile.maxSpanRounds) &&
    decide (demand.memoryMultiplier ≤ profile.maxMemoryMultiplier)

/-- Fully computational shared-occurrence check. -/
def sharingAccountedForBool (profile : Profile) : Bool :=
  decide (profile.sharedStateFanin ≤ 1) ||
    profile.sharedOccurrenceAggregationCertified

/-- Fully computational stability check. -/
def contractiveAndControlledBool (profile : Profile) : Bool :=
  decide (profile.jacobianSpectralRadius < 1) &&
    decide (profile.measuredContraction < 1) &&
    decide (profile.nonnormalGain ≤ 4) &&
    profile.settlingBoundCertified

/-- Fully computational common BP check. -/
def ordinaryBPPremisesBool (profile : Profile) : Bool :=
  profile.exactTaskGradient &&
    profile.reverseModeAvailable &&
    profile.stateCarrierReachable &&
    profile.adapterRankSufficient &&
    sharingAccountedForBool profile &&
    withinResourcesBool profile ⟨2, max 1 profile.graphDepth, 2⟩

/-- Transparent executable kernel for `MethodPremises`. -/
def methodPremisesBool (profile : Profile) : TrainingMethod → Bool
  | .ordinaryBP => ordinaryBPPremisesBool profile
  | .constrainedBP =>
      ordinaryBPPremisesBool profile &&
        profile.retentionProbeAvailable &&
        decide (1 / 2 ≤ profile.retentionPressure) &&
        decide (profile.retentionCurvature ≤ 2)
  | .errorCoordinatePC =>
      profile.residualEnergyAvailable &&
        profile.errorCoordinatesAvailable &&
        profile.stateCarrierReachable &&
        contractiveAndControlledBool profile &&
        sharingAccountedForBool profile &&
        withinResourcesBool profile
          ⟨3, if profile.localParallelHardware then 1
            else max 2 profile.graphDepth, 2⟩
  | .prospectivePrimalDualPC =>
      profile.residualEnergyAvailable &&
        profile.latentConstraintRepair &&
        profile.dualStabilityCertified &&
        profile.stateCarrierReachable &&
        contractiveAndControlledBool profile &&
        decide (profile.initializerRelativeError ≤ 1) &&
        sharingAccountedForBool profile &&
        withinResourcesBool profile
          ⟨4, if profile.localParallelHardware then 2
            else max 3 profile.graphDepth, 3⟩
  | .dfaDirectBroadcast =>
      !profile.reverseModeAvailable &&
        profile.broadcastFeedbackAvailable &&
        profile.broadcastRankSufficient &&
        profile.stateCarrierReachable &&
        profile.adapterRankSufficient &&
        sharingAccountedForBool profile &&
        withinResourcesBool profile ⟨1, 1, 1⟩
  | .syntheticGradient =>
      !profile.reverseModeAvailable &&
        profile.localParallelHardware &&
        decide (profile.syntheticGradientErrorBound < 1) &&
        decide (profile.driftRate ≤ profile.syntheticRefreshRate) &&
        profile.stateCarrierReachable &&
        withinResourcesBool profile ⟨2, 1, 1⟩
  | .targetPropagation =>
      !profile.reverseModeAvailable &&
        decide (profile.inverseModelErrorBound < 1 / 2) &&
        decide (profile.jacobianSpectralRadius < 1) &&
        profile.stateCarrierReachable &&
        profile.adapterRankSufficient &&
        withinResourcesBool profile ⟨3, 2, 2⟩
  | .forwardGradient =>
      !profile.reverseModeAvailable &&
        profile.forwardJvpAvailable &&
        profile.smoothSurrogateAvailable &&
        !profile.checkerPlateauDetected &&
        decide (profile.activeParameterDimension ≤ profile.perturbationBudget) &&
        profile.adapterRankSufficient &&
        withinResourcesBool profile ⟨2, 1, 1⟩
  | .zerothOrderAdapterTuning =>
      !profile.reverseModeAvailable &&
        !profile.forwardJvpAvailable &&
        profile.smoothSurrogateAvailable &&
        !profile.checkerPlateauDetected &&
        decide (profile.activeParameterDimension ≤ 64) &&
        decide (2 * profile.activeParameterDimension ≤ profile.perturbationBudget) &&
        withinResourcesBool profile ⟨2, 1, 1⟩
  | .equilibriumMethod =>
      profile.residualEnergyAvailable &&
        profile.freeNudgedPhasesAvailable &&
        profile.stateCarrierReachable &&
        contractiveAndControlledBool profile &&
        sharingAccountedForBool profile &&
        withinResourcesBool profile ⟨4, 2, 2⟩
  | .fastStateBeliefCarom =>
      profile.stateCarrierReachable &&
        profile.fastStateReachable &&
        profile.evidenceHeteroscedastic &&
        profile.evidenceCalibrated &&
        decide (1 / 4 ≤ profile.driftRate) &&
        decide (profile.operatorInterference ≤ 1) &&
        withinResourcesBool profile ⟨1, 1, 2⟩
  | .searchLevelFlow =>
      decide (profile.checkerFeedbackSupport ≠ .noFeedback) &&
        profile.compositionalAcyclicSearch &&
        profile.fairBaselineQueue &&
        decide (1 / 4 ≤ profile.discoveryComplementarity) &&
        withinResourcesBool profile ⟨2, 1, 1⟩
  | .periodicConsolidation =>
      profile.fastStateReachable &&
        profile.slowWeightReachable &&
        profile.adapterRankSufficient &&
        profile.longHorizonRecurringContext &&
        profile.consolidationPeriodIdentified &&
        profile.operatorsCommute &&
        decide (1 / 4 ≤ profile.replayFraction) &&
        withinResourcesBool profile ⟨2, 1, 2⟩
  | .unresolved => false

theorem withinResourcesBool_eq_true_iff
    (profile : Profile) (demand : ResourceDemand) :
  withinResourcesBool profile demand = true ↔
      WithinResources profile demand := by
  simp [withinResourcesBool, WithinResources, and_assoc]

theorem sharingAccountedForBool_eq_true_iff (profile : Profile) :
    sharingAccountedForBool profile = true ↔ SharingAccountedFor profile := by
  simp [sharingAccountedForBool, SharingAccountedFor]

theorem contractiveAndControlledBool_eq_true_iff (profile : Profile) :
    contractiveAndControlledBool profile = true ↔
      ContractiveAndControlled profile := by
  simp [contractiveAndControlledBool, ContractiveAndControlled, and_assoc]

theorem ordinaryBPPremisesBool_eq_true_iff (profile : Profile) :
    ordinaryBPPremisesBool profile = true ↔ OrdinaryBPPremises profile := by
  simp [ordinaryBPPremisesBool, OrdinaryBPPremises,
    sharingAccountedForBool_eq_true_iff, withinResourcesBool_eq_true_iff,
    and_assoc]

theorem methodPremisesBool_eq_true_iff
    (profile : Profile) (method : TrainingMethod) :
    methodPremisesBool profile method = true ↔ MethodPremises profile method := by
  cases method <;>
    simp [methodPremisesBool, MethodPremises,
      ordinaryBPPremisesBool_eq_true_iff,
      sharingAccountedForBool_eq_true_iff,
      contractiveAndControlledBool_eq_true_iff,
      withinResourcesBool_eq_true_iff, and_assoc]

/-- The thirteen substantive methods, excluding abstention. -/
def candidateMethods : Finset TrainingMethod :=
  Finset.univ.erase .unresolved

/-- All and only candidate methods whose premises hold. -/
def licensedCandidates (profile : Profile) : Finset TrainingMethod :=
  candidateMethods.filter fun method => methodPremisesBool profile method = true

/-- Set-valued recommendation with explicit abstention. -/
def selected (profile : Profile) : Finset TrainingMethod :=
  if licensedCandidates profile = ∅ then {.unresolved}
  else licensedCandidates profile

theorem mem_candidateMethods_iff (method : TrainingMethod) :
    method ∈ candidateMethods ↔ method ≠ .unresolved := by
  simp [candidateMethods]

theorem mem_licensedCandidates_iff
    (profile : Profile) (method : TrainingMethod) :
    method ∈ licensedCandidates profile ↔
      method ≠ .unresolved ∧ MethodPremises profile method := by
  simp only [licensedCandidates, Finset.mem_filter,
    methodPremisesBool_eq_true_iff]
  rw [mem_candidateMethods_iff]

theorem licensedCandidates_eq_empty_iff (profile : Profile) :
    licensedCandidates profile = ∅ ↔
      ∀ method, method ≠ .unresolved → ¬ MethodPremises profile method := by
  constructor
  · intro hempty method hcandidate hpremises
    have hmem : method ∈ licensedCandidates profile :=
      (mem_licensedCandidates_iff profile method).2
        ⟨hcandidate, hpremises⟩
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    ext method
    constructor
    · intro hmem
      obtain ⟨hcandidate, hpremises⟩ :=
        (mem_licensedCandidates_iff profile method).1 hmem
      exact (hnone method hcandidate hpremises).elim
    · intro hmem
      simp at hmem

theorem unresolved_mem_selected_iff (profile : Profile) :
    .unresolved ∈ selected profile ↔ licensedCandidates profile = ∅ := by
  by_cases hempty : licensedCandidates profile = ∅
  · simp [selected, hempty]
  · simp [selected, hempty, mem_licensedCandidates_iff]

theorem candidate_mem_selected_iff
    (profile : Profile) {method : TrainingMethod}
    (hcandidate : method ≠ .unresolved) :
    method ∈ selected profile ↔ MethodPremises profile method := by
  by_cases hempty : licensedCandidates profile = ∅
  · have hpremises : ¬ MethodPremises profile method := by
      intro hpremises
      have : method ∈ licensedCandidates profile :=
        (mem_licensedCandidates_iff profile method).2
          ⟨hcandidate, hpremises⟩
      rw [hempty] at this
      simp at this
    simp [selected, hempty, hcandidate, hpremises]
  · simp [selected, hempty, mem_licensedCandidates_iff, hcandidate]

/-- Complete selector characterization: a substantive output has its exact
premises, while `unresolved` means that every substantive premise set fails. -/
theorem mem_selected_iff
    (profile : Profile) (method : TrainingMethod) :
    method ∈ selected profile ↔
      (method = .unresolved ∧
        ∀ candidate, candidate ≠ .unresolved →
          ¬ MethodPremises profile candidate) ∨
      (method ≠ .unresolved ∧ MethodPremises profile method) := by
  by_cases hmethod : method = .unresolved
  · subst method
    rw [unresolved_mem_selected_iff, licensedCandidates_eq_empty_iff]
    simp
  · rw [candidate_mem_selected_iff profile hmethod]
    simp [hmethod]

theorem selected_nonempty (profile : Profile) :
    (selected profile).Nonempty := by
  by_cases hempty : licensedCandidates profile = ∅
  · exact ⟨.unresolved, by simp [selected, hempty]⟩
  · rw [selected, if_neg hempty]
    exact Finset.nonempty_iff_ne_empty.2 hempty

/-- Trust-facing subset of the complete premises.  This deliberately says
nothing about empirical superiority. -/
def TrustQualified (profile : Profile) : TrainingMethod → Prop
  | .ordinaryBP | .constrainedBP =>
      profile.exactTaskGradient = true ∧
        profile.reverseModeAvailable = true
  | .errorCoordinatePC =>
      profile.residualEnergyAvailable = true ∧
        profile.settlingBoundCertified = true
  | .prospectivePrimalDualPC =>
      profile.residualEnergyAvailable = true ∧
        profile.dualStabilityCertified = true
  | .dfaDirectBroadcast =>
      profile.broadcastFeedbackAvailable = true ∧
        profile.broadcastRankSufficient = true
  | .syntheticGradient => profile.syntheticGradientErrorBound < 1
  | .targetPropagation => profile.inverseModelErrorBound < 1 / 2
  | .forwardGradient =>
      profile.forwardJvpAvailable = true ∧
        profile.checkerPlateauDetected = false
  | .zerothOrderAdapterTuning =>
      profile.smoothSurrogateAvailable = true ∧
        profile.checkerPlateauDetected = false
  | .equilibriumMethod =>
      profile.freeNudgedPhasesAvailable = true ∧
        profile.settlingBoundCertified = true
  | .fastStateBeliefCarom =>
      profile.evidenceHeteroscedastic = true ∧
        profile.evidenceCalibrated = true
  | .searchLevelFlow =>
      profile.checkerFeedbackSupport ≠ .noFeedback ∧
        profile.fairBaselineQueue = true
  | .periodicConsolidation => profile.operatorsCommute = true
  | .unresolved => False

/-- A substantive selected method carries its premise, resource, and trust
qualification together. -/
structure LicenseCertificate
    (profile : Profile) (method : TrainingMethod) : Prop where
  candidate : method ≠ .unresolved
  premises : MethodPremises profile method
  resourceQualified :
    ∀ demand, resourceDemand profile method = some demand →
      WithinResources profile demand
  trustQualified : TrustQualified profile method

theorem methodPremises_resourceQualified
    (profile : Profile) (method : TrainingMethod)
    (hpremises : MethodPremises profile method) :
    ∀ demand, resourceDemand profile method = some demand →
      WithinResources profile demand := by
  cases method <;>
    simp only [MethodPremises, OrdinaryBPPremises, resourceDemand] at hpremises ⊢ <;>
    aesop

theorem methodPremises_trustQualified
    (profile : Profile) (method : TrainingMethod)
    (hpremises : MethodPremises profile method) :
    TrustQualified profile method := by
  cases method <;>
    simp only [MethodPremises, OrdinaryBPPremises, TrustQualified,
      ContractiveAndControlled] at hpremises ⊢ <;>
    aesop

/-- Selector soundness for every substantive output. -/
theorem selected_candidate_has_certificate
    (profile : Profile) {method : TrainingMethod}
    (hcandidate : method ≠ .unresolved)
    (hselected : method ∈ selected profile) :
    LicenseCertificate profile method := by
  have hpremises :=
    (candidate_mem_selected_iff profile hcandidate).1 hselected
  exact
    { candidate := hcandidate
      premises := hpremises
      resourceQualified :=
        methodPremises_resourceQualified profile method hpremises
      trustQualified :=
        methodPremises_trustQualified profile method hpremises }

/-! ## Observation-erasure no-go theorem -/

/-- Erasing a field means observing only a deterministic projection of the
full profile. -/
def ErasureConfound
    {Observation : Type} (observe : Profile → Observation) : Prop :=
  DecisionConfound observe selected

/-- Existing decision-identifiability theory applies directly: one same-view
pair with different eligibility sets rules out every sound selector over that
erased view. -/
theorem erasureConfound_no_soundSelector
    {Observation : Type} {observe : Profile → Observation}
    (hconfound : ErasureConfound observe) :
    ¬ ∃ selector : Observation → Finset TrainingMethod,
      SelectorSound observe selected selector :=
  decisionConfound_no_soundSelector ({.unresolved} : Finset TrainingMethod)
    hconfound

#print axioms mem_selected_iff
#print axioms selected_candidate_has_certificate
#print axioms erasureConfound_no_soundSelector

end Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector
