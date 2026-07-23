import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector

/-!
# Executable fixtures for the carrier-by-credit selector

These fixtures mirror the versioned selector conformance data.  Each positive
profile isolates one licensed regime (except constrained BP, which also retains
its ordinary-BP base license), and each paired negative profile removes one
load-bearing premise.  Four observation-erasure witnesses then show that no
selector can reconstruct the complete decision after hiding a relevant field.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector

open Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

/-! ## Versioned positive profiles -/

def baseProfile : Profile :=
  { graphDepth := 1
    sharedStateFanin := 1
    jacobianSpectralRadius := 1
    nonnormalGain := 1
    measuredContraction := 1
    initializerRelativeError := 2
    stateCarrierReachable := false
    adapterRankSufficient := false
    evidenceHeteroscedastic := false
    evidenceCalibrated := false
    operatorInterference := 2
    operatorsCommute := false
    replayFraction := 0
    driftRate := 0
    retentionCurvature := 3
    retentionPressure := 0
    retentionProbeAvailable := false
    maxWorkMultiplier := 0
    maxSpanRounds := 0
    maxMemoryMultiplier := 0
    localParallelHardware := false
    checkerFeedbackSupport := .noFeedback
    discoveryComplementarity := 0
    exactTaskGradient := false
    reverseModeAvailable := false
    residualEnergyAvailable := false
    errorCoordinatesAvailable := false
    latentConstraintRepair := false
    settlingBoundCertified := false
    dualStabilityCertified := false
    broadcastFeedbackAvailable := false
    broadcastRankSufficient := false
    sharedOccurrenceAggregationCertified := false
    syntheticGradientErrorBound := 2
    syntheticRefreshRate := 0
    inverseModelErrorBound := 2
    forwardJvpAvailable := false
    activeParameterDimension := 128
    perturbationBudget := 0
    smoothSurrogateAvailable := false
    checkerPlateauDetected := false
    freeNudgedPhasesAvailable := false
    fastStateReachable := false
    fastStateCalibrated := false
    slowWeightReachable := false
    longHorizonRecurringContext := false
    compositionalAcyclicSearch := false
    fairBaselineQueue := false
    consolidationPeriodIdentified := false }

def ordinaryBPProfile : Profile :=
  { baseProfile with
    graphDepth := 2
    stateCarrierReachable := true
    adapterRankSufficient := true
    exactTaskGradient := true
    reverseModeAvailable := true
    maxWorkMultiplier := 2
    maxSpanRounds := 2
    maxMemoryMultiplier := 2 }

def constrainedBPProfile : Profile :=
  { ordinaryBPProfile with
    retentionProbeAvailable := true
    retentionPressure := 1
    retentionCurvature := 1 }

def errorCoordinatePCProfile : Profile :=
  { baseProfile with
    graphDepth := 4
    jacobianSpectralRadius := 1 / 2
    nonnormalGain := 2
    measuredContraction := 1 / 2
    stateCarrierReachable := true
    residualEnergyAvailable := true
    errorCoordinatesAvailable := true
    settlingBoundCertified := true
    localParallelHardware := true
    maxWorkMultiplier := 3
    maxSpanRounds := 1
    maxMemoryMultiplier := 2 }

def prospectivePrimalDualPCProfile : Profile :=
  { baseProfile with
    graphDepth := 4
    jacobianSpectralRadius := 1 / 2
    nonnormalGain := 2
    measuredContraction := 1 / 2
    initializerRelativeError := 1 / 2
    stateCarrierReachable := true
    residualEnergyAvailable := true
    latentConstraintRepair := true
    settlingBoundCertified := true
    dualStabilityCertified := true
    localParallelHardware := true
    maxWorkMultiplier := 4
    maxSpanRounds := 2
    maxMemoryMultiplier := 3 }

def dfaProfile : Profile :=
  { baseProfile with
    graphDepth := 6
    stateCarrierReachable := true
    adapterRankSufficient := true
    broadcastFeedbackAvailable := true
    broadcastRankSufficient := true
    maxWorkMultiplier := 1
    maxSpanRounds := 1
    maxMemoryMultiplier := 1 }

def syntheticGradientProfile : Profile :=
  { baseProfile with
    stateCarrierReachable := true
    localParallelHardware := true
    syntheticGradientErrorBound := 1 / 4
    syntheticRefreshRate := 1 / 2
    driftRate := 1 / 4
    maxWorkMultiplier := 2
    maxSpanRounds := 1
    maxMemoryMultiplier := 1 }

def targetPropagationProfile : Profile :=
  { baseProfile with
    jacobianSpectralRadius := 1 / 2
    stateCarrierReachable := true
    adapterRankSufficient := true
    inverseModelErrorBound := 1 / 4
    maxWorkMultiplier := 3
    maxSpanRounds := 2
    maxMemoryMultiplier := 2 }

def forwardGradientProfile : Profile :=
  { baseProfile with
    adapterRankSufficient := true
    forwardJvpAvailable := true
    activeParameterDimension := 8
    perturbationBudget := 8
    smoothSurrogateAvailable := true
    maxWorkMultiplier := 2
    maxSpanRounds := 1
    maxMemoryMultiplier := 1 }

def zerothOrderProfile : Profile :=
  { baseProfile with
    activeParameterDimension := 8
    perturbationBudget := 16
    smoothSurrogateAvailable := true
    maxWorkMultiplier := 2
    maxSpanRounds := 1
    maxMemoryMultiplier := 1 }

def equilibriumProfile : Profile :=
  { baseProfile with
    jacobianSpectralRadius := 1 / 2
    nonnormalGain := 2
    measuredContraction := 1 / 2
    stateCarrierReachable := true
    residualEnergyAvailable := true
    settlingBoundCertified := true
    freeNudgedPhasesAvailable := true
    maxWorkMultiplier := 4
    maxSpanRounds := 2
    maxMemoryMultiplier := 2 }

def beliefCaromProfile : Profile :=
  { baseProfile with
    stateCarrierReachable := true
    evidenceHeteroscedastic := true
    evidenceCalibrated := true
    operatorInterference := 1 / 2
    driftRate := 1 / 2
    fastStateReachable := true
    fastStateCalibrated := true
    maxWorkMultiplier := 1
    maxSpanRounds := 1
    maxMemoryMultiplier := 2 }

def searchFlowProfile : Profile :=
  { baseProfile with
    checkerFeedbackSupport := .terminalOnly
    discoveryComplementarity := 1 / 2
    compositionalAcyclicSearch := true
    fairBaselineQueue := true
    maxWorkMultiplier := 2
    maxSpanRounds := 1
    maxMemoryMultiplier := 1 }

def periodicConsolidationProfile : Profile :=
  { baseProfile with
    adapterRankSufficient := true
    operatorsCommute := true
    replayFraction := 1 / 2
    fastStateReachable := true
    slowWeightReachable := true
    longHorizonRecurringContext := true
    consolidationPeriodIdentified := true
    maxWorkMultiplier := 2
    maxSpanRounds := 1
    maxMemoryMultiplier := 2 }

theorem ordinaryBPProfile_selected :
    selected ordinaryBPProfile = {.ordinaryBP} := by
  rfl

theorem constrainedBPProfile_selected :
    selected constrainedBPProfile = {.ordinaryBP, .constrainedBP} := by
  have hlicensed : licensedCandidates constrainedBPProfile =
      {.ordinaryBP, .constrainedBP} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, constrainedBPProfile, ordinaryBPProfile,
        baseProfile] <;> simp
  simp [selected, hlicensed]

theorem errorCoordinatePCProfile_selected :
    selected errorCoordinatePCProfile = {.errorCoordinatePC} := by
  have hlicensed : licensedCandidates errorCoordinatePCProfile =
      {.errorCoordinatePC} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, errorCoordinatePCProfile, baseProfile] <;>
      simp
  simp [selected, hlicensed]

theorem prospectivePrimalDualPCProfile_selected :
    selected prospectivePrimalDualPCProfile = {.prospectivePrimalDualPC} := by
  have hlicensed : licensedCandidates prospectivePrimalDualPCProfile =
      {.prospectivePrimalDualPC} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, prospectivePrimalDualPCProfile,
        baseProfile] <;> simp
  simp [selected, hlicensed]

theorem dfaProfile_selected :
    selected dfaProfile = {.dfaDirectBroadcast} := by
  have hlicensed : licensedCandidates dfaProfile = {.dfaDirectBroadcast} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, dfaProfile, baseProfile] <;> simp
  simp [selected, hlicensed]

theorem syntheticGradientProfile_selected :
    selected syntheticGradientProfile = {.syntheticGradient} := by
  have hlicensed : licensedCandidates syntheticGradientProfile =
      {.syntheticGradient} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, syntheticGradientProfile, baseProfile] <;>
      simp
  simp [selected, hlicensed]

theorem targetPropagationProfile_selected :
    selected targetPropagationProfile = {.targetPropagation} := by
  have hlicensed : licensedCandidates targetPropagationProfile =
      {.targetPropagation} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, targetPropagationProfile, baseProfile] <;>
      simp
  simp [selected, hlicensed]

theorem forwardGradientProfile_selected :
    selected forwardGradientProfile = {.forwardGradient} := by
  have hlicensed : licensedCandidates forwardGradientProfile =
      {.forwardGradient} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, forwardGradientProfile, baseProfile] <;>
      simp
  simp [selected, hlicensed]

theorem zerothOrderProfile_selected :
    selected zerothOrderProfile = {.zerothOrderAdapterTuning} := by
  have hlicensed : licensedCandidates zerothOrderProfile =
      {.zerothOrderAdapterTuning} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, zerothOrderProfile, baseProfile] <;> simp
  simp [selected, hlicensed]

theorem equilibriumProfile_selected :
    selected equilibriumProfile = {.equilibriumMethod} := by
  have hlicensed : licensedCandidates equilibriumProfile =
      {.equilibriumMethod} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, equilibriumProfile, baseProfile] <;> simp
  simp [selected, hlicensed]

theorem beliefCaromProfile_selected :
    selected beliefCaromProfile = {.fastStateBeliefCarom} := by
  have hlicensed : licensedCandidates beliefCaromProfile =
      {.fastStateBeliefCarom} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, beliefCaromProfile, baseProfile] <;> simp
  simp [selected, hlicensed]

theorem searchFlowProfile_selected :
    selected searchFlowProfile = {.searchLevelFlow} := by
  have hlicensed : licensedCandidates searchFlowProfile = {.searchLevelFlow} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, searchFlowProfile, baseProfile] <;> simp
  simp [selected, hlicensed]

theorem periodicConsolidationProfile_selected :
    selected periodicConsolidationProfile = {.periodicConsolidation} := by
  have hlicensed : licensedCandidates periodicConsolidationProfile =
      {.periodicConsolidation} := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, periodicConsolidationProfile,
        baseProfile] <;> simp
  simp [selected, hlicensed]

theorem insufficientEvidence_selected :
    selected baseProfile = {.unresolved} := by
  have hlicensed : licensedCandidates baseProfile = ∅ := by
    ext method
    cases method <;>
      norm_num [licensedCandidates, candidateMethods, methodPremisesBool,
        ordinaryBPPremisesBool, withinResourcesBool, sharingAccountedForBool,
        contractiveAndControlledBool, baseProfile]
  simp [selected, hlicensed]

/-! ## Paired premise failures -/

def ordinaryBPMissingReverse : Profile :=
  { ordinaryBPProfile with reverseModeAvailable := false }

def constrainedBPMissingProbe : Profile :=
  { constrainedBPProfile with retentionProbeAvailable := false }

def errorCoordinatePCMissingContraction : Profile :=
  { errorCoordinatePCProfile with measuredContraction := 1 }

def prospectivePCMissingDualStability : Profile :=
  { prospectivePrimalDualPCProfile with dualStabilityCertified := false }

def dfaMissingBroadcastRank : Profile :=
  { dfaProfile with broadcastRankSufficient := false }

def syntheticGradientMissingRefresh : Profile :=
  { syntheticGradientProfile with syntheticRefreshRate := 1 / 8 }

def targetPropagationMissingInverseAccuracy : Profile :=
  { targetPropagationProfile with inverseModelErrorBound := 1 / 2 }

def forwardGradientOverDimensionBudget : Profile :=
  { forwardGradientProfile with activeParameterDimension := 9 }

def zerothOrderAtCheckerPlateau : Profile :=
  { zerothOrderProfile with checkerPlateauDetected := true }

def equilibriumMissingNudgedPhase : Profile :=
  { equilibriumProfile with freeNudgedPhasesAvailable := false }

def beliefCaromMissingCalibration : Profile :=
  { beliefCaromProfile with evidenceCalibrated := false }

def searchFlowMissingFairQueue : Profile :=
  { searchFlowProfile with fairBaselineQueue := false }

def periodicConsolidationMissingCommutation : Profile :=
  { periodicConsolidationProfile with operatorsCommute := false }

theorem ordinaryBP_drops_without_reverseMode :
    .ordinaryBP ∉ selected ordinaryBPMissingReverse := by
  rw [candidate_mem_selected_iff ordinaryBPMissingReverse (by decide)]
  norm_num [MethodPremises, OrdinaryBPPremises, ordinaryBPMissingReverse,
    ordinaryBPProfile, baseProfile]

theorem constrainedBP_drops_without_retentionProbe :
    .constrainedBP ∉ selected constrainedBPMissingProbe := by decide

theorem errorCoordinatePC_drops_without_contraction :
    .errorCoordinatePC ∉ selected errorCoordinatePCMissingContraction := by
  rw [candidate_mem_selected_iff errorCoordinatePCMissingContraction (by decide)]
  norm_num [MethodPremises, ContractiveAndControlled,
    errorCoordinatePCMissingContraction, errorCoordinatePCProfile, baseProfile]

theorem prospectivePC_drops_without_dualStability :
    .prospectivePrimalDualPC ∉ selected prospectivePCMissingDualStability := by
  rw [candidate_mem_selected_iff prospectivePCMissingDualStability (by decide)]
  norm_num [MethodPremises, prospectivePCMissingDualStability,
    prospectivePrimalDualPCProfile, baseProfile]

theorem dfa_drops_without_broadcastRank :
    .dfaDirectBroadcast ∉ selected dfaMissingBroadcastRank := by
  rw [candidate_mem_selected_iff dfaMissingBroadcastRank (by decide)]
  norm_num [MethodPremises, dfaMissingBroadcastRank, dfaProfile, baseProfile]

theorem syntheticGradient_drops_without_refresh :
    .syntheticGradient ∉ selected syntheticGradientMissingRefresh := by
  rw [candidate_mem_selected_iff syntheticGradientMissingRefresh (by decide)]
  norm_num [MethodPremises, syntheticGradientMissingRefresh,
    syntheticGradientProfile, baseProfile]

theorem targetPropagation_drops_without_inverseAccuracy :
    .targetPropagation ∉ selected targetPropagationMissingInverseAccuracy := by
  rw [candidate_mem_selected_iff targetPropagationMissingInverseAccuracy (by decide)]
  norm_num [MethodPremises, targetPropagationMissingInverseAccuracy,
    targetPropagationProfile, baseProfile]

theorem forwardGradient_drops_over_dimensionBudget :
    .forwardGradient ∉ selected forwardGradientOverDimensionBudget := by
  rw [candidate_mem_selected_iff forwardGradientOverDimensionBudget (by decide)]
  norm_num [MethodPremises, forwardGradientOverDimensionBudget,
    forwardGradientProfile, baseProfile]

theorem zerothOrder_drops_at_checkerPlateau :
    .zerothOrderAdapterTuning ∉ selected zerothOrderAtCheckerPlateau := by
  rw [candidate_mem_selected_iff zerothOrderAtCheckerPlateau (by decide)]
  norm_num [MethodPremises, zerothOrderAtCheckerPlateau,
    zerothOrderProfile, baseProfile]

theorem equilibrium_drops_without_nudgedPhase :
    .equilibriumMethod ∉ selected equilibriumMissingNudgedPhase := by
  rw [candidate_mem_selected_iff equilibriumMissingNudgedPhase (by decide)]
  norm_num [MethodPremises, equilibriumMissingNudgedPhase,
    equilibriumProfile, baseProfile]

theorem beliefCarom_drops_without_calibration :
    .fastStateBeliefCarom ∉ selected beliefCaromMissingCalibration := by
  rw [candidate_mem_selected_iff beliefCaromMissingCalibration (by decide)]
  norm_num [MethodPremises, beliefCaromMissingCalibration,
    beliefCaromProfile, baseProfile]

theorem searchFlow_drops_without_fairQueue :
    .searchLevelFlow ∉ selected searchFlowMissingFairQueue := by
  rw [candidate_mem_selected_iff searchFlowMissingFairQueue (by decide)]
  norm_num [MethodPremises, searchFlowMissingFairQueue,
    searchFlowProfile, baseProfile]

theorem periodicConsolidation_drops_without_commutation :
    .periodicConsolidation ∉ selected periodicConsolidationMissingCommutation := by
  rw [candidate_mem_selected_iff periodicConsolidationMissingCommutation (by decide)]
  norm_num [MethodPremises, periodicConsolidationMissingCommutation,
    periodicConsolidationProfile, baseProfile]

/-! ## Four observation-erasure impossibility results -/

def eraseEvidenceCalibration (profile : Profile) : Profile :=
  { profile with evidenceCalibrated := false }

def eraseBroadcastRank (profile : Profile) : Profile :=
  { profile with broadcastRankSufficient := false }

def eraseCheckerPlateau (profile : Profile) : Profile :=
  { profile with checkerPlateauDetected := false }

def eraseOperatorCommutation (profile : Profile) : Profile :=
  { profile with operatorsCommute := false }

theorem evidenceCalibration_erasure_confound :
    ErasureConfound eraseEvidenceCalibration := by
  refine ⟨beliefCaromProfile, beliefCaromMissingCalibration, rfl, ?_⟩
  intro heq
  have hmem : .fastStateBeliefCarom ∈ selected beliefCaromProfile := by
    rw [beliefCaromProfile_selected]
    simp
  rw [heq] at hmem
  exact beliefCarom_drops_without_calibration hmem

theorem broadcastRank_erasure_confound :
    ErasureConfound eraseBroadcastRank := by
  refine ⟨dfaProfile, dfaMissingBroadcastRank, rfl, ?_⟩
  intro heq
  have hmem : .dfaDirectBroadcast ∈ selected dfaProfile := by
    rw [dfaProfile_selected]
    simp
  rw [heq] at hmem
  exact dfa_drops_without_broadcastRank hmem

theorem checkerPlateau_erasure_confound :
    ErasureConfound eraseCheckerPlateau := by
  refine ⟨zerothOrderProfile, zerothOrderAtCheckerPlateau, rfl, ?_⟩
  intro heq
  have hmem : .zerothOrderAdapterTuning ∈ selected zerothOrderProfile := by
    rw [zerothOrderProfile_selected]
    simp
  rw [heq] at hmem
  exact zerothOrder_drops_at_checkerPlateau hmem

theorem operatorCommutation_erasure_confound :
    ErasureConfound eraseOperatorCommutation := by
  refine ⟨periodicConsolidationProfile,
    periodicConsolidationMissingCommutation, rfl, ?_⟩
  intro heq
  have hmem : .periodicConsolidation ∈
      selected periodicConsolidationProfile := by
    rw [periodicConsolidationProfile_selected]
    simp
  rw [heq] at hmem
  exact periodicConsolidation_drops_without_commutation hmem

theorem no_soundSelector_without_evidenceCalibration :
    ¬ ∃ selector : Profile → Finset TrainingMethod,
      SelectorSound eraseEvidenceCalibration selected selector :=
  erasureConfound_no_soundSelector evidenceCalibration_erasure_confound

theorem no_soundSelector_without_broadcastRank :
    ¬ ∃ selector : Profile → Finset TrainingMethod,
      SelectorSound eraseBroadcastRank selected selector :=
  erasureConfound_no_soundSelector broadcastRank_erasure_confound

theorem no_soundSelector_without_checkerPlateau :
    ¬ ∃ selector : Profile → Finset TrainingMethod,
      SelectorSound eraseCheckerPlateau selected selector :=
  erasureConfound_no_soundSelector checkerPlateau_erasure_confound

theorem no_soundSelector_without_operatorCommutation :
    ¬ ∃ selector : Profile → Finset TrainingMethod,
      SelectorSound eraseOperatorCommutation selected selector :=
  erasureConfound_no_soundSelector operatorCommutation_erasure_confound

/-! The versioned executable rule intentionally does not yet consult
`fastStateCalibrated`; changing that is a schema revision, not a silent
strengthening of this conformance theorem. -/

theorem selected_ignores_fastStateCalibrated
    (profile : Profile) (value : Bool) :
    selected { profile with fastStateCalibrated := value } = selected profile := by
  rfl

#print axioms ordinaryBPProfile_selected
#print axioms periodicConsolidation_drops_without_commutation
#print axioms no_soundSelector_without_evidenceCalibration
#print axioms no_soundSelector_without_operatorCommutation
#print axioms selected_ignores_fastStateCalibrated

end Mettapedia.MachineLearning.NeuralNetworks.Architecture.TrainingSelector
