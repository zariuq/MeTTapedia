import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.SearchModes

/-!
# Safe semantic shaping crown

This certificate joins the seven semantic-shaping boundaries over the actual
Gauthier evaluator and checker: finite survival is censored evidence, not
extensional correctness; ranking cannot create acceptance; baseline search
remains fairly reachable; calibrated survival priority is conditionally
optimal; first mismatches provide authenticated repair feedback; repair
outcomes aggregate in overlap-corrected counts with drift-aware decay; and
hybrid search value depends on complementarity under a fixed budget.

The certificate summarizes the theorem families proved in the preceding
modules.  Its fields deliberately include both positive licenses and negative
boundaries.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity
open Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask
open Mettapedia.GSLT.LanguageDef.GauthierRefinement
open Mettapedia.MachineLearning.SearchGuidance
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.PLN.Evidence

/-- A theorem-level certificate for the complete safe semantic-shaping
boundary.  The polymorphic theorem families remain available in their source
modules; these fields join their operationally decisive consequences. -/
structure SafeSemanticShapingCertificate where
  exactPrefixBoundary :
    ∀ fuel program target,
      Gauthier.firstMismatchDepth fuel program target = target.length ↔
        EmitsPrefix orgE1Signature fuel program target
  laterMismatchCanBeLessRepairable :
    RepairFixtures.depth .farRepairable < RepairFixtures.depth .nearDead ∧
      RepairFixtures.Repairable .farRepairable ∧
        ¬ RepairFixtures.Repairable .nearDead
  smallerResidualCanBeLessRepairable :
    RepairFixtures.firstResidual .nearDead <
        RepairFixtures.firstResidual .farRepairable ∧
      ¬ RepairFixtures.Repairable .nearDead ∧
        RepairFixtures.Repairable .farRepairable
  finiteAgreementIsNotExtensional :
    Gauthier.PrefixEquivalent 20 1 probeId probeZeroAfterZero ∧
      ¬ Extensional orgE1Signature probeId probeZeroAfterZero
  sameTraceTermsAreDependent :
    (traceTermPacket 7 0).target ≠ (traceTermPacket 7 1).target ∧
      ¬ (traceTermPacket 7 0).SourceDisjoint (traceTermPacket 7 1)
  checkerBoundary :
    ∀ (ranking : orgMemoRoot.State → List orgMemoRoot.Action),
      orgMemoRoot.ListsAllLegalActions ranking →
        ∀ {budget trace program},
          orgMemoRoot.RankedAccepts ranking budget trace program ↔
            orgMemoRoot.Accepts budget trace program
  fairBaselineReachability :
    ∀ (baseline semantic : List ℕ) (semanticSlots rank : ℕ),
      twoQueueCandidate baseline semantic semanticSlots
          (queuePeriod semanticSlots * rank) = baseline[rank]?
  calibratedPriority :
    ∀ (predictedSurvival trueSuccess : Bool → ℝ)
      (pool chosen alternative : Finset Bool) (threshold : ℝ),
      (∀ candidate ∈ pool,
        predictedSurvival candidate = trueSuccess candidate) →
      ThresholdSeparated predictedSurvival pool chosen threshold →
      alternative ⊆ pool →
      EqualVisibleCost chosen alternative →
      expectedExactDiscoveries trueSuccess alternative ≤
        expectedExactDiscoveries trueSuccess chosen
  miscalibrationCanReversePriority :
    ThresholdSeparated reversedPrediction {false, true} {false} (1 / 2) ∧
      EqualVisibleCost ({false} : Finset Bool) {true} ∧
      expectedExactDiscoveries actualSuccess {false} <
        expectedExactDiscoveries actualSuccess {true}
  authenticatedRepairWitness :
    (Gauthier.counterexampleOfFirstMismatch 20 probeZeroAfterZero [0, 1]
      (by rw [Gauthier.probeZeroAfterZero_firstMismatch_is_one]; norm_num)).index = 1 ∧
    (Gauthier.counterexampleOfFirstMismatch 20 probeZeroAfterZero [0, 1]
      (by rw [Gauthier.probeZeroAfterZero_firstMismatch_is_one]; norm_num)).expected = 1 ∧
    Postfix.CompletedStackEntry [0] [Org.z] Org.z
  duplicateRepairIsCountedOnce :
    overlapCorrectedRepairRevision ⟨0, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ = ⟨1, 0⟩
  zeroDriftRecoversCounts :
    ∀ (oldVariance : ℝ), 0 < oldVariance →
      ∀ old fresh overlap : BinEvNat,
        driftAwareRepairRevision oldVariance 0 old fresh overlap =
          WeightedEvidence.ofBinEvNat (old + discountBinEvNat fresh overlap)
  equalYieldCanHideComplementarity :
    iidExpectedBipartiteTargetCoverage redundantArm 1 =
        iidExpectedBipartiteTargetCoverage complementaryArm 1 ∧
      twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 redundantArm 1 <
        twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 complementaryArm 1
  fixedSplitCanLose :
    twoArmExpectedUnionCoverage bestPortfolioPrior 1
        unproductivePortfolioPrior 1 portfolioAccepted <
      iidExpectedDistinctCoverage bestPortfolioPrior 2 portfolioAccepted

/-- Crown: partial sequence agreement is licensed as safe, fair, calibrated
search guidance exactly within the explicit boundaries above. -/
theorem safeSemanticShaping_crown : SafeSemanticShapingCertificate := by
  refine
    { exactPrefixBoundary := ?_
      laterMismatchCanBeLessRepairable :=
        RepairFixtures.greater_depth_not_unconditionally_repairable
      smallerResidualCanBeLessRepairable :=
        RepairFixtures.smaller_residual_not_unconditionally_repairable
      finiteAgreementIsNotExtensional :=
        greater_or_complete_finite_match_not_extensional_correctness
      sameTraceTermsAreDependent := distinctPositions_sameTrace_not_independent
      checkerBoundary := ?_
      fairBaselineReachability := ?_
      calibratedPriority := ?_
      miscalibrationCanReversePriority :=
        reversedCalibration_selects_strictly_worse_candidate
      authenticatedRepairWitness := ?_
      duplicateRepairIsCountedOnce := duplicatedRepairOutcome_contributes_once
      zeroDriftRecoversCounts := ?_
      equalYieldCanHideComplementarity :=
        equal_standalone_yield_does_not_determine_hybrid_value
      fixedSplitCanLose :=
        hybrid_has_no_unconditional_finiteBudget_improvement }
  · intro fuel program target
    exact Gauthier.firstMismatchDepth_eq_length_iff_emitsPrefix
      fuel program target
  · intro ranking hcoverage budget trace program
    exact partialRanking_cannot_create_acceptance ranking hcoverage
  · intro baseline semantic semanticSlots rank
    exact baseline_rank_submitted_at_explicit_time
      baseline semantic semanticSlots rank
  · intro predictedSurvival trueSuccess pool chosen alternative threshold
      hcalibrated htop haltSubset hcost
    exact calibrated_survival_priority_maximizes_expected_exactDiscoveries
      predictedSurvival trueSuccess pool chosen alternative threshold
      hcalibrated htop haltSubset hcost
  · exact ⟨Gauthier.probe_counterexample_index_one,
      Gauthier.probe_counterexample_expected_one,
      Postfix.zero_is_completedStackEntry⟩
  · intro oldVariance hold old fresh overlap
    exact zeroDrift_recovers_exactOverlapCorrectedAddition
      oldVariance hold old fresh overlap

#print axioms safeSemanticShaping_crown

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
