import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AnytimeMonitoring
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CapInvariance
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.LineageDependence

/-!
# Statistical adjudication crown

This certificate joins three boundaries required for checker-backed campaign
claims:

* adaptive monitoring is valid only through an e-process on the registered
  artifact filtration;
* capped views preserve only statistics licensed by exact representative
  conditions;
* additive evidence revision is licensed from the complete lineage DAG, not
  source inequality or pairwise non-ancestry alone.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open MeasureTheory ProbabilityTheory
open Mettapedia.PLN.Evidence

structure StatisticalAdjudicationCertificate : Prop where
  declaredOrderIsNaturalFiltration :
    ∀ {Ω Increment World Arm : Type}
      [MeasurableSpace Ω]
      [TopologicalSpace Increment]
      [TopologicalSpace.MetrizableSpace Increment]
      [MeasurableSpace Increment] [BorelSpace Increment]
      (stream : DeclaredCampaignStream Ω Increment World Arm),
      stream.filtration =
        Filtration.natural stream.reveal stream.reveal_stronglyMeasurable
  boundedOptionalStopping :
    ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
      (value : ℕ → Ω → ℝ),
      EProcess μ 𝓕 value →
      ∀ (τ : Ω → WithTop ℕ), IsStoppingTime 𝓕 τ →
        ∀ {horizon : ℕ}, (∀ ω, τ ω ≤ horizon) →
          (∫ ω, stoppedValue value τ ω ∂μ) ≤ 1
  campaignOptionalStopping :
    ∀ {Ω Increment World Arm : Type}
      [MeasurableSpace Ω]
      [TopologicalSpace Increment]
      [TopologicalSpace.MetrizableSpace Increment]
      [MeasurableSpace Increment] [BorelSpace Increment]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (stream : DeclaredCampaignStream Ω Increment World Arm)
      (value : ℕ → Ω → ℝ),
      EProcess μ stream.filtration value →
      ∀ (τ : Ω → WithTop ℕ), IsStoppingTime stream.filtration τ →
        ∀ {horizon : ℕ}, (∀ ω, τ ω ≤ horizon) →
          (∫ ω, stoppedValue value τ ω ∂μ) ≤ 1
  countsArePrimary :
    ∀ (p q : ℝ) (left right : BinEvNat),
      countLikelihoodEValue p q (left + right) =
        countLikelihoodEValue p q left * countLikelihoodEValue p q right
  localLikelihoodFairness :
    ∀ (p q : ℝ), p ≠ 0 → 1 - p ≠ 0 →
      p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1
  shortestRetentionIff :
    ∀ {Program : Type} (raw selected : Finset Program)
      (cost : Program → ProgramCost),
      selected ⊆ raw →
      (shortestPrograms selected cost = shortestPrograms raw cost ↔
        shortestPrograms raw cost ⊆ selected)
  fastestRetentionIff :
    ∀ {Program : Type} (raw selected : Finset Program)
      (cost : Program → ProgramCost),
      selected ⊆ raw →
      (fastestPrograms selected cost = fastestPrograms raw cost ↔
        fastestPrograms raw cost ⊆ selected)
  paretoRetentionIff :
    ∀ {Program : Type} (raw selected : Finset Program)
      (cost : Program → ProgramCost),
      selected ⊆ raw →
      (paretoPrograms selected cost = paretoPrograms raw cost ↔
        paretoPrograms raw cost ⊆ selected ∧
          ParetoSoundSelection raw selected cost)
  witnessCountCorruption :
    AccountingFixtures.capOneView.CoverageComplete ∧
      CapInvarianceFixtures.capTwoView.CoverageComplete ∧
      (programsFor AccountingFixtures.capOneView.selected Fixtures.Target.first).card ≠
        (programsFor CapInvarianceFixtures.capTwoView.selected Fixtures.Target.first).card
  diversityCorruption :
    targetCoverage AccountingFixtures.capOneView.selected =
        targetCoverage CapInvarianceFixtures.capTwoView.selected ∧
      programCoverage AccountingFixtures.capOneView.selected ≠
        programCoverage CapInvarianceFixtures.capTwoView.selected
  lineageDerivedRevision :
    ∀ {Source World Lineage Program Target : Type}
      [DecidableEq Source] [Fintype Source] [BEq Program] [BEq Target]
      (graph : LineageDAG Source World Lineage)
      (left right : Source) (leftProgram rightProgram : Program)
      (leftTarget rightTarget : Target),
      graph.GraphIndependent left right →
        LineageAdditiveRevisionLicense graph left right
          leftProgram rightProgram leftTarget rightTarget
  worldsIndependentFromManifest :
    ∀ {Source World Lineage : Type} [DecidableEq Source]
      (graph : LineageDAG Source World Lineage)
      (left right : Source),
      (graph.node left).world ≠ (graph.node right).world →
        graph.GraphIndependent left right
  missingEdgeBoundary :
    LineageFixtures.reportedDAG.GraphIndependent .left .right ∧
      ¬ LineageFixtures.completeDAG.GraphIndependent .left .right
  descendantsNotFresh :
    LineageFixtures.leftPacket.DependsOn LineageFixtures.rootPacket ∧
      ¬ LineageFixtures.rootPacket.SourceDisjoint LineageFixtures.leftPacket
  pairwiseDisjointnessInsufficient :
    LineageFixtures.leftPacket.SourceDisjoint LineageFixtures.rightPacket ∧
      ¬ LineageFixtures.completeDAG.GraphIndependent .left .right

/-- Integrated certificate for anytime-valid, cap-aware, lineage-aware
statistical adjudication of program-discovery campaigns. -/
theorem statisticalAdjudication_crown : StatisticalAdjudicationCertificate := by
  refine
    { declaredOrderIsNaturalFiltration := ?_
      boundedOptionalStopping := ?_
      campaignOptionalStopping := ?_
      countsArePrimary := countLikelihoodEValue_add
      localLikelihoodFairness := bernoulliLikelihoodFactor_nullMean
      shortestRetentionIff := shortestPrograms_eq_iff_retains
      fastestRetentionIff := fastestPrograms_eq_iff_retains
      paretoRetentionIff := paretoPrograms_eq_iff_retains_and_sound
      witnessCountCorruption :=
        CapInvarianceFixtures.selected_witness_count_not_cap_invariant
      diversityCorruption :=
        CapInvarianceFixtures.selected_program_diversity_not_cap_invariant
      lineageDerivedRevision := ?_
      worldsIndependentFromManifest := ?_
      missingEdgeBoundary :=
        LineageFixtures.missing_manifest_edges_invalidate_independence
      descendantsNotFresh := LineageFixtures.descendant_packet_is_not_fresh
      pairwiseDisjointnessInsufficient :=
        LineageFixtures.pairwise_sourceDisjoint_misses_common_cause }
  · intro Ω Increment World Arm instΩ instTop instMetric instIncrement instBorel stream
    rfl
  · intro Ω instΩ μ instProbability 𝓕 value hE τ hτ horizon hbounded
    exact hE.expected_stoppedValue_le_one τ hτ hbounded
  · intro Ω Increment World Arm instΩ instTop instMetric instIncrement instBorel
      μ instProbability stream value hE τ hτ horizon hbounded
    exact stream.expected_stoppedValue_le_one hE τ hτ hbounded
  · intro Source World Lineage Program Target instSource instFinite instProgram instTarget
      graph left right leftProgram rightProgram leftTarget rightTarget hindependent
    exact graphIndependent_licenses_lineageAdditiveRevision graph left right
      leftProgram rightProgram leftTarget rightTarget hindependent
  · intro Source World Lineage instSource graph left right hworld
    exact graph.graphIndependent_of_world_ne hworld

#print axioms statisticalAdjudication_crown

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
