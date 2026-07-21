import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ArtifactConformance

/-!
# Provenance-aware program-discovery crown

This certificate joins the witness-preserving discovery kernel, equivalence
boundaries, accounting laws, experiment estimands, dependence-aware evidence
rule, and finite bipartite portfolio theory.  Its population and finite-probe
counterexamples are fields of the certificate, so the crown does not silently
promote bounded observations to extensional or population claims.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Mettapedia.MachineLearning.SearchGuidance
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

structure ProgramDiscoveryCertificate : Prop where
  witnessPreservingFixture :
    witnessPrograms Fixtures.twoProgramsOneTarget Fixtures.Target.first =
        {.alpha, .beta} ∧
      (coveredTargets Fixtures.twoProgramsOneTarget).card = 1 ∧
      (distinctEdges Fixtures.twoProgramsOneTarget).card = 2
  exactRepeatBoundary :
    occurrenceCount Fixtures.repeatedExactProgram .alpha .first = 2 ∧
      (distinctPrograms Fixtures.repeatedExactProgram).card = 1 ∧
      (distinctEdges Fixtures.repeatedExactProgram).card = 1
  manyTargetFixture :
    (coveredTargets Fixtures.oneProgramManyTargets).card = 2 ∧
      (distinctPrograms Fixtures.oneProgramManyTargets).card = 1 ∧
      (distinctEdges Fixtures.oneProgramManyTargets).card = 2
  distinctSyntaxCanBeExtensionallyEqual :
    EquivalenceFixtures.Program.zeroA ≠ EquivalenceFixtures.Program.zeroB ∧
      ExtensionalEquivalent EquivalenceFixtures.semantics
        .zeroA .zeroB
  finitePrefixDoesNotImplyExtensional :
    PrefixEquivalent EquivalenceFixtures.semantics 2 .zeroA .lateOne ∧
      ¬ ExtensionalEquivalent EquivalenceFixtures.semantics .zeroA .lateOne
  finiteFootprintDoesNotIdentifyGlobalBehavior :
    FootprintEquivalent EquivalenceFixtures.solves {false} .zeroA .lateOne ∧
      ¬ (EquivalenceFixtures.solves .zeroA true ↔
        EquivalenceFixtures.solves .lateOne true)
  gauthierFiniteProbeBoundary :
    Gauthier.prefixDistance 20 1
          Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeId
          Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeZeroAfterZero = 0 ∧
      ¬ Mettapedia.GSLT.LanguageDef.GauthierE1.Extensional
        Mettapedia.GSLT.LanguageDef.GauthierE1.orgE1Signature
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeId
        Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity.probeZeroAfterZero
  targetAccounting :
    ∀ {Program Target : Type} [DecidableEq Program] [DecidableEq Target]
      (left right : SolveRelation Program Target),
      targetCoverage (left ∪ right) + (sharedTargets left right).card =
        targetCoverage left + targetCoverage right
  programAccounting :
    ∀ {Program Target : Type} [DecidableEq Program] [DecidableEq Target]
      (left right : SolveRelation Program Target),
      programCoverage (left ∪ right) + (sharedPrograms left right).card =
        programCoverage left + programCoverage right
  equalYieldNotEqualDiversity :
    targetCoverage AccountingFixtures.spreadPrograms =
        targetCoverage AccountingFixtures.sharedProgram ∧
      programCoverage AccountingFixtures.spreadPrograms ≠
        programCoverage AccountingFixtures.sharedProgram
  curationPreservesRawLedger :
    AccountingFixtures.capOneView.CoverageComplete ∧
      (programsFor AccountingFixtures.capOneView.selected Fixtures.Target.first).card = 1 ∧
      (witnessPrograms AccountingFixtures.capOneView.raw Fixtures.Target.first).card = 2
  pairedEffectRelabelInvariant :
    ∀ first second : ℤ,
      twoWorldAveragePairedEffect first second =
        twoWorldAveragePairedEffect second first
  populationBoundary :
    ∀ first second : ℤ,
      ∃ effectsA effectsB : ℕ → ℤ,
        effectsA 0 = first ∧ effectsB 0 = first ∧
        effectsA 1 = second ∧ effectsB 1 = second ∧
        effectsA 2 ≠ effectsB 2
  sourceDisjointRevisionLicense :
    AdditiveRevisionLicense EvidenceFixtures.first EvidenceFixtures.independentRefind
  exactRepeatOverlapCorrection :
    Mettapedia.PLN.WorldModel.PLNWorldModelGeneric.AdditiveWorldModel.extract
        (State := ExactPacketOverlap.State) (Query := ExactPacketOverlap.Query) (Ev := ℕ)
        ({ExactPacketOverlap.key} + {ExactPacketOverlap.key}) ExactPacketOverlap.key = 2 ∧
      ExactPacketOverlap.layer.overlap
        {ExactPacketOverlap.key} {ExactPacketOverlap.key} ExactPacketOverlap.key = 1 ∧
      Mettapedia.PLN.WorldModel.PLNWorldModelGeneric.AdditiveWorldModel.extract
        (State := ExactPacketOverlap.State) (Query := ExactPacketOverlap.Query) (Ev := ℕ)
        (ExactPacketOverlap.layer.merge
          {ExactPacketOverlap.key} {ExactPacketOverlap.key}) ExactPacketOverlap.key = 1
  descendantDependenceBoundary :
    EvidenceFixtures.trainedDescendant.DependsOn EvidenceFixtures.first ∧
      ¬ EvidenceFixtures.first.SourceDisjoint EvidenceFixtures.trainedDescendant
  exactBipartiteTargetCoverage :
    ∀ {programCount targetCount : ℕ}
      (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ),
      iidExpectedBipartiteTargetCoverage prior budget =
        ∑ target : Fin targetCount,
          (1 - (1 - targetSetMass prior (targetFiber target)) ^ budget)
  exactBipartiteWitnessCoverage :
    ∀ {programCount targetCount : ℕ}
      (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ),
      iidExpectedProgramWitnessCoverage prior budget =
        ∑ edge : Fin (programCount * targetCount),
          (1 - (1 - (prior : Fin (programCount * targetCount) → ℝ) edge) ^ budget)
  diminishingTargetDiscovery :
    ∀ {programCount targetCount : ℕ}
      (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ),
      expectedBipartiteTargetMarginal prior (budget + 1) ≤
        expectedBipartiteTargetMarginal prior budget
  complementarityAllocation :
    iidExpectedBipartiteTargetCoverage redundantArm 1 =
        iidExpectedBipartiteTargetCoverage complementaryArm 1 ∧
      twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 redundantArm 1 <
        twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 complementaryArm 1

/-- Integrated crown for provenance-aware checker-backed program discovery. -/
theorem provenanceAwareProgramDiscovery_crown : ProgramDiscoveryCertificate := by
  refine
    { witnessPreservingFixture := Fixtures.two_programs_one_target_fixture
      exactRepeatBoundary := Fixtures.exact_repeat_changes_occurrences_not_diversity_fixture
      manyTargetFixture := Fixtures.one_program_many_targets_fixture
      distinctSyntaxCanBeExtensionallyEqual :=
        EquivalenceFixtures.distinct_programs_can_be_extensionally_equal
      finitePrefixDoesNotImplyExtensional :=
        EquivalenceFixtures.finite_prefix_equality_not_extensional
      finiteFootprintDoesNotIdentifyGlobalBehavior :=
        EquivalenceFixtures.equal_finite_footprint_not_global
      gauthierFiniteProbeBoundary := Gauthier.probe_prefixDistance_zero_but_not_extensional
      targetAccounting := ?_
      programAccounting := ?_
      equalYieldNotEqualDiversity :=
        AccountingFixtures.equal_target_yield_different_program_diversity
      curationPreservesRawLedger :=
        AccountingFixtures.cap_preserves_coverage_not_multiplicity_fixture
      pairedEffectRelabelInvariant := twoWorldAveragePairedEffect_relabel
      populationBoundary := two_world_effects_do_not_identify_unseen_world
      sourceDisjointRevisionLicense :=
        EvidenceFixtures.source_disjoint_refind_has_additive_license
      exactRepeatOverlapCorrection := ExactPacketOverlap.exact_repeat_overlap_fixture
      descendantDependenceBoundary :=
        EvidenceFixtures.trained_descendant_not_source_disjoint
      exactBipartiteTargetCoverage := ?_
      exactBipartiteWitnessCoverage := ?_
      diminishingTargetDiscovery := ?_
      complementarityAllocation := equal_standalone_different_portfolio_value }
  · intro Program Target instProgram instTarget left right
    exact target_inclusion_exclusion left right
  · intro Program Target instProgram instTarget left right
    exact program_inclusion_exclusion left right
  · intro programCount targetCount prior budget
    exact iidExpectedBipartiteTargetCoverage_eq_sum_one_sub_pow prior budget
  · intro programCount targetCount prior budget
    exact iidExpectedProgramWitnessCoverage_eq_sum_one_sub_pow prior budget
  · intro programCount targetCount prior budget
    exact expectedBipartiteTargetMarginal_antitone prior budget

#print axioms provenanceAwareProgramDiscovery_crown

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
