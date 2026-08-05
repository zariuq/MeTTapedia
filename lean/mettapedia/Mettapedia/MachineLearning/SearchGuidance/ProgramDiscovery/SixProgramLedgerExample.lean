import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio

/-!
# Exact adaptive-portfolio oracle

Four arms, three generations, and a two-arm budget reproduce the frozen
adaptive-portfolio conformance fixture.  The examples separate verified union
coverage from lineage-dependent evidence licensing.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
namespace SixProgramLedgerExample

inductive Arm where
  | bpPrimary | bpOpportunity | pc | dfa
  deriving DecidableEq, Fintype, Repr

inductive Generation where
  | generation1 | generation2 | generation3
  deriving DecidableEq, Fintype, Repr

inductive Source where
  | world1BP | world1PC | world2PC | independentPC
  deriving DecidableEq, Fintype, Repr

open Arm Generation Source

def accepted : Generation → Arm → Finset ℕ
  | .generation1, .bpPrimary => {1, 2, 3}
  | .generation1, .bpOpportunity => {1, 2, 3, 4}
  | .generation1, .pc => {5, 6}
  | .generation1, .dfa => {1, 7}
  | .generation2, .bpPrimary => {8, 9}
  | .generation2, .bpOpportunity => {8, 9, 10}
  | .generation2, .pc => {5}
  | .generation2, .dfa => {11, 12, 13}
  | .generation3, .bpPrimary => {14, 15}
  | .generation3, .bpOpportunity => {14, 15, 16}
  | .generation3, .pc => {17, 18}
  | .generation3, .dfa => {14}

def model : PortfolioModel Generation Arm ℕ where
  arms := {.bpPrimary, .bpOpportunity, .pc, .dfa}
  accepted := accepted
  armBudget := 2
  primaryBP := .bpPrimary
  opportunityBP := .bpOpportunity
  primaryBP_mem := by simp
  opportunityBP_mem := by simp
  bpArms_distinct := by decide

def standaloneTopGeneration1 : Finset Arm := {.bpOpportunity, .bpPrimary}
def greedyGeneration1 : Finset Arm := {.bpOpportunity, .pc}
def greedyGeneration2 : Finset Arm := {.bpOpportunity, .dfa}

def feasiblePortfolios : Finset (Finset Arm) :=
  {∅,
   {.bpPrimary}, {.bpOpportunity}, {.pc}, {.dfa},
   {.bpPrimary, .bpOpportunity}, {.bpPrimary, .pc}, {.bpPrimary, .dfa},
   {.bpOpportunity, .pc}, {.bpOpportunity, .dfa}, {.pc, .dfa}}

theorem feasible_iff_mem_feasiblePortfolios (portfolio : Finset Arm) :
    Feasible model portfolio ↔ portfolio ∈ feasiblePortfolios := by
  fin_cases portfolio
  all_goals simp [Feasible, model, feasiblePortfolios]
  all_goals decide

theorem feasible_cases (portfolio : Finset Arm) (hfeasible : Feasible model portfolio) :
    portfolio = ∅ ∨
      portfolio = {.bpPrimary} ∨ portfolio = {.bpOpportunity} ∨
      portfolio = {.pc} ∨ portfolio = {.dfa} ∨
      portfolio = {.bpPrimary, .bpOpportunity} ∨
      portfolio = {.bpPrimary, .pc} ∨ portfolio = {.bpPrimary, .dfa} ∨
      portfolio = {.bpOpportunity, .pc} ∨
      portfolio = {.bpOpportunity, .dfa} ∨ portfolio = {.pc, .dfa} := by
  have hmember := (feasible_iff_mem_feasiblePortfolios portfolio).1 hfeasible
  simpa [feasiblePortfolios] using hmember

theorem standalone_selection_exposes_duplicate_mass :
    standaloneCoverageSum model .generation1 standaloneTopGeneration1 = 7 ∧
      verifiedUnionCoverage model .generation1 standaloneTopGeneration1 = 4 ∧
      duplicateCoverageMass model .generation1 standaloneTopGeneration1 = 3 := by
  decide

theorem opportunity_cost_and_pc_marginals :
    marginalCoverage model .generation1 {.bpPrimary} .bpOpportunity = 1 ∧
      marginalCoverage model .generation1 {.bpPrimary} .pc = 2 := by
  decide

theorem generation1_greedy_steps :
    IsMarginalGreedyStep model .generation1 ∅ .bpOpportunity ∧
      IsMarginalGreedyStep model .generation1 {.bpOpportunity} .pc := by
  constructor
  · constructor
    · simp [model]
    · intro competitor hcompetitor
      fin_cases competitor
      all_goals simp [model] at hcompetitor
      all_goals decide
  · constructor
    · simp [model]
    · intro competitor hcompetitor
      fin_cases competitor
      all_goals simp [model] at hcompetitor
      all_goals decide

theorem generation2_greedy_steps :
    IsMarginalGreedyStep model .generation2 ∅ .bpOpportunity ∧
      IsMarginalGreedyStep model .generation2 {.bpOpportunity} .dfa := by
  constructor
  · constructor
    · simp [model]
    · intro competitor hcompetitor
      fin_cases competitor
      all_goals simp [model] at hcompetitor
      all_goals decide
  · constructor
    · simp [model]
    · intro competitor hcompetitor
      fin_cases competitor
      all_goals simp [model] at hcompetitor
      all_goals decide

theorem generation1_greedy_union :
    verifiedUnionCoverage model .generation1 greedyGeneration1 = 6 := by
  decide

theorem generation2_greedy_union :
    verifiedUnionCoverage model .generation2 greedyGeneration2 = 6 := by
  decide

theorem generation1_unique_optimum :
    Optimizes model .generation1 greedyGeneration1 ∧
      ∀ portfolio, Optimizes model .generation1 portfolio →
        portfolio = greedyGeneration1 := by
  constructor
  · constructor
    · constructor <;> decide
    · intro alternative hfeasible
      rcases feasible_cases alternative hfeasible with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · intro portfolio hoptimal
    have hgreedyFeasible : Feasible model greedyGeneration1 := by
      constructor <;> decide
    have hbound := hoptimal.2 greedyGeneration1 hgreedyFeasible
    rcases feasible_cases portfolio hoptimal.1 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [verifiedUnionCoverage, coveredTargets, model, accepted,
      greedyGeneration1] at hbound
    all_goals simp [greedyGeneration1]

theorem generation2_unique_optimum :
    Optimizes model .generation2 greedyGeneration2 ∧
      ∀ portfolio, Optimizes model .generation2 portfolio →
        portfolio = greedyGeneration2 := by
  constructor
  · constructor
    · constructor <;> decide
    · intro alternative hfeasible
      rcases feasible_cases alternative hfeasible with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · intro portfolio hoptimal
    have hgreedyFeasible : Feasible model greedyGeneration2 := by
      constructor <;> decide
    have hbound := hoptimal.2 greedyGeneration2 hgreedyFeasible
    rcases feasible_cases portfolio hoptimal.1 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [verifiedUnionCoverage, coveredTargets, model, accepted,
      greedyGeneration2] at hbound
    all_goals simp [greedyGeneration2]

theorem frozen_generation1_choice_is_suboptimal_after_drift :
    verifiedUnionCoverage model .generation2 greedyGeneration1 = 4 ∧
      OptimizerChanges model .generation1 .generation2 greedyGeneration1 := by
  exact ⟨by decide, generation1_unique_optimum.1,
    fun hoptimizes ↦ by
      have hbound := hoptimizes.2 greedyGeneration2 generation2_unique_optimum.1.1
      norm_num [verifiedUnionCoverage, coveredTargets, model, accepted,
        greedyGeneration1, greedyGeneration2] at hbound⟩

theorem generation1_two_approximation_from_general_theorem
    (portfolio : Finset Arm) (hfeasible : Feasible model portfolio) :
    verifiedUnionCoverage model .generation1 portfolio ≤
      2 * verifiedUnionCoverage model .generation1 greedyGeneration1 := by
  simpa [model] using
    feasible_coverage_le_budget_mul_of_firstGreedy model .generation1
      generation1_greedy_steps.1 (by simp [greedyGeneration1]) hfeasible

/-! ## Mandatory-primary exploration -/

def explorer : Fin 3 → Arm
  | ⟨0, _⟩ => .pc
  | ⟨1, _⟩ => .dfa
  | ⟨2, _⟩ => .bpOpportunity

theorem explorer_mem_arms (round : Fin 3) : explorer round ∈ model.arms := by
  fin_cases round <;> simp [explorer, model]

theorem explorer_surjective_nonmandatory :
    ∀ arm, arm ≠ model.primaryBP → ∃ round, explorer round = arm := by
  intro arm hne
  fin_cases arm
  · exact False.elim (hne rfl)
  · exact ⟨⟨2, by decide⟩, rfl⟩
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩

theorem exploration_schedule_exact :
    mandatoryExplorationPortfolio model.primaryBP explorer ⟨0, by decide⟩ =
        {.bpPrimary, .pc} ∧
      mandatoryExplorationPortfolio model.primaryBP explorer ⟨1, by decide⟩ =
        {.bpPrimary, .dfa} ∧
      mandatoryExplorationPortfolio model.primaryBP explorer ⟨2, by decide⟩ =
        {.bpPrimary, .bpOpportunity} := by
  decide

theorem exploration_visits_every_nonmandatory_arm (arm : Arm)
    (hne : arm ≠ model.primaryBP) :
    ∃ round, arm ∈ mandatoryExplorationPortfolio model.primaryBP explorer round :=
  mandatoryExploration_visits model.primaryBP explorer
    explorer_surjective_nonmandatory hne

theorem exploration_respects_budget (round : Fin 3) :
    Feasible model (mandatoryExplorationPortfolio model.primaryBP explorer round) :=
  mandatoryExploration_feasible model explorer explorer_mem_arms (by decide) round

def explorationUnion : Fin 3 → ℕ
  | ⟨0, _⟩ => verifiedUnionCoverage model .generation1
      (mandatoryExplorationPortfolio model.primaryBP explorer ⟨0, by decide⟩)
  | ⟨1, _⟩ => verifiedUnionCoverage model .generation2
      (mandatoryExplorationPortfolio model.primaryBP explorer ⟨1, by decide⟩)
  | ⟨2, _⟩ => verifiedUnionCoverage model .generation3
      (mandatoryExplorationPortfolio model.primaryBP explorer ⟨2, by decide⟩)

theorem exploration_union_by_generation :
    explorationUnion 0 = 5 ∧ explorationUnion 1 = 5 ∧
      explorationUnion 2 = 3 := by
  decide

def stationaryAccepted : Arm → Finset ℕ := accepted .generation1

def stationaryModel : PortfolioModel Unit Arm ℕ where
  arms := model.arms
  accepted := fun _ ↦ stationaryAccepted
  armBudget := 2
  primaryBP := .bpPrimary
  opportunityBP := .bpOpportunity
  primaryBP_mem := model.primaryBP_mem
  opportunityBP_mem := model.opportunityBP_mem
  bpArms_distinct := model.bpArms_distinct

def stationaryFixedTotal : ℕ :=
  3 * verifiedUnionCoverage stationaryModel () {.bpPrimary, .pc}

def stationaryExplorationTotal : ℕ :=
  ∑ round : Fin 3,
    verifiedUnionCoverage stationaryModel ()
      (mandatoryExplorationPortfolio stationaryModel.primaryBP explorer round)

theorem exploration_can_reduce_stationary_yield :
    stationaryFixedTotal = 15 ∧ stationaryExplorationTotal = 13 ∧
      stationaryExplorationTotal < stationaryFixedTotal := by
  decide

/-! ## Coverage invariance and evidence-license sensitivity -/

def packet (arm : Arm) (program : ℕ) (source : Source)
    (ancestors : Finset Source) : PortfolioPacket Arm ℕ Unit Source where
  arm := arm
  provenance := {
    program := program
    target := ()
    source := source
    ancestors := ancestors
  }

def primaryPacket : PortfolioPacket Arm ℕ Unit Source :=
  packet .bpPrimary 1 .world1BP ∅

def descendantPacket : PortfolioPacket Arm ℕ Unit Source :=
  packet .pc 5 .world1PC {.world1BP}

def world2Packet : PortfolioPacket Arm ℕ Unit Source :=
  packet .pc 5 .world2PC ∅

def relabelledDescendant : PortfolioPacket Arm ℕ Unit Source :=
  descendantPacket.withLineage .independentPC ∅

def originalPackets : List (PortfolioPacket Arm ℕ Unit Source) :=
  [primaryPacket, descendantPacket, world2Packet]

def relabelledPackets : List (PortfolioPacket Arm ℕ Unit Source) :=
  [primaryPacket, relabelledDescendant, world2Packet]

theorem coverage_invariant_under_lineage_change :
    PortfolioPacket.coverageProjection originalPackets =
      PortfolioPacket.coverageProjection relabelledPackets := by
  simp [PortfolioPacket.coverageProjection, originalPackets, relabelledPackets,
    primaryPacket, descendantPacket, relabelledDescendant, world2Packet,
    packet, PortfolioPacket.withLineage, PortfolioPacket.coverageKey]

theorem original_evidence_licenses :
    ¬ PortfolioPacket.EvidenceAdditiveLicensed primaryPacket descendantPacket ∧
      PortfolioPacket.EvidenceAdditiveLicensed primaryPacket world2Packet ∧
      PortfolioPacket.EvidenceAdditiveLicensed descendantPacket world2Packet := by
  simp [PortfolioPacket.EvidenceAdditiveLicensed, SourcePacket.SourceDisjoint,
    primaryPacket, descendantPacket, world2Packet, packet]

theorem relabelled_evidence_licenses :
    PortfolioPacket.EvidenceAdditiveLicensed primaryPacket relabelledDescendant ∧
      PortfolioPacket.EvidenceAdditiveLicensed primaryPacket world2Packet ∧
      PortfolioPacket.EvidenceAdditiveLicensed relabelledDescendant world2Packet := by
  simp [PortfolioPacket.EvidenceAdditiveLicensed, SourcePacket.SourceDisjoint,
    primaryPacket, descendantPacket, relabelledDescendant, world2Packet,
    packet, PortfolioPacket.withLineage]

theorem evidence_license_changes_while_coverage_does_not :
    PortfolioPacket.coverageProjection originalPackets =
        PortfolioPacket.coverageProjection relabelledPackets ∧
      ¬ PortfolioPacket.EvidenceAdditiveLicensed primaryPacket descendantPacket ∧
      PortfolioPacket.EvidenceAdditiveLicensed primaryPacket relabelledDescendant :=
  ⟨coverage_invariant_under_lineage_change,
    original_evidence_licenses.1, relabelled_evidence_licenses.1⟩

#print axioms generation1_unique_optimum
#print axioms frozen_generation1_choice_is_suboptimal_after_drift
#print axioms generation1_two_approximation_from_general_theorem
#print axioms exploration_visits_every_nonmandatory_arm
#print axioms exploration_respects_budget
#print axioms exploration_can_reduce_stationary_yield
#print axioms evidence_license_changes_while_coverage_does_not

end SixProgramLedgerExample
end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
