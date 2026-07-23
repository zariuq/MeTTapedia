import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge
import Mathlib.Tactic

/-!
# Adaptive verified-coverage portfolios

This module separates three layers that must not be conflated: deterministic
checker-accepted union coverage, budgeted arm allocation, and lineage-aware
evidence licensing.  Coverage ignores provenance labels; additive evidence
does not.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio

universe uG uA uT uP uS

/-- A generation-indexed finite arm family.  The opportunity-cost BP arm is a
distinct registered arm, not additional output attributed to the primary BP
arm. -/
structure PortfolioModel (Generation : Type uG) (Arm : Type uA) (Target : Type uT) where
  arms : Finset Arm
  accepted : Generation → Arm → Finset Target
  armBudget : ℕ
  primaryBP : Arm
  opportunityBP : Arm
  primaryBP_mem : primaryBP ∈ arms
  opportunityBP_mem : opportunityBP ∈ arms
  bpArms_distinct : primaryBP ≠ opportunityBP

section Coverage

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Arm] [DecidableEq Target]

/-- Checker-accepted target union for a selected arm portfolio. -/
def coveredTargets (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (portfolio : Finset Arm) : Finset Target :=
  portfolio.biUnion (model.accepted generation)

def verifiedUnionCoverage (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (portfolio : Finset Arm) : ℕ :=
  (coveredTargets model generation portfolio).card

/-- The sum of standalone arm yields, before duplicate targets are collapsed. -/
def standaloneCoverageSum (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (portfolio : Finset Arm) : ℕ :=
  ∑ arm ∈ portfolio, (model.accepted generation arm).card

/-- Collision mass exposed by comparing the standalone sum with verified
union coverage. -/
def duplicateCoverageMass (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (portfolio : Finset Arm) : ℕ :=
  standaloneCoverageSum model generation portfolio -
    verifiedUnionCoverage model generation portfolio

def marginalTargets (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) (arm : Arm) : Finset Target :=
  model.accepted generation arm \ coveredTargets model generation selected

def marginalCoverage (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) (arm : Arm) : ℕ :=
  (marginalTargets model generation selected arm).card

def Feasible (model : PortfolioModel Generation Arm Target)
    (portfolio : Finset Arm) : Prop :=
  portfolio ⊆ model.arms ∧ portfolio.card ≤ model.armBudget

def Optimizes (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (portfolio : Finset Arm) : Prop :=
  Feasible model portfolio ∧
    ∀ alternative, Feasible model alternative →
      verifiedUnionCoverage model generation alternative ≤
        verifiedUnionCoverage model generation portfolio

/-- One exact marginal-greedy step over the registered arm family. -/
def IsMarginalGreedyStep (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) (chosen : Arm) : Prop :=
  chosen ∈ model.arms \ selected ∧
    ∀ competitor ∈ model.arms \ selected,
      marginalCoverage model generation selected competitor ≤
        marginalCoverage model generation selected chosen

omit [DecidableEq Arm] in
theorem coveredTargets_mono (model : PortfolioModel Generation Arm Target)
    (generation : Generation) {left right : Finset Arm} (hsubset : left ⊆ right) :
    coveredTargets model generation left ⊆ coveredTargets model generation right := by
  intro target htarget
  simp only [coveredTargets, Finset.mem_biUnion] at htarget ⊢
  rcases htarget with ⟨arm, harm, htarget⟩
  exact ⟨arm, hsubset harm, htarget⟩

omit [DecidableEq Arm] in
theorem verifiedUnionCoverage_mono
    (model : PortfolioModel Generation Arm Target) (generation : Generation)
    {left right : Finset Arm} (hsubset : left ⊆ right) :
    verifiedUnionCoverage model generation left ≤
      verifiedUnionCoverage model generation right :=
  Finset.card_le_card (coveredTargets_mono model generation hsubset)

-- Diminishing returns for checker-accepted union coverage.
omit [DecidableEq Arm] in
theorem marginalCoverage_antitone
    (model : PortfolioModel Generation Arm Target) (generation : Generation)
    {left right : Finset Arm} (arm : Arm) (hsubset : left ⊆ right) :
    marginalCoverage model generation right arm ≤
      marginalCoverage model generation left arm := by
  apply Finset.card_le_card
  intro target htarget
  rcases Finset.mem_sdiff.1 htarget with ⟨harm, hnotRight⟩
  exact Finset.mem_sdiff.2 ⟨harm, fun hleft ↦
    hnotRight (coveredTargets_mono model generation hsubset hleft)⟩

omit [DecidableEq Arm] in
theorem accepted_subset_covered_of_mem
    (model : PortfolioModel Generation Arm Target) (generation : Generation)
    {portfolio : Finset Arm} {arm : Arm} (harm : arm ∈ portfolio) :
    model.accepted generation arm ⊆ coveredTargets model generation portfolio := by
  intro target htarget
  exact Finset.mem_biUnion.2 ⟨arm, harm, htarget⟩

/-- The exact first-step oracle premise used by the conservative approximation
bound below. -/
def IsMaximumSingleton (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (chosen : Arm) : Prop :=
  chosen ∈ model.arms ∧ ∀ arm ∈ model.arms,
    (model.accepted generation arm).card ≤
      (model.accepted generation chosen).card

theorem marginalGreedy_empty_iff_maximumSingleton
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (chosen : Arm) :
    IsMarginalGreedyStep model generation ∅ chosen ↔
      IsMaximumSingleton model generation chosen := by
  constructor
  · intro hgreedy
    refine ⟨by simpa using hgreedy.1, ?_⟩
    intro arm harm
    have hgain := hgreedy.2 arm (by simpa using harm)
    simpa [marginalCoverage, marginalTargets, coveredTargets] using hgain
  · intro hmaximum
    refine ⟨by simpa using hmaximum.1, ?_⟩
    intro arm harm
    have hcard := hmaximum.2 arm (by simpa using harm)
    simpa [marginalCoverage, marginalTargets, coveredTargets] using hcard

/-- A conservative cardinality-budget guarantee.  If the selected portfolio
contains an exact first marginal-greedy choice, then every feasible comparator
has at most `budget` times its verified union coverage.  This is weaker than
the classical exponential greedy bound, but requires only the explicit finite
maximum-singleton oracle and no hidden tie, positivity, or normalization
assumptions. -/
theorem feasible_coverage_le_budget_mul_of_firstGreedy
    (model : PortfolioModel Generation Arm Target) (generation : Generation)
    {chosen : Arm} {selected comparator : Finset Arm}
    (hgreedy : IsMarginalGreedyStep model generation ∅ chosen)
    (hchosen : chosen ∈ selected)
    (hcomparator : Feasible model comparator) :
    verifiedUnionCoverage model generation comparator ≤
      model.armBudget * verifiedUnionCoverage model generation selected := by
  have hmaximum :=
    (marginalGreedy_empty_iff_maximumSingleton model generation chosen).1 hgreedy
  have hsum :
      (∑ arm ∈ comparator, (model.accepted generation arm).card) ≤
        ∑ _arm ∈ comparator, (model.accepted generation chosen).card := by
    exact Finset.sum_le_sum fun arm harm ↦ hmaximum.2 arm (hcomparator.1 harm)
  have hchosenCoverage :
      (model.accepted generation chosen).card ≤
        verifiedUnionCoverage model generation selected := by
    exact Finset.card_le_card
      (accepted_subset_covered_of_mem model generation hchosen)
  calc
    verifiedUnionCoverage model generation comparator
        ≤ ∑ arm ∈ comparator, (model.accepted generation arm).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ _arm ∈ comparator, (model.accepted generation chosen).card := hsum
    _ = comparator.card * (model.accepted generation chosen).card := by simp
    _ ≤ model.armBudget * (model.accepted generation chosen).card := by
          exact Nat.mul_le_mul_right _ hcomparator.2
    _ ≤ model.armBudget * verifiedUnionCoverage model generation selected := by
          exact Nat.mul_le_mul_left _ hchosenCoverage

/-- Drift is represented extensionally: an old optimizer can fail the new
generation's objective without any claim that one allocation is universally
best. -/
def OptimizerChanges
    (model : PortfolioModel Generation Arm Target)
    (earlier later : Generation) (oldPortfolio : Finset Arm) : Prop :=
  Optimizes model earlier oldPortfolio ∧ ¬ Optimizes model later oldPortfolio

end Coverage

/-! ## Mandatory-arm fair exploration -/

section Exploration

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Arm] [DecidableEq Target]

def mandatoryExplorationPortfolio {rounds : ℕ}
    (mandatory : Arm) (explorer : Fin rounds → Arm) (round : Fin rounds) : Finset Arm :=
  {mandatory, explorer round}

theorem mandatory_mem_explorationPortfolio {rounds : ℕ}
    (mandatory : Arm) (explorer : Fin rounds → Arm) (round : Fin rounds) :
    mandatory ∈ mandatoryExplorationPortfolio mandatory explorer round := by
  simp [mandatoryExplorationPortfolio]

theorem explorer_mem_explorationPortfolio {rounds : ℕ}
    (mandatory : Arm) (explorer : Fin rounds → Arm) (round : Fin rounds) :
    explorer round ∈ mandatoryExplorationPortfolio mandatory explorer round := by
  simp [mandatoryExplorationPortfolio]

theorem mandatoryExplorationPortfolio_card_le_two {rounds : ℕ}
    (mandatory : Arm) (explorer : Fin rounds → Arm) (round : Fin rounds) :
    (mandatoryExplorationPortfolio mandatory explorer round).card ≤ 2 := by
  simpa [mandatoryExplorationPortfolio] using
    Finset.card_insert_le mandatory ({explorer round} : Finset Arm)

omit [DecidableEq Target] in
theorem mandatoryExploration_feasible
    (model : PortfolioModel Generation Arm Target) {rounds : ℕ}
    (explorer : Fin rounds → Arm)
    (hexplorer : ∀ round, explorer round ∈ model.arms)
    (hbudget : 2 ≤ model.armBudget) (round : Fin rounds) :
    Feasible model
      (mandatoryExplorationPortfolio model.primaryBP explorer round) := by
  constructor
  · intro arm harm
    simp only [mandatoryExplorationPortfolio, Finset.mem_insert,
      Finset.mem_singleton] at harm
    rcases harm with rfl | rfl
    · exact model.primaryBP_mem
    · exact hexplorer round
  · exact (mandatoryExplorationPortfolio_card_le_two
      model.primaryBP explorer round).trans hbudget

/-- A declared surjective exploration order visits every nonmandatory arm in
one cycle. -/
theorem mandatoryExploration_visits
    {rounds : ℕ} (mandatory : Arm) (explorer : Fin rounds → Arm)
    (hsurjective : ∀ arm, arm ≠ mandatory → ∃ round, explorer round = arm)
    {arm : Arm} (hne : arm ≠ mandatory) :
    ∃ round, arm ∈ mandatoryExplorationPortfolio mandatory explorer round := by
  rcases hsurjective arm hne with ⟨round, hround⟩
  exact ⟨round, by simpa [hround] using
    explorer_mem_explorationPortfolio mandatory explorer round⟩

end Exploration

/-! ## Coverage projection and lineage-sensitive evidence -/

structure PortfolioPacket
    (Arm : Type uA) (Program : Type uP) (Target : Type uT) (Source : Type uS) where
  arm : Arm
  provenance : SourcePacket Program Target Source

namespace PortfolioPacket

variable {Arm : Type uA} {Program : Type uP} {Target : Type uT} {Source : Type uS}

def coverageKey (packet : PortfolioPacket Arm Program Target Source) : Arm × Program :=
  (packet.arm, packet.provenance.program)

noncomputable def coverageProjection
    (packets : List (PortfolioPacket Arm Program Target Source)) : Finset (Arm × Program) := by
  classical
  exact (packets.map coverageKey).toFinset

/-- Change only lineage metadata, preserving the arm, program, and target. -/
def withLineage [DecidableEq Source]
    (packet : PortfolioPacket Arm Program Target Source)
    (source : Source) (ancestors : Finset Source) :
    PortfolioPacket Arm Program Target Source where
  arm := packet.arm
  provenance := {
    program := packet.provenance.program
    target := packet.provenance.target
    source := source
    ancestors := ancestors
  }

@[simp] theorem coverageKey_withLineage [DecidableEq Source]
    (packet : PortfolioPacket Arm Program Target Source)
    (source : Source) (ancestors : Finset Source) :
    coverageKey (packet.withLineage source ancestors) = coverageKey packet := rfl

theorem coverageProjection_map_withLineage [DecidableEq Source]
    (packets : List (PortfolioPacket Arm Program Target Source))
    (source : PortfolioPacket Arm Program Target Source → Source)
    (ancestors : PortfolioPacket Arm Program Target Source → Finset Source) :
    coverageProjection
        (packets.map fun packet ↦ packet.withLineage (source packet) (ancestors packet)) =
      coverageProjection packets := by
  classical
  simp [coverageProjection, Function.comp_def]

def EvidenceAdditiveLicensed [DecidableEq Source]
    (left right : PortfolioPacket Arm Program Target Source) : Prop :=
  left.provenance.SourceDisjoint right.provenance

theorem evidenceAdditiveLicensed_uses_existingBridge
    [DecidableEq Source] [BEq Program] [BEq Target]
    (left right : PortfolioPacket Arm Program Target Source)
    (hlicensed : EvidenceAdditiveLicensed left right) :
    AdditiveRevisionLicense left.provenance right.provenance :=
  sourceDisjoint_licenses_additiveRevision _ _ hlicensed

end PortfolioPacket

#print axioms coveredTargets_mono
#print axioms marginalCoverage_antitone
#print axioms feasible_coverage_le_budget_mul_of_firstGreedy
#print axioms mandatoryExploration_feasible
#print axioms mandatoryExploration_visits
#print axioms PortfolioPacket.coverageProjection_map_withLineage
#print axioms PortfolioPacket.evidenceAdditiveLicensed_uses_existingBridge

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
