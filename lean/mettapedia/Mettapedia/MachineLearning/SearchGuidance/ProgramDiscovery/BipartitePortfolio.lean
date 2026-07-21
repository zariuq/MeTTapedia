import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge
import Mettapedia.MachineLearning.SearchGuidance.SharpnessPortfolio

/-!
# Finite bipartite coverage and portfolio complementarity

A categorical search outcome is an authenticated program-target edge.  This
file derives two different expectations from the same finite word law:
distinct target coverage and distinct program-target witness coverage.  It
also derives diminishing target-coverage returns and gives a constructive
example in which equal standalone target yield hides different portfolio
value.
-/

noncomputable section

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Finset BigOperators
open Mettapedia.MachineLearning.SearchGuidance
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

/-! ## Bipartite outcomes -/

/-- Decode one categorical outcome as a program-target edge. -/
def decodeEdge {programCount targetCount : ℕ}
    (edge : Fin (programCount * targetCount)) :
    Fin programCount × Fin targetCount :=
  finProdFinEquiv.symm edge

def edgeProgram {programCount targetCount : ℕ}
    (edge : Fin (programCount * targetCount)) : Fin programCount :=
  (decodeEdge edge).1

def edgeTarget {programCount targetCount : ℕ}
    (edge : Fin (programCount * targetCount)) : Fin targetCount :=
  (decodeEdge edge).2

/-- The categorical outcomes whose decoded target is `target`. -/
def targetFiber {programCount targetCount : ℕ}
    (target : Fin targetCount) : Finset (Fin (programCount * targetCount)) :=
  Finset.univ.filter (fun edge ↦ edgeTarget edge = target)

/-- A finite search word covers a target when at least one sampled edge ends
at that target. -/
def wordCoversBipartiteTarget {programCount targetCount budget : ℕ}
    (word : Fin budget → Fin (programCount * targetCount))
    (target : Fin targetCount) : Prop :=
  ∃ draw, edgeTarget (word draw) = target

theorem wordCoversBipartiteTarget_iff_hitsFiber
    {programCount targetCount budget : ℕ}
    (word : Fin budget → Fin (programCount * targetCount))
    (target : Fin targetCount) :
    wordCoversBipartiteTarget word target ↔
      wordHitsTargetSet word (targetFiber target) := by
  simp [wordCoversBipartiteTarget, wordHitsTargetSet, targetFiber]

/-- Number of distinct targets covered by a finite edge word. -/
def bipartiteTargetCoverage {programCount targetCount budget : ℕ}
    (word : Fin budget → Fin (programCount * targetCount)) : ℕ := by
  classical
  exact ∑ target : Fin targetCount,
    if wordCoversBipartiteTarget word target then 1 else 0

/-- Exact finite-word expectation of distinct target coverage. -/
def iidExpectedBipartiteTargetCoverage {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) : ℝ :=
  ∑ word : Fin budget → Fin (programCount * targetCount),
    categoricalProductPMF
        (prior : Fin (programCount * targetCount) → ℝ) word *
      (bipartiteTargetCoverage word : ℝ)

/-- Exact finite-word expectation of distinct authenticated program-target
witnesses.  This is the existing distinct-coverage expectation over the full
edge outcome space. -/
def iidExpectedProgramWitnessCoverage {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) : ℝ :=
  iidExpectedDistinctCoverage prior budget Finset.univ

theorem iidExpectedBipartiteTargetCoverage_eq_sum_success
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) :
    iidExpectedBipartiteTargetCoverage prior budget =
      ∑ target : Fin targetCount,
        iidAtLeastOneTargetSuccess prior budget (targetFiber target) := by
  classical
  unfold iidExpectedBipartiteTargetCoverage bipartiteTargetCoverage
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _htarget
  unfold iidAtLeastOneTargetSuccess
  apply Finset.sum_congr rfl
  intro word _hword
  rw [wordCoversBipartiteTarget_iff_hitsFiber]
  by_cases h : wordHitsTargetSet word (targetFiber target) <;> simp [h]

/-- Exact target-coverage formula: each target contributes one minus its
fiber-avoidance probability. -/
theorem iidExpectedBipartiteTargetCoverage_eq_sum_one_sub_pow
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) :
    iidExpectedBipartiteTargetCoverage prior budget =
      ∑ target : Fin targetCount,
        (1 - (1 - targetSetMass prior (targetFiber target)) ^ budget) := by
  rw [iidExpectedBipartiteTargetCoverage_eq_sum_success]
  apply Finset.sum_congr rfl
  intro target _htarget
  exact iidAtLeastOneTargetSuccess_eq_one_sub_pow
    prior budget (targetFiber target)

/-- Exact program-witness formula over all authenticated edges. -/
theorem iidExpectedProgramWitnessCoverage_eq_sum_one_sub_pow
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) :
    iidExpectedProgramWitnessCoverage prior budget =
      ∑ edge : Fin (programCount * targetCount),
        (1 - (1 - (prior : Fin (programCount * targetCount) → ℝ) edge) ^ budget) := by
  exact iidExpectedDistinctCoverage_eq_sum_one_sub_pow prior budget Finset.univ

/-! ## Diminishing expected target-coverage returns -/

def targetCoverageMarginal {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount))
    (budget : ℕ) (target : Fin targetCount) : ℝ :=
  targetSetMass prior (targetFiber target) *
    (1 - targetSetMass prior (targetFiber target)) ^ budget

def expectedBipartiteTargetMarginal {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) : ℝ :=
  iidExpectedBipartiteTargetCoverage prior (budget + 1) -
    iidExpectedBipartiteTargetCoverage prior budget

theorem expectedBipartiteTargetMarginal_eq_sum
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) :
    expectedBipartiteTargetMarginal prior budget =
      ∑ target : Fin targetCount, targetCoverageMarginal prior budget target := by
  rw [expectedBipartiteTargetMarginal,
    iidExpectedBipartiteTargetCoverage_eq_sum_one_sub_pow,
    iidExpectedBipartiteTargetCoverage_eq_sum_one_sub_pow,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro target _htarget
  unfold targetCoverageMarginal
  rw [pow_succ]
  ring

theorem targetCoverageMarginal_antitone_budget
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount))
    (budget : ℕ) (target : Fin targetCount) :
    targetCoverageMarginal prior (budget + 1) target ≤
      targetCoverageMarginal prior budget target := by
  let mass := targetSetMass prior (targetFiber target)
  have hmass0 : 0 ≤ mass := targetSetMass_nonneg prior (targetFiber target)
  have hmass1 : mass ≤ 1 := targetSetMass_le_one prior (targetFiber target)
  have havoid0 : 0 ≤ 1 - mass := sub_nonneg.mpr hmass1
  have havoid1 : 1 - mass ≤ 1 := by linarith
  have hprefix0 : 0 ≤ mass * (1 - mass) ^ budget :=
    mul_nonneg hmass0 (pow_nonneg havoid0 budget)
  unfold targetCoverageMarginal
  change mass * (1 - mass) ^ (budget + 1) ≤
    mass * (1 - mass) ^ budget
  rw [pow_succ]
  simpa [mul_assoc] using mul_le_of_le_one_right hprefix0 havoid1

/-- Expected distinct-target gain is diminishing with the sampling budget. -/
theorem expectedBipartiteTargetMarginal_antitone
    {programCount targetCount : ℕ}
    (prior : ProbSimplex (programCount * targetCount)) (budget : ℕ) :
    expectedBipartiteTargetMarginal prior (budget + 1) ≤
      expectedBipartiteTargetMarginal prior budget := by
  rw [expectedBipartiteTargetMarginal_eq_sum,
    expectedBipartiteTargetMarginal_eq_sum]
  exact Finset.sum_le_sum fun target _htarget ↦
    targetCoverageMarginal_antitone_budget prior budget target

/-! ## Exact portfolio complementarity -/

def twoArmBipartiteTargetUnionCoverage
    {programCount targetCount budgetLeft budgetRight : ℕ}
    (left : Fin budgetLeft → Fin (programCount * targetCount))
    (right : Fin budgetRight → Fin (programCount * targetCount)) : ℕ := by
  classical
  exact ∑ target : Fin targetCount,
    if wordCoversBipartiteTarget left target ∨
        wordCoversBipartiteTarget right target then 1 else 0

def twoArmExpectedBipartiteTargetUnionCoverage
    {programCount targetCount : ℕ}
    (leftPrior : ProbSimplex (programCount * targetCount)) (leftBudget : ℕ)
    (rightPrior : ProbSimplex (programCount * targetCount)) (rightBudget : ℕ) : ℝ :=
  ∑ left : Fin leftBudget → Fin (programCount * targetCount),
    ∑ right : Fin rightBudget → Fin (programCount * targetCount),
      categoricalProductPMF
          (leftPrior : Fin (programCount * targetCount) → ℝ) left *
        categoricalProductPMF
          (rightPrior : Fin (programCount * targetCount) → ℝ) right *
        (twoArmBipartiteTargetUnionCoverage left right : ℝ)

/-- A categorical point mass, used only for the constructive portfolio
separation below. -/
def pointPrior {outcomes : ℕ} (chosen : Fin outcomes) : ProbSimplex outcomes :=
  ⟨fun outcome ↦ if outcome = chosen then 1 else 0, by
    constructor
    · intro outcome
      by_cases h : outcome = chosen <;> simp [h]
    · simp⟩

@[simp] theorem pointPrior_apply {outcomes : ℕ}
    (chosen outcome : Fin outcomes) :
    (pointPrior chosen : Fin outcomes → ℝ) outcome =
      if outcome = chosen then 1 else 0 := rfl

def oneWordEquiv (outcomes : ℕ) : (Fin 1 → Fin outcomes) ≃ Fin outcomes where
  toFun word := word 0
  invFun outcome := fun _ ↦ outcome
  left_inv word := by
    funext draw
    fin_cases draw
    rfl
  right_inv _outcome := rfl

theorem oneDrawExpectation_pointPrior {outcomes : ℕ}
    (chosen : Fin outcomes) (payoff : (Fin 1 → Fin outcomes) → ℝ) :
    (∑ word : Fin 1 → Fin outcomes,
      categoricalProductPMF (pointPrior chosen : Fin outcomes → ℝ) word *
        payoff word) =
      payoff (fun _ ↦ chosen) := by
  let weighted : (Fin 1 → Fin outcomes) → ℝ := fun word ↦
    categoricalProductPMF (pointPrior chosen : Fin outcomes → ℝ) word *
      payoff word
  have hweighted : ∀ word,
      weighted word =
        (fun outcome ↦ weighted (fun _ ↦ outcome)) (oneWordEquiv outcomes word) := by
    intro word
    congr 1
    funext draw
    fin_cases draw
    rfl
  change ∑ word : Fin 1 → Fin outcomes, weighted word = _
  rw [Fintype.sum_equiv (oneWordEquiv outcomes) weighted
    (fun outcome ↦ weighted (fun _ ↦ outcome)) hweighted]
  unfold weighted categoricalProductPMF
  classical
  have hproduct (outcome : Fin outcomes) :
      (∏ draw : Fin 1,
        (if (fun _ : Fin 1 ↦ outcome) draw = chosen then (1 : ℝ) else 0)) =
        if outcome = chosen then 1 else 0 := by
    rw [Fin.prod_univ_succ]
    simp
  simp_rw [pointPrior_apply, hproduct]
  simp

theorem twoArmExpectedBipartiteTargetUnionCoverage_pointPriors
    {programCount targetCount : ℕ}
    (leftEdge rightEdge : Fin (programCount * targetCount)) :
    twoArmExpectedBipartiteTargetUnionCoverage
        (pointPrior leftEdge) 1 (pointPrior rightEdge) 1 =
      twoArmBipartiteTargetUnionCoverage
        (fun _ : Fin 1 ↦ leftEdge) (fun _ : Fin 1 ↦ rightEdge) := by
  unfold twoArmExpectedBipartiteTargetUnionCoverage
  have hright (left : Fin 1 → Fin (programCount * targetCount)) :
      (∑ right : Fin 1 → Fin (programCount * targetCount),
        categoricalProductPMF
            (pointPrior leftEdge : Fin (programCount * targetCount) → ℝ) left *
          categoricalProductPMF
            (pointPrior rightEdge : Fin (programCount * targetCount) → ℝ) right *
          (twoArmBipartiteTargetUnionCoverage left right : ℝ)) =
        categoricalProductPMF
            (pointPrior leftEdge : Fin (programCount * targetCount) → ℝ) left *
          (twoArmBipartiteTargetUnionCoverage
            left (fun _ : Fin 1 ↦ rightEdge) : ℝ) := by
    calc
      _ = categoricalProductPMF
            (pointPrior leftEdge : Fin (programCount * targetCount) → ℝ) left *
          (∑ right : Fin 1 → Fin (programCount * targetCount),
            categoricalProductPMF
                (pointPrior rightEdge : Fin (programCount * targetCount) → ℝ) right *
              (twoArmBipartiteTargetUnionCoverage left right : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro right _hright
            ring
      _ = _ := by
        rw [oneDrawExpectation_pointPrior]
  simp_rw [hright]
  exact oneDrawExpectation_pointPrior leftEdge
    (fun left ↦ (twoArmBipartiteTargetUnionCoverage
      left (fun _ : Fin 1 ↦ rightEdge) : ℝ))

def edge00 : Fin (2 * 2) := finProdFinEquiv (0, 0)
def edge11 : Fin (2 * 2) := finProdFinEquiv (1, 1)

def redundantArm : ProbSimplex (2 * 2) := pointPrior edge00
def complementaryArm : ProbSimplex (2 * 2) := pointPrior edge11

theorem equal_standalone_target_yield_fixture :
    iidExpectedBipartiteTargetCoverage redundantArm 1 = 1 ∧
      iidExpectedBipartiteTargetCoverage complementaryArm 1 = 1 := by
  constructor
  · unfold iidExpectedBipartiteTargetCoverage redundantArm
    rw [oneDrawExpectation_pointPrior]
    norm_num [bipartiteTargetCoverage, wordCoversBipartiteTarget,
      edgeTarget, decodeEdge, edge00, finProdFinEquiv]
  · unfold iidExpectedBipartiteTargetCoverage complementaryArm
    rw [oneDrawExpectation_pointPrior]
    norm_num [bipartiteTargetCoverage, wordCoversBipartiteTarget,
      edgeTarget, decodeEdge, edge11, finProdFinEquiv]

theorem redundant_portfolio_target_union_fixture :
    twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 redundantArm 1 = 1 := by
  unfold redundantArm
  rw [twoArmExpectedBipartiteTargetUnionCoverage_pointPriors]
  norm_num [
    twoArmBipartiteTargetUnionCoverage, wordCoversBipartiteTarget,
    redundantArm, edgeTarget, decodeEdge, edge00, finProdFinEquiv]

theorem complementary_portfolio_target_union_fixture :
    twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 complementaryArm 1 = 2 := by
  unfold redundantArm complementaryArm
  rw [twoArmExpectedBipartiteTargetUnionCoverage_pointPriors]
  have hzero :
      wordCoversBipartiteTarget (fun _ : Fin 1 ↦ edge00) (0 : Fin 2) ∨
        wordCoversBipartiteTarget (fun _ : Fin 1 ↦ edge11) (0 : Fin 2) := by
    left
    exact ⟨0, rfl⟩
  have hone :
      wordCoversBipartiteTarget (fun _ : Fin 1 ↦ edge00) (1 : Fin 2) ∨
        wordCoversBipartiteTarget (fun _ : Fin 1 ↦ edge11) (1 : Fin 2) := by
    right
    exact ⟨0, rfl⟩
  unfold twoArmBipartiteTargetUnionCoverage
  rw [Fin.sum_univ_two]
  simp [hzero, hone]

/-- Equal standalone target yield does not determine portfolio value: a
second arm concentrated on a new target strictly dominates a redundant arm. -/
theorem equal_standalone_different_portfolio_value :
    iidExpectedBipartiteTargetCoverage redundantArm 1 =
        iidExpectedBipartiteTargetCoverage complementaryArm 1 ∧
      twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 redundantArm 1 <
        twoArmExpectedBipartiteTargetUnionCoverage redundantArm 1 complementaryArm 1 := by
  constructor
  · exact equal_standalone_target_yield_fixture.1.trans
      equal_standalone_target_yield_fixture.2.symm
  · rw [redundant_portfolio_target_union_fixture,
      complementary_portfolio_target_union_fixture]
    norm_num

#print axioms iidExpectedBipartiteTargetCoverage_eq_sum_one_sub_pow
#print axioms iidExpectedProgramWitnessCoverage_eq_sum_one_sub_pow
#print axioms expectedBipartiteTargetMarginal_antitone
#print axioms equal_standalone_different_portfolio_value

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
