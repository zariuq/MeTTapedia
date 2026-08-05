import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
import Mathlib.Tactic

/-!
# Greedy guarantees for verified-union portfolios

Krause and Golovin's survey, *Submodular Function Maximization* (2014),
Theorem 3.5, derives the finite greedy recurrence behind the classical
cardinality-constrained coverage guarantee.  The same chapter also warns that
cost-benefit greedy alone can be arbitrarily bad for budgeted maximization.

This file specializes those two facts to checker-accepted program-discovery
portfolios.  The positive theorem retains the sharper finite factor
`1 - ((k - 1) / k) ^ rounds`; no asymptotic exponential relaxation is needed.
The negative family is genuine set coverage, not an abstract objective.

Primary source DOI: `10.1017/CBO9781139177801.004`.
Primary source artifact SHA-256:
`93dfd854e959acb6e62fb1de414d2bca30c21c1f82f56aac867b4ffc094913d9`.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio

universe uG uA uT

section ExactCoverage

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Arm] [DecidableEq Target]

theorem coveredTargets_insert
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) (arm : Arm) :
    coveredTargets model generation (insert arm selected) =
      model.accepted generation arm ∪
        coveredTargets model generation selected := by
  simp [coveredTargets]

omit [DecidableEq Arm] in
@[simp] theorem verifiedUnionCoverage_empty
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) :
    verifiedUnionCoverage model generation ∅ = 0 := by
  simp [verifiedUnionCoverage, coveredTargets]

/-- Adding one arm increases verified union coverage by exactly its targets
that were not already covered. -/
theorem verifiedUnionCoverage_insert_eq_add_marginalCoverage
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) (arm : Arm) :
    verifiedUnionCoverage model generation (insert arm selected) =
      verifiedUnionCoverage model generation selected +
        marginalCoverage model generation selected arm := by
  have hcard := Finset.card_sdiff_add_card
    (model.accepted generation arm)
    (coveredTargets model generation selected)
  unfold verifiedUnionCoverage
  rw [coveredTargets_insert]
  unfold marginalCoverage marginalTargets
  omega

omit [DecidableEq Arm] in
theorem marginalCoverage_eq_zero_of_mem
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm) {arm : Arm}
    (harm : arm ∈ selected) :
    marginalCoverage model generation selected arm = 0 := by
  have hsubset :
      model.accepted generation arm ⊆
        coveredTargets model generation selected :=
    accepted_subset_covered_of_mem model generation harm
  rw [marginalCoverage, marginalTargets,
    Finset.sdiff_eq_empty_iff_subset.mpr hsubset]
  simp

omit [DecidableEq Arm] in
/-- Every target of a comparator that is missing from the current portfolio
belongs to the current marginal set of at least one comparator arm. -/
theorem uncoveredComparator_subset_biUnion_marginalTargets
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm) :
    coveredTargets model generation comparator \
        coveredTargets model generation selected ⊆
      comparator.biUnion
        (marginalTargets model generation selected) := by
  intro target htarget
  rcases Finset.mem_sdiff.mp htarget with ⟨hcomparator, hnotSelected⟩
  rcases Finset.mem_biUnion.mp hcomparator with
    ⟨arm, harm, haccepted⟩
  exact Finset.mem_biUnion.mpr
    ⟨arm, harm, Finset.mem_sdiff.mpr ⟨haccepted, hnotSelected⟩⟩

omit [DecidableEq Arm] in
/-- Source equations (3.3)--(3.5), specialized to verified set coverage:
comparator coverage is at most current coverage plus the sum of its arms'
current marginal gains. -/
theorem comparatorCoverage_le_current_add_sum_marginals
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm) :
    verifiedUnionCoverage model generation comparator ≤
      verifiedUnionCoverage model generation selected +
        ∑ arm ∈ comparator,
          marginalCoverage model generation selected arm := by
  let comparatorTargets := coveredTargets model generation comparator
  let selectedTargets := coveredTargets model generation selected
  let marginalUnion := comparator.biUnion
    (marginalTargets model generation selected)
  have hsplit :
      comparatorTargets.card ≤
        (comparatorTargets \ selectedTargets).card +
          selectedTargets.card :=
    Finset.card_le_card_sdiff_add_card
  have hsubset :
      comparatorTargets \ selectedTargets ⊆ marginalUnion := by
    exact uncoveredComparator_subset_biUnion_marginalTargets
      model generation selected comparator
  have hmarginal :
      (comparatorTargets \ selectedTargets).card ≤
        ∑ arm ∈ comparator,
          marginalCoverage model generation selected arm := by
    calc
      (comparatorTargets \ selectedTargets).card
          ≤ marginalUnion.card := Finset.card_le_card hsubset
      _ ≤ ∑ arm ∈ comparator,
          (marginalTargets model generation selected arm).card :=
        Finset.card_biUnion_le
      _ = ∑ arm ∈ comparator,
          marginalCoverage model generation selected arm := by
        simp [marginalCoverage]
  change comparatorTargets.card ≤
    selectedTargets.card +
      ∑ arm ∈ comparator,
        marginalCoverage model generation selected arm
  omega

theorem feasibleArm_marginalCoverage_le_greedy
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm)
    (chosen arm : Arm)
    (hgreedy : IsMarginalGreedyStep model generation selected chosen)
    (hcomparator : Feasible model comparator)
    (harm : arm ∈ comparator) :
    marginalCoverage model generation selected arm ≤
      marginalCoverage model generation selected chosen := by
  by_cases hselected : arm ∈ selected
  · rw [marginalCoverage_eq_zero_of_mem
      model generation selected hselected]
    exact Nat.zero_le _
  · exact hgreedy.2 arm
      (Finset.mem_sdiff.mpr ⟨hcomparator.1 harm, hselected⟩)

/-- Source equations (3.6)--(3.8): one exact marginal-greedy step closes at
least one `armBudget`-th of the current gap to every feasible comparator. -/
theorem comparatorCoverage_le_current_add_budget_mul_greedyMarginal
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm)
    (chosen : Arm)
    (hgreedy : IsMarginalGreedyStep model generation selected chosen)
    (hcomparator : Feasible model comparator) :
    verifiedUnionCoverage model generation comparator ≤
      verifiedUnionCoverage model generation selected +
        model.armBudget *
          marginalCoverage model generation selected chosen := by
  have hsum :
      (∑ arm ∈ comparator,
          marginalCoverage model generation selected arm) ≤
        ∑ _arm ∈ comparator,
          marginalCoverage model generation selected chosen := by
    exact Finset.sum_le_sum fun arm harm ↦
      feasibleArm_marginalCoverage_le_greedy
        model generation selected comparator chosen arm
        hgreedy hcomparator harm
  have hcard :
      comparator.card *
          marginalCoverage model generation selected chosen ≤
        model.armBudget *
          marginalCoverage model generation selected chosen :=
    Nat.mul_le_mul_right
      (marginalCoverage model generation selected chosen)
      hcomparator.2
  have hsource :=
    comparatorCoverage_le_current_add_sum_marginals
      model generation selected comparator
  calc
    verifiedUnionCoverage model generation comparator
        ≤ verifiedUnionCoverage model generation selected +
            ∑ arm ∈ comparator,
              marginalCoverage model generation selected arm := hsource
    _ ≤ verifiedUnionCoverage model generation selected +
          ∑ _arm ∈ comparator,
            marginalCoverage model generation selected chosen :=
      Nat.add_le_add_left hsum _
    _ = verifiedUnionCoverage model generation selected +
          comparator.card *
            marginalCoverage model generation selected chosen := by
      simp
    _ ≤ verifiedUnionCoverage model generation selected +
          model.armBudget *
            marginalCoverage model generation selected chosen :=
      Nat.add_le_add_left hcard _

/-- Exact one-step gap recurrence over the reals. -/
theorem greedyStep_gap_mul_budget_le
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm)
    (chosen : Arm)
    (hgreedy : IsMarginalGreedyStep model generation selected chosen)
    (hcomparator : Feasible model comparator) :
    (model.armBudget : ℝ) *
        ((verifiedUnionCoverage model generation comparator : ℝ) -
          (verifiedUnionCoverage model generation
            (insert chosen selected) : ℝ)) ≤
      ((model.armBudget : ℝ) - 1) *
        ((verifiedUnionCoverage model generation comparator : ℝ) -
          (verifiedUnionCoverage model generation selected : ℝ)) := by
  have hsource :=
    comparatorCoverage_le_current_add_budget_mul_greedyMarginal
      model generation selected comparator chosen hgreedy hcomparator
  have hinsert :=
    verifiedUnionCoverage_insert_eq_add_marginalCoverage
      model generation selected chosen
  have hsourceReal :
      (verifiedUnionCoverage model generation comparator : ℝ) ≤
        (verifiedUnionCoverage model generation selected : ℝ) +
          (model.armBudget : ℝ) *
            (marginalCoverage model generation selected chosen : ℝ) := by
    exact_mod_cast hsource
  have hinsertReal :
      (verifiedUnionCoverage model generation
          (insert chosen selected) : ℝ) =
        (verifiedUnionCoverage model generation selected : ℝ) +
          (marginalCoverage model generation selected chosen : ℝ) := by
    exact_mod_cast hinsert
  rw [hinsertReal]
  nlinarith

theorem greedyStep_gap_le_factor
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected comparator : Finset Arm)
    (chosen : Arm)
    (hbudget : 0 < model.armBudget)
    (hgreedy : IsMarginalGreedyStep model generation selected chosen)
    (hcomparator : Feasible model comparator) :
    (verifiedUnionCoverage model generation comparator : ℝ) -
        (verifiedUnionCoverage model generation
          (insert chosen selected) : ℝ) ≤
      (((model.armBudget : ℝ) - 1) / model.armBudget) *
        ((verifiedUnionCoverage model generation comparator : ℝ) -
          (verifiedUnionCoverage model generation selected : ℝ)) := by
  have hbudgetReal : (0 : ℝ) < model.armBudget := by
    exact_mod_cast hbudget
  have hgap :=
    greedyStep_gap_mul_budget_le
      model generation selected comparator chosen hgreedy hcomparator
  calc
    (verifiedUnionCoverage model generation comparator : ℝ) -
          (verifiedUnionCoverage model generation
            (insert chosen selected) : ℝ)
        ≤ (((model.armBudget : ℝ) - 1) *
            ((verifiedUnionCoverage model generation comparator : ℝ) -
              (verifiedUnionCoverage model generation selected : ℝ))) /
            model.armBudget := by
          apply (le_div_iff₀ hbudgetReal).2
          nlinarith
    _ = (((model.armBudget : ℝ) - 1) / model.armBudget) *
          ((verifiedUnionCoverage model generation comparator : ℝ) -
            (verifiedUnionCoverage model generation selected : ℝ)) := by
      ring

/-! ## Finite exact greedy trace -/

def greedyPrefix (chosen : ℕ → Arm) : ℕ → Finset Arm
  | 0 => ∅
  | step + 1 => insert (chosen step) (greedyPrefix chosen step)

def IsMarginalGreedyRun
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (chosen : ℕ → Arm) : Prop :=
  ∀ step,
    IsMarginalGreedyStep model generation
      (greedyPrefix chosen step) (chosen step)

/-- Exact finite form of the Nemhauser--Wolsey--Fisher greedy recurrence.
It compares any number of greedy rounds with every feasible portfolio, not
only with a chosen optimizer witness. -/
theorem greedyPrefix_gap_le_geometric
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (chosen : ℕ → Arm)
    (comparator : Finset Arm)
    (hbudget : 0 < model.armBudget)
    (hrun : IsMarginalGreedyRun model generation chosen)
    (hcomparator : Feasible model comparator)
    (rounds : ℕ) :
    (verifiedUnionCoverage model generation comparator : ℝ) -
        (verifiedUnionCoverage model generation
          (greedyPrefix chosen rounds) : ℝ) ≤
      ((((model.armBudget : ℝ) - 1) / model.armBudget) ^ rounds) *
        (verifiedUnionCoverage model generation comparator : ℝ) := by
  let factor : ℝ :=
    ((model.armBudget : ℝ) - 1) / model.armBudget
  have hbudgetReal : (0 : ℝ) < model.armBudget := by
    exact_mod_cast hbudget
  have hone : (1 : ℝ) ≤ model.armBudget := by
    exact_mod_cast hbudget
  have hfactor : 0 ≤ factor := by
    exact div_nonneg (sub_nonneg.mpr hone) hbudgetReal.le
  induction rounds with
  | zero =>
      simp [greedyPrefix, verifiedUnionCoverage_empty]
  | succ rounds ih =>
      have hstep :=
        greedyStep_gap_le_factor
          model generation (greedyPrefix chosen rounds) comparator
          (chosen rounds) hbudget (hrun rounds) hcomparator
      calc
        (verifiedUnionCoverage model generation comparator : ℝ) -
              (verifiedUnionCoverage model generation
                (greedyPrefix chosen (rounds + 1)) : ℝ)
            ≤ factor *
                ((verifiedUnionCoverage model generation comparator : ℝ) -
                  (verifiedUnionCoverage model generation
                    (greedyPrefix chosen rounds) : ℝ)) := by
              simpa [greedyPrefix, factor] using hstep
        _ ≤ factor *
              (factor ^ rounds *
                (verifiedUnionCoverage model generation comparator : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hfactor
        _ = factor ^ (rounds + 1) *
              (verifiedUnionCoverage model generation comparator : ℝ) := by
          rw [pow_succ]
          ring

/-- The directly usable coverage form.  At `rounds = armBudget` this is the
usual finite predecessor of the `1 - 1/e` statement; retaining the exact
factor is stronger for small registered portfolios. -/
theorem greedyPrefix_coverage_ge_finiteFactor
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (chosen : ℕ → Arm)
    (comparator : Finset Arm)
    (hbudget : 0 < model.armBudget)
    (hrun : IsMarginalGreedyRun model generation chosen)
    (hcomparator : Feasible model comparator)
    (rounds : ℕ) :
    (1 - ((((model.armBudget : ℝ) - 1) / model.armBudget) ^ rounds)) *
        (verifiedUnionCoverage model generation comparator : ℝ) ≤
      (verifiedUnionCoverage model generation
        (greedyPrefix chosen rounds) : ℝ) := by
  have hgap :=
    greedyPrefix_gap_le_geometric
      model generation chosen comparator hbudget hrun hcomparator rounds
  linarith

end ExactCoverage

/-! ## Cost-aware promotion and its sharp boundary -/

section Cost

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Arm] [DecidableEq Target]

def portfolioCost (cost : Arm → ℕ) (portfolio : Finset Arm) : ℕ :=
  ∑ arm ∈ portfolio, cost arm

def CostFeasible (cost : Arm → ℕ) (budget : ℕ)
    (portfolio : Finset Arm) : Prop :=
  portfolioCost cost portfolio ≤ budget

/-- Cross-multiplied marginal-gain-per-cost comparison.  It is executable over
natural telemetry and avoids rounding a ratio. -/
def MarginalRateGE
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm)
    (cost : Arm → ℕ) (left right : Arm) : Prop :=
  marginalCoverage model generation selected right * cost left ≤
    marginalCoverage model generation selected left * cost right

omit [DecidableEq Arm] in
theorem marginalRateGE_iff_rat_div
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (selected : Finset Arm)
    (cost : Arm → ℕ) (left right : Arm)
    (hleft : 0 < cost left) (hright : 0 < cost right) :
    MarginalRateGE model generation selected cost left right ↔
      (marginalCoverage model generation selected right : ℚ) /
          cost right ≤
        (marginalCoverage model generation selected left : ℚ) /
          cost left := by
  have hleftRat : (0 : ℚ) < cost left := by exact_mod_cast hleft
  have hrightRat : (0 : ℚ) < cost right := by exact_mod_cast hright
  rw [div_le_div_iff₀ hrightRat hleftRat]
  exact_mod_cast
    (show marginalCoverage model generation selected right * cost left ≤
        marginalCoverage model generation selected left * cost right ↔
      marginalCoverage model generation selected right * cost left ≤
        marginalCoverage model generation selected left * cost right from
      Iff.rfl)

namespace DensityGreedyCounterexample

noncomputable def badModel (scale : ℕ) :
    PortfolioModel Unit (Fin 2) (Fin (2 * scale + 2)) where
  arms := Finset.univ
  accepted := fun _generation arm ↦
    if arm = 0 then {0, 1} else Finset.univ
  armBudget := 2
  primaryBP := 0
  opportunityBP := 1
  primaryBP_mem := Finset.mem_univ _
  opportunityBP_mem := Finset.mem_univ _
  bpArms_distinct := by decide

def badCost (scale : ℕ) (arm : Fin 2) : ℕ :=
  if arm = 0 then 1 else 2 * scale + 2

def badBudget (scale : ℕ) : ℕ := 2 * scale + 2

theorem small_coverage (scale : ℕ) :
    verifiedUnionCoverage (badModel scale) () {0} = 2 := by
  simp [badModel, verifiedUnionCoverage, coveredTargets]

theorem big_coverage (scale : ℕ) :
    verifiedUnionCoverage (badModel scale) () {1} = 2 * scale + 2 := by
  simp [badModel, verifiedUnionCoverage, coveredTargets]

theorem small_cost (scale : ℕ) :
    portfolioCost (badCost scale) {0} = 1 := by
  simp [portfolioCost, badCost]

theorem big_cost (scale : ℕ) :
    portfolioCost (badCost scale) {1} = badBudget scale := by
  simp [portfolioCost, badCost, badBudget]

theorem small_then_big_not_feasible (scale : ℕ) :
    ¬ CostFeasible (badCost scale) (badBudget scale) {0, 1} := by
  simp [CostFeasible, portfolioCost, badCost, badBudget]

/-- At the empty portfolio, the small arm has strictly larger gain per cost
than the full-coverage arm. -/
theorem small_strictly_better_density (scale : ℕ) :
    MarginalRateGE (badModel scale) () ∅ (badCost scale) 0 1 ∧
      ¬ MarginalRateGE (badModel scale) () ∅ (badCost scale) 1 0 := by
  simp [MarginalRateGE, marginalCoverage, marginalTargets, badModel,
    coveredTargets, badCost]

/-- Nevertheless the feasible full-coverage singleton beats the density
choice by an arbitrarily large multiplicative factor. -/
theorem densityGreedy_arbitrarily_bad (scale : ℕ) :
    scale * verifiedUnionCoverage (badModel scale) () {0} <
      verifiedUnionCoverage (badModel scale) () {1} := by
  rw [small_coverage, big_coverage]
  omega

end DensityGreedyCounterexample

end Cost

#print axioms verifiedUnionCoverage_insert_eq_add_marginalCoverage
#print axioms comparatorCoverage_le_current_add_budget_mul_greedyMarginal
#print axioms greedyPrefix_gap_le_geometric
#print axioms greedyPrefix_coverage_ge_finiteFactor
#print axioms marginalRateGE_iff_rat_div
#print axioms DensityGreedyCounterexample.densityGreedy_arbitrarily_bad

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
