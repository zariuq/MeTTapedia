import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SubmodularCoverageGreedy

/-!
# Cost-aware opportunity controls for verified search portfolios

Standalone yield is not the value of adding an arm to a search portfolio.
The relevant quantity is its checker-accepted marginal coverage, valued in
common units, minus its measured compute cost.  This module makes that
comparison exact and treats an independent backpropagation arm as an explicit
opportunity control.

Costs and target values are natural telemetry units.  Net values live in
`ℤ`, so an arm whose verified marginal does not repay its cost is represented
without truncated subtraction.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio

universe uG uA uT

section NetValue

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Arm] [DecidableEq Target]

/-- Net value of an entire selected portfolio: common value per newly covered
target times verified union coverage, minus measured arm cost. -/
def portfolioNetValue
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) : ℤ :=
  (targetValue : ℤ) *
      (verifiedUnionCoverage model generation selected : ℤ) -
    (portfolioCost cost selected : ℤ)

/-- Incremental net value of adding one arm to the current portfolio. -/
def marginalNetValue
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) : ℤ :=
  (targetValue : ℤ) *
      (marginalCoverage model generation selected arm : ℤ) -
    (cost arm : ℤ)

theorem portfolioCost_insert_of_not_mem
    (cost : Arm → ℕ) (selected : Finset Arm) (arm : Arm)
    (hnot : arm ∉ selected) :
    portfolioCost cost (insert arm selected) =
      portfolioCost cost selected + cost arm := by
  simp [portfolioCost, hnot, Nat.add_comm]

/-- Exact insertion law.  This is the bridge from set-valued verified coverage
to an experiment-allocation decision: no independence or distributional
assumption is used. -/
theorem portfolioNetValue_insert_eq_add_marginalNetValue
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) (hnot : arm ∉ selected) :
    portfolioNetValue model generation targetValue cost (insert arm selected) =
      portfolioNetValue model generation targetValue cost selected +
        marginalNetValue model generation targetValue cost selected arm := by
  unfold portfolioNetValue marginalNetValue
  rw [verifiedUnionCoverage_insert_eq_add_marginalCoverage,
    portfolioCost_insert_of_not_mem cost selected arm hnot]
  push_cast
  ring

/-- Comparing two fresh arms after the same portfolio is exactly comparison of
their marginal net values.  In particular, the opportunity control cannot be
credited to the candidate arm. -/
theorem insert_candidate_gt_insert_opportunity_iff
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (candidate : Arm)
    (hcandidate : candidate ∉ selected)
    (hopportunity : model.opportunityBP ∉ selected) :
    portfolioNetValue model generation targetValue cost
        (insert model.opportunityBP selected) <
      portfolioNetValue model generation targetValue cost
        (insert candidate selected) ↔
      marginalNetValue model generation targetValue cost selected
          model.opportunityBP <
        marginalNetValue model generation targetValue cost selected candidate := by
  rw [portfolioNetValue_insert_eq_add_marginalNetValue
      model generation targetValue cost selected candidate hcandidate,
    portfolioNetValue_insert_eq_add_marginalNetValue
      model generation targetValue cost selected model.opportunityBP hopportunity]
  omega

omit [DecidableEq Arm] in
/-- A candidate with no more verified marginal coverage and no lower cost than
the independent-BP opportunity control cannot have greater marginal net
value. -/
theorem marginalNetValue_le_opportunity_of_dominated
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation) (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (candidate : Arm)
    (hcoverage :
      marginalCoverage model generation selected candidate ≤
        marginalCoverage model generation selected model.opportunityBP)
    (hcost : cost model.opportunityBP ≤ cost candidate) :
    marginalNetValue model generation targetValue cost selected candidate ≤
      marginalNetValue model generation targetValue cost selected
        model.opportunityBP := by
  have hcoverageInt :
      (marginalCoverage model generation selected candidate : ℤ) ≤
        (marginalCoverage model generation selected model.opportunityBP : ℤ) := by
    exact_mod_cast hcoverage
  have hcostInt :
      (cost model.opportunityBP : ℤ) ≤ (cost candidate : ℤ) := by
    exact_mod_cast hcost
  have hscaled :
      (targetValue : ℤ) *
          (marginalCoverage model generation selected candidate : ℤ) ≤
        (targetValue : ℤ) *
          (marginalCoverage model generation selected model.opportunityBP : ℤ) :=
    mul_le_mul_of_nonneg_left hcoverageInt (by positivity)
  unfold marginalNetValue
  omega

end NetValue

/-! ## Positive and negative executable boundaries -/

namespace OpportunityFixture

inductive Arm where
  | primaryBP | opportunityBP | pc
  deriving DecidableEq, Fintype, Repr

open Arm

def accepted : Unit → Arm → Finset (Fin 10)
  | (), .primaryBP => {0, 1, 2, 3, 4, 5}
  | (), .opportunityBP => {0, 1, 2, 3, 4, 5, 6}
  | (), .pc => {0, 1, 7, 8}

def model : PortfolioModel Unit Arm (Fin 10) where
  arms := Finset.univ
  accepted := accepted
  armBudget := 2
  primaryBP := .primaryBP
  opportunityBP := .opportunityBP
  primaryBP_mem := Finset.mem_univ _
  opportunityBP_mem := Finset.mem_univ _
  bpArms_distinct := by decide

def equalCost (_arm : Arm) : ℕ := 1

def expensivePC : Arm → ℕ
  | .pc => 3
  | _ => 1

/-- Positive boundary: the PC arm has lower standalone coverage, but its two
exclusive targets beat the opportunity BP arm's one exclusive target at equal
cost. -/
theorem lower_standalone_pc_can_have_greater_net_value :
    (model.accepted () .pc).card <
        (model.accepted () .opportunityBP).card ∧
      marginalCoverage model () {.primaryBP} .opportunityBP = 1 ∧
      marginalCoverage model () {.primaryBP} .pc = 2 ∧
      marginalNetValue model () 1 equalCost {.primaryBP} .opportunityBP <
        marginalNetValue model () 1 equalCost {.primaryBP} .pc := by
  decide

/-- Negative boundary: exclusivity alone is insufficient.  With the same
accepted sets, a sufficiently expensive PC arm loses to the opportunity
control even though it contributes more new targets. -/
theorem excess_cost_can_reverse_exclusivity_preference :
    marginalCoverage model () {.primaryBP} .opportunityBP <
        marginalCoverage model () {.primaryBP} .pc ∧
      marginalNetValue model () 1 expensivePC {.primaryBP} .pc <
        marginalNetValue model () 1 expensivePC {.primaryBP} .opportunityBP := by
  decide

end OpportunityFixture

#print axioms portfolioNetValue_insert_eq_add_marginalNetValue
#print axioms insert_candidate_gt_insert_opportunity_iff
#print axioms marginalNetValue_le_opportunity_of_dominated
#print axioms OpportunityFixture.lower_standalone_pc_can_have_greater_net_value
#print axioms OpportunityFixture.excess_cost_can_reverse_exclusivity_preference

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio
