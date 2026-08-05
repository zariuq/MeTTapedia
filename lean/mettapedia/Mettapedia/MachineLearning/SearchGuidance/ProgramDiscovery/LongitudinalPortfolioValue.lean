import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CostAwareOpportunityControl
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.FinitePrefixIndistinguishability

/-!
# Longitudinal portfolio value and delayed yield

Cost-aware marginal-union accounting summed over a finite generation horizon,
with a two-world example: identical first-generation evidence, opposite
correct horizon decisions.  By the finite-prefix impossibility lemma, no
decision rule observing only the first generation is correct in both worlds.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

namespace AdaptivePortfolio

universe uG uA uT

section LongitudinalValue

variable {Generation : Type uG} {Arm : Type uA} {Target : Type uT}
variable [DecidableEq Target]

/-- Sum an arm's cost-aware marginal verified value over a finite registered
generation horizon, relative to the same declared base portfolio. -/
def longitudinalMarginalNetValue
    (model : PortfolioModel Generation Arm Target)
    (generations : Finset Generation)
    (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) : ℤ :=
  ∑ generation ∈ generations,
    marginalNetValue model generation targetValue cost selected arm

@[simp]
theorem longitudinalMarginalNetValue_empty
    (model : PortfolioModel Generation Arm Target)
    (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) :
    longitudinalMarginalNetValue model ∅ targetValue cost selected arm = 0 := by
  simp [longitudinalMarginalNetValue]

@[simp]
theorem longitudinalMarginalNetValue_singleton
    [DecidableEq Generation]
    (model : PortfolioModel Generation Arm Target)
    (generation : Generation)
    (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) :
    longitudinalMarginalNetValue model {generation}
        targetValue cost selected arm =
      marginalNetValue model generation targetValue cost selected arm := by
  simp [longitudinalMarginalNetValue]

theorem longitudinalMarginalNetValue_insert
    [DecidableEq Generation]
    (model : PortfolioModel Generation Arm Target)
    (generations : Finset Generation) (generation : Generation)
    (generationFresh : generation ∉ generations)
    (targetValue : ℕ) (cost : Arm → ℕ)
    (selected : Finset Arm) (arm : Arm) :
    longitudinalMarginalNetValue model (insert generation generations)
        targetValue cost selected arm =
      marginalNetValue model generation targetValue cost selected arm +
        longitudinalMarginalNetValue model generations
          targetValue cost selected arm := by
  simp [longitudinalMarginalNetValue, generationFresh]

end LongitudinalValue

/-! ## Executable two-generation boundary -/

namespace DelayedYieldExample

inductive Generation where
  | first | second
  deriving DecidableEq, Fintype, Repr

inductive Arm where
  | primaryBP | opportunityBP | pc
  deriving DecidableEq, Fintype, Repr

inductive World where
  | compounding | fading
  deriving DecidableEq, Fintype, Repr

open Generation Arm World

/-- Both worlds have identical first-generation evidence.  In the second
generation, the compounding world rewards the PC arm while the fading world
does not. -/
def accepted : World → Generation → Arm → Finset (Fin 9)
  | _, .first, .primaryBP => {0, 1, 2}
  | _, .first, .opportunityBP => {0, 1, 2, 3, 4}
  | _, .first, .pc => {0, 1, 2, 5}
  | .compounding, .second, .primaryBP => {0, 1, 2}
  | .compounding, .second, .opportunityBP => {0, 1, 2, 3}
  | .compounding, .second, .pc => {0, 1, 2, 5, 6, 7, 8}
  | .fading, .second, .primaryBP => {0, 1, 2}
  | .fading, .second, .opportunityBP => {0, 1, 2, 3, 4}
  | .fading, .second, .pc => {0, 1, 2}

def model (world : World) : PortfolioModel Generation Arm (Fin 9) where
  arms := Finset.univ
  accepted := accepted world
  armBudget := 2
  primaryBP := .primaryBP
  opportunityBP := .opportunityBP
  primaryBP_mem := Finset.mem_univ _
  opportunityBP_mem := Finset.mem_univ _
  bpArms_distinct := by decide

def equalCost (_arm : Arm) : ℕ := 1

def basePortfolio : Finset Arm := {.primaryBP}

def firstObservation (world : World) : Arm → Finset (Fin 9) :=
  accepted world .first

def horizon : Finset Generation := Finset.univ

def horizonValue (world : World) (arm : Arm) : ℤ :=
  longitudinalMarginalNetValue (model world) horizon 1 equalCost
    basePortfolio arm

def pcWinsHorizon (world : World) : Prop :=
  horizonValue world .opportunityBP < horizonValue world .pc

theorem firstObservations_identical :
    firstObservation .compounding = firstObservation .fading := by
  funext arm
  cases arm <;> rfl

theorem first_pc_value :
    marginalNetValue (model .compounding) .first 1 equalCost
        basePortfolio .pc = 0 := by
  decide

theorem first_opportunity_value :
    marginalNetValue (model .compounding) .first 1 equalCost
        basePortfolio .opportunityBP = 1 := by
  decide

theorem fading_first_pc_value :
    marginalNetValue (model .fading) .first 1 equalCost
        basePortfolio .pc = 0 := by
  decide

theorem fading_first_opportunity_value :
    marginalNetValue (model .fading) .first 1 equalCost
        basePortfolio .opportunityBP = 1 := by
  decide

theorem compounding_pc_horizon_value :
    horizonValue .compounding .pc = 3 := by
  decide

theorem compounding_opportunity_horizon_value :
    horizonValue .compounding .opportunityBP = 1 := by
  decide

theorem fading_pc_horizon_value :
    horizonValue .fading .pc = -1 := by
  decide

theorem fading_opportunity_horizon_value :
    horizonValue .fading .opportunityBP = 2 := by
  decide

/-- Positive boundary: PC loses the first generation but wins the registered
two-generation horizon after delayed exclusive yield arrives. -/
theorem compounding_firstValue_lt_and_horizonValue_gt :
    marginalNetValue (model .compounding) .first 1 equalCost
        basePortfolio .pc <
      marginalNetValue (model .compounding) .first 1 equalCost
        basePortfolio .opportunityBP ∧
      pcWinsHorizon .compounding := by
  rw [first_pc_value, first_opportunity_value]
  constructor
  · norm_num
  · rw [pcWinsHorizon, compounding_pc_horizon_value,
      compounding_opportunity_horizon_value]
    norm_num

/-- Negative boundary: when delayed exclusive yield does not arrive, the same
exploratory runway loses to the independent-BP opportunity control. -/
theorem fading_firstValue_lt_and_horizonValue_lt :
    marginalNetValue (model .fading) .first 1 equalCost
        basePortfolio .pc <
      marginalNetValue (model .fading) .first 1 equalCost
        basePortfolio .opportunityBP ∧
      ¬ pcWinsHorizon .fading := by
  rw [fading_first_pc_value, fading_first_opportunity_value]
  constructor
  · norm_num
  · rw [pcWinsHorizon, fading_pc_horizon_value,
      fading_opportunity_horizon_value]
    norm_num

/-- The two worlds are observationally indistinguishable after generation
one, yet their correct horizon-promotion decisions are opposite. -/
theorem not_correct_on_both_worlds
    (decision : (Arm → Finset (Fin 9)) → Bool) :
    ¬ ((decision (firstObservation .compounding) = true ↔
          pcWinsHorizon .compounding) ∧
        (decision (firstObservation .fading) = true ↔
          pcWinsHorizon .fading)) := by
  exact no_observationOnly_rule_correct_on_opposite_worlds
    firstObservation pcWinsHorizon
    firstObservations_identical
    compounding_firstValue_lt_and_horizonValue_gt.2
    fading_firstValue_lt_and_horizonValue_lt.2
    decision

end DelayedYieldExample


#print axioms longitudinalMarginalNetValue_insert
#print axioms DelayedYieldExample.firstObservations_identical
#print axioms DelayedYieldExample.compounding_firstValue_lt_and_horizonValue_gt
#print axioms DelayedYieldExample.fading_firstValue_lt_and_horizonValue_lt
#print axioms DelayedYieldExample.not_correct_on_both_worlds

end AdaptivePortfolio

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
