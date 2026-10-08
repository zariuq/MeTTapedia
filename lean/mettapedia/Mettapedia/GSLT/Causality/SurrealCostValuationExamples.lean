import Mettapedia.GSLT.Causality.SurrealCostValuation
import Mathlib.Order.WellFounded

/-!
# Budget and scheduling controls for the surreal cost reading

Two independent events have the same site-charged cost under either ordering.
A state-sensitive charge on the same events admits one schedule under a budget
of two and rejects the other. The numerical embedding retains that difference.
The infinite positive halving ladder refutes well-foundedness of numeric order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.SurrealCostValuationExamples

open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.Mazurkiewicz
open Mettapedia.GSLT.Causality.TraceCostValuation
open Mettapedia.GSLT.Causality.SurrealCostValuation
open Mettapedia.SetTheory.SignExpansion.Surreal

def halfWork : OccurrenceValuation gridPresentation SurrealCostValuation.Dyadic :=
  siteCostValuation gridPresentation (fun _ => Mettapedia.Algebra.Order.Dyadic.ofPair 1 1)

theorem halfWork_totals :
    halfWork.onPath gridTile.path = 1 ∧ halfWork.onPath gridTile.pathSwap' = 1 := by
  constructor <;> decide +kernel

theorem halfWork_schedule_invariant : Descends gridIndep (read halfWork) :=
  (descends_iff gridIndep halfWork).mpr (siteCostValuation_descends gridIndep _)

theorem halfWork_budget :
    (read halfWork).onPath gridTile.path ≤ toSurreal 1 ∧
      (read halfWork).onPath gridTile.pathSwap' ≤ toSurreal 1 := by
  constructor
  · exact (budget_iff halfWork _ _).mpr (le_of_eq halfWork_totals.1)
  · exact (budget_iff halfWork _ _).mpr (le_of_eq halfWork_totals.2)

def stateCost : OccurrenceValuation gridPresentation SurrealCostValuation.Dyadic where
  grade occurrence := (gridStateCost.grade occurrence : SurrealCostValuation.Dyadic)

theorem stateCost_totals :
    stateCost.onPath gridTile.path = 2 ∧ stateCost.onPath gridTile.pathSwap' = 6 := by
  constructor <;> decide +kernel

theorem stateCost_budget_separates :
    (read stateCost).onPath gridTile.path ≤ toSurreal 2 ∧
      ¬ (read stateCost).onPath gridTile.pathSwap' ≤ toSurreal 2 := by
  constructor
  · exact (budget_iff stateCost _ _).mpr (le_of_eq stateCost_totals.1)
  · rw [budget_iff, stateCost_totals.2]
    decide +kernel

theorem stateCost_not_descends : ¬ Descends gridIndep (read stateCost) := by
  intro descends
  have same := (cost_equal_iff stateCost gridTile.path gridTile.pathSwap').mp
    (descends gridTile.path gridTile.pathSwap' (.swap gridTile))
  rw [stateCost_totals.1, stateCost_totals.2] at same
  exact (by decide +kernel : (2 : SurrealCostValuation.Dyadic) ≠ 6) same

theorem positive_decreasing_ladder (n : Nat) :
    0 < ladder n ∧ ladder (n + 1) < ladder n := ⟨ladder_pos n, ladder_anti n⟩

theorem nonnegative_numeric_order_not_wellFounded :
    ¬ WellFounded (fun x y : {x : Surreal // 0 ≤ x} => x.1 < y.1) := by
  let sequence (n : Nat) : {x : Surreal // 0 ≤ x} := ⟨ladder n, (ladder_pos n).le⟩
  intro wellFounded
  have bad : ¬ Acc (fun x y : {x : Surreal // 0 ≤ x} => x.1 < y.1) (sequence 0) :=
    not_acc_iff_exists_descending_chain.mpr ⟨sequence, rfl, ladder_anti⟩
  exact bad (wellFounded.apply (sequence 0))

end Mettapedia.GSLT.Causality.SurrealCostValuationExamples
