import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls

/-!
# Shared coefficient merge controls

Shared prefixes are charged once. Fresh equal-valued factors are not
deduplicated. Conflicting values, dependencies and occurrence orders are
refused, while semantic zero is retained. Matrix coefficients demonstrate
why a worker's completion order cannot choose the logical factor order.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SharedCoefficientLedgerControls

open SharedCoefficientLedger

def factor (identity coefficient : Nat) (dependency : Nat := 0) : Factor Nat Nat Nat :=
  ⟨identity, dependency, coefficient⟩

def inherited : Ledger Nat Nat Nat := [factor 1 2]
def leftBranch : Ledger Nat Nat Nat := inherited ++ [factor 2 3]
def rightBranch : Ledger Nat Nat Nat := inherited ++ [factor 3 4]
def joined : Ledger Nat Nat Nat := [factor 1 2, factor 2 3, factor 3 4]

theorem shared_prefix_charged_once : merge? leftBranch rightBranch = some joined := by
  decide +kernel

theorem joined_coefficient : denote joined = 24 := by decide +kernel

/-- Multiplying the complete branch coefficients charges inherited work twice. -/
theorem multiplying_whole_branches_is_wrong :
    denote leftBranch * denote rightBranch = 48 ∧
      denote leftBranch * denote rightBranch ≠ denote joined := by decide +kernel

theorem equal_values_are_distinct_factors :
    merge? [factor 1 3] [factor 2 3] = some [factor 1 3, factor 2 3] ∧
      denote [factor 1 3, factor 2 3] = 9 := by decide +kernel

theorem conflicting_coefficient_refused : merge? [factor 1 2] [factor 1 5] = none := by
  decide +kernel

theorem conflicting_dependency_refused :
    merge? [factor 1 2 17] [factor 1 2 18] = none := by decide +kernel

theorem incompatible_order_refused :
    merge? [factor 1 2, factor 2 3] [factor 2 3, factor 1 2] = none := by decide +kernel

theorem refusal_preserves_destination :
    commitMerge [factor 1 2] [factor 1 5] = ([factor 1 2], false) :=
  refused_merge_retains_state _ _ conflicting_coefficient_refused

theorem repeated_append_refused : append? [factor 1 3] (factor 1 3) = none := by decide +kernel

theorem zero_append_retained : append? [factor 1 3] (factor 2 0) =
    some [factor 1 3, factor 2 0] := by decide +kernel

open Mettapedia.GSLT.Dynamics.WeightedResumptionControls

def matrixFactor (identity : Nat) (coefficient : TwoByTwo) : Factor Nat Nat TwoByTwo :=
  ⟨identity, 0, coefficient⟩

def logicalMatrixOrder : Ledger Nat Nat TwoByTwo :=
  [matrixFactor 1 upper, matrixFactor 2 lower]

def completionMatrixOrder : Ledger Nat Nat TwoByTwo :=
  [matrixFactor 2 lower, matrixFactor 1 upper]

/-- Equal sets of factors are insufficient for ordered coefficient composition. -/
theorem completion_order_changes_denotation :
    denote logicalMatrixOrder ≠ denote completionMatrixOrder := by
  simp only [denote, logicalMatrixOrder, completionMatrixOrder, List.map_cons,
    List.map_nil, matrixFactor, List.prod_cons, List.prod_nil, mul_one]
  exact matrix_composition_is_ordered

end Mettapedia.Algebra.SharedCoefficientLedgerControls
