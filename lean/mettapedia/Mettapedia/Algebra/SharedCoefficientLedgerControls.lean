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

/-! ## One renaming for the whole result -/

/-- A different allocation order may choose different names without changing
the inherited production, fresh suffixes or their ordered interpretation. -/
theorem common_renaming_preserves_join :
    merge? (rename (fun name => name + 10) id leftBranch)
        (rename (fun name => name + 10) id rightBranch) =
      some (rename (fun name => name + 10) id joined) := by
  rw [merge_rename (fun _ _ equal => Nat.add_right_cancel equal)
    Function.injective_id, shared_prefix_charged_once]
  rfl

/-- Each answer alone has the same coefficient. Independently renaming its
shared prefix nevertheless makes their future join charge the production twice. -/
theorem separate_renamings_hide_fractured_sharing :
    denote (rename (fun name => name + 10) id inherited) = denote inherited ∧
      denote (rename (fun name => name + 20) id inherited) = denote inherited ∧
      (merge? (rename (fun name => name + 10) id inherited)
        (rename (fun name => name + 20) id inherited)).map denote = some 4 ∧
      (merge? inherited inherited).map denote = some 2 := by
  decide +kernel

theorem fractured_sharing_has_no_common_renaming :
    ¬ ∃ name : Nat → Nat,
      rename name id inherited = rename (fun identity => identity + 10) id inherited ∧
      rename name id inherited = rename (fun identity => identity + 20) id inherited := by
  rintro ⟨name, left, right⟩
  have equal := left.symm.trans right
  have different : rename (fun identity => identity + 10) id inherited ≠
      rename (fun identity => identity + 20) id inherited := by decide +kernel
  exact different equal

/-- Coalescing equal-valued physical factors can keep each individual answer
unchanged while altering the coefficient of their join. -/
theorem noninjective_names_change_join :
    (merge? [factor 1 3] [factor 2 3]).map denote = some 9 ∧
      (merge? (rename (fun _ => 0) id [factor 1 3])
        (rename (fun _ => 0) id [factor 2 3])).map denote = some 3 := by
  decide +kernel

/-- Identity injectivity alone cannot preserve a refusal caused by unequal
dependency names. -/
theorem noninjective_dependencies_hide_conflict :
    merge? [factor 1 2 17] [factor 1 2 18] = none ∧
      merge? (rename id (fun _ => 0) [factor 1 2 17])
        (rename id (fun _ => 0) [factor 1 2 18]) = some [factor 1 2] := by
  decide +kernel

/-- Separate injective maps for two columns are insufficient when both columns
refer to the same name space. -/
theorem separate_columns_lose_dependency_alias :
    (factor 1 3 2).dependency = (factor 2 5 3).identity ∧
      ((factor 1 3 2).rename (fun name => name + 10) (fun name => name + 20)).dependency ≠
        ((factor 2 5 3).rename (fun name => name + 10) (fun name => name + 20)).identity := by
  decide +kernel

/-! ## Scoped reads retain productions and partition their observations -/

def unclaimed (productions : Ledger Nat Nat Nat) : Scoped Nat Nat Nat Nat :=
  ⟨productions, fun _ => none⟩

def innerWorld : Scoped Nat Nat Nat Nat := unclaimed [factor 1 2]
def innerHandled : Scoped Nat Nat Nat Nat := Scoped.handle 0 11 innerWorld
def afterInner : Scoped Nat Nat Nat Nat :=
  { innerHandled with productions := [factor 1 2, factor 2 3] }

/-- The inner two is returned as data, while the outer read observes three.
Both physical productions remain in the shared world. -/
theorem nested_reads_are_scoped :
    denote (Scoped.selected 0 innerWorld) = 2 ∧
      denote (Scoped.selected 0 afterInner) = 3 ∧
      afterInner.productions = [factor 1 2, factor 2 3] := by decide +kernel

/-- Folding the complete production list leaks the handled inner coefficient. -/
theorem whole_world_fold_leaks_handled_factor :
    denote afterInner.productions = 6 ∧
      denote afterInner.productions ≠ denote (Scoped.selected 0 afterInner) := by decide +kernel

/-- A reused shared factor is handled by the scope in which it was first
produced; forcing before entry yields a different observation partition. -/
theorem first_demand_changes_observation_partition :
    denote (Scoped.selected 0 innerHandled) = 1 ∧
      denote (Scoped.selected 1 innerWorld) = 1 ∧
      denote (Scoped.selected 0 innerWorld) = 2 := by decide +kernel

theorem old_cache_does_not_resurrect_left :
    (Scoped.merge? innerHandled innerWorld).map (fun world => world.claims 1) =
      some (some 11) := rfl

theorem old_cache_does_not_resurrect_right :
    (Scoped.merge? innerWorld innerHandled).map (fun world => world.claims 1) =
      some (some 11) := rfl

theorem same_owner_merge_is_idempotent :
    (Scoped.merge? innerHandled innerHandled).map (Scoped.selected 0) = some [] := rfl

/-- Incomparable observers cannot both acquire one shared production. -/
theorem conflicting_handlers_refused :
    Scoped.merge? innerHandled (Scoped.handle 0 12 innerWorld) = none := rfl

theorem changed_capture_refused :
    Scoped.handle? (unclaimed [factor 1 9]) innerWorld 11 = none := rfl

theorem lost_capture_claim_refused :
    Scoped.handle? innerHandled innerWorld 12 = none := rfl

theorem zero_is_handled_without_erasing_its_production :
    (Scoped.handle 0 11 (unclaimed [factor 1 0])).claims 1 = some 11 ∧
      (Scoped.handle 0 11 (unclaimed [factor 1 0])).productions = [factor 1 0] := by
  decide +kernel

/-- An interpretation callback runs after the snapshot claim and contributes
its own fresh factor to the enclosing scope. -/
theorem callback_factor_remains_outer :
    Scoped.selected 0 { innerHandled with productions := [factor 1 2, factor 2 7] } =
      [factor 2 7] := rfl

/-- Moving a production without its claim resurrects a coefficient already
consumed by the inner observer. Production renaming by itself is insufficient. -/
theorem lost_claim_recharges_renamed_production :
    denote (Scoped.selected 0 innerHandled) = 1 ∧
      denote (Scoped.selected 0 (unclaimed
        (rename (fun name => name + 10) id innerHandled.productions))) = 2 := by
  decide +kernel

def renamedInnerHandled : Scoped Nat Nat Nat Nat :=
  ⟨rename (fun name => name + 10) id innerHandled.productions,
    fun identity => if identity = 11 then some 21 else none⟩

theorem renamed_claim_keeps_read_empty :
    Scoped.selected 0 renamedInnerHandled = [] ∧ renamedInnerHandled.claims 11 = some 21 := by
  decide +kernel

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

/-- A common name change preserves an ordered matrix product; reordering its
factors does not. -/
theorem renaming_keeps_matrix_order :
    denote (rename (fun name => name + 10) id logicalMatrixOrder) =
        denote logicalMatrixOrder ∧
      denote (rename (fun name => name + 10) id logicalMatrixOrder) ≠
        denote completionMatrixOrder := by
  rw [denote_rename]
  exact ⟨rfl, completion_order_changes_denotation⟩

end Mettapedia.Algebra.SharedCoefficientLedgerControls
