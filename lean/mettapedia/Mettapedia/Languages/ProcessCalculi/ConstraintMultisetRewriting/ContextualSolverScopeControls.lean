import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivationControls

/-!
# Actual helper-producing solver runs preserve scope coverage

The constructor-free swapped-spine problem has no model in its original
endomorphic frame. Its actual completed solver run supplies a new helper.
The same computed activation has a covered root inventory after reserving
that helper namespace, while preserving the previous captured scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverScopeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport
open ContextualWorldScopeLedger
open ContextualFreshFrameScopeLedger
open ContextualTransportedActivationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Empty)

def initialScopes (_ : Unit) : Finset Nat := {2}

def inventory : Inventory locals captures (O := Nat) [(), ()] () where
  configuration := before
  rows := rows
  retained := []
  templates := ruleRoots rule

theorem the_actual_problem_retains_the_old_captured_scope :
    footprint locals captures initialScopes inventory = {2} := by decide

theorem the_initial_scope_ledger_covers_the_solver_fixture :
    CoveredWorld locals captures initialScopes occupied inventory := by
  apply (coveredWorld_iff locals captures initialScopes occupied inventory).mpr
  rw [the_actual_problem_retains_the_old_captured_scope]
  decide

theorem the_actual_helper_producing_run_has_a_covered_extended_inventory :
    ∃ update,
      ContextualTransportedActivation.FromRun locals captures 1 occupied selection rule rows before outputs update ∧
      CoveredWorld locals (ContextualComputedFreshFrame.active active update.declaration)
        (frameScopes (activeScopes initialScopes)
          (helperScope (ContextualActivationScopes.after occupied selection)))
        (helperLedger (ContextualActivationScopes.after occupied selection))
        (mapInventory locals active (ContextualComputedFreshFrame.includeSource update)
          (afterInventory locals captures occupied selection rule inventory outputs)) := by
  obtain ⟨update, origin, _⟩ := the_actual_guarded_activation_has_a_genuine_consistent_helper_frame
  refine ⟨update, origin, computed_activation_inventory_covered locals captures initialScopes occupied selection
    rule inventory outputs the_initial_scope_ledger_covers_the_solver_fixture ?_
    physical_and_guard_admission_does_not_supply_a_model update⟩
  exact rule_covered_from_templates locals captures initialScopes
    the_initial_scope_ledger_covers_the_solver_fixture rule (fun _ member => member)

theorem helpers_are_reserved_after_the_original_activation :
    ContextualActivationScopes.after occupied selection = {0, 2, 3} ∧
      helperScope (ContextualActivationScopes.after occupied selection) = 4 ∧
      helperLedger (ContextualActivationScopes.after occupied selection) = {0, 2, 3, 4} := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverScopeControls
