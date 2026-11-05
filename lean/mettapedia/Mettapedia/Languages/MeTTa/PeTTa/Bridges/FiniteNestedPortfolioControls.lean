import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedDriverControls

/-! Completed-source admission, exact entrance refusal and changed-read controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Dynamics ObservationQualified
open NamedSpaces
open FiniteNestedQuerySource.Controls (queries head domain caller before finalState no_head_constants rows pair)
open FiniteNestedQueryDriver.Controls (program driver certificate withProductive)

def plan := region (0 : Nat) certificate domain no_head_constants caller rfl 3
def shortPlan := region (0 : Nat) certificate domain no_head_constants caller rfl 2

theorem accepted_driver_commits_the_source_result :
    plan.attempt before = .committed (PureCallPortfolio.complete finalState (Effects.boolean true)) := by
  kernel_reflexivity

theorem insufficient_allowance_declines_at_exact_entrance : shortPlan.attempt before = .declined before := by
  kernel_reflexivity

theorem refusal_uses_full_reference_meaning :
    shortPlan.execute before = PureCallPortfolio.sourceMeaning program caller (FiniteNestedQueryDriver.call driver "out") before :=
  execute_exact 0 certificate domain no_head_constants caller rfl 2 before

theorem accepted_and_declined_routes_agree : plan.execute before = shortPlan.execute before := by
  unfold plan shortPlan
  rw [execute_exact 0 certificate domain no_head_constants caller rfl 3 before,
    execute_exact 0 certificate domain no_head_constants caller rfl 2 before]

def changed : Effects.State := Store.new (rows ++ [pair 3 0]) []

theorem changed_value_domain_declines_without_erasing_it : plan.attempt changed = .declined changed := by
  kernel_reflexivity

theorem completed_state_can_be_rechecked :
    plan.attempt finalState = .committed (PureCallPortfolio.complete finalState (Effects.boolean true)) := by
  kernel_reflexivity

theorem exact_source_pages_have_no_candidate :
    (classify .exactPage (0 : Nat) program queries head driver "out" "payload" "fresh" .self domain no_head_constants caller rfl 3).isNone = true := rfl

theorem changed_dispatch_has_no_candidate :
    (classify .completedResult (0 : Nat) withProductive queries head driver "out" "payload" "fresh" .self domain no_head_constants caller rfl 3).isNone = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio.Controls
