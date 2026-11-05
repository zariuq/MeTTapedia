import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionRank
import Mettapedia.Tools.KernelReflexivity

/-! Recursive insertion distinguishes callback answers, fresh entries and
published state. A complete two-node source cycle exercises the guard. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def node (name : String) : Atom := .expression [.symbol "node", .symbol name]
def before : Effects.State := Store.new [] []
def held : Effects.State := Store.new [node "a"] []
def both : Effects.State := Store.new [node "a", node "b"] []
def caller : Subst := [("space", .symbol "&self"), ("row", node "a")]
def emptyProgram : Program := {equations := [], declarations := []}
def silentBody : Body := fun _ state => some (state, [])
def deniedBody : Body := fun _ _ => none
def twoBody : Body := fun _ state => some (state, [.symbol "left", .symbol "right"])

theorem silent_callback_still_inserts : run .self (node "a") "written" silentBody caller before = some (held, []) := by
  kernel_reflexivity

theorem empty_source_result_can_change_state :
    Returns emptyProgram caller before (source "space" "row" "written" (.expression [.symbol "empty"])) held [] := by
  apply returns emptyProgram "space" "row" "written" _ .self (node "a") silentBody caller before held []
    rfl rfl rfl _ silent_callback_still_inserts
  intro current next values completed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
  exact empty_returns emptyProgram _ current

theorem zero_answers_is_not_zero_growth : held.core.length = before.core.length + 1 := rfl

theorem held_row_skips_unavailable_callback : run .self (node "a") "written" deniedBody caller held = some (held, []) := by
  kernel_reflexivity

theorem callback_answers_not_replaced_by_success_flag :
    run .self (node "a") "written" twoBody caller before = some (held, [.symbol "left", .symbol "right"]) := by kernel_reflexivity

theorem unavailable_callback_cannot_certify_rollback :
    FreshInsertionSource.update before .self (node "a") = some (held, true) ∧
      run .self (node "a") "written" deniedBody caller before = none := by
  exact ⟨rfl, by kernel_reflexivity⟩

def reenter : Body := fun bindings state => run .self (node "a") "again" deniedBody bindings state

theorem recursive_same_row_stops_after_publication :
    run .self (node "a") "written" reenter caller before = some (held, []) := by kernel_reflexivity

def eraseBody : Body := fun _ _ => some (before, [])

theorem destructive_callback_loses_the_progress_measure :
    run .self (node "a") "written" eraseBody caller before = some (before, []) ∧
      ¬ held.core.toFinset ⊆ before.core.toFinset := by
  constructor
  · kernel_reflexivity
  · decide +kernel

def body (label next : String) : Atom :=
  .expression [.symbol "let", .var "row", .expression [.symbol "quote", node label],
    source "space" "row" "written" (.expression [.symbol next, .var "space"])]

def cycleProgram : Program :=
  { equations := [⟨"cycle-a", [.var "space"], body "a" "cycle-b"⟩,
      ⟨"cycle-b", [.var "space"], body "b" "cycle-a"⟩], declarations := [] }

def cycleCall : Atom := .expression [.symbol "cycle-a", .symbol "&self"]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem recursive_source_cycle_returns_no_answers :
    evaluate cycleProgram 500 before cycleCall = .complete both [] [] [] := by kernel_reflexivity

theorem recursive_source_cycle_has_operational_derivation :
    Returns cycleProgram [] before cycleCall both [] :=
  completed_run_has_path cycleProgram 500 (start before cycleCall) both [] [] []
    recursive_source_cycle_returns_no_answers

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem repeated_recursive_source_does_not_refire :
    evaluate cycleProgram 500 both cycleCall = .complete both [] [] [] := by kernel_reflexivity

def catalogue : Finset Atom := {node "a", node "b"}

theorem initial_budget_is_two : FreshInsertionRank.remaining catalogue before.core = 2 := by decide +kernel
theorem first_entry_spends_one : FreshInsertionRank.remaining catalogue held.core = 1 := by decide +kernel
theorem completed_support_has_no_budget : FreshInsertionRank.remaining catalogue both.core = 0 := by decide +kernel

theorem unrelated_duplicate_rows_do_not_spend_budget :
    FreshInsertionRank.remaining catalogue [.symbol "other", .symbol "other"] = 2 := by decide +kernel

theorem uncatalogued_fresh_head_has_no_descent :
    FreshInsertionSource.update before .self (node "c") = some (Store.new [node "c"] [], true) ∧
      FreshInsertionRank.remaining catalogue [node "c"] = FreshInsertionRank.remaining catalogue before.core := by
  exact ⟨rfl, by decide +kernel⟩

def firstEntry : FreshInsertionRank.Entry catalogue .self before held :=
  ⟨node "a", by decide +kernel, held, rfl, held.core, held.core, rfl, rfl, Finset.Subset.refl _⟩

def secondEntry : FreshInsertionRank.Entry catalogue .self held both :=
  ⟨node "b", by decide +kernel, both, by kernel_reflexivity, both.core, both.core, rfl, rfl, Finset.Subset.refl _⟩

theorem cycle_fresh_entry_budget :
    FreshInsertionRank.Entries catalogue .self 2 before both :=
  .cons firstEntry (.cons secondEntry (.nil both))

theorem no_third_support_preserving_fresh_entry (after : Effects.State) (rows : List Atom)
    (reading : after.read .self = some rows) :
    ¬ FreshInsertionRank.Entries catalogue .self 3 before after := by
  intro path
  have bound := path.count_le before.core rows rfl reading
  have size : catalogue.card = 2 := by decide +kernel
  omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionContinuation.Controls
