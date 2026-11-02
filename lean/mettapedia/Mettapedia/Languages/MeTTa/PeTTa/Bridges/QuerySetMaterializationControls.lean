import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization

/-! Scope, aliasing, count and refusal controls for materialization phases. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def app (head : String) (fields : List Atom) : Atom := .expression (.symbol head :: fields)
def integer (value : Int) : Atom := .grounded (.int value)
def rows : List Atom := [app "edge" [integer 0, integer 1], app "edge" [integer 0, integer 2]]
def pattern : Atom := app "edge" [.var "x", .var "y"]
def template : Atom := app "sat" [.symbol "f", .var "x"]
def payload : Atom := app "sat" [.symbol "f", integer 0]
def caller : Subst := [("space", .symbol "&self")]
def program : Program := {equations := [], declarations := []}
def before : Effects.State := Store.new rows []
def after : Effects.State := Store.new (rows ++ [payload]) []

theorem before_core : before.core = rows := rfl

theorem payload_projection : (choices caller pattern rows).map (fun bindings =>
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings template) = [payload, payload] := by decide +kernel

theorem ordered_worker_keeps_one_payload_and_two_answers :
    traverse (emit .self template) (choices caller pattern rows) (before, []) =
      some (after, [Effects.boolean true, Effects.boolean true]) := by
  rw [traverse_emit_exact, payload_projection]
  rfl

theorem store_only_worker_does_not_need_success_atoms :
    installRows .self ((choices caller pattern rows).map (fun bindings =>
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings template)) before = some after := by
  rw [payload_projection]
  rfl

theorem actual_source_count_with_aliased_spaces :
    PureReturns program caller before
      (counted (.var "space") pattern (bodySource "space" "payload" template)) after (integer 2) := by
  have returned := counted_query_returns program caller before after "space" "space" "payload" .self .self
    pattern template rows [Effects.boolean true, Effects.boolean true] rfl rfl rfl (by decide) (by decide) rfl
    ordered_worker_keeps_one_payload_and_two_answers
  have count : (choices caller pattern rows).length = 2 := by decide +kernel
  simpa [count, integer] using returned

theorem source_rows_do_not_grow_the_captured_query :
    (choices caller pattern rows).length = 2 ∧ after.core.length = 3 ∧ after.core.count payload = 1 := by decide +kernel

def plan := region program caller "space" "space" "payload" .self .self pattern template
  rfl rfl rfl (by decide) (by decide)

theorem planned_phase_preserves_store_and_count :
    plan.attempt before = .committed ⟨after, [integer 2], [], []⟩ := by
  have ready : (choices caller pattern rows).all (fun bindings => GuardedInsertionSource.dataRow
      (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings template)) = true := by decide +kernel
  have count : (choices caller pattern rows).length = 2 := by decide +kernel
  simp only [plan, region, Store.read_self, before_core, List.all_map, Function.comp_def, List.length_map, ready,
    ↓reduceIte, store_only_worker_does_not_need_success_atoms, count]
  rfl

def unavailableCaller : Subst := [("input", .symbol "&self"), ("target", Effects.handleValue (.privateSpace 0))]
def emptyState : Effects.State := Store.new [] []
def unavailablePlan := region program unavailableCaller "input" "target" "payload" .self (.privateSpace 0)
  pattern template rfl rfl rfl (by decide) (by decide)

theorem empty_query_does_not_observe_missing_target :
    emptyState.read (.privateSpace 0) = none ∧
    unavailablePlan.attempt emptyState = .committed ⟨emptyState, [integer 0], [], []⟩ := ⟨rfl, rfl⟩

theorem nonempty_query_cannot_treat_missing_target_as_empty_output :
    unavailablePlan.attempt before = .declined before := by
  have ready : (choices unavailableCaller pattern rows).all (fun bindings => GuardedInsertionSource.dataRow
      (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings template)) = true := by decide +kernel
  have missing : installRows (.privateSpace 0) ((choices unavailableCaller pattern rows).map
      (fun bindings => Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings template)) before = none := by
    decide +kernel
  simp only [unavailablePlan, region, Store.read_self, before_core, List.all_map, Function.comp_def, ready, ↓reduceIte, missing]

def openTemplate : Atom := app "sat" [.symbol "f", .var "unbound"]
def openPlan := region program caller "space" "space" "payload" .self .self pattern openTemplate
  rfl rfl rfl (by decide) (by decide)

theorem unbound_output_payload_refuses : openPlan.attempt before = .declined before := by
  have refused : (choices caller pattern rows).all (fun bindings => GuardedInsertionSource.dataRow
      (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings openTemplate)) = false := by decide +kernel
  simp only [openPlan, region, Store.read_self, before_core, List.all_map, Function.comp_def, refused, Bool.false_eq_true, ↓reduceIte]

def declarationTemplate : Atom := app ":" [.symbol "f", .symbol "Atom"]
def declarationPlan := region program caller "space" "space" "payload" .self .self pattern declarationTemplate
  rfl rfl rfl (by decide) (by decide)

theorem program_mutation_is_not_a_data_phase : declarationPlan.attempt before = .declined before := by
  have refused : (choices caller pattern rows).all (fun bindings => GuardedInsertionSource.dataRow
      (Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings declarationTemplate)) = false := by decide +kernel
  simp only [declarationPlan, region, Store.read_self, before_core, List.all_map, Function.comp_def, refused, Bool.false_eq_true, ↓reduceIte]

theorem occupied_temporary_does_not_bind_the_payload :
    matchBinding [("x", integer 0)] (.var "x") payload = none := by decide +kernel

def growingTemplate : Atom := app "edge" [.var "x", integer 3]
def growingPayload : Atom := app "edge" [integer 0, integer 3]
def growingAfter : Effects.State := Store.new (rows ++ [growingPayload]) []
def growingPlan := region program caller "space" "space" "payload" .self .self pattern growingTemplate
  rfl rfl rfl (by decide) (by decide)

theorem newly_matching_row_is_not_a_new_captured_choice :
    growingPlan.attempt before = .committed ⟨growingAfter, [integer 2], [], []⟩ ∧
      (choices caller pattern growingAfter.core).length = 3 := by
  constructor
  · have projected : (choices caller pattern rows).map (fun bindings =>
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings growingTemplate) =
        [growingPayload, growingPayload] := by decide +kernel
    simp only [growingPlan, region, Store.read_self, before_core, projected]
    rfl
  · decide +kernel

theorem discarding_payload_duplicates_loses_success_count :
    emitRows .self [payload, payload] (before, []) = some (after, [Effects.boolean true, Effects.boolean true]) ∧
    emitRows .self [payload] (before, []) = some (after, [Effects.boolean true]) := ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization.Controls
