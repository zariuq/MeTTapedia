import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource
import Mettapedia.Tools.KernelReflexivity

/-! Bound constructor capture and raw insertion controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def app (name : String) (fields : List Atom) : Atom := .expression (.symbol name :: fields)
def number (value : Int) : Atom := .grounded (.int value)
def pattern : Atom := app "ty" [.var "class", .var "node"]
def row : Atom := app "ty" [.symbol "Student", number 7]
def caller : Subst := [("space", .symbol "&self"), ("class", .symbol "Student"), ("node", number 7)]
def before : Effects.State := Store.new [] []
def after : Effects.State := Store.new [row] []
def program : Program := {equations := [⟨"ty", [.var "c", .var "n"], .symbol "poisoned"⟩], declarations := []}
def silentBody : Body := fun _ state => some (state, [])
def continuation : Atom := .expression [.symbol "empty"]

def captured : BoundQueryPattern.Captured caller pattern where
  frozen := (BoundQueryPattern.check_iff caller pattern).mp (by decide +kernel)
  literal := (LiteralQuerySource.checkLiteral_iff _).mp (by decide +kernel)
  ordinarySource := rfl
  ordinaryValue := by decide +kernel

theorem actual_capture_succeeds : (BoundQueryPattern.capture caller pattern).isSome = true := by decide +kernel
theorem live_read_prepares : (prepare caller pattern .self before).isSome = true := by decide +kernel

theorem absent_field_refuses : (BoundQueryPattern.capture [("class", .symbol "Student")] pattern).isNone = true := by
  decide +kernel

theorem open_field_refuses :
    (BoundQueryPattern.capture [("class", .symbol "Student"), ("node", .var "unknown")] pattern).isNone = true := by
  decide +kernel

theorem captured_match_keeps_exact_bindings : matchValue caller pattern row = some caller := by decide +kernel
theorem conflicting_row_does_not_rebind : matchValue caller pattern (app "ty" [.symbol "Student", number 8]) = none := by
  decide +kernel

theorem repeated_variable_is_a_constraint :
    matchValue caller (app "pair" [.var "node", .var "node"]) (app "pair" [number 7, number 8]) = none := by
  decide +kernel

theorem nested_constructor_capture :
    (BoundQueryPattern.capture caller (app "deep" [.var "class", app "box" [.var "node"]])).isSome = true := by
  decide +kernel

theorem list_view_refuses :
    (BoundQueryPattern.capture caller (app "cons" [.var "node", .expression []])).isNone = true := by decide +kernel

theorem substituted_conjunction_refuses :
    (BoundQueryPattern.capture [("head", .symbol ",")] (.expression [.var "head", .symbol "a", .symbol "b"])).isNone = true := by
  decide +kernel

theorem relevant_open_row_refuses :
    (prepare caller pattern .self (Store.new [app "ty" [.symbol "Student", .var "open"]] [])).isNone = true := by
  decide +kernel

theorem unrelated_open_row_is_screened :
    (prepare caller pattern .self (Store.new [app "other" [.var "open"]] [])).isSome = true := by decide +kernel

theorem missing_space_refuses : (prepare caller pattern (.privateSpace 0) before).isNone = true := by decide +kernel
theorem declaration_row_refuses :
    (prepare [] (app ":" [.symbol "f", .symbol "Atom"]) .self before).isNone = true := by decide +kernel

def later : Subst := ("other", .symbol "fresh") :: caller

theorem later_extends : later.lookupExtends caller :=
  matchValue_lookup_extends (initial := caller) (final := later) (pattern := .var "other") (value := .symbol "fresh")
    (by decide +kernel)

theorem added_binding_keeps_captured_row : applySubst later pattern = row :=
  captured.frozen.subst_ext later_extends

theorem extended_capture_remains_admitted :
    BoundQueryPattern.capture later pattern = some (captured.extend later_extends) :=
  BoundQueryPattern.capture_complete _

theorem source_inserts_constructor_without_evaluating_it :
    Returns program caller before (source "space" "written" pattern (.symbol "t") continuation) after [] := by
  apply returns program "space" "written" pattern (.symbol "t") continuation .self silentBody caller before after []
    captured (.symbol "t") rfl rfl _ (by kernel_reflexivity)
  intro current next values completed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
  exact empty_returns program _ current

theorem false_guard_payload_is_still_a_witness :
    PureReturns program caller after (absent "space" pattern (Effects.boolean false)) after (Effects.boolean false) := by
  simpa only [show applySubst caller pattern ∈ [row] from by decide +kernel, not_true_eq_false, decide_false] using
    absent_returns program caller after "space" pattern (Effects.boolean false) .self [row]
      captured (.grounded (.bool false)) rfl rfl

theorem query_keeps_duplicate_payloads :
    Returns program caller (Store.new [row, row] []) (query "space" pattern (.symbol "t"))
      (Store.new [row, row] []) [.symbol "t", .symbol "t"] := by
  have returned := query_returns program caller (Store.new [row, row] []) "space" pattern (.symbol "t") .self [row, row]
    (.symbol "t") rfl rfl
  have witnesses : (FlatQueryRelationCompilation.sourceScan caller pattern 0 [row, row]).map (fun _ => Atom.symbol "t") =
      [.symbol "t", .symbol "t"] := by decide +kernel
  simpa only [witnesses] using returned

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem actual_source_run_keeps_raw_row :
    Eval.run program 500 {state := before, control := .evaluate caller (source "space" "written" pattern (.symbol "t") continuation)} =
      .complete after [] [] [] := by kernel_reflexivity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem evaluating_the_row_would_change_it :
    Eval.run program 100 {state := before, control := .evaluate caller pattern} =
      .complete before [.symbol "poisoned"] [] [] := by kernel_reflexivity

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource.Controls
