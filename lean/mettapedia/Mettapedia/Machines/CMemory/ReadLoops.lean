import Mettapedia.Machines.CMemory.ReadExpressions

/-!
# Source-retained counted loops with physical read expressions

This local-control fragment executes supplied scalar assignments, loop tests,
initializers and increments. Assignments update typed locals, while expressions
may load the physical heap. A loop declaration restores the exact prior local
binding, including an absent binding or a binding of a different scalar type.

Exhaustion is an explicit result, not a successful scan or an undefined load.
Unsupported statements and types are undefined rather than replaced by a scan
template. This module does not execute allocation or physical stores.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ReadLoops

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

def assignValue (old value : CVal) : CProg CVal CVal := match old, value with
  | .bool _, value => truth value >>= fun selected => pure (.bool selected)
  | .i32 _, .i32 value => pure (.i32 value)
  | .u32 _, .u32 value => pure (.u32 value)
  | .ptr _, .ptr value => pure (.ptr value)
  | _, _ => CProg.undefined

theorem signed_assignment_retains_actual_value (old value : Int32) :
    assignValue (.i32 old) (.i32 value) = pure (.i32 value) := rfl

def statements (layout : Layout) : Environment → List CStatement → CProg CVal Environment
  | environment, [] => pure environment
  | environment, .assign (.identifier name) value :: rest => do
      let old ← resolved (environment name)
      let actual ← expression layout environment value
      let converted ← assignValue old actual
      statements layout (Function.update environment name (some converted)) rest
  | _, _ => CProg.undefined

def increment (environment : Environment) : CExpr → CProg CVal Environment
  | .postIncrement (.identifier name) => do
      let value ← resolved (environment name)
      let value ← word value
      pure (Function.update environment name (some (.u32 (value + 1))))
  | _ => CProg.undefined

inductive Result where
  | finished (environment : Environment)
  | exhausted

def run (layout : Layout) (condition step : CExpr) (body : List CStatement)
    (fuel : Nat) (environment : Environment) : CProg CVal Result := do
  let value ← expression layout environment condition
  let selected ← truth value
  if selected then match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => do
        let updated ← statements layout environment body
        let advanced ← increment updated step
        run layout condition step body fuel advanced
  else pure (.finished environment)

def restore (name : Name) (old : Option CVal) : Result → Result
  | .finished environment => .finished (Function.update environment name old)
  | .exhausted => .exhausted

def counted (layout : Layout) (fuel : Nat) (environment : Environment) :
    CStatement → CProg CVal Result
  | .forLoop type counter initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let value ← expression layout environment initial
        let first ← word value
        let initialized := Function.update environment counter (some (.u32 first))
        let result ← run layout condition step body fuel initialized
        pure (restore counter (environment counter) result)
      else CProg.undefined
  | _ => CProg.undefined

def executeNode (layout : Layout) (fuel : Nat) (environment : Environment) :
    Option CStatement → CProg CVal Result
  | some statement => counted layout fuel environment statement
  | none => CProg.undefined

theorem false_condition_skips_body_and_increment (layout : Layout) (environment : Environment)
    (step : CExpr) (body : List CStatement) (fuel : Nat) :
    run layout (.bool false) step body fuel environment = pure (.finished environment) := by
  rw [run.eq_def]
  rfl

theorem zero_fuel_with_true_condition_is_exhausted (layout : Layout) (environment : Environment)
    (step : CExpr) (body : List CStatement) :
    run layout (.bool true) step body 0 environment = pure .exhausted := rfl

theorem declaration_uses_actual_initializer_and_loop (layout : Layout) (fuel : Nat)
    (environment : Environment) (counter : Name) (condition step : CExpr)
    (body : List CStatement) :
    counted layout fuel environment
      (.forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0) condition step body) =
      (run layout condition step body fuel (Function.update environment counter (some (.u32 0)))
        >>= fun result => pure (restore counter (environment counter) result)) := rfl

namespace Controls

def emptyEnvironment : Environment := fun _ => none
def emptyLayout : Layout := fun _ => none

theorem missing_loop_is_not_empty_success (fuel : Nat) :
    executeNode emptyLayout fuel emptyEnvironment none = CProg.undefined := rfl

theorem unsupported_body_is_not_removed :
    statements emptyLayout emptyEnvironment [.effect (.call "io".toList [])] =
      CProg.undefined := rfl

theorem wrong_counter_type_is_not_synthesized :
    increment (fun _ => some (.bool false)) (.postIncrement (.identifier "j".toList)) =
      CProg.undefined := by
  simp [increment, resolved, word]
  exact undefined_bind _

theorem missing_condition_is_not_false_success :
    run emptyLayout (.identifier "absent".toList) (.postIncrement (.identifier "j".toList))
      [] 0 emptyEnvironment = CProg.undefined := by
  simp [run, expression]
  exact undefined_bind _

theorem false_condition_does_not_check_invalid_counter :
    run emptyLayout (.bool false) (.identifier "absent".toList) [] 0 emptyEnvironment =
      pure (.finished emptyEnvironment) := rfl

theorem changed_initializer_retains_nonzero_start :
    counted emptyLayout 0 emptyEnvironment
      (.forLoop ⟨"uint32_t".toList, 0⟩ "j".toList (.unsignedInteger 7) (.bool false)
        (.postIncrement (.identifier "j".toList)) []) =
      pure (.finished (Function.update (Function.update emptyEnvironment "j".toList
        (some (.u32 7))) "j".toList none)) := rfl

end Controls

end Mettapedia.Machines.CMemory.ReadLoops
