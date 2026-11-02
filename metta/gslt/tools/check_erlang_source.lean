import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering
import Mettapedia.Languages.Erlang.ActorExamples
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Selected textual Core Erlang enters the independent actor model. Expected
observations are fixture data, not results obtained from prepared IR. The fair
driver witnesses one schedule; a schedule-sensitive case checks membership in
its declared outcome set, not equality of every possible outcome.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering (lower)
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa

def n (value : Int) : Value := .literal (.integer value)
def a (name : String) : Value := .literal (.atom name)
def list (numbers : List Int) : Value :=
  numbers.foldr (fun head tail => .cons (n head) tail) (.literal .nil)

def accepts (label : String) (observed : ActorSystem.Observation) : Bool :=
  match label, observed with
  | "core_blocked", .blocked => true
  | "core_sequential", .returned (.ok values) =>
      values == [.tuple [n 120, list [3, 2, 1], list [1, 2, 3], list [2, 3]]]
  | "core_pingpong", .returned (.ok values) => values == [a "done"]
  | "core_counter", .returned (.ok values) => values == [n 2]
  | "core_function_message", .returned (.ok values) => values == [n 42]
  | "core_selective", .returned (.ok values) => values == [.tuple [a "a", a "b"]]
  | "core_parallel_map", .returned (.ok values) => values == [list [9, 1, 4]]
  | "core_sender_order", .returned (.ok values) =>
      let letters := fun names => names.foldr (fun name tail => Value.cons (a name) tail) (.literal .nil)
      [letters ["a1", "a2", "b"], letters ["a1", "b", "a2"], letters ["b", "a1", "a2"]].any
        (fun result => values == [result])
  | "core_multiple_values", .returned (.ok values) => values == [.tuple [n 1, n 2]]
  | "core_factorial_entry", .returned (.ok values) => values == [n 120]
  | "core_shadow", .returned (.ok values) => values == [n 2]
  | "core_local_shadow", .returned (.ok values) => values == [n 7]
  | _, _ => false

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packetPath, label] := arguments
    | throw (IO.userError "expected source, selected parser packet and case name")
  let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
      SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected one explicitly selected whole-input result")
  let input ← IO.FS.readFile sourcePath
  let lowered := if label == "core_factorial_entry" then
      lower input tree "factorial" [n 5]
    else lower input tree
  if label == "--refuse" then
    match lowered with
    | .error _ => IO.println "(ErlangSourceRefusal true)"; return
    | .ok _ => throw (IO.userError "unexpected frontend acceptance")
  let compiled ← match lowered with
    | .ok compiled => pure compiled
    | .error reason => throw (IO.userError reason)
  let initial := ActorSystem.begin compiled.program
  let .ok direct := ActorExamples.runFair 6000 initial
    | throw (IO.userError "reference actor model encountered an internal error")
  unless accepts label direct.observe do
    throw (IO.userError s!"unexpected reference observation: {reprStr direct.observe}")
  let .ok first := ActorExamples.runFair 17 initial
    | throw (IO.userError "reference prefix encountered an internal error")
  let .ok resumed := ActorExamples.runFair 5983 first
    | throw (IO.userError "reference resumption encountered an internal error")
  unless reprStr direct == reprStr resumed do
    throw (IO.userError "whole-state actor resumption differs")
  IO.println s!"(ErlangSourceControl {reprStr label} true true {compiled.program.code.size} {compiled.retained.length} {compiled.omitted.length})"
