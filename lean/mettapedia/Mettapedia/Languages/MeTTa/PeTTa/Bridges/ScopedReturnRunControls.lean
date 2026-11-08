import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnFunction

/-!
# Recursive and effectful source-return controls

The program below uses the actual clause table, shared space, recursive
prefix call, nested collection, query templates and committed case choice.
The closed run is an executed control; the all-budget contract is a kernel
theorem instantiated from the checked source program.
-/

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRunControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination

def num (n : Int) : Atom := .grounded (.int n)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def discard (producer body : Atom) : Atom := call "let" [.var "ignored", producer, body]

def helper : SpaceSemantics.Equation :=
  ⟨"prefix-loop", [.var "n"], call "if" [call ">" [.var "n", num 0],
    discard (call "println!" [.var "n"]) (call "prefix-loop" [call "-" [.var "n", num 1]]),
    .expression []]⟩

def branchEffect : Atom := call "case" [.var "r", .expression
  [.expression [num 7, call "println!" [.symbol "Seven"]],
   .expression [.var "other", call "println!" [.symbol "Other"]]]]

def firstBody : Atom := call "let*" [.expression
  [.expression [.var "looped", call "prefix-loop" [num 2]],
   .expression [.var "collected", call "collapse" [call "superpose" [.expression [num 10, num 20]]]]],
  call "match" [.symbol "&self", call "row" [.var "r"], discard branchEffect (.var "x")]]

def program : SpaceSemantics.Program :=
  {equations := [helper, ⟨"keep", [.var "x"], firstBody⟩,
      ⟨"keep", [.var "y"], discard (call "println!" [.symbol "Alt"]) (.var "y")⟩],
    declarations := [], facts := [call "row" [num 7], call "row" [num 7], call "row" [num 9]],
    layout := [.equation, .equation, .equation, .fact, .fact, .fact]}

def caller : Control := {bindings := [], goals := [], destination := .var "out"}
def selected := ClauseChoice.choices program caller "keep" [num 4] (.var "out") []
def initial : ScopedCursor Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded program, [], []⟩,
    [⟨selected.map (fun choice => (predicateEntry 0 choice.2, (), [choice.1])), [], none⟩]⟩)

def observed : Option (List Atom × List Atom) :=
  let result := (ScopedQuerySource.ownedMachine .eagerValue program).run 500 initial
  match result.2 with
  | .finished final => some (result.1.map CollectedAnswer.value, final.2.world.output)
  | _ => none

#guard observed == some ([num 4, num 4, num 4, num 4],
  [num 2, num 1, .symbol "Seven", .symbol "Seven", .symbol "Other", .symbol "Alt"])

theorem source_check_accepts_all_keep_rows : ScopedReturnFunction.checksHead program "keep" 0 5 = true := by
  decide +kernel

theorem every_budget_keeps_each_actual_occurrence (fuel : Nat) :
    let packets := ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel initial).1
    packets.map CollectedAnswer.value = List.replicate packets.length (num 4) := by
  exact ScopedReturnFunction.checked_ground_function_run program "keep" 0 5 source_check_accepts_all_keep_rows
    caller [num 4] (num 4) (.var "out") rfl rfl (Allocator.empty 8 64)
    ⟨Effects.loaded program, [], []⟩ () [] fuel (by simp [num, encode, Mettapedia.Logic.LP.Term.isGround])

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRunControls
