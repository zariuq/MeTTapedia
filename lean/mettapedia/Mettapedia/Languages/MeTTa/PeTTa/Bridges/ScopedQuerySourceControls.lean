import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding
import Mettapedia.Languages.MeTTa.PeTTa.DestinationMatchSource

/-!
# Surface query controls over the existing occurrence driver

The executable examples enter through an authored expression, not an externally
supplied query operation. The kernel controls separately check retained
ownership requests and the two-way occurrence frontier.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination

def num (n : Int) : Atom := .grounded (.int n)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def row (value : Atom) : Atom := call "row" [value]
def program : SpaceSemantics.Program :=
  {equations := [], declarations := [], facts := [row (num 7), row (num 7)], layout := [.fact, .fact]}
def pattern : Atom := row (.var "x")
def code : Atom := call "+" [num 1, num 2]
def initial (registry : SpaceSemantics.Program) (template : Atom)
    (bindings : Equations := []) : ScopedCursor Unit :=
  let control : Control :=
    {bindings, goals := [.evaluate (call "match" [.symbol "&self", pattern, template]) (.var "out")],
      destination := .var "out"}
  (Allocator.empty 0 0,
    ⟨⟨Effects.loaded registry, [], []⟩, [⟨[(control, (), [])], [], none⟩]⟩)

def answers (registry : SpaceSemantics.Program) (template : Atom)
    (bindings : Equations := []) : List Atom :=
  ((ownedMachine .eagerValue registry).run 60 (initial registry template bindings)).1.map CollectedAnswer.value

-- These are executed source controls, distinct from the general preservation proofs.
#guard answers program code == [num 3, num 3]
#guard answers program (.var "held") [(.var "held", code)] == [code, code]

def openProgram : SpaceSemantics.Program :=
  {program with facts := [row (.var "stored"), row (num 9)]}

#guard answers openProgram (call "let" [.var "x", num 7, .var "x"]) == [num 7]

def queryControl : Control :=
  {bindings := [], goals := [], destination := .var "out"}

theorem open_row_is_not_a_closed_capture :
    ClosedQueryAdmission.rowsReady pattern [row (.var "stored")] = false := by decide +kernel

theorem open_row_has_two_way_admission :
    unifyingReady pattern [row (.var "stored")] = true := by decide +kernel

theorem duplicate_rows_keep_ordered_origins :
    (queryChoices queryControl pattern code (.var "out") []
      [row (num 7), row (num 7), .symbol "unrelated"]).map Prod.fst = [0, 1] := by
  cbv

def shadowed : SpaceSemantics.Program :=
  {program with equations :=
    [{head := "match", arguments := [.var "s", .var "p", .var "t"], body := .symbol "override"}]}

theorem shadowed_source_retains_unstarted_operand :
    ownedStep .eagerValue shadowed (initial shadowed code) =
      .call (.branch (.invoke "match" [.symbol "&self", pattern, code] (.var "out")))
        (initial shadowed code) := by
  simp [ownedStep, ScopedCaseSource.entryStep, ScopedCaseSource.readyStep,
    ownershipStep, queryOwned, shadowed, initial, call]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Controls
