import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlayControls

/-!
# Written match ownership at the typed-call boundary

The three-argument written form keeps its source pattern and template. It
does not select an ordinary grounded-function row protocol. Other arities
remain ordinary calls, and authored ownership still retains the canonical
source request before operands begin.
-/

set_option autoImplicit false
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaWrittenMatchControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open PettaOccurrenceOverlay
open PettaOccurrenceOverlay.Controls (sym num call services)

def badSignature : Atom := call ":" [sym "match", call "->" [sym "Number", sym "Number", sym "Number", sym "Number"]]
def program : SpaceSemantics.Program :=
  {equations := [], declarations := [badSignature], facts := [call "row" [num 7]], layout := [.declaration, .fact]}
def rows (head : String) (_arguments : List Atom) : RowLookup :=
  if head = "match" then .typed [⟨[.sym "Number", .sym "Number", .sym "Number"], .sym "Number"⟩] else .untyped
def expression : Atom := call "match" [sym "&self", call "row" [.var "x"], call "+" [.var "x", num 1]]
def initial (registry : SpaceSemantics.Program) : State Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded registry, [], []⟩,
    [{frontier := [(⟨[], [.evaluate expression (.var "out")], .var "out", ∅, 0⟩, ⟨(), []⟩, [])]}]⟩)

def observed : Option (List Atom) :=
  let result := (machine (services rows) .eagerValue program).run 80 (initial program)
  match result.2 with
  | .finished _ => some (result.1.map (·.value))
  | _ => none

#guard observed == some [num 8]

theorem written_match_is_source_owned (space pattern body : Atom) :
    sourceOwned (call "match" [space, pattern, body]) = true := by simp [sourceOwned, call]

theorem wrong_arity_is_not_a_written_match (space pattern : Atom) :
    sourceOwned (call "match" [space, pattern]) = false := by simp [sourceOwned, call, EagerDFS.eagerControlForm]

def authored : SpaceSemantics.Program :=
  {program with equations := [⟨"match", [.var "s", .var "p", .var "t"], sym "override"⟩]}

theorem authored_match_retains_unstarted_request :
    step (services rows) .eagerValue authored (initial authored) =
      .call (.source (.branch (.invoke "match" [sym "&self", call "row" [.var "x"], call "+" [.var "x", num 1]] (.var "out"))))
        (initial authored) := by
  simp [step, delegate, initial, expression, sourceOwned, call,
    liftSource, Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    EagerDFS.Destination.queryOwned, authored]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaWrittenMatchControls
