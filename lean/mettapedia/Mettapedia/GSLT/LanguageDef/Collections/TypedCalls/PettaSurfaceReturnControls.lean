import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlayControls

/-!
# Typed effectful surface-query return controls

These executed controls use the real source query, equation, let, print and
typed occurrence drivers. The scalar guard service is separately proved in
PettaOccurrenceOverlayControls. Native layouts are not supplied by these runs.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open PettaOccurrenceOverlay
open PettaOccurrenceOverlay.Controls (sym num call printThen services)

def body (tail : Atom) : Atom :=
  call "match" [sym "&self", call "row" [.var "r"],
    call "let" [.var "printed", call "println!" [.var "r"], tail]]

def program (tail : Atom) : SpaceSemantics.Program :=
  {equations := [⟨"keep", [.var "x"], body tail⟩], declarations := [],
    facts := [call "row" [num 7], call "row" [num 7], call "row" [num 9]],
    layout := [.equation, .fact, .fact, .fact]}

def rows (head : String) (_arguments : List Atom) : RowLookup :=
  if head = "keep" then .typed [⟨[.sym "Number"], .sym "Number"⟩] else .untyped

def initial (tail : Atom) : State Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded (program tail), [], []⟩,
    [{frontier := [(⟨[], [.evaluate (call "keep" [num 4]) (.var "result")], .var "result", ∅, 0⟩,
      ⟨(), []⟩, [])]}]⟩)

def observed (tail : Atom) : Option (List Atom × List Atom) :=
  let result := (machine (services rows) .eagerValue (program tail)).run 300 (initial tail)
  match result.2 with
  | .finished final => some (result.1.map (·.value), final.2.world.output)
  | _ => none

#guard observed (.var "x") == some ([num 4, num 4, num 4], [num 7, num 7, num 9])
#guard observed (call "let" [.var "x", num 9, .var "x"]) == some ([], [num 7, num 7, num 9])
#guard observed (call "let*" [.expression [.expression [.var "y", num 2]], .var "x"]) ==
  some ([num 4, num 4, num 4], [num 7, num 7, num 9])

#guard observed (call "case" [num 1, .expression
    [.expression [.var "first", call "empty" []], .expression [.var "later", .var "x"]]]) ==
  some ([], [num 7, num 7, num 9])

#guard observed (call "case" [call "superpose" [.expression [num 1, num 2]], .expression
    [.expression [num 1, call "empty" []], .expression [.var "later", .var "x"]]]) ==
  some ([num 4, num 4, num 4], [num 7, num 7, num 9])

#guard observed (call "case" [printThen "key" (num 1), .expression
    [.expression [.var "first", call "empty" []], .expression [.var "later", printThen "wrong" (.var "x")]]]) ==
  some ([], [num 7, sym "key", num 7, sym "key", num 9, sym "key"])

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn.Controls
