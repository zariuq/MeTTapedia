import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls

/-! Occurrence, value/code and collection boundaries for retained query callers. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Caller.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination EagerDFSStreaming.Scoped
open ScopedQuerySource.Controls (call number self row mark program copying answers finalRows)

def caller : Control :=
  {bindings := [], goals := [], destination := .var "answer", reserved := {"saved"}}
def suffix : List Goal := [.equate (.var "x") (.var "saved")]

def selected := capture caller (call "row" [.var "x"]) (.var "x") (.var "answer") [] 0
  [row 7, row 7, row 8]

#guard selected.map (List.map Prod.fst) == some [0, 1, 2]
#guard (selected.map (List.map fun entry => entry.2.bindings)) ==
  some [[(.var "x", number 7)], [(.var "x", number 7)], [(.var "x", number 8)]]

-- Appending a caller does not turn a rejected captured frame into an empty query.
def conflicted : Control := {caller with bindings := [(.var "x", number 9)]}
#guard capture conflicted (call "row" [.var "x"]) (.var "x") (.var "answer") [] 0 [row 7] == none
#guard capture (ProtectedContinuation.attach suffix conflicted)
  (call "row" [.var "x"]) (.var "x") (.var "answer") suffix 0 [row 7] == none

theorem argument_return_depth_follows_caller :
    (ProtectedContinuation.attach suffix
      {caller with goals := [.argumentReturn (number 7) (.var "answer") 2]}).goals =
      [.argumentReturn (number 7) (.var "answer") 3, .equate (.var "x") (.var "saved")] := rfl

-- A collection owns its continuation once, rather than once per captured row.
def collectedThenWrite : Atom := call "let" [.var "collected", call "collapse" [copying],
  call "add-atom" [self, mark 99]]
def writeInEachChild : Atom := call "match" [self, call "row" [.var "x"],
  call "let" [.var "ignored", call "add-atom" [self, call "mark" [.var "x"]],
    call "add-atom" [self, mark 99]]]

#guard answers program [row 7, row 8] collectedThenWrite == some [Effects.boolean true]
#guard finalRows program [row 7, row 8] collectedThenWrite ==
  some [row 7, row 8, mark 7, mark 8, mark 99]
#guard finalRows program [row 7, row 8] writeInEachChild ==
  some [row 7, row 8, mark 7, mark 99, mark 8, mark 99]
#guard finalRows program [row 7, row 8] collectedThenWrite !=
  finalRows program [row 7, row 8] writeInEachChild

-- The retained caller observes captured values but does not execute them as code.
def retrieveThenPair : Atom := call "let" [.var "value",
  call "match" [self, call "payload" [.var "x"], .var "x"],
  call "quote" [.expression [.var "value", .var "x"]]]
def payload : Atom := call "add-atom" [self, mark 99]
#guard answers program [call "payload" [payload]] retrieveThenPair ==
  some [.expression [payload, payload]]
#guard finalRows program [call "payload" [payload]] retrieveThenPair == some [call "payload" [payload]]

#print axioms capture_attach
#print axioms captured_step_attach
#print axioms captured_literal_read
#print axioms primitive_step_attach
#print axioms literal_absence_step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Caller.Controls
