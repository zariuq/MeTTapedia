import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundControls

/-! The complete authored EU driver, including sequential binding, seeding,
frontier cleanup and the final quiet round. These executed source controls
do not replace the arbitrary-graph source/fixed-point correspondence theorem. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.CTLUntilDriverControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics
open Controls (call number self execute answers finalRows)
open CTLUntilControls (sat frontier reverseEdge guard roundEquation)

def counted (body : Atom) : Atom := call "size-atom" [call "collapse" [body]]

def dropEquation : Equation := ⟨"drop", [.var "f", .var "k"], counted
  (call "match" [self, frontier (.var "f") (.var "k") (.var "x"),
    call "remove-atom" [self, frontier (.var "f") (.var "k") (.var "x")]])⟩

def loopBody : Atom := call "let*" [.expression [
  .expression [.var "k1", call "+" [.var "k", number 1]],
  .expression [.var "n", call "eu-round" [.var "f", .var "a", .var "k", .var "k1"]],
  .expression [.var "d", call "drop" [.var "f", .var "k"]]],
  call "if" [call "==" [.var "n", number 0], .var "k1", call "eu-loop" [.var "f", .var "a", .var "k1"]]]
def loopEquation : Equation := ⟨"eu-loop", [.var "f", .var "a", .var "k"], loopBody⟩

def entryBody : Atom := call "let" [.var "n", counted
  (call "match" [self, sat (.var "b") (.var "x"),
    call "let" [.var "ignored", call "add-atom" [self, sat (.var "f") (.var "x")],
      call "add-atom" [self, frontier (.var "f") (number 0) (.var "x")]]]),
  call "eu-loop" [.var "f", .var "a", number 0]]
def entryEquation : Equation := ⟨"do-eu", [.var "f", .var "a", .var "b"], entryBody⟩

def program : Program := {equations := [guard, roundEquation, dropEquation, loopEquation, entryEquation], declarations := []}
def entry : Atom := call "do-eu" [.symbol "f", .symbol "a", .symbol "b"]
def input : List Atom := [reverseEdge (number 1) (number 0), reverseEdge (number 2) (number 1),
  sat (.symbol "a") (number 0), sat (.symbol "a") (number 1), sat (.symbol "a") (number 3),
  sat (.symbol "b") (number 2)]
def added : List Atom := [sat (.symbol "f") (number 2), sat (.symbol "f") (number 1), sat (.symbol "f") (number 0)]

#guard answers program input entry 15000 == some [number 3]
#guard finalRows program input entry 15000 == some (input ++ added)
#guard answers program [] entry 1000 == some [number 1]
#guard finalRows program [] entry 1000 == some []

def duplicateInput : List Atom := input ++ [sat (.symbol "b") (number 2)]
def duplicateAdded : List Atom := [sat (.symbol "f") (number 2)] ++ added
#guard answers program duplicateInput entry 20000 == some [number 3]
#guard finalRows program duplicateInput entry 20000 == some (duplicateInput ++ duplicateAdded)

def paused := (execute program input entry 110).bind fun result => EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved => (machine .relational program).run 15000 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (input ++ added)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.CTLUntilDriverControls
