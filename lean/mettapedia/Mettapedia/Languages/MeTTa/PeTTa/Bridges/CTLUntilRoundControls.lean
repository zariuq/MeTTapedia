import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls

/-! Authored CTL EU round with nested current-state queries, a named presence
guard and two writes per genuinely new predecessor. This is a round control,
not the complete EU driver/fixed-point theorem. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.CTLUntilControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics EagerDFS.Destination
open Controls (call number self presence execute answers finalRows)

def sat (label node : Atom) : Atom := call "sat" [label, node]
def frontier (label round node : Atom) : Atom := call "fr" [label, round, node]
def reverseEdge (next prior : Atom) : Atom := call "rt" [next, prior]

def guard : Equation := ⟨"in", [.var "f", .var "x"], presence (sat (.var "f") (.var "x"))⟩

def roundBody : Atom := call "size-atom" [call "collapse" [
  call "match" [self, frontier (.var "f") (.var "k") (.var "y"),
    call "match" [self, reverseEdge (.var "y") (.var "x"),
      call "match" [self, sat (.var "a") (.var "x"),
        call "if" [call "in" [.var "f", .var "x"], call "empty" [],
          call "let" [.var "ignored", call "add-atom" [self, sat (.var "f") (.var "x")],
            call "add-atom" [self, frontier (.var "f") (.var "k1") (.var "x")]]]]]]]]

def roundEquation : Equation := ⟨"eu-round", [.var "f", .var "a", .var "k", .var "k1"], roundBody⟩
def program : Program := {equations := [guard, roundEquation], declarations := []}
def input : List Atom := [frontier (.symbol "f") (number 0) (number 1),
  frontier (.symbol "f") (number 0) (number 1), reverseEdge (number 1) (number 0),
  reverseEdge (number 1) (number 0), sat (.symbol "a") (number 0), sat (.symbol "a") (number 0)]
def added : List Atom := [sat (.symbol "f") (number 0), frontier (.symbol "f") (number 1) (number 0)]
def firstRound : Atom := call "eu-round" [.symbol "f", .symbol "a", number 0, number 1]
def nextRound : Atom := call "eu-round" [.symbol "f", .symbol "a", number 0, number 2]

-- Eight producer combinations collapse to one fresh insertion event.
#guard answers program input firstRound 5000 == some [number 1]
#guard finalRows program input firstRound 5000 == some (input ++ added)
#guard answers program (input ++ added) nextRound 5000 == some [number 0]
#guard finalRows program (input ++ added) nextRound 5000 == some (input ++ added)

def paused := (execute program input firstRound 80).bind fun result =>
  EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved => (machine .relational program).run 5000 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (input ++ added)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.CTLUntilControls
