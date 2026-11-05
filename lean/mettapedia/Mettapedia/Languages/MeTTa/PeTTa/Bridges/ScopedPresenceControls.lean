import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedPresenceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls

/-! Presence, allocation, sibling retention and partially published effects. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number self row mark program presence)

def run (capacity : Nat) (rows : List Atom) (expression : Atom) (fuel : Nat := 200) :=
  (loadScoped? (Allocator.empty capacity 8) rows [] []
    {bindings := [], goals := [.evaluate expression (.var "answer")], destination := .var "answer"} []).map
      fun initial => (machine .relational program).run fuel initial

def answers (capacity : Nat) (rows : List Atom) (expression : Atom) :=
  (run capacity rows expression).map fun result => result.1.map CollectedAnswer.value

def finalRows (capacity : Nat) (rows : List Atom) (expression : Atom) :=
  (run capacity rows expression).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).bind fun saved => saved.2.world.state.read .self

def choose (n : Int) : Atom := call "if" [presence (row n),
  call "add-atom" [self, mark 1], call "add-atom" [self, mark 0]]
def rows : List Atom := [row 7, row 7, row 8]

#guard answers 8 rows (choose 7) == some [Effects.boolean true]
#guard finalRows 8 rows (choose 7) == some (rows ++ [mark 1])
#guard finalRows 8 rows (choose 9) == some (rows ++ [mark 0])

def copyRefused : Bool := match run 1 rows (choose 7) with
  | some ([], .suspended .allocation _) => true
  | _ => false
#guard copyRefused
#guard finalRows 1 rows (choose 7) == some rows
-- A complete miss has no copied witness; the absence branch still runs.
#guard finalRows 1 rows (choose 9) == some (rows ++ [mark 0])

def sibling : Atom := call "superpose" [.expression [choose 7, .symbol "outside"]]
#guard answers 8 rows sibling == some [Effects.boolean true, .symbol "outside"]
#guard finalRows 8 rows sibling == some (rows ++ [mark 1])

def precedingWrite : Atom := call "let" [.var "ignored", call "add-atom" [self, mark 99], choose 7]
#guard finalRows 1 rows precedingWrite == some (rows ++ [mark 99])
def paused := (run 8 rows precedingWrite 15).bind fun result => EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved => (machine .relational program).run 200 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [mark 99, mark 1])

def failingSecondWrite : Atom := call "let" [.var "ignored", call "add-atom" [self, mark 99],
  call "add-atom" [.symbol "missing-space", mark 100]]
#guard finalRows 8 rows failingSecondWrite == some (rows ++ [mark 99])

-- A visible first witness does not excuse an unsupported open candidate.
def openRows : List Atom := [row 7, call "row" [.var "stored"]]
def openGuardRefused : Bool := match run 8 openRows (choose 7) with
  | some ([], .suspended (.branch (.invoke "match" _ _)) _) => true
  | _ => false
#guard openGuardRefused

#print axioms ClosedOnceQueryFrame.fresh_read
#print axioms fresh_primitive_prefix
#print axioms literal_first_prefix
#print axioms collected_return_boundary
#print axioms conditional_prefix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards.Controls
