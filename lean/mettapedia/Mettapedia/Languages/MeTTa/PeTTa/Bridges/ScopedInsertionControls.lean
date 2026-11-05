import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryControls

/-! Authored insertion order, duplicates, aliased binders and a mid-body pause. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number self program mark)

def firstCode : Atom := call "sat" [.var "f", .var "x"]
def secondCode : Atom := call "fr" [.var "f", .var "k", .var "x"]
def firstValue : Atom := call "sat" [.symbol "out", number 7]
def secondValue : Atom := call "fr" [.symbol "out", number 1, number 7]
def bindings : Equations := [(.var "f", .symbol "out"), (.var "x", number 7), (.var "k", number 1)]
def caller : Control := {bindings, goals := [], destination := .var "answer"}

def execute (control : Control := caller) (temporary : String := "ignored")
    (first : Atom := firstCode) (second : Atom := secondCode) (fuel : Nat := 100) :=
  (ScopedQuerySource.machine .relational program).run fuel
    (ClosedOnceQueryFrame.placed (Allocator.empty 8 8) ⟨NamedSpaces.Store.new [] [], [], []⟩
      (⟨[], [], none⟩ : CollectionScope Unit) [] (entry control "answer" temporary .self .self first second) () [2] [])

def finalRows (control : Control := caller) (temporary : String := "ignored")
    (first : Atom := firstCode) (second : Atom := secondCode) (fuel : Nat := 100) :=
  (EagerDFSStreaming.Scoped.readback (execute control temporary first second fuel).2).bind
    fun saved => saved.2.world.state.read .self

#guard (execute caller).1.map CollectedAnswer.value == [Effects.boolean true]
#guard finalRows caller == some [firstValue, secondValue]
#guard finalRows caller "ignored" secondCode firstCode == some [secondValue, firstValue]
#guard finalRows caller "ignored" secondCode firstCode != finalRows caller

-- Two writes are not two returned body answers, and equal payloads stay two rows.
#guard finalRows caller "ignored" firstCode firstCode == some [firstValue, firstValue]
#guard (execute caller "ignored" firstCode firstCode).1.map CollectedAnswer.value == [Effects.boolean true]

#guard finalRows caller "ignored" firstCode secondCode 8 == some [firstValue]
def paused := EagerDFSStreaming.Scoped.readback (execute caller "ignored" firstCode secondCode 8).2
def resumed := paused.map fun saved => (ScopedQuerySource.machine .relational program).run 100 saved
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some [firstValue, secondValue]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]

def codeValue : Atom := call "payload" [call "add-atom" [self, mark 99]]
def codeCaller : Control := {caller with bindings := bindings ++ [(.var "held", codeValue)]}
#guard finalRows codeCaller "ignored" (.var "held") secondCode == some [codeValue, secondValue]

-- A binder constrained beforehand is outside the fresh-local theorem.
def constrained : Control := {caller with bindings := bindings ++ [(.var "ignored", Effects.boolean false)]}
def refusedBeforeWrite : Bool := match (execute constrained).2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard refusedBeforeWrite
#guard finalRows constrained == some []

-- Aliasing the local binder to the output is not the admitted source shape.
-- Refusal of its second call retains the first completed insertion.
def sharedResultRefused : Bool := match (execute caller "answer").2 with
  | .suspended (.branch (.invoke "add-atom" _ _)) _ => true
  | _ => false
#guard sharedResultRefused
#guard finalRows caller "answer" == some [firstValue]

#print axioms ScopedMutationSource.unbound_after_fresh_operand
#print axioms ScopedInsertionSource.source_prefix
#print axioms source_prefix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence.Controls
