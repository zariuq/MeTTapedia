import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardControls

/-! Guarded source effects: duplicate witnesses do not repeat the body;
failure does not become success, and suspended work retains its world. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open CollectedOnceQuerySource.Controls (program call tagged rows before)
open PresenceGuardSource.Controls (execute answers done allocated)

def mark : Atom := call "visited" [.symbol "entered"]
def insertion : Atom := call "add-atom" [.symbol "&self", mark]
def guarded (required : Bool) (node : Int) : Atom := source required (tagged node) insertion

def finalRows (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).bind fun saved => saved.2.world.state.read .self

def printed (capacity : Nat) (expression : Atom) (fuel : Nat := 120) :=
  (execute capacity expression fuel).bind fun result =>
    (EagerDFSStreaming.Scoped.readback result.2).map fun saved => saved.2.world.output

-- The input has two occurrences of the queried row. The body runs once.
#guard answers 8 (guarded true 7) == some [Effects.boolean true]
#guard finalRows 8 (guarded true 7) == some (rows ++ [mark])
#guard done 8 (guarded true 7) == some true
#guard answers 8 (guarded true 9) == some []
#guard finalRows 8 (guarded true 9) == some rows
#guard answers 8 (guarded false 7) == some []
#guard finalRows 8 (guarded false 7) == some rows
#guard answers 8 (guarded false 9) == some [Effects.boolean true]
#guard finalRows 8 (guarded false 9) == some (rows ++ [mark])

-- An empty answer is not evidence that the body performed no effect.
def writesThenFails : Atom := source true (tagged 7)
  (call "let" [.var "inserted", insertion, call "empty" []])
#guard answers 8 writesThenFails == some []
#guard finalRows 8 writesThenFails == some (rows ++ [mark])

-- The copied positive witness needs an identity even if the guard will fail.
#guard allocated 1 (guarded false 7) == some true
#guard finalRows 1 (guarded false 7) == some rows
#guard allocated 1 (guarded true 7) == some true
#guard printed 1 (before (guarded true 7)) == some [.symbol "prefix"]
#guard finalRows 1 (before (guarded true 7)) == some rows

def paused := (execute 8 (before (guarded true 7)) 18).bind fun result =>
  EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 saved

#guard paused.map (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [mark])
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "prefix"]

def withAlternative : Atom := call "superpose"
  [.expression [guarded true 7, call "quote" [.symbol "outside"]]]
#guard answers 8 withAlternative == some [Effects.boolean true, .symbol "outside"]
#guard finalRows 8 withAlternative == some (rows ++ [mark])

-- A later test reads the reached world, not the earlier absence snapshot.
def insertMissing : Atom := source false (tagged 9)
  (call "add-atom" [.symbol "&self", (tagged 9).pattern])
def duplicateCandidates : Atom := call "superpose" [.expression [insertMissing, insertMissing]]
#guard answers 8 duplicateCandidates == some [Effects.boolean true]
#guard finalRows 8 duplicateCandidates == some (rows ++ [(tagged 9).pattern])
#guard done 8 duplicateCandidates == some true

-- Collapsing success with failed search changes the answer stream.
#guard answers 8 (guarded true 7) != answers 8 (guarded true 9)
-- Dropping the mutation of an empty-producing continuation changes state.
#guard finalRows 8 writesThenFails != some rows

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation.Controls
