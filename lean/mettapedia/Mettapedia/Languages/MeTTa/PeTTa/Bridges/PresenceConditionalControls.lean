import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalRegion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuationControls

/-! Literal conditional controls: only the selected body runs, and a pause
or allocation boundary retains the condition's effects and both branches. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open CollectedOnceQuerySource.Controls (program call tagged rows before)
open PresenceGuardSource.Controls (execute answers done allocated)
open PresenceGuardContinuation.Controls (finalRows printed)

def yesRow : Atom := call "picked" [.symbol "yes"]
def noRow : Atom := call "picked" [.symbol "no"]
def insertYes : Atom := call "add-atom" [.symbol "&self", yesRow]
def insertNo : Atom := call "add-atom" [.symbol "&self", noRow]
def choose (node : Int) : Atom := source (tagged node) insertYes insertNo
def bad : Atom := call "add-atom" [.symbol "missing-space", noRow]

#guard answers 8 (choose 7) == some [Effects.boolean true]
#guard finalRows 8 (choose 7) == some (rows ++ [yesRow])
#guard answers 8 (choose 9) == some [Effects.boolean true]
#guard finalRows 8 (choose 9) == some (rows ++ [noRow])
#guard answers 8 (source (tagged 7) (.symbol "kept") bad) == some [.symbol "kept"]
#guard done 8 (source (tagged 7) (.symbol "kept") bad) == some true
#guard answers 8 (source (tagged 9) bad (.symbol "missing")) == some [.symbol "missing"]
#guard done 8 (source (tagged 9) bad (.symbol "missing")) == some true

def tested : Atom := call "if"
  [before (PresenceGuardSource.source (tagged 7)), insertYes, insertNo]
#guard printed 8 tested == some [.symbol "prefix"]
#guard finalRows 8 tested == some (rows ++ [yesRow])

def paused := (execute 8 tested 15).bind fun result => EagerDFSStreaming.Scoped.readback result.2
def resumed := paused.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 120 saved
#guard paused.map (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard resumed.map (fun result => result.1.map CollectedAnswer.value) == some [Effects.boolean true]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "prefix"]
#guard (resumed.bind fun result => EagerDFSStreaming.Scoped.readback result.2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [yesRow])

#guard allocated 1 (choose 7) == some true
#guard finalRows 1 (choose 7) == some rows
#guard printed 1 tested == some [.symbol "prefix"]
#guard finalRows 1 tested == some rows

def conditionAlternatives : Atom := call "if"
  [call "superpose" [.expression [Effects.boolean false, Effects.boolean true]], .symbol "yes", .symbol "no"]
#guard answers 8 conditionAlternatives == some [.symbol "no", .symbol "yes"]

def sibling : Atom := call "superpose" [.expression [choose 7, .symbol "outside"]]
#guard answers 8 sibling == some [Effects.boolean true, .symbol "outside"]
#guard finalRows 8 sibling == some (rows ++ [yesRow])

/-- Both branch references are part of the pending work's support. -/
theorem branch_tracks_both_alternatives :
    (.branch (.var "condition") (.var "yes") (.var "no") (.var "result") : Goal).atoms =
      [.var "condition", .var "yes", .var "no", .var "result"] := rfl

def frame (node : Int) : PresenceConditionalRegion.Frame Unit where
  scope := {frontier := []}
  parents := []
  caller := {bindings := [], goals := [], destination := .var "answer"}
  context := ()
  origins := [5]
  pending := []
  destination := .var "answer"
  request := tagged node
  yes := insertYes
  no := insertNo
  consistent := ⟨fun name => .var name, by simp [Solves]⟩

def input : ClosedOnceQueryRegion.Input :=
  ⟨Allocator.empty 8 8, ⟨NamedSpaces.Store.new rows [], [], [.symbol "already-emitted"]⟩, 120⟩

def plan (node : Int) (budget : Nat) := PresenceConditionalRegion.region "presence-conditional" program (frame node) budget

def committed (node : Int) (budget : Nat) (current : ClosedOnceQueryRegion.Input) : Option (List Atom) :=
  match (plan node budget).attempt current with
  | .declined _ => none
  | .committed result => some (result.1.map CollectedAnswer.value)

def late : ClosedOnceQueryRegion.Input :=
  {input with world := {input.world with state := NamedSpaces.Store.new [(tagged 8).pattern, (tagged 7).pattern] []}}

#guard committed 7 1 input == some [Effects.boolean true]
#guard committed 9 10 input == some [Effects.boolean true]
#guard committed 7 0 input == none
#guard committed 7 1 late == none
#guard committed 7 1 {input with sourceFuel := 0} == none
#guard committed 7 1 {input with allocator := Allocator.empty 0 0} == none
#guard committed 7 10 {input with world := {input.world with state := (NamedSpaces.Store.new
  [call "sat" [.var "stored", .grounded (.int 7)]] [])}} == none

#guard ((plan 7 1).execute late).1.map CollectedAnswer.value == [Effects.boolean true]
#guard (EagerDFSStreaming.Scoped.readback ((plan 7 1).execute late).2).map
  (fun saved => saved.2.world.output) == some [.symbol "already-emitted"]
#guard (EagerDFSStreaming.Scoped.readback ((plan 7 1).execute input).2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [yesRow])
#guard (EagerDFSStreaming.Scoped.readback ((plan 9 10).execute input).2).bind
  (fun saved => saved.2.world.state.read .self) == some (rows ++ [noRow])

theorem partial_probe_uses_the_unchanged_reference :
    (plan 7 1).execute late = (PresenceConditionalRegion.boundary program (frame 7)).reference late :=
  PresenceConditionalRegion.fallback_is_reference "presence-conditional" program (frame 7) 1 late

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource.Controls
