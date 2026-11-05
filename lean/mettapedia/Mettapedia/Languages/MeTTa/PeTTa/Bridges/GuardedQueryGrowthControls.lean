import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilQueryGrowth
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatchControls

/-! Completed growth, local versus public packets, aliasing writes, and the
failure controls that forbid counting a stopped prefix as a completed round. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ScopedNestedQueryExecution (Execution)
open ScopedNestedQueryExecution.Controls
open ScopedQuerySource.Controls (call number)

def after? (execution : Execution Unit) : Option (State Unit) := match execution.stop with
  | .complete after => some after
  | _ => none

def balanced (handle : NamedSpaces.Handle) (before : State Unit) (execution : Execution Unit) : Bool :=
  match after? execution with
  | some after => measure handle after.world.state + before.scope.collected.length ==
      measure handle before.world.state + after.scope.collected.length
  | none => false

-- Initial duplicates remain stored; distinct support does not count them twice.
#guard measure .self initial.world.state == 2
#guard balanced .self initial full
#guard (after? full).map (fun after => measure .self after.world.state) == some 3
#guard balanced .self collecting localRun
#guard localRun.events.isEmpty
#guard (after? localRun).map (fun after => after.scope.collected.length) == some 1
#guard balanced .self changingState changing
#guard (after? changing).map (fun after => measure .self after.world.state) == some 2

-- The codec projection preserves pair identity across formula labels.
theorem initial_pair_projection :
    (support CTLUntilMixedStore.Controls.atoms).card =
      (CTLUntilQueryGrowth.pairs CTLUntilMixedStore.Controls.rows).toFinset.card :=
  CTLUntilQueryGrowth.support_card FlatQueryRowCodec.integers CTLUntilMixedStore.Controls.rows
    (by simp [CTLUntilMixedStore.Controls.rows, CTLUntilMixedStore.Row.admitted])
#guard (CTLUntilQueryGrowth.pairs CTLUntilMixedStore.Controls.rows).toFinset.card == 2
def malformed := [call "sat" [.symbol "incomplete"]]
#guard (support malformed).card == 1
#guard (CTLUntilMixedStore.decodeRows FlatQueryRowCodec.integers malformed).isNone

-- A completed zero-growth branch can still consume witness-copy resources.
def heldInitial : State Unit := {initial with world := ⟨NamedSpaces.Store.new
  (CTLUntilMixedStore.Controls.atoms ++ [call "sat" [number 10, number 1]]) [], [], []⟩}
def held := execute legs template heldInitial
#guard completed held
#guard balanced .self heldInitial held
#guard held.events.isEmpty
#guard (after? held).map (fun after => after.scope.collected.length) == some 0
#guard (after? held).map (fun after => decide (after.allocator = heldInitial.allocator)) == some false

-- The second write may add another sat key if the fr-head condition is
-- removed: one packet then accounts for two new keys, so the law must refuse.
def twoSatTemplate : GuardedNestedQuerySource.Template := {template with
  body := {template.body with secondCode := call "sat" [.var "f", number 2]}}
def oneLeg : List NestedQuerySource.Leg := [(.self, call "fr" [.var "f", .var "round", .var "x"])]
def twoSat := execute oneLeg twoSatTemplate changingState
#guard completed twoSat
#guard twoSat.events.length == 1
#guard (after? twoSat).map (fun after => measure .self after.world.state) == some 2
#guard !balanced .self changingState twoSat

-- Raw growth does not establish preservation of the typed row format.
-- A malformed fr payload is non-sat, yet makes the final decoder refuse.
def malformedFrTemplate : GuardedNestedQuerySource.Template := {template with
  body := {template.body with secondCode := call "fr" []}}
def malformedFrRun := execute oneLeg malformedFrTemplate changingState
#guard completed malformedFrRun
#guard balanced .self changingState malformedFrRun
#guard ((after? malformedFrRun).bind (fun after => after.world.state.read .self)).bind
  (CTLUntilMixedStore.decodeRows FlatQueryRowCodec.integers) == none

-- A partial publication can increase support without a delivered packet.
def partialSaved := NamedGuardedCandidateBatch.Controls.saved NamedGuardedCandidateBatch.Controls.partialWrite
#guard NamedGuardedCandidateBatch.Controls.secondStopped
#guard partialSaved.map (fun cursor => measure (.privateSpace 0) cursor.2.world.state) == some 1
#guard partialSaved.map (fun cursor => cursor.2.scopes.head?.map (fun scope => scope.collected.length)) == some (some 0)
#guard !balanced .self initial noCopy

-- Zero for a missing measurement is not an absence/admission certificate.
#guard measure (.privateSpace 99) initial.world.state == 0
#guard !completed missing

def packetsReady (execution : Execution Unit) : Bool := match after? execution with
  | none => false
  | some after => after.scope.collected.all (fun packet => packet.value == Effects.boolean true && packet.associated.isEmpty)
#guard packetsReady full
#guard packetsReady localRun
#guard packetsReady changing
#guard packetsReady held
#guard packetsReady malformedFrRun
#guard !packetsReady noCopy

-- An older associated-work packet must not be silently cleared by a later
-- completed query. The empty-initial-collector premise is substantive.
def olderPacket : CollectedAnswer := ⟨.symbol "older", [], [77], [.var "retained"]⟩
def olderState : State Unit := {collecting with scope := {collecting.scope with collected := [olderPacket]}}
def withOlder := execute legs template olderState
#guard completed withOlder
#guard !packetsReady withOlder
#guard (after? withOlder).map (fun after => after.scope.collected.head?.map (fun packet => packet.associated)) ==
  some (some [.var "retained"])

-- Empty associated work is not copy capacity. The branch can finish with a
-- ready Boolean packet while the subsequent collector exit still suspends.
def noExitCapacity : State Unit := {changingState with
  allocator := Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator.empty 0 8
  scope := collecting.scope, parents := collecting.parents }
def beforeExit := execute oneLeg template noExitCapacity
#guard completed beforeExit
#guard balanced .self noExitCapacity beforeExit
#guard packetsReady beforeExit
def exitRefuses : Bool := match after? beforeExit with
  | none => false
  | some after => match (ScopedQuerySource.machine .relational program).step (after.cursor []) with
    | some (.call .allocation _) => true
    | _ => false
#guard exitRefuses

#print axioms leaf_balanced
#print axioms nested_packet_count
#print axioms source_packet_count
#print axioms CTLUntilQueryGrowth.completed_pair_count
#print axioms GuardedQueryPackets.completed_ready
#print axioms GuardedQueryPackets.associated_clear
#print axioms GuardedQueryPackets.values_true

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth.Controls
