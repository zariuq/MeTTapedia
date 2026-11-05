import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmissionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdateControls

/-!
The eight physical candidate occurrences receive completion and a final copy
receipt from the usable-capacity theorem. Smaller or unusable allocations
remain observable resource failures; the complete run is not reduced to prove
the existence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open CTLUntilScopedRound (Decoded)
open CTLUntilScopedRound.Controls (query initial_decoded)
open CTLUntilRoundAdmission.Controls (fixture_guard fixture_names_distinct fixture_admission)
open CTLUntilWordUpdate.Controls (candidateWord)
open ScopedNestedQueryExecution.Controls renaming caller → fixtureCaller,
  program → fixtureProgram, collecting → fixtureCollecting

def word : List Nat := candidateWord CTLUntilMixedStore.Controls.rows

theorem word_length : word.length = 8 := by decide +kernel

def eightState : State Unit := {fixtureCollecting with allocator := Allocator.empty 8 8}

def roundExecution (state : State Unit) := ScopedNestedQueryExecution.run fixtureProgram
  (GuardedNestedQuerySource.leaf fixtureProgram query.template Unit) query.legs
  fixtureCaller state () [9] []

theorem eight_decoded : Decoded FlatQueryRowCodec.integers query.handles eightState := initial_decoded

theorem eight_ready : GuardedQueryPackets.CollectedReady eightState := by
  intro packet member
  change packet ∈ ([] : List CollectedAnswer) at member
  cases member

theorem eight_usable : eightState.allocator.usableCount = 8 := by decide +kernel

/-- Completion and copying are constructed from the source profile, actual
initial rows and eight usable identities, not assumed from an observed run. -/
theorem eight_occurrences_complete_and_copy :
    ∃ (after : State Unit) (next : Allocator) (copies : List (Token × (Atom × List Atom))),
      (roundExecution eightState).stop = .complete after ∧
      CTLUntilWordUpdate.Update FlatQueryRowCodec.integers 10 0 query word eightState after ∧
      EagerDFS.Collection.copyOwnedAnswers? after.allocator (collectionSupport (after.cursor []).2)
        (after.scope.collected.map (fun packet => (packet.value, packet.associated))) = some (next, copies) ∧
      next.usableCount = 0 := by
  have reserve : word.length + eightState.scope.collected.length ≤ eightState.allocator.usableCount := by
    change word.length + 0 ≤ eightState.allocator.usableCount
    rw [word_length, eight_usable]
  obtain ⟨after, completed, _decoded, _stable, updated, copyAvailable⟩ :=
    round_and_copy FlatQueryRowCodec.integers 10 20 (by decide) 0 query fixture_names_distinct
      CTLUntilMixedStore.Controls.rows CTLUntilMixedStore.Controls.rows CTLUntilMixedStore.Controls.rows
      fixtureProgram fixture_guard fixtureCaller eightState () [9] [] fixture_admission eight_decoded eight_ready
      CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.atoms CTLUntilMixedStore.Controls.atoms
      rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
      rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
      rfl CTLUntilMixedStore.Controls.raw_rows_decode_without_loss reserve
  obtain ⟨next, copies, copied, charged⟩ := copyAvailable (collectionSupport (after.cursor []).2)
  refine ⟨after, next, copies, completed, updated, copied, ?_⟩
  change next.usableCount + word.length + 0 = eightState.allocator.usableCount at charged
  rw [word_length, eight_usable] at charged
  omega

def completedState (state : State Unit) : Option (State Unit) := match (roundExecution state).stop with
  | .complete after => some after
  | _ => none

def copied (state : State Unit) := (completedState state).bind fun after =>
  EagerDFS.Collection.copyOwnedAnswers? after.allocator (collectionSupport (after.cursor []).2)
    (after.scope.collected.map (fun packet => (packet.value, packet.associated)))

#guard (completedState eightState).isSome
#guard (copied eightState).map (fun result => result.1.usableCount) == some 0
#guard (completedState eightState).map (fun after => after.scope.collected.length) == some 1

-- Seven identities finish the child but leave no identity for its one packet.
def sevenState : State Unit := {eightState with allocator := Allocator.empty 7 8}
#guard (completedState sevenState).isSome
#guard (completedState sevenState).map (fun after => after.allocator.usableCount) == some 0
#guard (copied sevenState).isNone

def owned : Allocator := ⟨Array.replicate 8 ⟨0, 1⟩, 8⟩
def retired : Allocator := ⟨Array.replicate 8 ⟨8, 0⟩, 8⟩

theorem raw_slots_do_not_supply_usable_quota :
    owned.cells.size = 8 ∧ owned.usableCount = 0 ∧ retired.cells.size = 8 ∧ retired.usableCount = 0 := by
  decide +kernel

theorem occupied_or_retired_quota_is_insufficient :
    ¬word.length ≤ owned.usableCount ∧ ¬word.length ≤ retired.usableCount := by
  decide +kernel

def allocationStopped (state : State Unit) : Bool := match (roundExecution state).stop with
  | .suspended .allocation _ => true
  | _ => false

#guard allocationStopped {eightState with allocator := owned}
#guard allocationStopped {eightState with allocator := retired}

-- An empty captured frontier needs no witness or result-copy identity.
def emptyState : State Unit := {eightState with
  allocator := Allocator.empty 0 8
  world := ⟨NamedSpaces.Store.new [] [], [], []⟩}
#guard (completedState emptyState).isSome
#guard (completedState emptyState).map (fun after => after.scope.collected.length) == some 0
#guard (copied emptyState).map (fun result => result.1.usableCount) == some 0

#print axioms word_length
#print axioms eight_occurrences_complete_and_copy
#print axioms occupied_or_retired_quota_is_insufficient
#print axioms round_and_copy

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundCompletion.Controls
