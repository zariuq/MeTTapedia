import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Resumable
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

/-!
# Paused structural matching with two derivations of one conclusion

The source joins two distinct physical paths. One grant leaves one private
answer; a longer grant has both answers but has not established exhaustion.
Resuming the retained packet publishes exactly once with both path receipts.
Restarting and resuming have different bounded results, and an intervening
store edit invalidates this adapter's atomic snapshot boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Mettapedia.Machines.Cursor
open ProgrammableSpaceMM2Resumable ProgrammableSpaceMM2ReceiptControls

def pausedPacket? (result : ProgrammableSpaceMM2Matching.Result joinSource joinRequest) :
    Option (PacketFor joinSource joinRequest) :=
  match result with
  | .paused packet => some packet
  | .done _ => none

def packet100 : PacketFor joinSource joinRequest :=
  (pausedPacket? (ProgrammableSpaceMM2Matching.run joinSource joinRequest 100).2).get
    (by decide +kernel)

def packet150 : PacketFor joinSource joinRequest :=
  (pausedPacket? (ProgrammableSpaceMM2Matching.run joinSource joinRequest 150).2).get
    (by decide +kernel)

def start : Checkpoint := Checkpoint.start joinSource joinRequest

def checkpoint100 : Checkpoint where
  before := joinSource
  request := joinRequest
  granted := 100
  spent := 100
  packet := packet100
  reached := rfl

set_option maxRecDepth 2048 in
def checkpoint150 : Checkpoint where
  before := joinSource
  request := joinRequest
  granted := 150
  spent := 150
  packet := packet150
  reached := rfl

theorem selected : MM2MatchingBatch.SelectedFor .leaveInert joinSource joinRequest.directive := by
  unfold MM2MatchingBatch.SelectedFor
  decide +kernel

theorem first_grant_has_private_answer :
    checkpoint100.privateRows.length = 1 ∧ checkpoint100.remainingSyntax ≠ [] := by
  decide +kernel

theorem all_answers_are_not_exhaustion :
    checkpoint150.privateRows.length = 2 ∧ checkpoint150.remainingSyntax ≠ [] ∧
      ProgrammableSpaceMM2Matching.publish joinSource joinRequest
        (ProgrammableSpaceMM2Matching.run joinSource joinRequest 150).2 = none := by
  decide +kernel

theorem first_grant_is_actual_private_step :
    language.advance .leaveInert joinSource (.matching start) ⟨100, 0, 100, none⟩
      joinSource (.matching checkpoint100) :=
  Advance.pause start 100 100 packet100 selected (by rfl)

theorem next_private_grant_retains_both_paths :
    language.advance .leaveInert joinSource (.matching checkpoint100) ⟨50, 100, 150, none⟩
      joinSource (.matching checkpoint150) :=
  Advance.pause checkpoint100 50 150 packet150 selected (by rfl)

def finished : FinishedFor joinSource joinRequest := ⟨(), joinRows, []⟩

theorem continued_cursor_finishes :
    checkpoint100.resume 100 = (177, .done finished) := by rfl

theorem actual_publication :
    language.advance .leaveInert joinSource (.matching checkpoint100)
      ⟨100, 100, 177, some ⟨joinRequest, joinSource, joinRows⟩⟩
      (context ++ [reachable]) (.committed ⟨joinRequest, joinSource, joinRows⟩) := by
  have committed := Advance.commit (scope := .leaveInert) checkpoint100 100 177
    finished selected continued_cursor_finishes
  change Advance .leaveInert joinSource (.matching checkpoint100)
    ⟨100, 100, 177, some ⟨joinRequest, joinSource, joinRows⟩⟩
    (ProgrammableSpaceMM2Matching.finalize joinSource joinRequest joinRows)
    (.committed ⟨joinRequest, joinSource, joinRows⟩) at committed
  rwa [publication_preserves_support_not_derivation_multiplicity] at committed

theorem public_observation_has_both_paths :
    language.observes (.committed ⟨joinRequest, joinSource, joinRows⟩)
      ⟨context ++ [reachable], joinRows⟩ ∧
    (ProgrammableSpaceMM2.Receipt.witnessesInSourceOrder
      ⟨joinRequest, joinSource, joinRows⟩).map (List.map Prod.snd) = [[0, 1, 2], [0, 3, 4]] := by
  exact ⟨⟨publication_preserves_support_not_derivation_multiplicity.symm, rfl⟩,
    two_paths_retain_physical_positions⟩

theorem restarting_loses_bounded_completion :
    ProgrammableSpaceMM2Matching.publish joinSource joinRequest
        (start.resume 100).2 = none ∧
    ProgrammableSpaceMM2Matching.publish joinSource joinRequest
        (checkpoint100.resume 100).2 = some (context ++ [reachable]) := by
  constructor
  · rfl
  · rw [continued_cursor_finishes]
    exact congrArg some publication_preserves_support_not_derivation_multiplicity

theorem zero_budget_is_not_publication :
    ¬ ∃ (spent : Nat) (result : FinishedFor joinSource joinRequest),
      start.resume 0 = (spent, .done result) := by
  rintro ⟨spent, result, impossible⟩
  rw [Checkpoint.zero_grant] at impossible
  cases Prod.mk.inj impossible |>.2

theorem changed_store_rejects_old_cursor (receipt : Receipt) (target : List Atom)
    (after : Residual) :
    ¬ language.advance .leaveInert (.symbol "new" :: joinSource)
      (.matching checkpoint100) receipt target after := by
  apply stale_snapshot_cannot_step
  intro impossible
  have lengths := congrArg List.length impossible
  change joinSource.length + 1 = joinSource.length at lengths
  omega

/-- The integrated fine language has a genuine two-event execution:
private work followed by the same completed atomic source event. -/
theorem actual_two_grant_run :
    Relation.ReflTransGen (Transition .leaveInert)
      (joinSource, language.initial .leaveInert joinRequest joinSource)
      (context ++ [reachable], .committed ⟨joinRequest, joinSource, joinRows⟩) := by
  have first : Transition .leaveInert (joinSource, .matching start)
      (joinSource, .matching checkpoint100) := ⟨_, first_grant_is_actual_private_step⟩
  have second : Transition .leaveInert (joinSource, .matching checkpoint100)
      (context ++ [reachable], .committed ⟨joinRequest, joinSource, joinRows⟩) :=
    ⟨_, actual_publication⟩
  exact (Relation.ReflTransGen.single first).trans (Relation.ReflTransGen.single second)

theorem two_grants_have_atomic_source_meaning :
    Relation.ReflTransGen (AtomicTransition .leaveInert)
      (joinSource, .pending joinRequest)
      (context ++ [reachable], .committed ⟨joinRequest, joinSource, joinRows⟩) :=
  run_refines_atomic_run actual_two_grant_run

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls
