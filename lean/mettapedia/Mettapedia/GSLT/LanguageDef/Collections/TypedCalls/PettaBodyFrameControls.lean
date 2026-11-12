import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameEmbedding
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls

/-!
# Saved-frame freshness and actual typed-step controls

These typed-phase states isolate the frame embedding; they are not claimed
to be a complete enclosing-call execution. The negative control removes the
saved frame's name reservation and changes the actual next argument slot.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaBodyFrameEmbedding
open PettaTypedReturnControls (num)

def saved : CallFrame :=
  ⟨"outer", ⟨[.sym "Atom"], .sym "Atom"⟩, [], [], 1, [], [], .var "####", 0,
    .var "out", 1, .body⟩

def inner : CallFrame :=
  ⟨"inner", ⟨[.sym "Number"], .sym "Number"⟩, [(.sym "Number", num 7)], [], 0, [], [],
    .var "out", 0, .var "out", 1, .nextArgument⟩

def control : DControl := ⟨[], [], .var "out", ∅, 0⟩
def inside : Context Unit := ⟨(), [inner]⟩
def current : Scope Unit := ⟨[(control, inside, [2])], [], none⟩

def program : SpaceSemantics.Program where
  equations := [⟨"inner", [.var "x"], .var "x"⟩]
  declarations := [PettaSourceTypeRows.declaration "inner" (arrow [.sym "Number"] (.sym "Number"))]
  layout := [.equation, .declaration]

def source : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded program, output := [num 5]}, [current]⟩)

def original : Services Unit := PettaSourceTypeServices.services []

theorem actual_typed_phase_retains_the_enclosing_frame :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      action saved (PettaOccurrenceOverlay.step (services saved original) .eagerValue program source) := by
  exact active_typed_step_commutes saved original program source current [] control inside [2] [] inner []
    rfl rfl rfl rfl (.inl rfl)

def nextDestination : Step Unit → Option Atom
  | .silent next => do
      let root ← next.2.scopes.head?
      let item ← root.frontier.head?
      pure item.1.destination
  | _ => none

theorem omitting_the_saved_reservation_changes_the_actual_slot :
    nextDestination (PettaOccurrenceOverlay.step original .eagerValue program (state saved source)) ≠
      nextDestination (action saved (PettaOccurrenceOverlay.step original .eagerValue program source)) := by
  cbv
  decide

theorem unreserved_slot_reuses_the_saved_caller_name :
    nextDestination (action saved (PettaOccurrenceOverlay.step original .eagerValue program source)) =
      some saved.callerDestination := by cbv

theorem carried_frame_slot_avoids_the_saved_caller_name :
    nextDestination (PettaOccurrenceOverlay.step original .eagerValue program (state saved source)) ≠
      some saved.callerDestination := by
  cbv
  decide

theorem reserved_slot_is_exactly_the_carried_frame_slot :
    nextDestination (PettaOccurrenceOverlay.step original .eagerValue program (state saved source)) =
      nextDestination (action saved
        (PettaOccurrenceOverlay.step (services saved original) .eagerValue program source)) :=
  congrArg nextDestination actual_typed_phase_retains_the_enclosing_frame

theorem embedding_keeps_existing_effects_and_bindings :
    (state saved source).2.world.output = [num 5] ∧
      ((state saved source).2.scopes.head?.bind fun root => root.frontier.head?).map
        (fun item => (item.1.bindings, item.2.2)) = some ([], [2]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameControls
