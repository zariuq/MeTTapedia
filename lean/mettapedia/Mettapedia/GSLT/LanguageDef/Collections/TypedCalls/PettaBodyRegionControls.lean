import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionTransport
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures

/-! # Retained body checkpoints precede actual return checking -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionControls

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaBodyFrameEmbedding PettaBodySourceEmbedding
open PettaBodyRegionTransport
open PettaCallerReturnRunFixtures (num emptyProgram syntheticControl syntheticFrame services)

def current : Scope Unit := ⟨[(syntheticControl, ⟨(), []⟩, [4])], [], none⟩
def source : State Unit :=
  (Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator.empty 8 64,
    ⟨{state := Effects.empty, output := [num 7]}, [current]⟩)
def saved : CallFrame := syntheticFrame 1

theorem source_exit_is_recognized : exitReady saved source = true := by cbv

theorem carried_exit_is_recognized : carriedExit (state saved source) = true := by cbv

theorem source_region_pauses_before_dispatch :
    (PettaBodyRegionTransport.machine (exitReady saved) (PettaBodyFrameEmbedding.services saved services) emptyProgram).run 1 source =
      ([], .suspended (.inl ()) source) := by cbv

theorem carried_region_keeps_the_full_typed_frame :
    (PettaBodyRegionTransport.machine carriedExit services emptyProgram).run 1 (state saved source) =
      ([], .suspended (.inl ()) (state saved source)) := by cbv

theorem checkpoint_does_not_erase_the_actual_return_operation :
    PettaOccurrenceOverlay.step services .eagerValue emptyProgram (state saved source) ≠
      .publish [⟨num 1, [], [4], []⟩] source := by
  intro impossible
  cbv at impossible
  cases impossible

theorem every_budget_has_exact_packets_and_retained_state (fuel : Nat) :
    (PettaBodyRegionTransport.machine carriedExit services emptyProgram).run fuel (state saved source) =
      let result := (PettaBodyRegionTransport.machine (exitReady saved)
        (PettaBodyFrameEmbedding.services saved services) emptyProgram).run fuel source
      (result.1, PettaBodyRegionTransport.outcome saved result.2) :=
  run_transport saved services emptyProgram fuel source rfl

theorem live_body_has_a_checked_source_head :
    Bridges.ScopedReturnFunction.checksHead PettaCallerReturnRunFixtures.ordinary "keep" 0 12 = true :=
  PettaCallerReturnRunFixtures.source_body_is_checked

theorem live_body_is_not_a_terminal_checkpoint :
    exitReady saved (PettaCallerReturnRunFixtures.initial
      (PettaBodyFrameEmbedding.services saved services) PettaCallerReturnRunFixtures.ordinary) = false := by cbv

/-- The live source includes the stored-row query, effectful typed prefix
calls and the source-checked return. No closed answer list is supplied. -/
theorem live_body_transport_for_every_budget (fuel : Nat) :
    let initial := PettaCallerReturnRunFixtures.initial
      (PettaBodyFrameEmbedding.services saved services) PettaCallerReturnRunFixtures.ordinary
    (PettaBodyRegionTransport.machine carriedExit services PettaCallerReturnRunFixtures.ordinary).run fuel (state saved initial) =
      let result := (PettaBodyRegionTransport.machine (exitReady saved)
        (PettaBodyFrameEmbedding.services saved services) PettaCallerReturnRunFixtures.ordinary).run fuel initial
      (result.1, PettaBodyRegionTransport.outcome saved result.2) :=
  run_transport saved services PettaCallerReturnRunFixtures.ordinary fuel _ rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionControls
