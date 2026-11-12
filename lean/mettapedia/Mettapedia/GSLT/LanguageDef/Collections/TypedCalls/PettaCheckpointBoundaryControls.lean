import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures

/-!
# A terminal checkpoint does not certify solvable bindings

The deliberately inconsistent record below is synthetic, not claimed to be
reachable from checked source entry. It isolates why the terminal decoder
must still execute the solver rather than treat the checkpoint as an answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointBoundaryControls

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaBodyFrameEmbedding PettaBodySourceEmbedding PettaBodyRegionTransport
open PettaCheckpointFixtures (num services)

def program : SpaceSemantics.Program := {equations := [], declarations := []}
def control : DControl := ⟨[(num 0, num 1)], [], .var "result", ∅, 0⟩
def saved : CallFrame := ⟨"closed", ⟨[], .sym "Number"⟩, [], [], 0, [], [], .var "result", 0,
  .var "result", 1, .body⟩
def malformed : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.empty, output := [num 7]},
    [⟨[(control, ⟨(), []⟩, [])], [], none⟩]⟩)

theorem terminal_flag_alone_accepts_this_checkpoint : exitReady saved malformed = true := by cbv

theorem solver_still_rejects_its_bindings : resolve control.bindings = none := by cbv

theorem actual_dispatch_requests_resolution_failure :
    PettaOccurrenceOverlay.step services .eagerValue program (state saved malformed) =
      .call (.source (.branch .invalidEnvironment)) (state saved malformed) := by cbv

theorem the_checkpoint_preserves_the_unresolved_state :
    (PettaBodyRegionTransport.machine carriedExit services program).run 1 (state saved malformed) =
      ([], .suspended (.inl ()) (state saved malformed)) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointBoundaryControls
