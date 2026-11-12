import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionWorldControls

/-!
# A function wrapper delivered as an input is still held data

Source clause matching binds a fresh formal to the wrapper. The authored
body is that formal, not an authored execution marker. The quoted and fused
source schedules return the same wrapper without executing it.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBoundMarkerControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaHeldBodyControls (text)
open PettaSelectedBodyControls (caller observe)

def argument : Atom := PettaHeldBodyFusion.Controls.wrapper
def program : SpaceSemantics.Program := PettaHeldFusionWorldControls.program false (.var "x")

theorem program_balanced : SpaceSemantics.Balanced program :=
  PettaHeldFusionWorldControls.balanced false (.var "x")

def choices (fused : Bool) : List (Nat × Control) :=
  if fused then
    PettaHeldBodyFusion.frontier program caller "raw" [argument] (.var "out") []
  else
    PettaSelectedBodyFrontier.frontier program caller "raw" [argument] (.var "out") []

def initial (fused : Bool) : State Unit :=
  let frame := {PettaSelectedBodyControls.frame true with ready := [argument]}
  (Allocator.empty 8 64,
    ⟨{state := Effects.loaded program, output := [text "before"]},
      [⟨(choices fused).map (fun (occurrence, branchControl) =>
        (predicateEntry 0 branchControl, ⟨(), [frame]⟩, [3, occurrence])), [], none⟩]⟩)

theorem the_live_declaration_is_the_held_family :
    PettaSourceTypeRows.lookup [] (initial true).2.world "raw" [argument] =
      .typed [⟨[.sym "Atom"], .sym "Atom"⟩] := by cbv

theorem the_fresh_authored_formal_is_not_an_execution_marker :
    PettaHeldBodyFusion.explicitFunction
      (ClauseChoice.freshBody caller 0 (PettaSelectedBodyControls.equation (.var "x"))) = false := by cbv

theorem source_and_fusion_return_the_bound_wrapper_as_data :
    observe program (initial false) = some ([argument], [text "before"]) ∧
      observe program (initial true) = some ([argument], [text "before"]) := by cbv

theorem testing_the_readback_instead_of_the_authored_body_changes_the_mode :
    PettaHeldBodyFusion.nativeRoute false
      (ClauseChoice.freshBody caller 0 (PettaSelectedBodyControls.equation (.var "x"))) = .held ∧
      PettaHeldBodyFusion.nativeRoute false argument = .executed := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBoundMarkerControls
