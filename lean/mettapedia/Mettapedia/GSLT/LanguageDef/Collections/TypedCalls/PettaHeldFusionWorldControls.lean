import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionControls

/-!
# Held-return fusion with declarations in the actual loaded world

The selected-body controls are strengthened here with an explicitly balanced
program layout. Its loaded store supplies the literal declaration observed
by the live type service as well as the static clause frontier.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionWorldControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay
open PettaHeldBodyControls (num text effectBody emptyBody)
open PettaSelectedBodyControls (caller placedChoices observe)

def program (duplicate : Bool) (body : Atom) : SpaceSemantics.Program :=
  {PettaSelectedBodyControls.program true duplicate false body with
    layout := List.replicate (if duplicate then 2 else 1) .equation ++ [.declaration]}

theorem balanced (duplicate : Bool) (body : Atom) : SpaceSemantics.Balanced (program duplicate body) := by
  cases duplicate <;> simp [program, SpaceSemantics.Balanced, PettaSelectedBodyControls.program,
    PettaSelectedBodyControls.equation, PettaSelectedBodyControls.declaration]

def world (duplicate : Bool) (body : Atom) : EagerDFS.World :=
  {state := Effects.loaded (program duplicate body), output := [text "before"]}

theorem the_live_service_reads_the_written_held_signature :
    PettaSourceTypeRows.lookup [] (world false effectBody) "raw" [num 4] =
      .typed [⟨[.sym "Atom"], .sym "Atom"⟩] := by cbv

def selected (duplicate : Bool) (body : Atom) : List (Nat × EagerDFS.Destination.Control) :=
  PettaHeldBodyFusion.frontier (program duplicate body) caller "raw" [num 4] (.var "out") []

def initial (duplicate : Bool) (body : Atom) : State Unit :=
  placedChoices (program duplicate body) true (selected duplicate body)

theorem coherent_world_keeps_both_duplicate_returns_without_their_effects :
    observe (program true effectBody) (initial true effectBody) =
      some ([effectBody, effectBody], [text "before"]) := by cbv

theorem coherent_world_keeps_empty_syntax_as_one_return :
    observe (program false emptyBody) (initial false emptyBody) = some ([emptyBody], [text "before"]) := by cbv

theorem a_coherent_world_does_not_make_the_explicit_escape_plain_holding :
    selected false PettaHeldBodyFusion.Controls.wrapper = [] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaHeldFusionWorldControls
