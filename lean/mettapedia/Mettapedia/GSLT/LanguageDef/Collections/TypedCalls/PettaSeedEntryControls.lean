import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeededRegionEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures

/-!
# A second protection pass is not literal source-entry equality

Both entries have a return invariant, but their reserved-name fields differ.
The full-call connection must use the actual selected controls or prove the
additional representation transport; it cannot substitute one state by reflexivity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeedEntryControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCheckpointFixtures (num program services)

def control : DControl := ⟨[], [], .var "result", ∅, 9⟩
def world : EagerDFS.World := {state := Effects.loaded (program false)}

def seeded : State Unit :=
  PettaCallerReturnEntry.seed (program false) control "keep" [num 4] (.var "result") () [] (Allocator.empty 8 64) world

def protectedEntry : State Unit :=
  PettaCallerReturnEntry.enter services (program false) control "keep" [num 4] (.var "result") () []
    (Allocator.empty 8 64) world

def reservesResult (source : State Unit) : Option Bool := do
  let current ← source.2.scopes.head?
  let item ← current.frontier.head?
  pure (decide ("result" ∈ item.1.reserved))

theorem seed_has_the_original_reservation : reservesResult seeded = some false := by cbv

theorem protected_adapter_adds_reservation : reservesResult protectedEntry = some true := by cbv

theorem exact_seed_is_not_the_protected_adapter : seeded ≠ protectedEntry := by
  intro same
  have observed := congrArg reservesResult same
  rw [seed_has_the_original_reservation, protected_adapter_adds_reservation] at observed
  cases observed

theorem source_checked_seed_earns_the_actual_return_invariant :
    PettaCallerReturnMachine.Invariant (fun _ : Unit => num 4) seeded :=
  PettaSeededRegionEntry.checked_seed_invariant (program false) "keep" 0 12
    PettaCheckpointFixtures.good_head_is_source_checked control [num 4] (num 4) (.var "result")
    rfl rfl () [] (Allocator.empty 8 64) world

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeedEntryControls
