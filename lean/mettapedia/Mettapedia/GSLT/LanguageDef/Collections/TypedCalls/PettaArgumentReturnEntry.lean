import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSeededRegionEntry

/-!
# Produced ready operands enter the source-checked return region

The ready operand is obtained from the actual producer prefix and its frame
invariant. It is read at the reached solver before the existing exact clause
seed and body-region checkpoint theorem are used. Neither an operand witness
nor successful body evaluation is supplied as an assumption.

The clause/checkpoint adapter here still has its explicit isolated-root,
ordinary-head and unbound-output profile. This does not supply an optimized
mixed-host body implementation or its native lowering.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem ready_read_index_available {frame : CallFrame} (good : Aligned frame)
    (phase : frame.phase = .body) (index : Nat) (within : index < frame.row.parameters.length)
    (environment : Environment) :
    ∃ recipe, frame.ready[index]? = some recipe ∧
      (frame.ready.map (read environment))[index]? = some (read environment recipe) := by
  obtain ⟨recipe, present⟩ := ready_index_available good phase index within
  refine ⟨recipe, present, ?_⟩
  simp only [List.getElem?_map, present, Option.map_some]

theorem produced_checkpoint_contract {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (entryFuel : Nat) (entry : State User) (entryGood : Safe entry)
    (allocator : Allocator) (world : EagerDFS.World) (control : DControl)
    (user : User) (origins : List Nat) (saved : CallFrame)
    (produced : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run entryFuel entry).2 =
        some (PettaSeededRegionEntry.readyRoot allocator world control user origins saved))
    (environment : Environment) (resultName : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head index inspectionFuel = true)
    (within : index < saved.row.parameters.length)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (fuel : Nat) (final : State User)
    (captured : ((PettaBodyRegionTransport.machine PettaBodyRegionTransport.carriedExit operations program).run
      (fuel + 1) (PettaSeededRegionEntry.readyRoot allocator world control user origins saved)).2 =
        .suspended (.inl ()) final) :
    ∃ recipe, saved.ready[index]? = some recipe ∧
      ∃ reached, final = PettaBodyFrameEmbedding.state saved reached ∧
        Nonempty (PettaBodyCheckpoint.ExitView (fun _ : User => read environment recipe) reached) := by
  have readyGood := run_retained operations program entryFuel entry entryGood _ produced
  have aligned := active_frame
    (PettaSeededRegionEntry.readyRoot allocator world control user origins saved)
    ⟨[(control, (⟨user, [saved]⟩ : Context User), origins)], [], none⟩ []
    control (⟨user, [saved]⟩ : Context User) origins [] saved [] readyGood rfl rfl rfl
  obtain ⟨recipe, present, readPresent⟩ := ready_read_index_available aligned phase index within environment
  refine ⟨recipe, present, ?_⟩
  exact PettaSeededRegionEntry.ready_checkpoint_contract operations program allocator world control user origins
    saved environment resultName index inspectionFuel (read environment recipe) checked atCall target readPresent
    resolved unbound unknown notIO notCase phase depth fuel final captured

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
