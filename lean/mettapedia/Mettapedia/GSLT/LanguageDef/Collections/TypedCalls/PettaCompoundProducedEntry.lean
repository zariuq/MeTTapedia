import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnFunction

/-!
# Compound return contracts earned at actual full-host body entry

The source checker covers the named head's complete equation table. Actual
argument production earns the ready operand; actual equation selection earns
the common fresh recipe and body. Other work and inherited frames remain
unrestricted. This is entry evidence, not an optimized-body adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundProducedEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaArgumentProgress

theorem equation_work_aliases {User : Type} (program : SpaceSemantics.Program)
    (control : DControl) (boundary : Finset String) (context : Context User)
    (origins : List Nat) (frame : CallFrame) (environment : Environment)
    (index inspectionFuel retained : Nat)
    (checked : Bridges.DestinationDataReturnFunction.checksHead program frame.head index inspectionFuel = true)
    (aligned : Aligned frame) (phase : frame.phase = .body)
    (within : index < frame.row.parameters.length) (target : control.destination = frame.callDestination)
    (resolved : resolve control.bindings = some environment) :
    ∃ recipe, frame.ready[index]? = some recipe ∧
      ∀ item ∈ equationWork program control boundary context origins frame.head
          (frame.ready.map (read environment)) frame.callDestination [] retained,
        item.2.1 = context ∧ Bridges.DestinationDataReturnState.AliasHolds program recipe item.1 := by
  obtain ⟨recipe, present, readPresent⟩ := ready_read_index_available aligned phase index within environment
  refine ⟨recipe, present, ?_⟩
  intro item member
  have extended := Bridges.ScopedReturnReadRecipe.equation_work_extends program control boundary context origins
    frame.head (frame.ready.map (read environment)) frame.callDestination [] retained item member
  obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
  refine ⟨rfl, ?_⟩
  apply Bridges.DestinationDataReturnState.original_recipe_alias control.bindings environment resolved _ recipe extended
  exact Bridges.DestinationDataReturnFunction.checked_frontier_aliases program frame.head index inspectionFuel retained checked
    (protectControl control boundary) (frame.ready.map (read environment)) (read environment recipe)
    frame.callDestination readPresent target choice selected

theorem produced_frame_entry {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source final : State User) (good : Safe source)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (environment : Environment) (resultName : String)
    (scopes : final.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (atCall : control.goals = [.invoke frame.head frame.ready frame.callDestination])
    (target : control.destination = frame.callDestination)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment frame.callDestination = .var resultName)
    (unknown : StdLib.known frame.head = false) (notIO : Eval.ioHead frame.head = false)
    (notCase : frame.head ≠ "case") (phase : frame.phase = .body)
    (index inspectionFuel : Nat) (within : index < frame.row.parameters.length)
    (checked : Bridges.DestinationDataReturnFunction.checksHead program frame.head index inspectionFuel = true) :
    ∃ recipe, frame.ready[index]? = some recipe ∧
      let children := equationWork program control (collectionSupport final.2) context origins frame.head
        (frame.ready.map (read environment)) frame.callDestination [] pending.length
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        .silent (final.1, ⟨final.2.world, {current with frontier := children ++ pending} :: parents⟩) ∧
      ∀ item ∈ children, item.2.1 = context ∧ Bridges.DestinationDataReturnState.AliasHolds program recipe item.1 := by
  have aligned := active_frame final current parents control context origins pending frame outside
    (run_retained operations program fuel source good final reached) scopes frontier calls
  obtain ⟨recipe, present, contracts⟩ := equation_work_aliases program control (collectionSupport final.2)
    context origins frame environment index inspectionFuel pending.length checked aligned phase within target resolved
  refine ⟨recipe, present, ?_, contracts⟩
  rcases final with ⟨allocator, world, stack⟩
  change stack = current :: parents at scopes
  subst stack
  exact PettaProducedFrameEntry.actual_equation_entry operations program allocator world current parents
    control context origins pending frame outside environment resultName frontier calls atCall resolved unbound
    unknown notIO notCase (Bridges.DestinationDataReturnFunction.checked_has_head program frame.head index inspectionFuel checked) phase

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundProducedEntry
