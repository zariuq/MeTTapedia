import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkMachine

/-!
# Source-produced body entries compose with every retained finite run

An actual producer prefix earns the ready operand and the freshened body
frontier. The source head certificate and the existing scope-depth admission
test then install the initial marks. No return contract on unrelated work or
inherited frames is assumed, and no successful completion is required.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack)

theorem root_source_facts {User : Type} (allocator : Allocator) (world : EagerDFS.World)
    (frontier : List (Work User)) (emptyCalls : ∀ item ∈ frontier, item.2.1.calls = []) :
    PettaArgumentProgress.Safe (allocator, ⟨world, [⟨frontier, [], none⟩]⟩) ∧
      PettaCallOrder.Invariant (allocator, ⟨world, [⟨frontier, [], none⟩]⟩) := by
  constructor
  · apply PettaContextFacts.root_frontier_safe
    intro item member frame present
    rw [emptyCalls item member] at present
    cases present
  · exact PettaCallOrder.root_frontier allocator world frontier emptyCalls

theorem source_produced_runs {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (prefixFuel : Nat) (source entry : State User)
    (argumentsGood : PettaArgumentProgress.Safe source) (ordered : PettaCallOrder.Invariant source)
    (produced : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run prefixFuel source).2 = some entry)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (saved : CallFrame) (outside : List CallFrame) (environment : Environment) (resultName : String)
    (scopes : entry.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (body : saved.phase = .body)
    (owner : saved.scopeDepth = entry.2.scopes.length)
    (parameterIndex inspectionFuel : Nat) (within : parameterIndex < saved.row.parameters.length)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head parameterIndex inspectionFuel = true) :
    ∃ recipe, saved.ready[parameterIndex]? = some recipe ∧
      let generated := equationWork program control (collectionSupport entry.2) context origins saved.head
        (saved.ready.map (read environment)) saved.callDestination [] pending.length
      let after : State User := (entry.1, ⟨entry.2.world, {current with frontier := generated ++ pending} :: parents⟩)
      let marks : List Marks :=
        ⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ ::
          parents.map PettaSelectedReturnScopes.untracked
      PettaOccurrenceOverlay.step operations .eagerValue program entry = .silent after ∧
        ∀ fuel final,
          PettaCallerReturnMachine.exitState
            ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel after).2 = some final →
          ∃ next, runMarks operations program fuel after marks = some next ∧
            Stack saved recipe next final.2.scopes ∧ PettaReturnMarkDepth.Depths saved.scopeDepth next ∧
            PettaCallOrder.Invariant final := by
  obtain ⟨recipe, available, entered, tracked⟩ := PettaSelectedReturnScopes.source_produced_entry operations program prefixFuel
    source entry argumentsGood produced current parents control context origins pending saved outside environment resultName
    scopes front calls atCall target resolved unbound unknown notIO notCase body parameterIndex inspectionFuel within checked
  refine ⟨recipe, available, entered, ?_⟩
  have entryGood := PettaCallOrder.run_retained operations program prefixFuel source ordered entry produced
  have afterGood := PettaCallOrder.step_invariant operations program entry entryGood
  rw [entered] at afterGood
  have initialDepths := PettaReturnMarkDepth.initial_depths saved parents
    (equationWork program control (collectionSupport entry.2) context origins saved.head
      (saved.ready.map (read environment)) saved.callDestination [] pending.length).length pending.length
    (by simpa only [scopes, List.length_cons] using owner)
  intro fuel final reached
  exact run_retained operations program fuel _ _ tracked initialDepths
    (afterGood _ (by simp [PettaOccurrenceBinding.retained])) body final reached

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
