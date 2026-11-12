import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentReturnEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnReadRecipe

/-!
# Source-produced frame entry inside the complete host

Argument alignment supplies the selected frame's operand recipe. The actual
source equation operation then supplies its freshened body alternatives and
their return-alias contracts. Other frontier work, inherited calls and
collection parents remain in place; none is required to return this operand.

This is the equation-entry boundary, not yet preservation of the selective
contract through an optimized body or a native compiler realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry

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
    (checked : Bridges.ScopedReturnFunction.checksHead program frame.head index inspectionFuel = true)
    (aligned : Aligned frame) (phase : frame.phase = .body)
    (within : index < frame.row.parameters.length) (target : control.destination = frame.callDestination)
    (resolved : resolve control.bindings = some environment) :
    ∃ recipe, frame.ready[index]? = some recipe ∧
      ∀ item ∈ equationWork program control boundary context origins frame.head
          (frame.ready.map (read environment)) frame.callDestination [] retained,
        item.2.1 = context ∧ Bridges.ScopedReturnLocal.AliasHolds recipe item.1 := by
  obtain ⟨recipe, present, readPresent⟩ := ready_read_index_available aligned phase index within environment
  refine ⟨recipe, present, ?_⟩
  intro item member
  have extended := Bridges.ScopedReturnReadRecipe.equation_work_extends program control boundary context origins
    frame.head (frame.ready.map (read environment)) frame.callDestination [] retained item member
  obtain ⟨choice, selected, rfl⟩ := List.mem_map.mp member
  refine ⟨rfl, ?_⟩
  apply Bridges.ScopedReturnReadRecipe.original_recipe_alias control.bindings environment resolved _ recipe extended
  exact Bridges.ScopedReturnFunction.checked_frontier_aliases program frame.head index inspectionFuel checked
    (protectControl control boundary) (frame.ready.map (read environment)) (read environment recipe)
    frame.callDestination readPresent target choice selected

theorem actual_equation_entry {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : EagerDFS.World)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (environment : Environment) (resultName : String)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (atCall : control.goals = [.invoke frame.head frame.ready frame.callDestination])
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment frame.callDestination = .var resultName)
    (unknown : StdLib.known frame.head = false) (notIO : Eval.ioHead frame.head = false)
    (notCase : frame.head ≠ "case")
    (declared : program.equations.any (·.head == frame.head) = true) (phase : frame.phase = .body) :
    let before : State User := (allocator, ⟨world, current :: parents⟩)
    let children := equationWork program control (collectionSupport before.2) context origins frame.head
      (frame.ready.map (read environment)) frame.callDestination [] pending.length
    PettaOccurrenceOverlay.step operations .eagerValue program before =
      .silent (allocator, ⟨world, {current with frontier := children ++ pending} :: parents⟩) := by
  dsimp only
  let before : State User := (allocator, ⟨world, current :: parents⟩)
  let selectedControl := protectControl control (collectionSupport before.2)
  let selected := ClauseChoice.choices program selectedControl frame.head (frame.ready.map (read environment))
    frame.callDestination []
  let children := equationWork program control (collectionSupport before.2) context origins frame.head
    (frame.ready.map (read environment)) frame.callDestination [] pending.length
  let after : State User := (allocator, ⟨world, {current with frontier := children ++ pending} :: parents⟩)
  have notParse : frame.head ≠ "parse" := by
    intro same
    simp [same, StdLib.known] at unknown
  have notMatch : frame.head ≠ "match" := by
    intro same
    simp [same, StdLib.known] at unknown
  have entered := Bridges.ScopedQuerySource.Equations.enter .eagerValue program allocator world current parents
    control context origins pending frame.head frame.ready frame.callDestination [] environment resultName selected
    frontier atCall resolved unbound notParse unknown notIO declared
    ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)
  have base : Bridges.ScopedQuerySource.step .eagerValue program before = .silent after := by
    apply Option.some.inj
    simpa only [Bridges.ScopedQuerySource.machine, before, after, children, equationWork,
      selected, selectedControl] using entered
  have noEntry : Bridges.ScopedCaseSource.entryStep before = none := by
    simp [Bridges.ScopedCaseSource.entryStep, before, frontier, atCall]
  have noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern before = none := by
    simp only [Bridges.ScopedCaseSource.readyStep, before, frontier, atCall]
    split
    next key rows destination older same =>
      have headEq : frame.head = "case" := by
        simp only [List.cons.injEq, Goal.invoke.injEq] at same
        tauto
      exact (notCase headEq).elim
    next => rfl
  have noOwnership : Bridges.ScopedQuerySource.ownershipStep program before = none := by
    simp [Bridges.ScopedQuerySource.ownershipStep, before, frontier, atCall, notMatch]
  have owned := Bridges.ScopedQuerySource.owned_keeps_completed_step .eagerValue program before after
    noOwnership noEntry noCase base
  have delegated : delegate operations .eagerValue program before current parents
      control context origins pending = .silent after := by
    simpa only [delegate, before, frontier, atCall, liftSource] using congrArg liftSource owned
  by_cases depth : frame.scopeDepth = parents.length + 1
  · simpa only [PettaOccurrenceOverlay.step, before, frontier, calls, List.length_cons,
      if_pos depth, phase, atCall, List.isEmpty_cons, Bool.false_eq_true, if_false] using delegated
  · simpa only [PettaOccurrenceOverlay.step, before, frontier, calls, List.length_cons,
      if_neg depth] using delegated

/-- A finite producer prefix earns the operand used by each actual selected
body. The complete host's pending work and collection parents are untouched
by this entry; their return behavior is not an assumption. -/
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
    (checked : Bridges.ScopedReturnFunction.checksHead program frame.head index inspectionFuel = true) :
    ∃ recipe, frame.ready[index]? = some recipe ∧
      let children := equationWork program control (collectionSupport final.2) context origins frame.head
        (frame.ready.map (read environment)) frame.callDestination [] pending.length
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        .silent (final.1, ⟨final.2.world, {current with frontier := children ++ pending} :: parents⟩) ∧
      ∀ item ∈ children, item.2.1 = context ∧
        Bridges.ScopedReturnLocal.AliasHolds recipe item.1 := by
  have aligned := active_frame final current parents control context origins pending frame outside
    (run_retained operations program fuel source good final reached) scopes frontier calls
  obtain ⟨recipe, present, contracts⟩ := equation_work_aliases program control (collectionSupport final.2)
    context origins frame environment index inspectionFuel pending.length checked aligned phase within target resolved
  refine ⟨recipe, present, ?_, contracts⟩
  rcases final with ⟨allocator, world, stack⟩
  change stack = current :: parents at scopes
  subst stack
  exact actual_equation_entry operations program allocator world current parents
    control context origins pending frame outside environment resultName frontier calls atCall resolved unbound
    unknown notIO notCase
    (PettaSeededRegionEntry.source_check_derives_equation_presence program frame.head index inspectionFuel checked) phase

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry
