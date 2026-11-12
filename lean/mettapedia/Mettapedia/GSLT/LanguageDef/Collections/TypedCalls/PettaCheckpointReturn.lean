import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyCheckpoint
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery

/-!
# A retained, source-earned checkpoint dispatches the actual result guard

The carried checkpoint is obtained from the actual region run, not made by
replacing a computed body value. Its reached return equation selects the
guard input. Missing service retains that exact state; served alternatives
restore the caller with the exact protocol multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaBodyFrameEmbedding PettaBodySourceEmbedding
open PettaBodyRegionTransport PettaBodyCheckpoint

theorem carried_checkpoint_view {User : Type} (inputs : User → Atom) (saved : CallFrame)
    (original : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source final : State User) (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (valid : PettaCallerReturnMachine.Invariant inputs source) (bounded : PettaFrameScopes.Bounded source)
    (captured : ((PettaBodyRegionTransport.machine carriedExit original program).run fuel (state saved source)).2 =
      .suspended (.inl ()) final) :
    ∃ reached, final = state saved reached ∧ Nonempty (ExitView inputs reached) := by
  have related := congrArg
    (fun result : List CollectedAnswer × Outcome (State User) (State User) RegionRequest => result.2)
    (run_transport saved original program fuel source phase)
  rw [captured] at related
  cases status : ((PettaBodyRegionTransport.machine (exitReady saved) (services saved original) program).run fuel source).2 with
  | finished reached | stuck reached | exhausted reached | faulted =>
      simp only [status, PettaBodyRegionTransport.outcome] at related
      cases related
  | suspended request reached =>
      simp only [status, PettaBodyRegionTransport.outcome] at related
      cases request with
      | inr request => cases (Outcome.suspended.inj related).1
      | inl marker =>
          cases marker
          have preserved := checkpoint_invariant inputs (exitReady saved) (services saved original) program
            fuel source reached valid bounded status
          exact ⟨reached, (Outcome.suspended.inj related).2,
            exit_view inputs saved reached depth preserved.1 preserved.2.1⟩

/-- Actual source checking and complete clause selection earn entry to the
carried region. The only completion premise is the observed checkpoint. -/
theorem checked_carried_checkpoint {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : EagerDFS.World)
    (phase : saved.phase = .body) (depth : saved.scopeDepth = 1) (fuel : Nat) (final : State User)
    (captured : ((PettaBodyRegionTransport.machine carriedExit original program).run fuel
      (state saved (PettaCallerReturnEntry.enter (services saved original) program control head arguments destination
        user origins allocator world))).2 = .suspended (.inl ()) final) :
    ∃ reached, final = state saved reached ∧ Nonempty (ExitView (fun _ : User => argument) reached) := by
  exact carried_checkpoint_view (fun _ : User => argument) saved original program fuel _ final phase depth
    (PettaCallerReturnEntry.checked_entry_invariant (services saved original) program head index inspectionFuel checked
      control arguments argument destination actual target user origins allocator world)
    (PettaTypedBodyRun.entered_frames_bounded (services saved original) program control head arguments destination
      user origins allocator world) captured

theorem guard_dispatch {User : Type} {inputs : User → Atom} (saved : CallFrame)
    (original : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : ExitView inputs source) (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (environment : Environment) (resolved : resolve view.control.bindings = some environment) :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      consumeBody original (state saved source) (scope saved view.current) [] view.control
        (context saved view.context) view.origins (view.pending.map (work saved)) saved []
        (read environment (inputs view.context.user)) := by
  have scopes : (state saved source).2.scopes = [scope saved view.current] := by
    simp [state, view.root]
  have frontier : (scope saved view.current).frontier =
      (view.control, context saved view.context, view.origins) :: view.pending.map (work saved) := by
    simp [scope, view.frontier, work]
  have calls : (context saved view.context).calls = [saved] := by simp [context, view.noCalls]
  have ownedDepth : saved.scopeDepth = (state saved source).2.scopes.length := by simp [scopes, depth]
  have actual := terminal_body_step original .eagerValue program (state saved source) (scope saved view.current) []
    view.control (context saved view.context) view.origins (view.pending.map (work saved)) saved [] environment
    scopes frontier calls ownedDepth phase view.terminal resolved
  simpa only [view.reads environment resolved] using actual

theorem missing_guard_retains_reached_state {User : Type} {inputs : User → Atom} (saved : CallFrame)
    (original : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : ExitView inputs source) (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (environment : Environment) (resolved : resolve view.control.bindings = some environment)
    (missing : guardResult original source.2.world saved saved.row.range
      (read environment (inputs view.context.user)) (decide (ResultGuarded saved.row.range)) = none) :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      .call (.guard saved.head saved.index saved.row.range (read environment (inputs view.context.user))) (state saved source) := by
  rw [guard_dispatch saved original program source view phase depth environment resolved]
  exact PettaTypedReturnDelivery.missing_return_retains_boundary original (state saved source)
    (scope saved view.current) [] view.control (context saved view.context) view.origins
    (view.pending.map (work saved)) saved [] _ missing

/-- Resolution is performed by the existing solver. An unresolved checkpoint
does not become an answer or an invented successful guard. -/
theorem terminal_dispatch {User : Type} {inputs : User → Atom} (saved : CallFrame)
    (original : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : ExitView inputs source) (phase : saved.phase = .body) (depth : saved.scopeDepth = 1) :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      match resolve view.control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) (state saved source)
      | some environment => consumeBody original (state saved source) (scope saved view.current) [] view.control
          (context saved view.context) view.origins (view.pending.map (work saved)) saved []
          (read environment (inputs view.context.user)) := by
  cases resolved : resolve view.control.bindings with
  | some environment => exact guard_dispatch saved original program source view phase depth environment resolved
  | none =>
      have scopes : (state saved source).2.scopes = [scope saved view.current] := by simp [state, view.root]
      have frontier : (scope saved view.current).frontier =
          (view.control, context saved view.context, view.origins) :: view.pending.map (work saved) := by
        simp [scope, view.frontier, work]
      have calls : (context saved view.context).calls = [saved] := by simp [context, view.noCalls]
      simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons, List.length_nil,
        depth, if_true, phase, view.terminal, List.isEmpty_nil, resolved]

theorem served_guard_exact {User : Type} {inputs : User → Atom} (saved : CallFrame)
    (original : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : ExitView inputs source) (phase : saved.phase = .body) (depth : saved.scopeDepth = 1)
    (environment : Environment) (resolved : resolve view.control.bindings = some environment) (stores : List Store)
    (served : guardResult original source.2.world saved saved.row.range
      (read environment (inputs view.context.user)) (decide (ResultGuarded saved.row.range)) = some stores) :
    let target := state saved source
    let generated := PettaTypedReturnDelivery.continuations original target view.control
      (context saved view.context) view.origins saved [] stores
    PettaOccurrenceOverlay.step original .eagerValue program target =
        .silent (install target (scope saved view.current) [] generated (view.pending.map (work saved))) ∧
      generated.length = Multiset.card (resultGuard (original.declarations source.2.world) (original.kind source.2.world)
        saved.index saved.row.range saved.store (read environment (inputs view.context.user))) := by
  dsimp only
  constructor
  · rw [guard_dispatch saved original program source view phase depth environment resolved]
    exact PettaTypedReturnDelivery.served_return_step original (state saved source) (scope saved view.current) []
      view.control (context saved view.context) view.origins (view.pending.map (work saved)) saved [] _ stores served
  · have exactBag := PettaTypedReturnDelivery.continuation_value_bag original (state saved source)
      view.control (context saved view.context) view.origins saved [] _ stores served
    have exactCount := congrArg Multiset.card exactBag
    simpa only [Multiset.coe_card, List.length_map, PettaBodyFrameEmbedding.state] using exactCount

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn
