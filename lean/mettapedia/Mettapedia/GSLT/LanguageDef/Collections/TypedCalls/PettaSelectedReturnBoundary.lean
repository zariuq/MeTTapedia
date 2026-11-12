import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

/-!
# The selected frame's terminal obligation reaches its actual result guard

The whole host remains present. The selected frame is at position zero in the
active work and at its own scope depth; inherited frames and older alternatives
are unrestricted. Resolution and the guard service are executed at the reached
state. No successful result or completed call is an input to these laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

structure View {User : Type} (saved : CallFrame) (argument : Atom) (source : State User) where
  current : Scope User
  parents : List (Scope User)
  control : DControl
  context : Context User
  origins : List Nat
  pending : List (Work User)
  outside : List CallFrame
  scopes : source.2.scopes = current :: parents
  frontier : current.frontier = (control, context, origins) :: pending
  calls : context.calls = saved :: outside
  depth : saved.scopeDepth = source.2.scopes.length
  phase : saved.phase = .body
  terminal : control.goals = []
  returning : PettaSelectedReturnWork.Holds saved argument 0 (control, context, origins)

theorem view_of_mark {User : Type} (saved : CallFrame) (argument : Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (held : PettaSelectedReturnWork.Holds saved argument 0 (control, context, origins))
    (depth : saved.scopeDepth = source.2.scopes.length) (phase : saved.phase = .body)
    (terminal : control.goals = []) : Nonempty (View saved argument source) := by
  have original := held
  obtain ⟨above, outside, length, calls, _returning⟩ := held
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  exact ⟨⟨current, parents, control, context, origins, pending, outside, scopes, frontier, calls,
    depth, phase, terminal, original⟩⟩

theorem value_read {User : Type} {saved : CallFrame} {argument : Atom} {source : State User}
    (view : View saved argument source) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment) :
    read environment view.control.destination = read environment argument :=
  PettaSelectedReturnWork.head_observation view.returning view.terminal source.2.world environment resolved

theorem dispatch {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) :
    PettaOccurrenceOverlay.step operations .eagerValue program source =
      match resolve view.control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) source
      | some environment => consumeBody operations source view.current view.parents view.control view.context
          view.origins view.pending saved view.outside (read environment argument) := by
  cases resolved : resolve view.control.bindings with
  | none =>
      have depth : saved.scopeDepth = (view.current :: view.parents).length := by
        simpa only [view.scopes] using view.depth
      simp only [PettaOccurrenceOverlay.step, view.scopes, view.frontier, view.calls, if_pos depth,
        view.phase, view.terminal, List.isEmpty_nil, if_true, resolved]
  | some environment =>
      have actual := terminal_body_step operations .eagerValue program source view.current view.parents
        view.control view.context view.origins view.pending saved view.outside environment
        view.scopes view.frontier view.calls view.depth view.phase view.terminal resolved
      simpa only [value_read view environment resolved] using actual

theorem unresolved_run {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) (fuel : Nat) (unresolved : resolve view.control.bindings = none) :
    (PettaOccurrenceOverlay.machine operations .eagerValue program).run (fuel + 1) source =
      ([], .suspended (.source (.branch .invalidEnvironment)) source) := by
  apply Machine.run_succ_call
  change some (PettaOccurrenceOverlay.step operations .eagerValue program source) = some _
  rw [dispatch operations program source view, unresolved]

theorem missing_guard_step {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment)
    (missing : guardResult operations source.2.world saved saved.row.range
      (read environment argument) (decide (ResultGuarded saved.row.range)) = none) :
    PettaOccurrenceOverlay.step operations .eagerValue program source =
      .call (.guard saved.head saved.index saved.row.range (read environment argument)) source := by
  rw [dispatch operations program source view, resolved]
  exact PettaTypedReturnDelivery.missing_return_retains_boundary operations source view.current view.parents
    view.control view.context view.origins view.pending saved view.outside _ missing

theorem missing_guard_run {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) (fuel : Nat) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment)
    (missing : guardResult operations source.2.world saved saved.row.range
      (read environment argument) (decide (ResultGuarded saved.row.range)) = none) :
    (PettaOccurrenceOverlay.machine operations .eagerValue program).run (fuel + 1) source =
      ([], .suspended (.guard saved.head saved.index saved.row.range (read environment argument)) source) := by
  apply Machine.run_succ_call
  exact congrArg some (missing_guard_step operations program source view environment resolved missing)

theorem served_guard_exact {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment) (stores : List Store)
    (served : guardResult operations source.2.world saved saved.row.range
      (read environment argument) (decide (ResultGuarded saved.row.range)) = some stores) :
    let generated := PettaTypedReturnDelivery.continuations operations source view.control view.context
      view.origins saved view.outside stores
    PettaOccurrenceOverlay.step operations .eagerValue program source =
        .silent (install source view.current view.parents generated view.pending) ∧
      ((generated.map fun _ => read environment argument : List Atom) : Multiset Atom) =
        resultGuard (operations.declarations source.2.world) (operations.kind source.2.world)
          saved.index saved.row.range saved.store (read environment argument) ∧
      generated.map (fun item => (item.1.bindings, item.1.goals, item.1.destination, item.1.cutBoundary,
        item.2.1.calls, item.2.2)) =
      stores.zipIdx.map (fun (_, occurrence) =>
        (view.control.bindings, saved.callerGoals, saved.callerDestination, saved.callerCutBoundary,
          view.outside, view.origins ++ [occurrence])) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [dispatch operations program source view, resolved]
    exact PettaTypedReturnDelivery.served_return_step operations source view.current view.parents view.control
      view.context view.origins view.pending saved view.outside _ stores served
  · exact PettaTypedReturnDelivery.continuation_value_bag operations source view.control view.context
      view.origins saved view.outside _ stores served
  · exact PettaTypedReturnDelivery.continuations_records operations source view.control view.context
      view.origins saved view.outside stores

theorem refusal_removes_only_the_active_work {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (view : View saved argument source) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment)
    (refused : guardResult operations source.2.world saved saved.row.range
      (read environment argument) (decide (ResultGuarded saved.row.range)) = some []) :
    PettaOccurrenceOverlay.step operations .eagerValue program source =
      .silent (install source view.current view.parents [] view.pending) := by
  have exactReply := (served_guard_exact operations program source view environment resolved [] refused).1
  simpa only [PettaTypedReturnDelivery.continuations, List.zipIdx_nil, List.map_nil] using exactReply

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary
