import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedExecution

/-!
# Decoding an inherited boundary and executing its actual result protocol

The boundary test earns the active caller view in the full host stack. A body
handoff resolves the reached equations, then uses the original result guard.
Missing service suspends at that state; served alternatives resume the actual
caller once per guard occurrence, without replaying the body.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

structure ActiveInherited {User : Type} (source : LocalState User) where
  current : Scope (Context User)
  parents : List (Scope (Context User))
  control : DControl
  inside : Context (Context User)
  origins : List Nat
  pending : List (Work (Context User))
  frame : CallFrame
  outside : List CallFrame
  scopes : source.2.scopes = current :: parents
  frontier : current.frontier = (control, inside, origins) :: pending
  owned : inside.calls = []
  inherited : inside.user.calls = frame :: outside
  depth : frame.scopeDepth = source.2.scopes.length
  active : frame.phase = .nextArgument ∨ control.goals = []

theorem boundary_view {User : Type} (source : LocalState User) (entered : boundary source = true) :
    Nonempty (ActiveInherited source) := by
  cases scopes : source.2.scopes with
  | nil => simp [boundary, scopes] at entered
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [boundary, scopes, frontier] at entered
      | cons item pending =>
          rcases item with ⟨control, inside, origins⟩
          cases owned : inside.calls with
          | cons frame rest => simp [boundary, scopes, frontier, owned] at entered
          | nil =>
              cases inherited : inside.user.calls with
              | nil => simp [boundary, scopes, frontier, owned, inherited] at entered
              | cons frame outside =>
                  simp only [boundary, scopes, frontier, owned, inherited] at entered
                  have parts := Bool.and_eq_true_iff.mp entered
                  have depth : frame.scopeDepth = source.2.scopes.length := by
                    simpa only [scopes] using of_decide_eq_true parts.1
                  have active : frame.phase = .nextArgument ∨ control.goals = [] := by
                    cases phase : frame.phase with
                    | nextArgument => exact Or.inl rfl
                    | argument formal slot | body =>
                        exact Or.inr (List.isEmpty_iff.mp (by simpa only [phase] using parts.2))
                  exact ⟨⟨current, parents, control, inside, origins, pending, frame, outside,
                    scopes, frontier, owned, inherited, depth, active⟩⟩

theorem body_dispatch {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (source : LocalState User) (view : ActiveInherited source) (phase : view.frame.phase = .body) :
    PettaOccurrenceOverlay.step original .eagerValue program (state source) =
      match resolve view.control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) (state source)
      | some environment => consumeBody original (state source) (scope view.current) (view.parents.map scope)
          view.control (flatten view.inside) view.origins (view.pending.map work) view.frame view.outside
          (read environment view.control.destination) := by
  have scopes : (state source).2.scopes = scope view.current :: view.parents.map scope := by
    change source.2.scopes.map scope = _
    rw [view.scopes, List.map_cons]
  have frontier : (scope view.current).frontier =
      (view.control, flatten view.inside, view.origins) :: view.pending.map work := by
    change view.current.frontier.map work = _
    rw [view.frontier, List.map_cons]
    rfl
  have calls : (flatten view.inside).calls = view.frame :: view.outside := by
    simp [flatten, view.owned, view.inherited]
  have depth : view.frame.scopeDepth = view.parents.length + 1 := by
    simpa only [view.scopes, List.length_cons] using view.depth
  have terminal : view.control.goals = [] := view.active.resolve_left (by simp [phase])
  simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons,
    List.length_map, if_pos depth, phase, terminal, List.isEmpty_nil, if_true]
  rfl

theorem unresolved_body_handoff {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) (view : ActiveInherited source)
    (phase : view.frame.phase = .body) (unresolved : resolve view.control.bindings = none) :
    execute original program (fuel + 1) source =
      ([], .suspended (.source (.branch .invalidEnvironment)) (state source)) := by
  rw [execute_eq_actual]
  apply Machine.run_succ_call
  change some (PettaOccurrenceOverlay.step original .eagerValue program (state source)) = some _
  apply congrArg some
  rw [body_dispatch original program source view phase, unresolved]

theorem missing_body_guard_handoff {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) (view : ActiveInherited source)
    (phase : view.frame.phase = .body) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment)
    (missing : guardResult original source.2.world view.frame view.frame.row.range
      (read environment view.control.destination) (decide (ResultGuarded view.frame.row.range)) = none) :
    execute original program (fuel + 1) source =
      ([], .suspended (.guard view.frame.head view.frame.index view.frame.row.range
        (read environment view.control.destination)) (state source)) := by
  rw [execute_eq_actual]
  apply Machine.run_succ_call
  change some (PettaOccurrenceOverlay.step original .eagerValue program (state source)) = some _
  apply congrArg some
  rw [body_dispatch original program source view phase, resolved]
  exact PettaTypedReturnDelivery.missing_return_retains_boundary original (state source) (scope view.current)
    (view.parents.map scope) view.control (flatten view.inside) view.origins (view.pending.map work)
    view.frame view.outside _ missing

theorem served_body_guard_handoff {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) (view : ActiveInherited source)
    (phase : view.frame.phase = .body) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment) (stores : List Store)
    (served : guardResult original source.2.world view.frame view.frame.row.range
      (read environment view.control.destination) (decide (ResultGuarded view.frame.row.range)) = some stores) :
    let generated := PettaTypedReturnDelivery.continuations original (state source) view.control
      (flatten view.inside) view.origins view.frame view.outside stores
    execute original program (fuel + 1) source =
        (PettaOccurrenceOverlay.machine original .eagerValue program).run fuel
          (install (state source) (scope view.current) (view.parents.map scope) generated (view.pending.map work)) ∧
      generated.length = Multiset.card (resultGuard (original.declarations source.2.world) (original.kind source.2.world)
        view.frame.index view.frame.row.range view.frame.store (read environment view.control.destination)) := by
  dsimp only
  constructor
  · rw [execute_eq_actual]
    apply Machine.run_succ_silent
    change some (PettaOccurrenceOverlay.step original .eagerValue program (state source)) = some _
    apply congrArg some
    rw [body_dispatch original program source view phase, resolved]
    exact PettaTypedReturnDelivery.served_return_step original (state source) (scope view.current)
      (view.parents.map scope) view.control (flatten view.inside) view.origins (view.pending.map work)
      view.frame view.outside _ stores served
  · have bag := PettaTypedReturnDelivery.continuation_value_bag original (state source) view.control
      (flatten view.inside) view.origins view.frame view.outside _ stores served
    have count := congrArg Multiset.card bag
    simpa only [Multiset.coe_card, List.length_map, (state_world source).2] using count

theorem charging_handoff_a_source_step_loses_the_request {User : Type} (original : Services User)
    (program : SpaceSemantics.Program) (source : LocalState User) (view : ActiveInherited source)
    (phase : view.frame.phase = .body) (environment : Environment)
    (resolved : resolve view.control.bindings = some environment)
    (missing : guardResult original source.2.world view.frame view.frame.row.range
      (read environment view.control.destination) (decide (ResultGuarded view.frame.row.range)) = none) :
    execute original program 0 source ≠ execute original program 1 source := by
  rw [missing_body_guard_handoff original program 0 source view phase environment resolved missing]
  intro same
  have outcomes := congrArg Prod.snd same
  cases outcomes

theorem actual_run_retained_bounds {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : State User) (valid : PettaFrameScopes.Bounded source) :
    ∀ final, PettaCallerReturnMachine.exitState
        ((PettaOccurrenceOverlay.machine original .eagerValue program).run fuel source).2 = some final →
      PettaFrameScopes.Bounded final := by
  induction fuel generalizing source with
  | zero =>
      intro final same
      cases Option.some.inj same
      exact valid
  | succ fuel ih =>
      have kept := PettaFrameScopeMachine.step_keeps original program source valid
      cases advanced : PettaOccurrenceOverlay.step original .eagerValue program source with
      | silent next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | publish events next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | finish final =>
          rw [advanced] at kept
          intro reached same
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at same
          cases Option.some.inj same
          exact kept final (by simp [PettaOccurrenceBinding.retained])
      | call request final =>
          rw [advanced] at kept
          intro reached same
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at same
          cases Option.some.inj same
          exact kept final (by simp [PettaOccurrenceBinding.retained])
      | fail events =>
          intro reached impossible
          simp [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at impossible

theorem execute_retained_bounds {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) (valid : PettaFrameScopes.Bounded (state source)) :
    ∀ final, PettaCallerReturnMachine.exitState (execute original program fuel source).2 = some final →
      PettaFrameScopes.Bounded final := by
  rw [execute_eq_actual]
  exact actual_run_retained_bounds original program fuel (state source) valid

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
