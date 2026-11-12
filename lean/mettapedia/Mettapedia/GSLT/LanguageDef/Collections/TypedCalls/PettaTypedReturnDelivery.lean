import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun

/-!
# Earned body publications and the actual enclosing return operation

A body-region publication supplies its actual terminal control, reached
equations, world and occurrence. Reinstalling a saved typed frame at that
boundary invokes the existing return operation, before caller restoration.
Its full ordered guard reply supplies the continuation multiplicity.

This is a region-exit connection, not a proof that execution with an enclosing
frame present throughout the body agrees with the body-region execution.
The incoming call/frame embedding and native boundary lowering remain open.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes

/-- The frontier installed by the existing return operation. This is a view
of that operation's continuations, not another body evaluator. -/
def continuations {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (stores : List Store) : List (Work User) :=
  stores.zipIdx.map fun (_, occurrence) =>
    (protect services source (resumeCaller control frame) {context with calls := outside},
      {context with calls := outside}, origins ++ [occurrence])

theorem continuations_length {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (stores : List Store) :
    (continuations services source control context origins frame outside stores).length = stores.length := by
  simp [continuations]

theorem continuations_records {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (stores : List Store) :
    (continuations services source control context origins frame outside stores).map
      (fun item => (item.1.bindings, item.1.goals, item.1.destination, item.1.cutBoundary,
        item.2.1.calls, item.2.2)) =
      stores.zipIdx.map (fun (_, occurrence) =>
        (control.bindings, frame.callerGoals, frame.callerDestination, frame.callerCutBoundary,
          outside, origins ++ [occurrence])) := by
  simp [continuations, List.map_map, protect, resumeCaller]

theorem result_reply_values_exact {User : Type} (services : Services User) (world : EagerDFS.World)
    (frame : CallFrame) (value : Atom) (stores : List Store)
    (served : guardResult services world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = some stores) :
    ((stores.map fun _ => value : List Atom) : Multiset Atom) =
      resultGuard (services.declarations world) (services.kind world)
        frame.index frame.row.range frame.store value := by
  by_cases checked : ResultGuarded frame.row.range
  · rw [resultGuard, if_pos checked, ← result_guard_exact services world frame value stores checked served]
    simp
  · have singleton := unchecked_result_keeps_entry_store services world frame value checked
    rw [singleton] at served
    cases Option.some.inj served
    simp [resultGuard, checked]

theorem served_return_step {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom) (stores : List Store)
    (served : guardResult services source.2.world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = some stores) :
    consumeBody services source current parents control context origins pending frame outside value =
      .silent (install source current parents
        (continuations services source control context origins frame outside stores) pending) := by
  simp only [consumeBody, served, continuations]

theorem missing_return_retains_boundary {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (missing : guardResult services source.2.world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = none) :
    consumeBody services source current parents control context origins pending frame outside value =
      .call (.guard frame.head frame.index frame.row.range value) source := by
  simp only [consumeBody, missing]

theorem continuation_value_bag {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (value : Atom) (stores : List Store)
    (served : guardResult services source.2.world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = some stores) :
    (((continuations services source control context origins frame outside stores).map
      fun _ => value : List Atom) : Multiset Atom) =
      resultGuard (services.declarations source.2.world) (services.kind source.2.world)
        frame.index frame.row.range frame.store value := by
  have same : (continuations services source control context origins frame outside stores).map (fun _ => value) =
      stores.map (fun _ => value) := by
    simp only [List.map_const', continuations_length]
  rw [same]
  exact result_reply_values_exact services source.2.world frame value stores served

/-- The target boundary retains the reached body control and world. It changes
only the active continuation context, not the completed body computation. -/
def attach {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) : State User :=
  (source.1, ⟨source.2.world,
    {current with frontier := (control, {context with calls := frame :: outside}, origins) :: pending} :: parents⟩)

theorem attached_terminal_step {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (environment : Environment)
    (depth : frame.scopeDepth = parents.length + 1) (phase : frame.phase = .body)
    (terminal : control.goals = []) (resolved : resolve control.bindings = some environment) :
    let target := attach source current parents control context origins pending frame outside
    PettaOccurrenceOverlay.step services .eagerValue program target =
      consumeBody services target
        {current with frontier := (control, {context with calls := frame :: outside}, origins) :: pending}
        parents control {context with calls := frame :: outside} origins pending frame outside
        (read environment control.destination) := by
  dsimp only
  exact terminal_body_step services .eagerValue program _ _ parents control _ origins pending
    frame outside environment rfl rfl rfl (by simpa [attach] using depth) phase terminal resolved

theorem published_terminal_origin {User : Type} (services : Services User)
    (program : SpaceSemantics.Program) (source after : State User) (events : List CollectedAnswer)
    (bounded : Bounded source)
    (published : PettaOccurrenceOverlay.step services .eagerValue program source = .publish events after) :
    ∃ current control context pending value bindings origins environment,
      source.2.scopes = [current] ∧
      current.frontier = (control, context, origins) :: pending ∧
      control.goals = [] ∧ resolve control.bindings = some environment ∧
      context.calls = [] ∧
      events = [⟨value, bindings, origins, []⟩] ∧ bindings = control.bindings ∧
      value = read environment control.destination := by
  have owned := PettaCallerReturnPublication.publication_is_source services program source after events published
  have raw := Bridges.ScopedQueryBinding.owned_publication_is_raw .eagerValue program source after events owned
  have derived := (Source.scoped_step_iff_source .eagerValue program source bounded.valid _).mp raw
  obtain ⟨root, roots⟩ := Bridges.ScopedReturnPublication.source_publication_is_root derived bounded.valid events rfl
  obtain ⟨current, parents, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, terminal, resolved, emitted, records, output, _solved⟩ :=
    scope_published_origin .eagerValue program source after events raw
  have shape : current :: parents = [root] := scopes.symm.trans roots
  cases shape
  have noCalls : context.calls = [] := by
    cases calls : context.calls with
    | nil => rfl
    | cons frame outside =>
        have depth := root_depths source bounded root control context origins pending roots frontier frame
          (calls ▸ List.mem_cons_self)
        simp only [PettaOccurrenceOverlay.step, roots, frontier, calls, List.length_cons, List.length_nil,
          depth] at published
        cases phase : frame.phase <;>
          simp only [phase, terminal, List.isEmpty_nil, if_true, resolved] at published
        all_goals repeat' first
          | (cases published)
          | (unfold nextArgument at published)
          | (unfold consumeArgument at published)
          | (unfold consumeBody at published)
          | (split at published <;> try dsimp only at published)
  exact ⟨root, control, context, pending, value, bindings, origins, environment,
    roots, frontier, terminal, resolved, noCalls, emitted, records, output⟩

/-- Actual source-reachable body publications provide the return operation's
value and reached record. The path is a source execution, not a body-output
specification supplied as an assumption. -/
theorem reached_publication_then_return {User : Type} (inputs : User → Atom)
    (services : Services User) (program : SpaceSemantics.Program)
    (entry source after : State User) (events : List CollectedAnswer)
    (entryReturn : PettaCallerReturnMachine.Invariant inputs entry) (entryFrames : Bounded entry)
    (path : Relation.ReflTransGen (PettaOccurrenceBinding.Continues services .eagerValue program) entry source)
    (published : PettaOccurrenceOverlay.step services .eagerValue program source = .publish events after)
    (frame : CallFrame) (outside : List CallFrame) (outerPending : List (Work User))
    (depth : frame.scopeDepth = 1) (phase : frame.phase = .body) :
    ∃ current control context bodyPending origins environment value,
      source.2.scopes = [current] ∧
      current.frontier = (control, context, origins) :: bodyPending ∧ context.calls = [] ∧
      control.goals = [] ∧ resolve control.bindings = some environment ∧
      events = [⟨value, control.bindings, origins, []⟩] ∧
      value = read environment (inputs context.user) ∧
      let target := attach source current [] control context origins outerPending frame outside
      PettaOccurrenceOverlay.step services .eagerValue program target =
        consumeBody services target
          {current with frontier := (control, {context with calls := frame :: outside}, origins) :: outerPending}
          [] control {context with calls := frame :: outside} origins outerPending frame outside value := by
  have bounded := PettaFrameScopeMachine.path_keeps services program path entryFrames
  have returning := PettaCallerReturnMachine.path_invariant inputs services program path entryReturn
  obtain ⟨current, control, context, pending, value, bindings, origins, environment,
    scopes, frontier, terminal, resolved, noCalls, emitted, records, output⟩ :=
    published_terminal_origin services program source after events bounded published
  have held := PettaCallerReturnView.root_work inputs source current scopes returning.2
    (control, context, origins) (frontier ▸ List.mem_cons_self)
  have localHeld : PettaCallerReturnFrames.Frames (inputs context.user) control [] := by
    simpa only [PettaCallerReturnPhases.WorkHolds, noCalls] using held
  have actualValue := Bridges.ScopedReturnLocal.terminal_alias_observation (inputs context.user)
    (⟨source.2.world, control, context⟩ : Cursor (Context User)) localHeld.no_calls terminal environment resolved
  refine ⟨current, control, context, pending, origins, environment, value,
    scopes, frontier, noCalls, terminal, resolved, ?_, output.trans actualValue, ?_⟩
  · simpa only [records] using emitted
  · dsimp only
    simpa only [output] using attached_terminal_step services program source current [] control context origins
      outerPending frame outside environment depth phase terminal resolved

/-- The source checker and complete clause frontier earn the initial
obligations; only an actual reached publication is required subsequently. -/
theorem checked_publication_then_return {User : Type} (services : Services User)
    (program : SpaceSemantics.Program) (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : EagerDFS.World)
    (source after : State User) (events : List CollectedAnswer)
    (path : Relation.ReflTransGen (PettaOccurrenceBinding.Continues services .eagerValue program)
      (PettaCallerReturnEntry.enter services program control head arguments destination user origins allocator world) source)
    (published : PettaOccurrenceOverlay.step services .eagerValue program source = .publish events after)
    (frame : CallFrame) (outside : List CallFrame) (outerPending : List (Work User))
    (depth : frame.scopeDepth = 1) (phase : frame.phase = .body) :
    ∃ current reached context bodyPending occurrences environment value,
      source.2.scopes = [current] ∧
      current.frontier = (reached, context, occurrences) :: bodyPending ∧ context.calls = [] ∧
      reached.goals = [] ∧ resolve reached.bindings = some environment ∧
      events = [⟨value, reached.bindings, occurrences, []⟩] ∧
      value = read environment argument ∧
      let boundary := attach source current [] reached context occurrences outerPending frame outside
      PettaOccurrenceOverlay.step services .eagerValue program boundary =
        consumeBody services boundary
          {current with frontier := (reached, {context with calls := frame :: outside}, occurrences) :: outerPending}
          [] reached {context with calls := frame :: outside} occurrences outerPending frame outside value :=
  reached_publication_then_return (fun _ : User => argument) services program _ source after events
    (PettaCallerReturnEntry.checked_entry_invariant services program head index inspectionFuel checked
      control arguments argument destination actual target user origins allocator world)
    (PettaTypedBodyRun.entered_frames_bounded services program control head arguments destination user origins allocator world)
    path published frame outside outerPending depth phase

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery
