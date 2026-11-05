import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution

/-!
# Checked removal leaves with actual packet publication

Admission reads the current source frame and target. Accepted execution
computes the erasure, prepares the written handle, performs the mutation and
records one true packet through the actual terminal source step. Collector
copying is separate: this leaf spends no allocator identities. Refusal keeps
the exact entrance, before any source effect is consumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ScopedNestedQueryExecution (Execution Stop Leaf)
open ClosedOnceQueryFrame (FreshFor placed)

variable {Context : Type}

structure Evidence (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) where
  finished : caller.goals = []
  output : caller.destination = .var result
  fresh : FreshFor result caller.bindings
  principal : Environment
  resolved : resolve caller.bindings = some principal
  payload : Atom
  reading : read principal payloadCode = payload
  literal : SpaceSemantics.Literal payload
  ordinary : ScopedQuerySource.mutationPayload true payload = true
  rows : List Atom
  snapshot : state.world.state.read handle = some rows
  complete : ClosedQueryAdmission.rowsReady payload rows = true

def prepare (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) : Option (Evidence result handle payloadCode caller state) :=
  if finished : caller.goals = [] then
    if output : caller.destination = .var result then
      if fresh : FreshFor result caller.bindings then
        match resolved : resolve caller.bindings with
        | none => none
        | some principal =>
          let payload := read principal payloadCode
          if literal : LiteralQuerySource.checkLiteral payload = true then
            if ordinary : ScopedQuerySource.mutationPayload true payload = true then
              match snapshot : state.world.state.read handle with
              | none => none
              | some rows =>
                if complete : ClosedQueryAdmission.rowsReady payload rows = true then
                  some ⟨finished, output, fresh, principal, resolved, payload, rfl,
                    (LiteralQuerySource.checkLiteral_iff payload).mp literal, ordinary, rows, snapshot, complete⟩
                else none
            else none
          else none
      else none
    else none
  else none

def packet (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (origins : List Nat) : CollectedAnswer :=
  ⟨Effects.boolean true, (ScopedRemovalSource.returned caller (.var result) handle payloadCode).bindings, origins ++ [0], []⟩

def advance (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (origins : List Nat) (state : State Context) (after : Effects.State) : State Context :=
  {state with
    world := {state.world with state := after}
    scope := {state.scope with collected := state.scope.collected ++ [packet result handle payloadCode caller origins]}}

def events (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (origins : List Nat) (state : State Context) : List CollectedAnswer :=
  if state.scope.caller.isNone then [packet result handle payloadCode caller origins] else []

/-- Five source steps perform preparation/removal/refinement; the sixth
publishes or locally records the actual returned packet. -/
theorem source_return (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (evidence : Evidence result handle payloadCode caller state) (after : Effects.State)
    (erased : Effects.erase state.world.state handle evidence.payload = some after) :
    (ScopedQuerySource.machine .relational program).run 6
      (ScopedMatchEntry.entrance (ScopedRemovalSource.source handle payloadCode) (.var result) caller state context origins pending) =
      (events result handle payloadCode caller origins state,
        .exhausted ((advance result handle payloadCode caller origins state after).cursor pending)) := by
  let returned := ScopedRemovalSource.returned caller (.var result) handle payloadCode
  let answer := packet result handle payloadCode caller origins
  let finalCursor := (advance result handle payloadCode caller origins state after).cursor pending
  have unbound := ClosedOnceQueryFrame.fresh_read caller.bindings result evidence.principal evidence.fresh evidence.resolved
  obtain ⟨environment, resolved⟩ := resolve_complete
    (ScopedRemovalSource.returned_consistent caller (.var result) handle payloadCode evidence.principal result evidence.resolved unbound)
  have value : read environment (.var result) = Effects.boolean true :=
    PresenceGuardSource.bound_closed_value _ (Effects.boolean true) result environment resolved
      (by simp [ScopedRemovalSource.returned]) (PresenceGuardSource.read_boolean true environment)
  have terminal : returned.goals = [] := evidence.finished
  have actualValue : read environment returned.destination = Effects.boolean true := by
    change read environment caller.destination = Effects.boolean true
    rw [evidence.output]
    exact value
  have last : (ScopedQuerySource.machine .relational program).step
      (placed state.allocator {state.world with state := after} state.scope state.parents returned context (origins ++ [0]) pending) =
      some (if state.scope.caller.isNone then .publish [answer] finalCursor else .silent finalCursor) := by
    simp only [placed]
    rw [ScopedQuerySource.Guards.empty_goals_step .relational program state.allocator {state.world with state := after}
      {state.scope with frontier := (returned, context, origins ++ [0]) :: pending}
      state.parents returned context (origins ++ [0]) pending rfl terminal]
    have delivered := scope_terminal_value .relational program state.allocator {state.world with state := after}
      {state.scope with frontier := (returned, context, origins ++ [0]) :: pending}
      state.parents returned context (origins ++ [0]) pending environment rfl terminal resolved
    simp only [actualValue] at delivered
    simpa [answer, packet, returned, finalCursor, advance, State.cursor, EagerDFS.Scope.record] using congrArg some delivered
  have finalStep : (ScopedQuerySource.machine .relational program).run 1
      (placed state.allocator {state.world with state := after} state.scope state.parents returned context (origins ++ [0]) pending) =
      (events result handle payloadCode caller origins state, .exhausted finalCursor) := by
    cases parent : state.scope.caller <;> simp [Machine.run, last, events, answer, parent]
  have before := ScopedRemovalSource.source_prefix program state.allocator state.world state.scope state.parents caller context
    origins pending (.var result) handle payloadCode evidence.payload evidence.principal result evidence.rows after evidence.resolved
    unbound evidence.reading (LiteralQuerySource.read_literal _ evidence.literal) evidence.ordinary evidence.snapshot evidence.complete erased
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 5 1 _ _ [] before
  rw [finalStep] at combined
  simpa only [List.nil_append, ScopedMatchEntry.entrance, ScopedRemovalSource.entry] using combined

structure Receipt (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) where
  execution : Execution Context
  exact : (ScopedQuerySource.machine .relational program).run execution.budget
    (ScopedMatchEntry.entrance (ScopedRemovalSource.source handle payloadCode) (.var result) caller state context origins pending) =
    execution.observation pending

def declined (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    Receipt program result handle payloadCode caller state context origins pending :=
  ⟨⟨0, [], .reference (ScopedMatchEntry.entrance (ScopedRemovalSource.source handle payloadCode)
    (.var result) caller state context origins pending)⟩, rfl⟩

def execute (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    Receipt program result handle payloadCode caller state context origins pending :=
  match prepare result handle payloadCode caller state with
  | none => declined program result handle payloadCode caller state context origins pending
  | some evidence =>
      match erased : Effects.erase state.world.state handle evidence.payload with
      | none => declined program result handle payloadCode caller state context origins pending
      | some after =>
          ⟨⟨6, events result handle payloadCode caller origins state,
            .complete (advance result handle payloadCode caller origins state after)⟩,
            source_return program result handle payloadCode caller state context origins pending evidence after erased⟩

def leaf (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (Context : Type) : Leaf program Context where
  source := ScopedRemovalSource.source handle payloadCode
  destination := .var result
  execute caller state context origins pending := (execute program result handle payloadCode caller state context origins pending).execution
  exact caller state context origins pending := (execute program result handle payloadCode caller state context origins pending).exact

/-- All admission premises concern the entrance, not a future successful
primitive or an already-prepared invocation. -/
theorem prepare_complete (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) (principal : Environment) (payload : Atom) (rows : List Atom)
    (finished : caller.goals = []) (output : caller.destination = .var result) (fresh : FreshFor result caller.bindings)
    (resolved : resolve caller.bindings = some principal) (reading : read principal payloadCode = payload)
    (literal : SpaceSemantics.Literal payload) (ordinary : ScopedQuerySource.mutationPayload true payload = true)
    (snapshot : state.world.state.read handle = some rows) (complete : ClosedQueryAdmission.rowsReady payload rows = true) :
    ∃ evidence, prepare result handle payloadCode caller state = some evidence := by
  have checked := (LiteralQuerySource.checkLiteral_iff payload).mpr literal
  unfold prepare
  simp only [dif_pos finished, dif_pos output, dif_pos fresh]
  split
  next failed => simp [resolved] at failed
  next environment found =>
    have same : environment = principal := Option.some.inj (found.symm.trans resolved)
    subst environment
    simp only [reading, dif_pos checked, dif_pos ordinary]
    split
    next failed => simp [snapshot] at failed
    next values found =>
      have same : values = rows := Option.some.inj (found.symm.trans snapshot)
      subst values
      simp only [dif_pos complete]
      exact ⟨_, rfl⟩

theorem execute_prepared (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (evidence : Evidence result handle payloadCode caller state)
    (prepared : prepare result handle payloadCode caller state = some evidence) :
    ∃ after, Effects.erase state.world.state handle evidence.payload = some after ∧
      (execute program result handle payloadCode caller state context origins pending).execution =
        ⟨6, events result handle payloadCode caller origins state,
          .complete (advance result handle payloadCode caller origins state after)⟩ := by
  obtain ⟨after, erased⟩ := Effects.erase_exists_of_read_some evidence.snapshot evidence.payload
  refine ⟨after, erased, ?_⟩
  simp only [execute, prepared]
  split
  next failed => simp [erased] at failed
  next received actual =>
    have same : received = after := Option.some.inj (actual.symm.trans erased)
    subst received
    rfl

/-- Successful execution reveals its checked payload and actual erase. -/
theorem completed_origin (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (execute program result handle payloadCode caller state context origins pending).execution.stop = .complete after) :
    ∃ evidence, prepare result handle payloadCode caller state = some evidence ∧
      ∃ erased, Effects.erase state.world.state handle evidence.payload = some erased ∧
        after = advance result handle payloadCode caller origins state erased := by
  unfold execute at completed
  split at completed
  · cases completed
  next evidence checked =>
      split at completed
      · cases completed
      next erased actual =>
        exact ⟨evidence, checked, erased, actual, (Stop.complete.inj completed).symm⟩

theorem completed_preserves_allocator (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (execute program result handle payloadCode caller state context origins pending).execution.stop = .complete after) :
    after.allocator = state.allocator ∧
      after.scope.collected = state.scope.collected ++ [packet result handle payloadCode caller origins] := by
  obtain ⟨_, _, _, _, rfl⟩ := completed_origin program result handle payloadCode caller state context origins pending after completed
  exact ⟨rfl, rfl⟩

theorem packet_value (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom) (caller : Control) (origins : List Nat) :
    (packet result handle payloadCode caller origins).value = Effects.boolean true ∧
      (packet result handle payloadCode caller origins).associated = [] := ⟨rfl, rfl⟩

/-- An unreadable target is not an empty relation or a completed deletion. -/
theorem prepare_none_of_unreadable (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (caller : Control) (state : State Context) (unreadable : state.world.state.read handle = none) :
    prepare result handle payloadCode caller state = none := by
  cases prepared : prepare result handle payloadCode caller state with
  | none => rfl
  | some evidence =>
    have impossible := evidence.snapshot
    rw [unreadable] at impossible
    contradiction

theorem unreadable_keeps_entrance (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (unreadable : state.world.state.read handle = none) :
    (execute program result handle payloadCode caller state context origins pending).execution =
      ⟨0, [], .reference (ScopedMatchEntry.entrance (ScopedRemovalSource.source handle payloadCode)
        (.var result) caller state context origins pending)⟩ := by
  simp only [execute, prepare_none_of_unreadable result handle payloadCode caller state unreadable, declined]

/-- A live suffix must not be swallowed as though the removal were the whole
branch. The caller is returned intact for source execution instead. -/
theorem unfinished_keeps_entrance (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (unfinished : caller.goals ≠ []) :
    (execute program result handle payloadCode caller state context origins pending).execution =
      ⟨0, [], .reference (ScopedMatchEntry.entrance (ScopedRemovalSource.source handle payloadCode)
        (.var result) caller state context origins pending)⟩ := by
  simp only [execute, prepare, dif_neg unfinished, declined]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalExecution.source_return
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalExecution.execute_prepared
