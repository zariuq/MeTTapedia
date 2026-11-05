import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionAdmission

/-!
# Current-world execution of admitted guarded candidates

The worker checks the actual source frame and current store, then performs
the guard/copy/two-write calculation. Its receipt is related to the source
machine by the established component theorems, not by running that machine.
Admission refusal retains the entrance. A missing second target retains the
first write and pending second request. A held witness may refuse copying.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedPresenceConditional (Input)
open NamedGuardedInsertionSource (Body Evidence afterGuard afterInsert finalOrigins)

variable {Context : Type}

structure Advance where
  allocator : Allocator
  state : Effects.State
  answers : List CollectedAnswer

def Advance.endpoint (input : Input Context) (advance : Advance) : ScopedCursor Context :=
  (advance.allocator, ⟨{input.world with state := advance.state},
    {input.scope with frontier := input.pending, collected := input.scope.collected ++ advance.answers} :: input.parents⟩)

def Advance.events (input : Input Context) (advance : Advance) : List CollectedAnswer :=
  if input.scope.caller.isNone then advance.answers else []

inductive Result (Context : Type) where
  | advanced (next : Advance)
  | suspended (request : ScopeBoundary) (saved : ScopedCursor Context)
  | reference

def Result.observation (input : Input Context) : Result Context →
    List CollectedAnswer × Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary
  | .advanced next => (next.events input, .exhausted (next.endpoint input))
  | .suspended request saved => ([], .suspended request saved)
  | .reference => ([], .exhausted input.before)

structure Receipt (input : Input Context) where
  /-- Supplied source budget, not a claim about consumed instructions. -/
  budget : Nat
  result : Result Context
  exact : (ScopedQuerySource.machine .relational input.program).run budget input.before = result.observation input

def declined (input : Input Context) : Receipt input :=
  ⟨0, .reference, rfl⟩

theorem insert_none_read_none (state : Effects.State) (target : NamedSpaces.Handle) (value : Atom)
    (unavailable : Effects.insert state target value = none) : state.read target = none := by
  cases readable : state.read target with
  | none => rfl
  | some rows =>
    obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some readable value
    rw [unavailable] at inserted
    cases inserted

def missingSecond (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (middle : Effects.State) : Result Context :=
  let later := ScopedInsertionSequence.secondCaller (afterGuard guard) body.result body.temporary
    input.request.handle body.secondHandle body.firstCode body.secondCode
  .suspended (.branch (.invoke "add-atom"
    [.var (ScopedInsertionSource.location later (.var body.result) body.secondHandle body.secondCode), body.secondCode]
    (.var body.result)))
    (ClosedOnceQueryFrame.placed input.allocator {input.world with state := middle} input.callScope input.parents
      (ScopedInsertionSource.ready later (.var body.result) body.secondHandle body.secondCode)
      input.context (guard.selectedOrigins ++ [0, 0, 0]) input.pending)

/-- Independent execution of one admitted leaf. The current snapshot is read
here, after any earlier candidate's publication. -/
def executeAdmitted (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result) : Receipt input :=
  match snapshot : input.world.state.read input.request.handle with
  | none => declined input
  | some rows =>
    if closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true then
      if present : input.request.pattern ∈ rows then
        match copied : PresenceGuardSource.copyAllocator input.allocator true with
        | none => {
          budget := 31
          result := .suspended .allocation (guard.copyBoundary true)
          exact := by
            simpa only [copied, Result.observation] using
              NamedGuardedInsertionSource.held_prefix evidence rows snapshot closed present }
        | some next => {
          budget := 31
          result := .advanced ⟨next, input.world.state, []⟩
          exact := by
            simpa [copied, Result.observation, Advance.events, Advance.endpoint,
              NamedPresenceConditional.Input.callScope] using
              NamedGuardedInsertionSource.held_prefix evidence rows snapshot closed present }
      else
        match first : Effects.insert input.world.state input.request.handle input.request.pattern with
        | none => declined input
        | some middle =>
          match second : Effects.insert middle body.secondHandle evidence.secondValue with
          | none => {
            budget := 38
            result := missingSecond input guard body middle
            exact := NamedGuardedInsertionSource.second_unavailable_prefix evidence rows middle
              snapshot closed present first (insert_none_read_none _ _ _ second) }
          | some after => {
            budget := 40
            result := .advanced ⟨input.allocator, after,
              [⟨Effects.boolean true, (afterInsert evidence).bindings, finalOrigins guard, []⟩]⟩
            exact := by
              simpa only [Result.observation, Advance.events, Advance.endpoint, EagerDFS.Scope.record] using
                NamedGuardedInsertionSource.fresh_return evidence rows middle after finished output
                  snapshot closed present first second }
    else declined input

/-- Both proof-producing preparers inspect the current invocation. Unsupported
frames return an unchanged entrance, never an empty source answer. -/
def execute (input : Input Context) (body : Body) : Receipt input :=
  if finished : input.caller.goals = [] then
    if output : input.caller.destination = .var body.result then
      match NamedPresenceConditional.prepare input with
      | none => declined input
      | some guard =>
        match NamedGuardedInsertionSource.prepare input guard body with
        | none => declined input
        | some evidence => executeAdmitted input guard body evidence finished output
    else declined input
  else declined input

theorem execute_exact (input : Input Context) (body : Body) :
    (ScopedQuerySource.machine .relational input.program).run (execute input body).budget input.before =
      (execute input body).result.observation input := (execute input body).exact

/-- A bound on the supplied source prefix budget, including early handoff.
It is not a native cost or a guarantee that a suspended leaf has completed. -/
theorem executeAdmitted_budget (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result) :
    (executeAdmitted input guard body evidence finished output).budget ≤ 40 := by
  unfold executeAdmitted
  split
  · simp [declined]
  · split
    · split
      · split <;> simp
      · split
        · simp [declined]
        · split <;> simp
    · simp [declined]

theorem execute_budget (input : Input Context) (body : Body) : (execute input body).budget ≤ 40 := by
  unfold execute
  split
  next finished =>
    split
    next output =>
      split
      · simp [declined]
      next guard found =>
        split
        · simp [declined]
        next evidence checked => exact executeAdmitted_budget input guard body evidence finished output
    · simp [declined]
  · simp [declined]

/-- Complete readable guard rows prevent admission handoff after static
admission. Allocation or publication failure is still an explicit source
suspension, not a promise of successful completion. -/
theorem executeAdmitted_not_reference (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (rows : List Atom) (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true) :
    (executeAdmitted input guard body evidence finished output).result ≠ .reference := by
  unfold executeAdmitted
  split
  next absent => simp [snapshot] at absent
  next actual found =>
    have same := Option.some.inj (found.symm.trans snapshot)
    subst actual
    split
    next ready =>
      split
      · split <;> simp
      · split
        next unavailable =>
          obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some snapshot input.request.pattern
          rw [unavailable] at inserted
          cases inserted
        next middle first =>
          split <;> simp [missingSecond]
    next rejected => exact (rejected closed).elim

theorem execute_not_reference (input : Input Context) (body : Body)
    (guard : NamedPresenceConditional.Evidence input) (evidence : Evidence input guard body)
    (preparedGuard : NamedPresenceConditional.prepare input = some guard)
    (preparedBody : NamedGuardedInsertionSource.prepare input guard body = some evidence)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (rows : List Atom) (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true) :
    (execute input body).result ≠ .reference := by
  simpa only [execute, dif_pos finished, dif_pos output, preparedGuard, preparedBody] using
    executeAdmitted_not_reference input guard body evidence finished output rows snapshot closed

/-- The actual completed publication, including its source membership test,
copy result or two primitive writes. No final-store decoding is assumed. -/
inductive Publication (input : Input Context) (body : Body) (after : Advance) : Prop where
  | held (rows : List Atom)
      (snapshot : input.world.state.read input.request.handle = some rows)
      (present : input.request.pattern ∈ rows)
      (copied : PresenceGuardSource.copyAllocator input.allocator true = some after.allocator)
      (unchanged : after.state = input.world.state) (noPacket : after.answers = []) : Publication input body after
  | fresh (guard : NamedPresenceConditional.Evidence input) (evidence : Evidence input guard body)
      (rows : List Atom) (middle : Effects.State)
      (snapshot : input.world.state.read input.request.handle = some rows)
      (absent : input.request.pattern ∉ rows)
      (first : Effects.insert input.world.state input.request.handle input.request.pattern = some middle)
      (second : Effects.insert middle body.secondHandle evidence.secondValue = some after.state)
      (allocator : after.allocator = input.allocator)
      (packet : after.answers = [⟨Effects.boolean true, (afterInsert evidence).bindings, finalOrigins guard, []⟩]) :
      Publication input body after

theorem admitted_publication (input : Input Context) (guard : NamedPresenceConditional.Evidence input)
    (body : Body) (evidence : Evidence input guard body)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (after : Advance) (completed : (executeAdmitted input guard body evidence finished output).result = .advanced after) :
    Publication input body after := by
  unfold executeAdmitted at completed
  split at completed
  · cases completed
  next rows snapshot =>
    split at completed
    next ready =>
      split at completed
      next present =>
        split at completed
        · cases completed
        next allocated copied =>
          cases Result.advanced.inj completed
          exact .held rows snapshot present copied rfl rfl
      next absent =>
        split at completed
        · cases completed
        next middle first =>
          split at completed
          · cases completed
          next final second =>
            cases Result.advanced.inj completed
            exact .fresh guard evidence rows middle snapshot absent first second rfl rfl
    · cases completed

theorem execute_publication (input : Input Context) (body : Body) (after : Advance)
    (completed : (execute input body).result = .advanced after) : Publication input body after := by
  unfold execute at completed
  split at completed
  next finished =>
    split at completed
    next output =>
      split at completed
      · cases completed
      next guard guardReady =>
        split at completed
        · cases completed
        next evidence bodyReady => exact admitted_publication input guard body evidence finished output after completed
    · cases completed
  · cases completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateExecution
