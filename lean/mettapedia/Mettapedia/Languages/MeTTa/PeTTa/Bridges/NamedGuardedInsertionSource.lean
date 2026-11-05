import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceConditional
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence

/-!
# Named guarded insertion candidates

The actual named conditional selects either an empty branch or the authored
two-write body. Admission checks the reached false-branch frame, not a source
result. Exactly one selected guard equation is required for this whole-leaf
route; the more general conditional prefix retains arbitrary alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open NamedPresenceConditional (Input)

variable {Context : Type}

structure Body where
  result : String
  temporary : String
  secondHandle : NamedSpaces.Handle
  firstCode : Atom
  secondCode : Atom

def empty : Atom := .expression [.symbol "empty"]

def afterGuard {input : Input Context} (guard : NamedPresenceConditional.Evidence input) : Control :=
  {NamedPresenceSource.returned input.pending.length guard.selected input.waiting.goals input.slot input.request false with
    goals := input.caller.goals}

structure Evidence (input : Input Context) (guard : NamedPresenceConditional.Evidence input) (body : Body) where
  single : guard.alternatives = []
  destination : input.destination = .var body.result
  yesEmpty : input.yes = empty
  noBody : input.no = ScopedInsertionSequence.source body.temporary input.request.handle body.secondHandle body.firstCode body.secondCode
  principal : Environment
  resolved : resolve (afterGuard guard).bindings = some principal
  freshTemporary : FreshFor body.temporary (afterGuard guard).bindings
  freshResult : FreshFor body.result (afterGuard guard).bindings
  distinct : body.temporary ≠ body.result
  firstRead : read principal body.firstCode = input.request.pattern
  secondValue : Atom
  secondRead : read principal body.secondCode = secondValue
  secondLiteral : SpaceSemantics.Literal secondValue
  firstOrdinary : ScopedQuerySource.mutationPayload false input.request.pattern = true
  secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true

/-- The body proposal is checked against the original syntax and actual
post-guard equations. No store mutation or body evaluation occurs here. -/
def prepare (input : Input Context) (guard : NamedPresenceConditional.Evidence input) (body : Body) :
    Option (Evidence input guard body) := do
  if single : guard.alternatives = [] then
    if destination : input.destination = .var body.result then
      if yesEmpty : input.yes = empty then
        if noBody : input.no = ScopedInsertionSequence.source body.temporary input.request.handle body.secondHandle body.firstCode body.secondCode then
          match resolved : resolve (afterGuard guard).bindings with
          | none => none
          | some principal =>
            if freshTemporary : FreshFor body.temporary (afterGuard guard).bindings then
              if freshResult : FreshFor body.result (afterGuard guard).bindings then
                if distinct : body.temporary ≠ body.result then
                  if firstRead : read principal body.firstCode = input.request.pattern then
                    let secondValue := read principal body.secondCode
                    if literal : LiteralQuerySource.checkLiteral secondValue = true then
                      if firstOrdinary : ScopedQuerySource.mutationPayload false input.request.pattern = true then
                        if secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true then
                          some {
                            single, destination, yesEmpty, noBody, principal, resolved,
                            freshTemporary, freshResult, distinct, firstRead, secondValue,
                            secondRead := rfl
                            secondLiteral := (LiteralQuerySource.checkLiteral_iff _).mp literal,
                            firstOrdinary, secondOrdinary }
                        else none
                      else none
                    else none
                  else none
                else none
              else none
            else none
        else none
      else none
    else none
  else none

def afterInsert {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (_evidence : Evidence input guard body) : Control :=
  ScopedInsertionSequence.returned (afterGuard guard) body.result body.temporary input.request.handle
    body.secondHandle body.firstCode body.secondCode

def finalOrigins {input : Input Context} (guard : NamedPresenceConditional.Evidence input) : List Nat :=
  guard.selectedOrigins ++ [0, 0, 0, 0]

theorem false_endpoint {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) :
    guard.endpoint input.allocator false = placed input.allocator input.world input.callScope input.parents
      (ScopedInsertionSequence.entry (afterGuard guard) body.result body.temporary input.request.handle
        body.secondHandle body.firstCode body.secondCode)
      input.context (guard.selectedOrigins ++ [0, 0]) input.pending := by
  simp only [NamedPresenceConditional.Evidence.endpoint, NamedPresenceConditional.Evidence.remaining,
    evidence.single, List.map_nil, List.nil_append, NamedPresenceSource.branchReached,
    afterGuard, ScopedInsertionSequence.entry, NamedPresenceConditional.Input.waiting,
    Bool.false_eq_true, ↓reduceIte, evidence.noBody, evidence.destination]

/-- A fresh candidate performs the actual named guard and both source
insertions. The original caller is still pending at the 39-step endpoint. -/
theorem fresh_prefix {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (rows : List Atom) (middle after : Effects.State)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (absent : input.request.pattern ∉ rows)
    (first : Effects.insert input.world.state input.request.handle input.request.pattern = some middle)
    (second : Effects.insert middle body.secondHandle evidence.secondValue = some after) :
    (ScopedQuerySource.machine .relational input.program).run 39 input.before =
      ([], .exhausted (placed input.allocator {input.world with state := after} input.callScope input.parents
        (afterInsert evidence) input.context (finalOrigins guard) input.pending)) := by
  have tested := NamedPresenceConditional.source_prefix input guard rows snapshot closed
  simp only [absent, decide_false, CollectedOnceQuerySource.childBudget, Bool.false_eq_true, ↓reduceIte,
    PresenceGuardSource.copyAllocator] at tested
  rw [false_endpoint evidence] at tested
  have inserted := ScopedInsertionSequence.source_prefix input.program input.allocator input.world input.callScope input.parents
    (afterGuard guard) input.context (guard.selectedOrigins ++ [0, 0]) input.pending body.result body.temporary
    input.request.handle body.secondHandle body.firstCode body.secondCode input.request.pattern evidence.secondValue
    evidence.principal middle after evidence.resolved evidence.freshTemporary evidence.freshResult evidence.distinct
    evidence.firstRead evidence.secondRead (LiteralQuerySource.read_pattern input.request)
    (LiteralQuerySource.read_literal _ evidence.secondLiteral) evidence.firstOrdinary evidence.secondOrdinary first second
  have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending 26 13 _ _ [] tested
  rw [inserted] at combined
  simpa [afterInsert, finalOrigins, List.append_assoc] using combined

/-- Readable logical targets construct the primitive results; they are not
assumed as an oracle for successful source execution. -/
theorem fresh_exists {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (rows frontierRows : List Atom)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (frontierSnapshot : input.world.state.read body.secondHandle = some frontierRows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (absent : input.request.pattern ∉ rows) :
    ∃ middle after, Effects.insert input.world.state input.request.handle input.request.pattern = some middle ∧
      Effects.insert middle body.secondHandle evidence.secondValue = some after ∧
      (ScopedQuerySource.machine .relational input.program).run 39 input.before =
        ([], .exhausted (placed input.allocator {input.world with state := after} input.callScope input.parents
          (afterInsert evidence) input.context (finalOrigins guard) input.pending)) := by
  obtain ⟨middle, after, first, second⟩ := ScopedInsertionSequence.pair_exists input.world.state input.request.handle
    body.secondHandle input.request.pattern evidence.secondValue rows frontierRows snapshot frontierSnapshot
  exact ⟨middle, after, first, second, fresh_prefix evidence rows middle after snapshot closed absent first second⟩

/-- A held candidate drops only its branch, preserving the current world and
older alternatives. Refused copying is still a suspension, not zero progress. -/
theorem held_prefix {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (rows : List Atom)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (present : input.request.pattern ∈ rows) :
    (ScopedQuerySource.machine .relational input.program).run 31 input.before =
      ([], match PresenceGuardSource.copyAllocator input.allocator true with
        | some next => .exhausted (next, ⟨input.world, {input.callScope with frontier := input.pending} :: input.parents⟩)
        | none => .suspended .allocation (guard.copyBoundary true)) := by
  have tested := NamedPresenceConditional.source_prefix input guard rows snapshot closed
  simp only [present, decide_true, CollectedOnceQuerySource.childBudget, ↓reduceIte] at tested
  cases copied : PresenceGuardSource.copyAllocator input.allocator true with
  | none =>
      rw [copied] at tested
      have stable := (ScopedQuerySource.machine .relational input.program).run_stable 30 1 input.before
        (fun residual => by rw [tested]; simp)
      rw [tested] at stable
      exact stable
  | some next =>
      rw [copied] at tested
      let reached := NamedPresenceSource.branchReached input.pending.length guard.selected input.caller.goals input.slot
        input.request true input.yes input.no input.destination
      have last : (ScopedQuerySource.machine .relational input.program).step (guard.endpoint next true) =
          some (.silent (next, ⟨input.world, {input.callScope with frontier := input.pending} :: input.parents⟩)) := by
        change (ScopedQuerySource.machine .relational input.program).step
          (placed next input.world input.callScope input.parents reached input.context
            (guard.selectedOrigins ++ [0, 0]) guard.remaining) = _
        have goals : reached.goals = .evaluate empty input.destination :: input.caller.goals := by
          simp [reached, NamedPresenceSource.branchReached, evidence.yesEmpty]
        rw [ScopedQuerySource.Guards.placed_ordinary_step .relational input.program next input.world input.callScope input.parents
          reached input.context (guard.selectedOrigins ++ [0, 0]) guard.remaining
          (.evaluate empty input.destination) input.caller.goals goals rfl]
        have stopped := scope_empty .relational input.program next input.world
          {input.callScope with frontier := (reached, input.context, guard.selectedOrigins ++ [0, 0]) :: guard.remaining}
          input.parents reached input.context (guard.selectedOrigins ++ [0, 0]) guard.remaining
          input.destination input.caller.goals rfl goals
        simpa [placed, NamedPresenceConditional.Evidence.remaining, evidence.single] using congrArg some stopped
      have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending 30 1 _ _ [] tested
      rw [Machine.run_succ_silent _ last] at combined
      simpa [Machine.run] using combined

theorem after_guard_destination {input : Input Context} (guard : NamedPresenceConditional.Evidence input) :
    (afterGuard guard).destination = input.caller.destination := guard.selected_destination

theorem after_insert_consistent {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) : ∃ environment, Solves environment (afterInsert evidence).bindings :=
  ScopedInsertionSequence.returned_consistent (afterGuard guard) body.result body.temporary input.request.handle
    body.secondHandle body.firstCode body.secondCode evidence.principal evidence.resolved
    evidence.freshTemporary evidence.freshResult evidence.distinct

theorem after_insert_value {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (environment : Environment)
    (solved : Solves environment (afterInsert evidence).bindings) :
    read environment (.var body.result) = Effects.boolean true :=
  ScopedInsertionSequence.returned_value (afterGuard guard) body.result body.temporary input.request.handle
    body.secondHandle body.firstCode body.secondCode environment solved

/-- A fresh named candidate returns exactly one true packet. In a collection
the packet is recorded locally, rather than published to its outer caller. -/
theorem fresh_return {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (rows : List Atom) (middle after : Effects.State)
    (finished : input.caller.goals = []) (output : input.caller.destination = .var body.result)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (absent : input.request.pattern ∉ rows)
    (first : Effects.insert input.world.state input.request.handle input.request.pattern = some middle)
    (second : Effects.insert middle body.secondHandle evidence.secondValue = some after) :
    let answer : CollectedAnswer := ⟨Effects.boolean true, (afterInsert evidence).bindings, finalOrigins guard, []⟩
    (ScopedQuerySource.machine .relational input.program).run 40 input.before =
      (if input.scope.caller.isNone then [answer] else [],
        .exhausted (input.allocator, ⟨{input.world with state := after},
          EagerDFS.Scope.record input.scope input.pending answer :: input.parents⟩)) := by
  dsimp only
  let returned := afterInsert evidence
  let answer : CollectedAnswer := ⟨Effects.boolean true, returned.bindings, finalOrigins guard, []⟩
  let finalCursor : ScopedCursor Context := (input.allocator, ⟨{input.world with state := after},
    EagerDFS.Scope.record input.scope input.pending answer :: input.parents⟩)
  obtain ⟨environment, resolved⟩ := resolve_complete (after_insert_consistent evidence)
  have value := after_insert_value evidence environment (resolve_sound resolved)
  have terminal : returned.goals = [] := finished
  have actualValue : read environment returned.destination = Effects.boolean true := by
    change read environment (afterGuard guard).destination = Effects.boolean true
    rw [after_guard_destination, output]
    exact value
  have last : (ScopedQuerySource.machine .relational input.program).step
      (placed input.allocator {input.world with state := after} input.callScope input.parents returned
        input.context (finalOrigins guard) input.pending) =
      some (if input.scope.caller.isNone then .publish [answer] finalCursor else .silent finalCursor) := by
    simp only [placed]
    rw [ScopedQuerySource.Guards.empty_goals_step .relational input.program input.allocator {input.world with state := after}
      {input.callScope with frontier := (returned, input.context, finalOrigins guard) :: input.pending}
      input.parents returned input.context (finalOrigins guard) input.pending rfl terminal]
    have delivered := scope_terminal_value .relational input.program input.allocator {input.world with state := after}
      {input.callScope with frontier := (returned, input.context, finalOrigins guard) :: input.pending}
      input.parents returned input.context (finalOrigins guard) input.pending environment rfl terminal resolved
    simp only [actualValue] at delivered
    simpa [answer, finalCursor, EagerDFS.Scope.record, NamedPresenceConditional.Input.callScope] using congrArg some delivered
  have finalStep : (ScopedQuerySource.machine .relational input.program).run 1
      (placed input.allocator {input.world with state := after} input.callScope input.parents returned
        input.context (finalOrigins guard) input.pending) =
      (if input.scope.caller.isNone then [answer] else [], .exhausted finalCursor) := by
    cases parent : input.scope.caller <;> simp [Machine.run, last, parent]
  have before := fresh_prefix evidence rows middle after snapshot closed absent first second
  have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending 39 1 _ _ [] before
  rw [finalStep] at combined
  simpa only [List.nil_append] using combined

/-- A missing second target after a fresh guard yields the retained request,
not a completed candidate or a rollback of the first write. -/
theorem second_unavailable_prefix {input : Input Context} {guard : NamedPresenceConditional.Evidence input} {body : Body}
    (evidence : Evidence input guard body) (rows : List Atom) (middle : Effects.State)
    (snapshot : input.world.state.read input.request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady input.request.pattern rows = true)
    (absent : input.request.pattern ∉ rows)
    (first : Effects.insert input.world.state input.request.handle input.request.pattern = some middle)
    (unavailable : middle.read body.secondHandle = none) :
    let later := ScopedInsertionSequence.secondCaller (afterGuard guard) body.result body.temporary
      input.request.handle body.secondHandle body.firstCode body.secondCode
    (ScopedQuerySource.machine .relational input.program).run 38 input.before =
      ([], .suspended (.branch (.invoke "add-atom"
        [.var (ScopedInsertionSource.location later (.var body.result) body.secondHandle body.secondCode), body.secondCode]
        (.var body.result)))
        (placed input.allocator {input.world with state := middle} input.callScope input.parents
          (ScopedInsertionSource.ready later (.var body.result) body.secondHandle body.secondCode)
          input.context (guard.selectedOrigins ++ [0, 0, 0]) input.pending)) := by
  dsimp only
  have tested := NamedPresenceConditional.source_prefix input guard rows snapshot closed
  simp only [absent, decide_false, CollectedOnceQuerySource.childBudget, Bool.false_eq_true, ↓reduceIte,
    PresenceGuardSource.copyAllocator] at tested
  rw [false_endpoint evidence] at tested
  have stopped := ScopedInsertionSequence.second_unavailable_prefix input.program input.allocator input.world input.callScope input.parents
    (afterGuard guard) input.context (guard.selectedOrigins ++ [0, 0]) input.pending body.result body.temporary
    input.request.handle body.secondHandle body.firstCode body.secondCode input.request.pattern evidence.principal middle
    evidence.resolved evidence.freshTemporary evidence.firstRead (LiteralQuerySource.read_pattern input.request)
    evidence.firstOrdinary first unavailable
  have combined := (ScopedQuerySource.machine .relational input.program).established_and_pending 26 12 _ _ [] tested
  rw [stopped] at combined
  simpa [List.append_assoc] using combined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedInsertionSource
