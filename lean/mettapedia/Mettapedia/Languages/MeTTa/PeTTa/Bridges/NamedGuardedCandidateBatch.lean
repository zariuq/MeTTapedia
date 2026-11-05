import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateExecution

/-!
# Sequential source batches of reached guarded leaf controls

Each descriptor denotes its exact source control, including the caller's
reserved names and cut boundary. The batch starts only at that actual source
frontier. Every leaf is rechecked in the world, allocator and collector left
by its predecessor. Refusal and source suspension stop the batch separately.
This does not flatten nested query entry into precomputed leaf enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open NamedGuardedInsertionSource (Body)

structure Candidate (Context : Type) where
  caller : Control
  context : Context
  origins : List Nat
  formulaName : String
  nodeName : String
  request : LiteralQuerySource.Request
  body : Body

variable {Context : Type}

def Candidate.source (candidate : Candidate Context) : Atom :=
  .expression [.symbol "if", ScopedCallOperands.source "in" candidate.formulaName candidate.nodeName,
    NamedGuardedInsertionSource.empty,
    ScopedInsertionSequence.source candidate.body.temporary candidate.request.handle candidate.body.secondHandle
      candidate.body.firstCode candidate.body.secondCode]

def Candidate.control (candidate : Candidate Context) : Control :=
  {candidate.caller with goals := .evaluate candidate.source (.var candidate.body.result) :: candidate.caller.goals}

def Candidate.work (candidate : Candidate Context) : CollectionWork Context :=
  (candidate.control, candidate.context, candidate.origins)

-- Realize shared equation helpers in their defining module. Otherwise two
-- independent importing modules can each generate the same helper name.
#print equations Candidate.source
#print equations Candidate.control
#print equations Candidate.work

structure State (Context : Type) where
  allocator : Allocator
  world : World
  /-- Collector metadata; `cursor` installs the authoritative reached frontier. -/
  scope : CollectionScope Context
  parents : List (CollectionScope Context)

def State.cursor (state : State Context) (pending : List (CollectionWork Context)) : ScopedCursor Context :=
  (state.allocator, ⟨state.world, {state.scope with frontier := pending} :: state.parents⟩)

def Candidate.input (candidate : Candidate Context) (program : SpaceSemantics.Program)
    (state : State Context) (pending : List (CollectionWork Context)) : NamedPresenceConditional.Input Context := {
  program, allocator := state.allocator, world := state.world, scope := state.scope, parents := state.parents,
  caller := candidate.caller, context := candidate.context, origins := candidate.origins, pending,
  destination := .var candidate.body.result, formulaName := candidate.formulaName, nodeName := candidate.nodeName,
  yes := NamedGuardedInsertionSource.empty,
  no := ScopedInsertionSequence.source candidate.body.temporary candidate.request.handle candidate.body.secondHandle
    candidate.body.firstCode candidate.body.secondCode,
  request := candidate.request }

theorem input_before (candidate : Candidate Context) (program : SpaceSemantics.Program)
    (state : State Context) (pending : List (CollectionWork Context)) :
    (candidate.input program state pending).before = state.cursor (candidate.work :: pending) := rfl

def State.advance (state : State Context) (next : NamedGuardedCandidateExecution.Advance) : State Context :=
  {state with
    allocator := next.allocator
    world := {state.world with state := next.state}
    scope := {state.scope with collected := state.scope.collected ++ next.answers}}

#print equations State.advance

theorem advanced_endpoint (candidate : Candidate Context) (program : SpaceSemantics.Program)
    (state : State Context) (pending : List (CollectionWork Context)) (next : NamedGuardedCandidateExecution.Advance) :
    next.endpoint (candidate.input program state pending) = (state.advance next).cursor pending := rfl

inductive Stop (Context : Type) where
  /-- The described leaf prefix is complete; its enclosing scope is not. -/
  | complete (state : State Context)
  | reference (remaining : List (Candidate Context)) (state : State Context)
  /-- Remaining descriptors are diagnostic. Resume `saved`, not the active
  descriptor's entrance: it may already have published its first write. -/
  | suspended (remaining : List (Candidate Context)) (request : ScopeBoundary) (saved : ScopedCursor Context)

def Stop.outcome (tail : List (CollectionWork Context)) : Stop Context →
    Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary
  | .complete state => .exhausted (state.cursor tail)
  | .reference remaining state => .exhausted (state.cursor (remaining.map Candidate.work ++ tail))
  | .suspended _ request saved => .suspended request saved

structure Execution (Context : Type) where
  budget : Nat
  events : List CollectedAnswer
  stop : Stop Context

def Execution.observation (tail : List (CollectionWork Context)) (execution : Execution Context) :=
  (execution.events, execution.stop.outcome tail)

/-- Admission refusal does not consume the descriptor. Source suspension
keeps the internal leaf residual; neither is confused with an empty batch. -/
def run (program : SpaceSemantics.Program) : List (Candidate Context) → State Context →
    List (CollectionWork Context) → Execution Context
  | [], state, _ => ⟨0, [], .complete state⟩
  | candidate :: rest, state, tail =>
    let input := candidate.input program state (rest.map Candidate.work ++ tail)
    let leaf := NamedGuardedCandidateExecution.execute input candidate.body
    match leaf.result with
    | .reference => ⟨leaf.budget, [], .reference (candidate :: rest) state⟩
    | .suspended request saved => ⟨leaf.budget, [], .suspended (candidate :: rest) request saved⟩
    | .advanced next =>
      let later := run program rest (state.advance next) tail
      ⟨leaf.budget + later.budget, next.events input ++ later.events, later.stop⟩

/-- Exact source execution, including every public packet, collected frame,
partial write and retained source request. No completed batch is assumed. -/
theorem run_exact (program : SpaceSemantics.Program) (candidates : List (Candidate Context))
    (state : State Context) (tail : List (CollectionWork Context)) :
    (ScopedQuerySource.machine .relational program).run (run program candidates state tail).budget
      (state.cursor (candidates.map Candidate.work ++ tail)) =
      (run program candidates state tail).observation tail := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest ih =>
    let input := candidate.input program state (rest.map Candidate.work ++ tail)
    let leaf := NamedGuardedCandidateExecution.execute input candidate.body
    have actual := leaf.exact
    change (ScopedQuerySource.machine .relational program).run leaf.budget input.before =
      leaf.result.observation input at actual
    cases result : leaf.result with
    | reference =>
      dsimp only [leaf, input] at result
      simpa only [run, leaf, input, result, Execution.observation, Stop.outcome,
        NamedGuardedCandidateExecution.Result.observation, input_before, List.map_cons, List.cons_append] using actual
    | suspended request saved =>
      dsimp only [leaf, input] at result
      simpa only [run, leaf, input, result, Execution.observation, Stop.outcome,
        NamedGuardedCandidateExecution.Result.observation, input_before, List.map_cons, List.cons_append] using actual
    | advanced next =>
      rw [result] at actual
      change (ScopedQuerySource.machine .relational program).run leaf.budget
        (state.cursor (candidate.work :: (rest.map Candidate.work ++ tail))) =
        (next.events input, .exhausted ((state.advance next).cursor (rest.map Candidate.work ++ tail))) at actual
      have joined := (ScopedQuerySource.machine .relational program).established_and_pending leaf.budget
        (run program rest (state.advance next) tail).budget _ _ _ actual
      rw [ih (state.advance next)] at joined
      dsimp only [leaf, input] at result
      simpa only [run, leaf, input, result, Execution.observation, List.map_cons, List.cons_append] using joined

/-- Application to an already-reached source scope requires exact frontier
correspondence. A descriptor cannot overwrite unrelated pending work. -/
theorem reached_exact (program : SpaceSemantics.Program) (candidates : List (Candidate Context))
    (state : State Context) (tail : List (CollectionWork Context))
    (reached : state.scope.frontier = candidates.map Candidate.work ++ tail) :
    (ScopedQuerySource.machine .relational program).run (run program candidates state tail).budget
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) =
      (run program candidates state tail).observation tail := by
  have same : state.cursor (candidates.map Candidate.work ++ tail) =
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) := by
    simp only [State.cursor, ← reached]
  rw [← same]
  exact run_exact program candidates state tail

/-- The described candidate prefix needs at most forty source steps per
candidate. Refusal/suspension stops early; enclosing query/collection work is
not included in this prefix bound. -/
theorem run_budget (program : SpaceSemantics.Program) (candidates : List (Candidate Context))
    (state : State Context) (tail : List (CollectionWork Context)) :
    (run program candidates state tail).budget ≤ 40 * candidates.length := by
  induction candidates generalizing state with
  | nil => simp [run]
  | cons candidate rest ih =>
    have bound := NamedGuardedCandidateExecution.execute_budget
      (candidate.input program state (rest.map Candidate.work ++ tail)) candidate.body
    cases result : (NamedGuardedCandidateExecution.execute
        (candidate.input program state (rest.map Candidate.work ++ tail)) candidate.body).result with
    | reference =>
      simp only [run, result, List.length_cons]
      omega
    | suspended request saved =>
      simp only [run, result, List.length_cons]
      omega
    | advanced next =>
      have later := ih (state.advance next)
      simp only [run, result, List.length_cons]
      omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch
