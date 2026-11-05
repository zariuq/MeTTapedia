import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution

/-!
# Named guarded leaves in live nested queries

One raw source template is shared by all captured predecessors. Its literal
guard request is constructed separately from each reached principal frame.
Reading a payload proposes admission; the named checker still verifies the
actual guard operands and source declaration. Refusal never substitutes the
read value into executable source or discards the current continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (Candidate State)
open ScopedNestedQueryExecution (Execution Stop Leaf)
open ScopedMatchEntry (entrance)

structure Template where
  formulaName : String
  nodeName : String
  satisfactionHandle : NamedSpaces.Handle
  body : NamedGuardedInsertionSource.Body

def Template.source (template : Template) : Atom :=
  .expression [.symbol "if", ScopedCallOperands.source "in" template.formulaName template.nodeName,
    NamedGuardedInsertionSource.empty,
    ScopedInsertionSequence.source template.body.temporary template.satisfactionHandle template.body.secondHandle
      template.body.firstCode template.body.secondCode]

variable {Context : Type}

def Template.candidate (template : Template) (caller : Control) (context : Context) (origins : List Nat)
    (request : LiteralQuerySource.Request) : Candidate Context :=
  ⟨caller, context, origins, template.formulaName, template.nodeName, request, template.body⟩

theorem candidate_entrance (template : Template) (caller : Control) (context : Context) (origins : List Nat)
    (request : LiteralQuerySource.Request) (handle : request.handle = template.satisfactionHandle)
    (program : SpaceSemantics.Program) (state : State Context) (pending : List (CollectionWork Context)) :
    ((template.candidate caller context origins request).input program state pending).before =
      entrance template.source (.var template.body.result) caller state context origins pending := by
  rw [NamedGuardedCandidateBatch.input_before]
  simp only [Template.candidate, Candidate.work, Candidate.control, Candidate.source, handle,
    Template.source, State.cursor, entrance, ClosedOnceQueryFrame.placed]

structure Receipt (program : SpaceSemantics.Program) (template : Template) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) where
  execution : Execution Context
  exact : (ScopedQuerySource.machine .relational program).run execution.budget
    (entrance template.source (.var template.body.result) caller state context origins pending) =
      execution.observation pending

def invoke (program : SpaceSemantics.Program) (template : Template) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    Receipt program template caller state context origins pending :=
  match resolve caller.bindings with
  | none => ⟨⟨0, [], .reference (entrance template.source (.var template.body.result) caller state context origins pending)⟩, rfl⟩
  | some principal =>
    match requested : LiteralQuerySource.ofPattern template.satisfactionHandle
        (read principal template.body.firstCode) (.symbol "t") with
    | none => ⟨⟨0, [], .reference (entrance template.source (.var template.body.result) caller state context origins pending)⟩, rfl⟩
    | some request =>
      let candidate := template.candidate caller context origins request
      let input := candidate.input program state pending
      let receipt := NamedGuardedCandidateExecution.execute input template.body
      let execution : Execution Context := match receipt.result with
        | .reference => ⟨receipt.budget, [], .reference input.before⟩
        | .suspended reason saved => ⟨receipt.budget, [], .suspended reason saved⟩
        | .advanced next => ⟨receipt.budget, next.events input, .complete (state.advance next)⟩
      ⟨execution, by
        have fields := CapturedQueryOperands.request_fields _ _ _ request requested
        have same := candidate_entrance template caller context origins request fields.1 program state pending
        change input.before = entrance template.source (.var template.body.result) caller state context origins pending at same
        have actual := receipt.exact
        change (ScopedQuerySource.machine .relational program).run receipt.budget input.before =
          receipt.result.observation input at actual
        rw [same] at actual
        cases result : receipt.result with
        | reference =>
          simpa only [execution, result, Execution.observation, Stop.outcome,
            NamedGuardedCandidateExecution.Result.observation] using actual
        | suspended reason saved =>
          simpa only [execution, result, Execution.observation, Stop.outcome,
            NamedGuardedCandidateExecution.Result.observation] using actual
        | advanced next =>
          have endpoint : next.endpoint input = (state.advance next).cursor pending :=
            NamedGuardedCandidateBatch.advanced_endpoint candidate program state pending next
          simpa only [execution, result, Execution.observation, Stop.outcome,
            NamedGuardedCandidateExecution.Result.observation, endpoint] using actual⟩

def leaf (program : SpaceSemantics.Program) (template : Template) (Context : Type) : Leaf program Context where
  source := template.source
  destination := .var template.body.result
  execute caller state context origins pending := (invoke program template caller state context origins pending).execution
  exact caller state context origins pending := (invoke program template caller state context origins pending).exact

/-- Recover the actual request and completed primitive publication from the
executed leaf, rather than accepting a predicted post-state as a premise. -/
theorem completed_origin (program : SpaceSemantics.Program) (template : Template)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (invoke program template caller state context origins pending).execution.stop = .complete after) :
    ∃ principal request advance,
      resolve caller.bindings = some principal ∧
      LiteralQuerySource.ofPattern template.satisfactionHandle (read principal template.body.firstCode) (.symbol "t") = some request ∧
      (NamedGuardedCandidateExecution.execute
        ((template.candidate caller context origins request).input program state pending) template.body).result = .advanced advance ∧
      after = state.advance advance := by
  unfold invoke at completed
  dsimp only at completed
  split at completed
  · cases completed
  next principal resolved =>
    split at completed
    · cases completed
    next request requested =>
      dsimp only at completed
      split at completed
      · cases completed
      · cases completed
      next advance actual =>
        exact ⟨principal, request, advance, resolved, requested, actual, (Stop.complete.inj completed).symm⟩

/-- Successful completion comes from an actual leaf advance; caller/parent
metadata are not fabricated by the nested traversal. -/
theorem completed_advance (program : SpaceSemantics.Program) (template : Template)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (invoke program template caller state context origins pending).execution.stop = .complete after) :
    ∃ advance, after = state.advance advance := by
  unfold invoke at completed
  dsimp only at completed
  split at completed
  · cases completed
  next principal resolved =>
    split at completed
    · cases completed
    next request requested =>
      dsimp only at completed
      split at completed
      · cases completed
      · cases completed
      next advance actual => exact ⟨advance, (Stop.complete.inj completed).symm⟩

theorem completed_context (program : SpaceSemantics.Program) (template : Template)
    (legs : List NestedQuerySource.Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (ScopedNestedQueryExecution.run program (leaf program template Context)
      legs caller state context origins pending).stop = .complete after) :
    after.scope.caller = state.scope.caller ∧ after.parents = state.parents := by
  let invariant : State Context → Prop := fun current =>
    current.scope.caller = state.scope.caller ∧ current.parents = state.parents
  have preserves : ScopedNestedQueryExecution.Preserves invariant (leaf program template Context).execute := by
    intro currentCaller current currentContext currentOrigins currentPending next valid done
    obtain ⟨advance, rfl⟩ := completed_advance program template currentCaller current currentContext currentOrigins currentPending next done
    exact valid
  exact ScopedNestedQueryExecution.run_preserves program (leaf program template Context) invariant preserves legs
    caller state context origins pending after ⟨rfl, rfl⟩ completed

/-- The instantiated guarded chain has exact scoped source semantics, not
only the generic theorem's assumed leaf interface. -/
theorem run_exact (program : SpaceSemantics.Program) (template : Template) (legs : List NestedQuerySource.Leg) :
    ScopedNestedQueryExecution.Correct program (ScopedNestedQueryExecution.source legs template.source)
      (.var template.body.result) (ScopedNestedQueryExecution.run program (leaf program template Context) legs) :=
  ScopedNestedQueryExecution.run_exact program (leaf program template Context) legs

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource
