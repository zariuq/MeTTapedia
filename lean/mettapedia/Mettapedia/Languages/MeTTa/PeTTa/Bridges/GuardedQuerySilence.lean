import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource

/-!
# Collection-local guarded execution publishes no root answer events

A held collection caller keeps answer packets in its local collector.
Reference handoff and suspension likewise publish no root answer packets.
The result says nothing about rollback: world writes and reached residuals
remain in the execution result, and output effects are separate observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQuerySilence

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ScopedNestedQueryExecution (Worker Execution Stop visit run)

variable {Context : Type}

theorem invoke_events (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (held : state.scope.caller.isNone = false) :
    (GuardedNestedQuerySource.invoke program template caller state context origins pending).execution.events = [] := by
  unfold GuardedNestedQuerySource.invoke
  dsimp only
  split
  · rfl
  next principal resolved =>
    split
    · rfl
    next request requested =>
      dsimp only
      split
      · rfl
      · rfl
      next advance completed =>
        simp only [NamedGuardedCandidateExecution.Advance.events, NamedGuardedCandidateBatch.Candidate.input,
          held, Bool.false_eq_true, ↓reduceIte]

private theorem visit_events (worker : Worker Context)
    (quiet : ∀ caller state context origins pending, state.scope.caller.isNone = false →
      (worker caller state context origins pending).events = [])
    (keeps : ∀ caller state context origins pending after,
      (worker caller state context origins pending).stop = .complete after →
        after.scope.caller = state.scope.caller)
    (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (state : State Context) (pending : List (CollectionWork Context))
    (held : state.scope.caller.isNone = false) :
    (visit worker older context origins selected state pending).events = [] := by
  induction selected generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    have firstQuiet := quiet {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending) held
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first] at stopped
      simpa only [visit, stopped] using firstQuiet
    | suspended request saved =>
      dsimp only [first] at stopped
      simpa only [visit, stopped] using firstQuiet
    | complete next =>
      have same := keeps {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) next stopped
      have nextHeld : next.scope.caller.isNone = false := by rw [same]; exact held
      have tailQuiet := ih next nextHeld
      dsimp only [first] at stopped
      simp only [visit, stopped, firstQuiet, tailQuiet, List.nil_append]

/-- Silence concerns all outcomes of the actual traversal, not only the
completed case. Earlier completed siblings can still have changed the world. -/
theorem run_events (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (legs : List NestedQuerySource.Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (held : state.scope.caller.isNone = false) :
    (run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller state context origins pending).events = [] := by
  induction legs generalizing caller state context origins pending with
  | nil => exact invoke_events program template caller state context origins pending held
  | cons leg rest ih =>
    unfold run
    dsimp only
    split
    · rfl
    next selected captured =>
      exact visit_events (run program (GuardedNestedQuerySource.leaf program template Context) rest)
        (fun current before currentContext currentOrigins currentPending childHeld =>
          ih current before currentContext currentOrigins currentPending childHeld)
        (fun current before currentContext currentOrigins currentPending after completed =>
          (GuardedNestedQuerySource.completed_context program template rest current before currentContext
            currentOrigins currentPending after completed).1)
        caller.goals context origins selected.choices state pending held

theorem childExecution_events (input : GuardedCountSource.Input Context) : input.childExecution.events = [] :=
  run_events input.program input.childTemplate input.legs input.childCaller input.childState
    input.context input.origins [] rfl

/-- Root packets are not covered by the collection-local silence theorem. -/
theorem root_packets_remain_visible (input : NamedPresenceConditional.Input Context)
    (advance : NamedGuardedCandidateExecution.Advance) (root : input.scope.caller.isNone = true) :
    advance.events input = advance.answers := by
  simp only [NamedGuardedCandidateExecution.Advance.events, root, ↓reduceIte]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQuerySilence
