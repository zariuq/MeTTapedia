import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-!
# Ordered HE application without rereading the space

An application schedules its next obligation with the activation of that
branch. It keeps the other occurrences literal and ordered. Scheduling only
uses the pending task: type lookup and evaluation belong to the work it
schedules, not to scheduling itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEApplicationEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentStopped Result Policy WorldEnvironment argumentScope invocationReturnType)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation Task)
open HEFocused (Focus Leaf Parent)

def covered : Task → Bool
  | .tuple .. | .branches .. | .arguments .. | .argumentBranches ..
  | .function .. | .functionBranches .. | .invocations .. | .calls .. => true
  | _ => false

inductive Plan : Task → Leaf → List Continuation → Prop where
  | tupleEmpty {live scope frame} :
      Plan (.tuple live scope [] frame) (.returning [(.expression .active [], frame)]) []
  | tupleOne {live scope value frame} :
      Plan (.tuple live scope [value] frame)
        (.work (.atom live scope value Atom.undefinedType frame)) [.singleton]
  | tupleMore {live scope head second tail frame} :
      Plan (.tuple live scope (head :: second :: tail) frame)
        (.work (.atom (.expression ((second :: tail).map Entry.Value.erase) :: live)
          scope head Atom.undefinedType frame)) [.branches live scope (second :: tail)]
  | branchesEnd {live scope tail} : Plan (.branches live scope tail []) (.returning []) []
  | branchesStop {live scope tail first rest} :
      IsEmptyOrErrorRel first.1.erase →
      Plan (.branches live scope tail (first :: rest))
        (.work (.branches live scope tail rest)) [.prepend [first]]
  | branchesNext {live scope tail first rest} :
      ¬ IsEmptyOrErrorRel first.1.erase →
      Plan (.branches live scope tail (first :: rest))
        (.work (.tuple (first.1.erase :: live) scope tail first.2))
        [.tupleTail first.1, .append (.branches live scope tail rest)]
  | argumentsEnd {live scope frame} :
      Plan (.arguments live scope [] frame) (.returning [(Entry.Value.argumentPacket [], frame)]) []
  | argumentsNext {live scope request requests frame} :
      Plan (.arguments live scope (request :: requests) frame)
        (.work (.atom (argumentScope requests ++ live) scope request.1 request.2 frame))
        [.arguments live scope request.1 requests]
  | argumentBranchesEnd {live scope original requests} :
      Plan (.argumentBranches live scope original requests []) (.returning []) []
  | argumentBranchesStop {live scope original requests first rest} :
      ArgumentStopped original first →
      Plan (.argumentBranches live scope original requests (first :: rest))
        (.work (.argumentBranches live scope original requests rest)) [.prepend [first]]
  | argumentBranchesNext {live scope original requests first rest} :
      ¬ ArgumentStopped original first →
      Plan (.argumentBranches live scope original requests (first :: rest))
        (.work (.arguments (first.1.erase :: live) scope requests first.2))
        [.argumentTail first.1, .append (.argumentBranches live scope original requests rest)]
  | functionStart {live scope expected signature operator arguments frame} :
      arguments.length = signature.argumentTypes.length →
      Plan (.function live scope expected signature operator arguments frame)
        (.work (.atom (signature.functionType :: arguments.map Entry.Value.erase ++ live)
          (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
          operator signature.functionType frame))
        [.functionHeads live scope (arguments.zip signature.argumentTypes)]
  | functionBranchesEnd {live scope requests} :
      Plan (.functionBranches live scope requests []) (.returning []) []
  | functionBranchesStop {live scope requests first rest} :
      IsEmptyOrErrorRel first.1.erase →
      Plan (.functionBranches live scope requests (first :: rest))
        (.work (.functionBranches live scope requests rest)) [.prepend [first]]
  | functionBranchesNext {live scope requests first rest} :
      ¬ IsEmptyOrErrorRel first.1.erase →
      Plan (.functionBranches live scope requests (first :: rest))
        (.work (.arguments (first.1.erase :: live) scope requests first.2))
        [.functionAssemble first.1, .append (.functionBranches live scope requests rest)]
  | invocationsEnd {live scope expected signature operator arguments} :
      Plan (.invocations live scope expected signature operator arguments []) (.returning []) []
  | invocationsNext {live scope expected signature operator arguments frame pending} :
      Plan (.invocations live scope expected signature operator arguments (frame :: pending))
        (.work (.function (invocationReturnType signature :: live) scope expected signature operator arguments frame))
        [.calls live scope (invocationReturnType signature),
          .append (.invocations live scope expected signature operator arguments pending)]
  | callsEnd {live scope expected} : Plan (.calls live scope expected []) (.returning []) []
  | callsNext {live scope expected first rest} :
      Plan (.calls live scope expected (first :: rest)) (.work (.call live scope first.1 expected first.2))
        [.append (.calls live scope expected rest)]

theorem Plan.covered {task body frames} (scheduled : Plan task body frames) : covered task = true := by
  cases scheduled <;> rfl

theorem Plan.frames_bound {task body frames} (scheduled : Plan task body frames) : frames.length ≤ 2 := by
  cases scheduled <;> simp

/-- No extra scheduling alternative comes from seeing a different space
or lookup service. In the two error-sensitive branches the test and its
negation are mutually exclusive. -/
theorem Plan.functional {task first second front tail}
    (left : Plan task first front) (right : Plan task second tail) :
    first = second ∧ front = tail := by
  cases left <;> cases right <;> first
  | exact ⟨rfl, rfl⟩
  | exact (by contradiction)

variable {Context World : Type}

theorem step_iff (env : WorldEnvironment Context World) (policy : Policy)
    (task : Task) (supported : covered task = true) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (seen : List Result)
    (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
        ⟨world, scope, .work task, stack, parents, seen⟩ target ↔
      ∃ body frames, Plan task body frames ∧ target = ⟨world, scope, body, frames ++ stack, parents, seen⟩ := by
  constructor
  · intro moved
    cases task <;> simp only [covered, Bool.false_eq_true] at supported
    all_goals
      cases moved with
      | perform step =>
        cases step with
        | core incoming _ localStep outgoing =>
          cases incoming
          cases localStep <;> cases outgoing
          all_goals first
            | exact ⟨_, _, .tupleEmpty, rfl⟩
            | exact ⟨_, _, .tupleOne, rfl⟩
            | exact ⟨_, _, .tupleMore, rfl⟩
            | exact ⟨_, _, .branchesEnd, rfl⟩
            | exact ⟨_, _, .branchesStop (by assumption), rfl⟩
            | exact ⟨_, _, .branchesNext (by assumption), rfl⟩
            | exact ⟨_, _, .argumentsEnd, rfl⟩
            | exact ⟨_, _, .argumentsNext, rfl⟩
            | exact ⟨_, _, .argumentBranchesEnd, rfl⟩
            | exact ⟨_, _, .argumentBranchesStop (by assumption), rfl⟩
            | exact ⟨_, _, .argumentBranchesNext (by assumption), rfl⟩
            | exact ⟨_, _, .functionStart (by assumption), rfl⟩
            | exact ⟨_, _, .functionBranchesEnd, rfl⟩
            | exact ⟨_, _, .functionBranchesStop (by assumption), rfl⟩
            | exact ⟨_, _, .functionBranchesNext (by assumption), rfl⟩
            | exact ⟨_, _, .invocationsEnd, rfl⟩
            | exact ⟨_, _, .invocationsNext, rfl⟩
            | exact ⟨_, _, .callsEnd, rfl⟩
            | exact ⟨_, _, .callsNext, rfl⟩
  · rintro ⟨body, frames, scheduled, rfl⟩
    let before : Focus Context World := ⟨world, scope, .work task, stack, parents, seen⟩
    cases scheduled with
    | tupleEmpty => exact .perform (before := before) (.core (.work _) rfl .tupleNil (.returning _))
    | tupleOne => exact .perform (before := before) (.core (.work _) rfl .tupleSingleton (.work _))
    | tupleMore => exact .perform (before := before) (.core (.work _) rfl .tupleCons (.work _))
    | branchesEnd => exact .perform (before := before) (.core (.work _) rfl .branchesNil (.returning _))
    | branchesStop stopped => exact .perform (before := before) (.core (.work _) rfl (.branchesStopped stopped) (.work _))
    | branchesNext ready => exact .perform (before := before) (.core (.work _) rfl (.branchesContinue ready) (.work _))
    | argumentsEnd => exact .perform (before := before) (.core (.work _) rfl .argumentsNil (.returning _))
    | argumentsNext => exact .perform (before := before) (.core (.work _) rfl .argumentsCons (.work _))
    | argumentBranchesEnd => exact .perform (before := before) (.core (.work _) rfl .argumentBranchesNil (.returning _))
    | argumentBranchesStop stopped =>
      exact .perform (before := before) (.core (.work _) rfl (.argumentBranchesStopped stopped) (.work _))
    | argumentBranchesNext ready =>
      exact .perform (before := before) (.core (.work _) rfl (.argumentBranchesContinue ready) (.work _))
    | functionStart arity => exact .perform (before := before) (.core (.work _) rfl (.functionStart arity) (.work _))
    | functionBranchesEnd => exact .perform (before := before) (.core (.work _) rfl .functionBranchesNil (.returning _))
    | functionBranchesStop stopped =>
      exact .perform (before := before) (.core (.work _) rfl (.functionBranchesStopped stopped) (.work _))
    | functionBranchesNext ready =>
      exact .perform (before := before) (.core (.work _) rfl (.functionBranchesContinue ready) (.work _))
    | invocationsEnd => exact .perform (before := before) (.core (.work _) rfl .invocationsNil (.returning _))
    | invocationsNext => exact .perform (before := before) (.core (.work _) rfl .invocationsCons (.work _))
    | callsEnd => exact .perform (before := before) (.core (.work _) rfl .callsNil (.returning _))
    | callsNext => exact .perform (before := before) (.core (.work _) rfl .callsCons (.work _))

end Mettapedia.Languages.MeTTa.SpaceTheory.HEApplicationEntry
