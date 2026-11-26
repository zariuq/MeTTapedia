import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-! An ordinary returned batch uses the nearest continuation, not the
rest of the stack. These laws keep list order and duplicate occurrences.
Collection snapshots use a separate world service. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEReturnEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Policy Result WorldEnvironment readResult publishResult tupleSingleton tuplePrepend argumentPrepend
    functionAssemble diagnosticResults)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open Mettapedia.Machines.OrderedProtocol.Completion (SuccessPriorityRel)
open HEFocused (Focus Parent Leaf)

def covered : Continuation → Bool
  | .collect _ => false
  | _ => true

inductive Plan (policy : Policy) : Continuation → List Result → Leaf → List Continuation → Prop where
  | publish {original raw selected} :
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      Plan policy (.publish original) raw (.returning (selected.map (publishResult policy original))) []
  | singleton {results} :
      Plan policy .singleton results (.returning (results.map tupleSingleton)) []
  | branches {live scope tail heads} :
      Plan policy (.branches live scope tail) heads (.work (.branches live scope tail heads)) []
  | tupleTail {head results} :
      Plan policy (.tupleTail head) results (.returning (results.map (tuplePrepend head))) []
  | arguments {live scope original requests heads} :
      Plan policy (.arguments live scope original requests) heads
        (.work (.argumentBranches live scope original requests heads)) []
  | argumentTail {head results} :
      Plan policy (.argumentTail head) results (.returning (results.map (argumentPrepend head))) []
  | functionHeads {live scope requests heads} :
      Plan policy (.functionHeads live scope requests) heads (.work (.functionBranches live scope requests heads)) []
  | functionAssemble {head results} :
      Plan policy (.functionAssemble head) results (.returning (results.map (functionAssemble head))) []
  | diagnostics {errors activation results} :
      Plan policy (.diagnostics errors activation) results (.returning (results ++ diagnosticResults errors activation)) []
  | boundaryBatch {live scope caller site results} :
      Plan policy (.boundaryBatch live scope caller site) results (.work (.boundaryBatch live scope caller site results)) []
  | calls {live scope expected results} :
      Plan policy (.calls live scope expected) results (.work (.calls live scope expected results)) []
  | append {remaining results} :
      Plan policy (.append remaining) results (.work remaining) [.prepend results]
  | prepend {selected results} :
      Plan policy (.prepend selected) results (.returning (selected ++ results)) []

theorem Plan.covered {policy frame results body frames} (scheduled : Plan policy frame results body frames) :
    covered frame = true := by cases scheduled <;> rfl

theorem Plan.frames_bound {policy frame results body frames} (scheduled : Plan policy frame results body frames) :
    frames.length ≤ 1 := by cases scheduled <;> simp

/-- Returning to an ordinary continuation is determined by the batch
and the nearest frame. In particular, success priority does not choose
one of several equal successes. -/
theorem Plan.functional {policy frame results first second front tail}
    (left : Plan policy frame results first front) (right : Plan policy frame results second tail) :
    first = second ∧ front = tail := by
  cases left <;> cases right <;> try exact ⟨rfl, rfl⟩
  case publish.publish =>
    refine ⟨congrArg (fun batch : List Result => Leaf.returning (batch.map (publishResult policy _))) ?_, rfl⟩
    apply SuccessPriorityRel.functional <;> assumption

variable {Context World : Type}

theorem step_iff (env : WorldEnvironment Context World) (policy : Policy)
    (frame : Continuation) (supported : covered frame = true) (results : List Result)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (seen : List Result) (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
      ⟨world, scope, .returning results, frame :: stack, parents, seen⟩ target ↔
      ∃ body newFrames, Plan policy frame results body newFrames ∧
        target = ⟨world, scope, body, newFrames ++ stack, parents, seen⟩ := by
  constructor
  · intro moved
    cases moved with
    | perform stepped =>
      change WorldLocalStepWith env.arguments env.view env.services env.dispatch env.lookup policy world scope
        (.returning results, frame :: stack) _ _ at stepped
      cases stepped with
      | core incoming _ localStep outgoing =>
        cases incoming
        cases localStep <;> cases outgoing
        all_goals first
          | exact ⟨_, _, .publish (by assumption), rfl⟩
          | exact ⟨_, _, .singleton, rfl⟩
          | exact ⟨_, _, .branches, rfl⟩
          | exact ⟨_, _, .tupleTail, rfl⟩
          | exact ⟨_, _, .arguments, rfl⟩
          | exact ⟨_, _, .argumentTail, rfl⟩
          | exact ⟨_, _, .functionHeads, rfl⟩
          | exact ⟨_, _, .functionAssemble, rfl⟩
          | exact ⟨_, _, .diagnostics, rfl⟩
          | exact ⟨_, _, .boundaryBatch, rfl⟩
          | exact ⟨_, _, .calls, rfl⟩
          | exact ⟨_, _, .append, rfl⟩
          | exact ⟨_, _, .prepend, rfl⟩
      | collectEnter _ => cases supported
  · rintro ⟨body, newFrames, planned, rfl⟩
    let before : Focus Context World := ⟨world, scope, .returning results, frame :: stack, parents, seen⟩
    cases planned with
    | publish chosen => exact .perform (before := before) (.core (.returning _) rfl (.publish chosen) (.returning _))
    | singleton => exact .perform (before := before) (.core (.returning _) rfl .singleton (.returning _))
    | branches => exact .perform (before := before) (.core (.returning _) rfl .branches (.work _))
    | tupleTail => exact .perform (before := before) (.core (.returning _) rfl .tupleTail (.returning _))
    | arguments => exact .perform (before := before) (.core (.returning _) rfl .arguments (.work _))
    | argumentTail => exact .perform (before := before) (.core (.returning _) rfl .argumentTail (.returning _))
    | functionHeads => exact .perform (before := before) (.core (.returning _) rfl .functionHeads (.work _))
    | functionAssemble => exact .perform (before := before) (.core (.returning _) rfl .functionAssemble (.returning _))
    | diagnostics => exact .perform (before := before) (.core (.returning _) rfl .diagnostics (.returning _))
    | boundaryBatch => exact .perform (before := before) (.core (.returning _) rfl .boundaryBatch (.work _))
    | calls => exact .perform (before := before) (.core (.returning _) rfl .calls (.work _))
    | append => exact .perform (before := before) (.core (.returning _) rfl .append (.work _))
    | prepend => exact .perform (before := before) (.core (.returning _) rfl .prepend (.returning _))

theorem result_unique (env : WorldEnvironment Context World) (policy : Policy)
    (frame : Continuation) (supported : covered frame = true) (results : List Result)
    (world : World) (scope : Context) (stack : List Continuation) (parents : List (Parent Context))
    (seen : List Result) {first second : Focus Context World}
    (left : HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
      ⟨world, scope, .returning results, frame :: stack, parents, seen⟩ first)
    (right : HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
      ⟨world, scope, .returning results, frame :: stack, parents, seen⟩ second) :
    first = second := by
  obtain ⟨_, _, leftPlan, rfl⟩ := (step_iff env policy frame supported results world scope stack parents seen _).mp left
  obtain ⟨_, _, rightPlan, rfl⟩ := (step_iff env policy frame supported results world scope stack parents seen _).mp right
  obtain ⟨rfl, rfl⟩ := leftPlan.functional rightPlan
  rfl

end Mettapedia.Languages.MeTTa.SpaceTheory.HEReturnEntry
