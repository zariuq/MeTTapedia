import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-! The local scheduling laws for completed producers and body boundaries.
Each law owes only a new task or answer batch and a short continuation
prefix. It does not execute the newly scheduled task. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (CastLookup FunctionPending NativeCompletedReturnRel Policy WorldEnvironment substituteBinder)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith)
open HEFocused (Focus Leaf Parent)

def covered : Task → Bool
  | .body .. | .boundary .. | .boundaryBatch .. | .returned .. => true
  | _ => false

inductive Plan (space : Space) (lookup : CastLookup) (policy : Policy) : Task → Leaf → List Continuation → Prop where
  | beginBody {live scope caller value activation} :
      Plan space lookup policy (.body live scope caller value activation)
        (.work (.minimal live scope caller value activation)) [.boundaryBatch live scope caller .body]
  | chain {live scope caller name template value activation} :
      Plan space lookup policy (.boundary live scope caller (.chain name template) value activation)
        (.work (.minimal live scope caller (substituteBinder policy name (activation.read policy value) template) activation)) []
  | bodyTerminal {live scope caller value activation} :
      Minimal.embeddedInstruction (activation.read policy value).erase = false →
      Plan space lookup policy (.boundary live scope caller .body value activation)
        (.returning [(activation.read policy value, activation)]) []
  | bodyResume {live scope caller value activation} :
      Minimal.embeddedInstruction (activation.read policy value).erase = true →
      Plan space lookup policy (.boundary live scope caller .body value activation)
        (.work (.body live scope caller (activation.read policy value) activation)) []
  | functionReturn {live scope caller readiness value activation} :
      Plan space lookup policy
        (.boundary live scope caller .functionDone (.expression readiness [.symbol "return", value]) activation)
        (.returning [(value, activation)]) []
  | functionNoReturn {live scope caller value activation} :
      (∀ returned, value.erase ≠ .expression [.symbol "return", returned]) →
      Plan space lookup policy (.boundary live scope caller .functionDone value activation)
        (.returning [(Entry.Value.ofAtom (Minimal.functionTerminalResult caller value.erase), activation)]) []
  | producerRaw {live scope caller value activation} :
      ¬ FunctionPending policy value →
      Plan space lookup policy (.boundary live scope caller .producer value activation)
        (.returning [(value, activation)]) []
  | producerFunction {live scope caller value activation} :
      FunctionPending policy value →
      Plan space lookup policy (.boundary live scope caller .producer value activation)
        (.work (.minimal live scope caller value activation)) []
  | acceptReturn {live scope caller original expected value activation} :
      Plan space lookup policy (.boundary live scope caller (.returned original expected) value activation)
        (.work (.returned live scope original expected value activation)) []
  | batchNil {live scope caller site} :
      Plan space lookup policy (.boundaryBatch live scope caller site []) (.returning []) []
  | batchCons {live scope caller site head tail} :
      Plan space lookup policy (.boundaryBatch live scope caller site (head :: tail))
        (.work (.boundary live scope caller site head.1 head.2)) [.append (.boundaryBatch live scope caller site tail)]
  | nativeEmittedRaw {live scope caller original value activation} :
      Plan space lookup policy (.boundary live scope caller (.native original none .emitted) value activation)
        (.work (.boundary live scope (some original.erase) .producer value activation)) []
  | nativeEmittedTyped {live scope caller original expected value activation} :
      Plan space lookup policy
        (.boundary live scope caller (.native original (some expected) .emitted) value activation)
        (.work (.boundary (expected :: live) scope (some original.erase) .producer value activation))
        [.boundaryBatch live scope caller (.returned original expected)]
  | nativeCompletedRaw {live scope caller original value activation} :
      Plan space lookup policy (.boundary live scope caller (.native original none .completed) value activation)
        (.returning [(value, activation)]) []
  | nativeCompletedTyped {live scope caller original expected value activation results} :
      NativeCompletedReturnRel space
        (lookup (invocationTypeScope scope live original.erase expected activation.bindings) space)
        policy value expected activation results →
      Plan space lookup policy
        (.boundary live scope caller (.native original (some expected) .completed) value activation)
        (.returning results) []
  | refused {live scope original expected value activation} :
      value.erase = Atom.notReducible →
      Plan space lookup policy (.returned live scope original expected value activation)
        (.returning [(original, activation)]) []
  | stopped {live scope original expected value activation} :
      IsEmptyOrErrorRel value.erase →
      Plan space lookup policy (.returned live scope original expected value activation)
        (.returning [(value, activation)]) []
  | evaluate {live scope original expected value activation} :
      value.erase ≠ Atom.notReducible → ¬ IsEmptyOrErrorRel value.erase →
      Plan space lookup policy (.returned live scope original expected value activation)
        (.work (.atom live scope value expected activation)) []

theorem Plan.covered {space lookup policy task body frames} (schedule : Plan space lookup policy task body frames) :
    covered task = true := by cases schedule <;> rfl

theorem Plan.frames_bound {space lookup policy task body frames} (schedule : Plan space lookup policy task body frames) :
    frames.length ≤ 1 := by cases schedule <;> simp

variable {Context World : Type}

theorem step_iff (env : WorldEnvironment Context World) (policy : Policy)
    (task : Task) (supported : covered task = true) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (seen : List Completed.Result)
    (target : Focus Context World) :
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup policy
        ⟨world, scope, .work task, stack, parents, seen⟩ target ↔
      ∃ body frames, Plan (env.view world scope) env.lookup policy task body frames ∧
        target = ⟨world, scope, body, frames ++ stack, parents, seen⟩ := by
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
            | exact ⟨_, _, .beginBody, rfl⟩
            | exact ⟨_, _, .chain, rfl⟩
            | exact ⟨_, _, .bodyTerminal (by assumption), rfl⟩
            | exact ⟨_, _, .bodyResume (by assumption), rfl⟩
            | exact ⟨_, _, .functionReturn, rfl⟩
            | exact ⟨_, _, .functionNoReturn (by assumption), rfl⟩
            | exact ⟨_, _, .producerRaw (by assumption), rfl⟩
            | exact ⟨_, _, .producerFunction (by assumption), rfl⟩
            | exact ⟨_, _, .acceptReturn, rfl⟩
            | exact ⟨_, _, .batchNil, rfl⟩
            | exact ⟨_, _, .batchCons, rfl⟩
            | exact ⟨_, _, .nativeEmittedRaw, rfl⟩
            | exact ⟨_, _, .nativeEmittedTyped, rfl⟩
            | exact ⟨_, _, .nativeCompletedRaw, rfl⟩
            | exact ⟨_, _, .nativeCompletedTyped (by assumption), rfl⟩
            | exact ⟨_, _, .refused (by assumption), rfl⟩
            | exact ⟨_, _, .stopped (by assumption), rfl⟩
            | exact ⟨_, _, .evaluate (by assumption) (by assumption), rfl⟩
  · rintro ⟨body, frames, planned, rfl⟩
    let before : Focus Context World := ⟨world, scope, .work task, stack, parents, seen⟩
    cases planned with
    | beginBody => exact .perform (before := before) (.core (.work _) rfl .bodyStart (.work _))
    | chain => exact .perform (before := before) (.core (.work _) rfl .boundaryChain (.work _))
    | bodyTerminal terminal => exact .perform (before := before) (.core (.work _) rfl (.boundaryBodyTerminal terminal) (.returning _))
    | bodyResume resume => exact .perform (before := before) (.core (.work _) rfl (.boundaryBodyResume resume) (.work _))
    | functionReturn => exact .perform (before := before) (.core (.work _) rfl .boundaryFunctionReturn (.returning _))
    | functionNoReturn missing =>
      exact .perform (before := before) (.core (.work _) rfl (.boundaryFunctionNoReturn missing) (.returning _))
    | producerRaw raw => exact .perform (before := before) (.core (.work _) rfl (.boundaryProducerRaw raw) (.returning _))
    | producerFunction pending =>
      exact .perform (before := before) (.core (.work _) rfl (.boundaryProducerFunction pending) (.work _))
    | acceptReturn => exact .perform (before := before) (.core (.work _) rfl .boundaryReturned (.work _))
    | batchNil => exact .perform (before := before) (.core (.work _) rfl .boundaryBatchNil (.returning _))
    | batchCons => exact .perform (before := before) (.core (.work _) rfl .boundaryBatchCons (.work _))
    | nativeEmittedRaw => exact .perform (before := before) (.core (.work _) rfl .boundaryNativeEmittedRaw (.work _))
    | nativeEmittedTyped => exact .perform (before := before) (.core (.work _) rfl .boundaryNativeEmittedReturn (.work _))
    | nativeCompletedRaw => exact .perform (before := before) (.core (.work _) rfl .boundaryNativeCompletedRaw (.returning _))
    | nativeCompletedTyped admitted =>
      exact .perform (before := before) (.core (.work _) rfl (.boundaryNativeCompletedReturn admitted) (.returning _))
    | refused bad => exact .perform (before := before) (.core (.work _) rfl (.returnRefused bad) (.returning _))
    | stopped error => exact .perform (before := before) (.core (.work _) rfl (.returnStopped error) (.returning _))
    | evaluate success ready => exact .perform (before := before) (.core (.work _) rfl (.returnEvaluate success ready) (.work _))

end Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyEntry
