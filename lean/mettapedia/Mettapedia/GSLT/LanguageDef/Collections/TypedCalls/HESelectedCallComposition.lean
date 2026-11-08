import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReadyConstructorBoundary

/-!
# Selected-function composition through an earned ordinary call

Type selection, operator evaluation and argument delivery do not require the
reached call to match an equation. The ordinary call can instead restore an
absent constructor, return an error, or evaluate matched equations. This module
composes the existing source judgments and checked worker blocks at that exact
boundary. It retains caller stacks, emitted prefixes, binding records and final
publication; no second evaluator or whole-expression execution premise is used
by the derivation-level theorem.

The administrative composition has twenty steps in addition to its three
earned child blocks. This count is not a native instruction-cost claim.

This composition selects one signature/record, one delivered operator and
one complete argument packet; its ordinary call may return an arbitrary
ordered result batch. Multiple operator or argument packets require the
corresponding outer branch-spine composition. The derivation-level wrapper
uses the existing error/absence/equation call grammar; additional host calls
can use the component theorem after earning their own source and task laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Machines.OrderedProtocol.Completion
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveStrategy FirstSuccessRecursiveExecution
open FirstSuccessSourceExecution FirstSuccessSourceApplicability
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Spec.Type.Presentation.Exact Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedCastAndHeadBoundary
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

/-- Compose the checked worker's selected-entry prefix with its earned
operator, argument and ordinary-call blocks. The independent source judgment
is supplied to this low-level assembly lemma; the public derivation lemma
below reconstructs it from the same local source components. -/
theorem selectedWorker_of_runs
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator opVal expected : Atom) (arguments retVals : List Atom)
    (ctxVal ctxOp ctxOpVal : Entry.Value)
    (ctxArgs ctxRetVals : List Entry.Value)
    (wB wBSelected wBHead wBArgs : Bindings)
    (cFrame cFrameSelected cFrameHead cFrameArgs : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (finalResults : ResultSet)
    (ctxFinalResults : List Completed.Result)
    (fuel opSteps argSteps callSteps readDepth : Nat)
    (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (readiness : Entry.Status)
    (entry : ScopedSelectedFunctionEntry space policy operator arguments opVal expected
      wB wBSelected fuel live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
      readiness signature candidates wStack wEmitted)
    (opRun :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedTaskRun space dispatch hostDispatch policy
        (.atom operator signature.functionType wBSelected (fuel + 1)
          (signature.functionType :: arguments ++ (resultType :: live)))
        (.atom
          (signature.functionType :: ctxArgs.map Entry.Value.erase ++ (resultType :: live))
          (scope ++ expectedApplicationScope
            (.expression ((ctxOp :: ctxArgs).map Entry.Value.erase)) expected)
          ctxOp signature.functionType cFrameSelected)
        (.heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack)
        (.functionHeads (resultType :: live) scope
          (ctxArgs.zip signature.argumentTypes) :: cCallStack)
        wEmitted cEmitted opSteps
        [(opVal, wBHead)] [(ctxOpVal, cFrameHead)])
    (argsRun :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedTaskRun space dispatch hostDispatch policy
        (.args arguments signature.argumentTypes wBHead (fuel + 1)
          (opVal :: resultType :: live))
        (.arguments (opVal :: resultType :: live) scope
          (ctxArgs.zip signature.argumentTypes) cFrameHead)
        (.functionTail opVal ::
          .append (.heads signature.functionType arguments (fuel + 1) []
            (resultType :: live)) :: wCallStack)
        (.functionAssemble ctxOpVal ::
          .append (.functionBranches (resultType :: live) scope
            (ctxArgs.zip signature.argumentTypes) []) :: cCallStack)
        wEmitted cEmitted argSteps
        [(argumentPacket retVals, wBArgs)]
        [(Entry.Value.argumentPacket ctxRetVals, cFrameArgs)])
    (callRun :
      let resultType := Completed.invocationReturnType signature
      let outAtom : Atom := .expression (opVal :: retVals)
      let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
      let wDrainStack : List RecursiveTasks.Frame :=
        .append (.calls resultType (fuel + 2) [] live) ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cDrainStack : List RecursiveTasks.Contextual.Continuation :=
        .append (.calls live scope resultType []) ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedTaskRun space dispatch hostDispatch policy
        (.call outAtom resultType wBArgs (fuel + 2) live)
        (.call live scope ctxCall resultType cFrameArgs)
        wDrainStack cDrainStack wEmitted cEmitted callSteps finalResults ctxFinalResults)
    (returnedCovered : ∀ pair ∈ finalResults, pair.2.applyFullCovered pair.1 readDepth = true)
    (returnedStable : ∀ pair ∈ finalResults, pair.2.applyFull pair.1 readDepth = pair.1)
    (source :
      Completed.AtomRel space hostDispatch Completed.scopedLookup live scope
        ctxVal expected cFrame
        ((completedSuccessPriority
          (ctxFinalResults.map (Completed.readResult policy))).map
            (Completed.publishResult policy (.expression (operator :: arguments))))
        (policy := policy)) :
    let expr := Atom.expression (operator :: arguments)
    let cSelected := completedSuccessPriority
      (ctxFinalResults.map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 4) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted
      (opSteps + argSteps + callSteps + 20)
      (successPriority finalResults) cPublished := by
  intro expr cSelected cPublished
  dsimp only at opRun argsRun callRun source
  let resultType := Completed.invocationReturnType signature
  let outAtom : Atom := .expression (opVal :: retVals)
  let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
  let wInvAppend : RecursiveTasks.Frame :=
    .append (.bindingAlternatives expr signature.functionType resultType
      (fuel + 2) [] live)
  let wCallStack : List RecursiveTasks.Frame :=
    .calls resultType (fuel + 2) live :: wInvAppend :: .filter :: wStack
  let wOperatorStack : List RecursiveTasks.Frame :=
    .heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack
  let wArgsStack : List RecursiveTasks.Frame :=
    .functionTail opVal ::
      .append (.heads signature.functionType arguments (fuel + 1) []
        (resultType :: live)) :: wCallStack
  let wDrainStack : List RecursiveTasks.Frame :=
    .append (.calls resultType (fuel + 2) [] live) ::
      wInvAppend :: .filter :: wStack
  have entryBlock := scoped_selected_function_entry_run
    space dispatch hostDispatch policy operator arguments expected
    wB wBSelected (fuel + 2) live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
    readiness signature candidates wStack cStack wEmitted cEmitted
    entry.entry_ready entry.read_shape entry.operator_erase
    entry.input_not_stopped entry.expected_not_atom entry.expected_not_expression
    (by simpa only [show fuel + 2 + 1 = fuel + 3 by omega] using entry.candidate_eq)
    entry.selection_ready entry.worker_selected entry.contextual_selected
  dsimp only at entryBlock
  have finalRel := callRun.results_rel
  have readRel : List.Forall₂ ScopedResultRel finalResults
      (ctxFinalResults.map (Completed.readResult policy)) :=
    ScopedResultRel.forall2_materialized_readResult_stable policy finalRel readDepth
      returnedCovered returnedStable
  have publishedRel : List.Forall₂ ScopedResultRel
      (successPriority finalResults) cPublished :=
    ScopedResultRel.forall2_publishResult policy expr
      (ScopedResultRel.forall2_successPriority readRel)
  have wStepInv : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
        (fuel + 2) [wBSelected] live), .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.func expr signature.functionType wBSelected
          (fuel + 2) (resultType :: live)), wCallStack, wEmitted⟩) := rfl
  have wStepFunc : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.func expr signature.functionType wBSelected
        (fuel + 2) (resultType :: live)), wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.atom operator signature.functionType wBSelected
          (fuel + 1) (signature.functionType :: arguments ++ (resultType :: live))),
          wOperatorStack, wEmitted⟩) := rfl
  have wStepHeads : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(opVal, wBHead)], wOperatorStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.heads signature.functionType arguments (fuel + 1)
          [(opVal, wBHead)] (resultType :: live)), wCallStack, wEmitted⟩) := rfl
  have wStepArgs : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.heads signature.functionType arguments (fuel + 1)
        [(opVal, wBHead)] (resultType :: live)), wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.args arguments signature.argumentTypes wBHead
          (fuel + 1) (opVal :: resultType :: live)), wArgsStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      entry.operator_not_stopped, entry.argument_types_eq, wArgsStack, wCallStack,
      wInvAppend, Transition.relabel]
  have wStepFunctionTail : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(argumentPacket retVals, wBArgs)], wArgsStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [(outAtom, wBArgs)],
          .append (.heads signature.functionType arguments (fuel + 1) []
            (resultType :: live)) :: wCallStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      RecursiveMachine.resume, RecursiveTasks.functionTail, argumentPacket,
      argumentsSucceeded, unpackArguments, argumentValues,
      outAtom, wArgsStack, Transition.relabel]
  have wStepAppendHeads : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(outAtom, wBArgs)],
        .append (.heads signature.functionType arguments (fuel + 1) []
          (resultType :: live)) :: wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.heads signature.functionType arguments (fuel + 1) []
          (resultType :: live)), .prepend [(outAtom, wBArgs)] :: wCallStack,
          wEmitted⟩) := rfl
  have wStepHeadsNil : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.heads signature.functionType arguments (fuel + 1) []
        (resultType :: live)), .prepend [(outAtom, wBArgs)] :: wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [], .prepend [(outAtom, wBArgs)] :: wCallStack,
          wEmitted⟩) := rfl
  have wStepPrependHead : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [], .prepend [(outAtom, wBArgs)] :: wCallStack, wEmitted⟩ =
      some (.silent ⟨space, .returning [(outAtom, wBArgs)], wCallStack, wEmitted⟩) := rfl
  have wStepCalls : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [(outAtom, wBArgs)], wCallStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.calls resultType (fuel + 2) [(outAtom, wBArgs)] live),
          wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepCallsCons : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.calls resultType (fuel + 2) [(outAtom, wBArgs)] live),
        wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.call outAtom resultType wBArgs (fuel + 2) live),
          wDrainStack, wEmitted⟩) := rfl
  have wStepDrain1 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, wDrainStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.calls resultType (fuel + 2) [] live),
          .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepDrain2 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.calls resultType (fuel + 2) [] live),
        .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [],
          .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩) := rfl
  have wStepDrain3 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [],
        .prepend finalResults :: wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning finalResults, wInvAppend :: .filter :: wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have wStepDrain4 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, wInvAppend :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
          (fuel + 2) [] live), .prepend finalResults :: .filter :: wStack,
          wEmitted⟩) := rfl
  have wStepDrain5 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
        (fuel + 2) [] live), .prepend finalResults :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning [], .prepend finalResults :: .filter :: wStack,
          wEmitted⟩) := rfl
  have wStepDrain6 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [], .prepend finalResults :: .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning finalResults, .filter :: wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have wStepPublish : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning finalResults, .filter :: wStack, wEmitted⟩ =
      some (.silent
        ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  have afterEntryRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((opSteps + argSteps + callSteps + 17) + budget)
          ⟨space, .work (.bindingAlternatives expr signature.functionType resultType
            (fuel + 2) [wBSelected] live), .filter :: wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩ := by
    intro budget
    calc
      (Checked.machine dispatch scopedTypes).run
          ((opSteps + argSteps + callSteps + 17) + budget) _ =
        (Checked.machine dispatch scopedTypes).run
          (opSteps + argSteps + callSteps + 16 + budget) _ := by
            rw [show (opSteps + argSteps + callSteps + 17) + budget =
              (opSteps + argSteps + callSteps + 16 + budget) + 1
              by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepInv
      _ = (Checked.machine dispatch scopedTypes).run
          (opSteps + argSteps + callSteps + 15 + budget) _ := by
            rw [show opSteps + argSteps + callSteps + 16 + budget =
              (opSteps + argSteps + callSteps + 15 + budget) + 1
              by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepFunc
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + callSteps + 15 + budget) _ :=
            by
              simpa only [resultType, wOperatorStack, wCallStack, wInvAppend,
                Nat.add_assoc] using
                opRun.worker_run (argSteps + callSteps + 15 + budget)
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + callSteps + 14 + budget) _ := by
            rw [show argSteps + callSteps + 15 + budget =
              (argSteps + callSteps + 14 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepHeads
      _ = (Checked.machine dispatch scopedTypes).run
          (argSteps + callSteps + 13 + budget) _ := by
            rw [show argSteps + callSteps + 14 + budget =
              (argSteps + callSteps + 13 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepArgs
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 13 + budget) _ :=
            by
              simpa only [resultType, wArgsStack, wCallStack, wInvAppend,
                Nat.add_assoc] using
                argsRun.worker_run (callSteps + 13 + budget)
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 12 + budget) _ := by
            rw [show callSteps + 13 + budget =
              (callSteps + 12 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepFunctionTail
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 11 + budget) _ := by
            rw [show callSteps + 12 + budget =
              (callSteps + 11 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepAppendHeads
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 10 + budget) _ := by
            rw [show callSteps + 11 + budget =
              (callSteps + 10 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepHeadsNil
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 9 + budget) _ := by
            rw [show callSteps + 10 + budget =
              (callSteps + 9 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepPrependHead
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 8 + budget) _ := by
            rw [show callSteps + 9 + budget =
              (callSteps + 8 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepCalls
      _ = (Checked.machine dispatch scopedTypes).run
          (callSteps + 7 + budget) _ := by
            rw [show callSteps + 8 + budget =
              (callSteps + 7 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepCallsCons
      _ = (Checked.machine dispatch scopedTypes).run (7 + budget) _ :=
            by
              simpa only [resultType, outAtom, ctxCall, wDrainStack, wInvAppend,
                Nat.add_assoc] using callRun.worker_run (7 + budget)
      _ = (Checked.machine dispatch scopedTypes).run (6 + budget) _ := by
            rw [show 7 + budget = (6 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain1
      _ = (Checked.machine dispatch scopedTypes).run (5 + budget) _ := by
            rw [show 6 + budget = (5 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain2
      _ = (Checked.machine dispatch scopedTypes).run (4 + budget) _ := by
            rw [show 5 + budget = (4 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain3
      _ = (Checked.machine dispatch scopedTypes).run (3 + budget) _ := by
            rw [show 4 + budget = (3 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain4
      _ = (Checked.machine dispatch scopedTypes).run (2 + budget) _ := by
            rw [show 3 + budget = (2 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain5
      _ = (Checked.machine dispatch scopedTypes).run (1 + budget) _ := by
            rw [show 2 + budget = (1 + budget) + 1 by omega]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepDrain6
      _ = (Checked.machine dispatch scopedTypes).run budget _ := by
            rw [Nat.add_comm 1 budget]
            exact (Checked.machine dispatch scopedTypes).run_succ_silent wStepPublish
  have workerRun : ∀ budget,
      (Checked.machine dispatch scopedTypes).run
        ((opSteps + argSteps + callSteps + 20) + budget)
          ⟨space, .work (.atom expr expected wB (fuel + 4) live),
            wStack, wEmitted⟩ =
      (Checked.machine dispatch scopedTypes).run budget
          ⟨space, .returning (successPriority finalResults), wStack, wEmitted⟩ := by
    intro budget
    rw [show (opSteps + argSteps + callSteps + 20) + budget =
        3 + ((opSteps + argSteps + callSteps + 17) + budget)
        by omega,
      entryBlock.2.1 _, afterEntryRun budget]
  exact ⟨by omega, publishedRel, workerRun,
    RecursiveExecution.Contextual.atom_complete source cStack⟩

/-- Reconstruct the independent selected-call source judgment from local
operator, argument and ordinary-call judgments. The call may be absent;
there is no nonempty-equation premise. -/
theorem selectedSource_of_parts
    (space : Space) (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator opVal expected : Atom) (arguments : List Atom)
    (ctxVal ctxOp ctxOpVal : Entry.Value) (ctxArgs ctxRetVals : List Entry.Value)
    (wB wBSelected wBHead : Bindings)
    (cFrame cFrameSelected cFrameHead cFrameArgs : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (ctxFinalResults : List Completed.Result) (fuel : Nat)
    (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (wEmitted : ResultSet) (readiness : Entry.Status)
    (entry : ScopedSelectedFunctionEntry space policy operator arguments opVal expected
      wB wBSelected fuel live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
      readiness signature candidates wStack wEmitted)
    (operatorResultRel : ScopedResultRel (opVal, wBHead) (ctxOpVal, cFrameHead))
    (operatorSource : Completed.AtomRel space hostDispatch Completed.scopedLookup
      (signature.functionType :: ctxArgs.map Entry.Value.erase ++
        (Completed.invocationReturnType signature :: live))
      (scope ++ expectedApplicationScope
        (.expression ((ctxOp :: ctxArgs).map Entry.Value.erase)) expected)
      ctxOp signature.functionType cFrameSelected [(ctxOpVal, cFrameHead)] (policy := policy))
    (argumentsSource : Completed.ArgumentsRel space hostDispatch Completed.scopedLookup
      (opVal :: Completed.invocationReturnType signature :: live) scope
      (ctxArgs.zip signature.argumentTypes) cFrameHead
      [(Entry.Value.argumentPacket ctxRetVals, cFrameArgs)] (policy := policy))
    (callSource : Completed.CallRel space hostDispatch Completed.scopedLookup
      live scope (.expression .active (ctxOpVal :: ctxRetVals))
      (Completed.invocationReturnType signature) cFrameArgs ctxFinalResults (policy := policy)) :
    Completed.AtomRel space hostDispatch Completed.scopedLookup live scope ctxVal expected cFrame
      ((completedSuccessPriority (ctxFinalResults.map (Completed.readResult policy))).map
        (Completed.publishResult policy (.expression (operator :: arguments)))) (policy := policy) := by
  have operatorErase : ctxOpVal.erase = opVal := operatorResultRel.1.symm
  have operatorContinues : ¬IsEmptyOrErrorRel ctxOpVal.erase := by
    rw [operatorErase, Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
    simp [entry.operator_not_stopped]
  have functionBranches : Completed.FunctionBranchesRel space hostDispatch
      Completed.scopedLookup (Completed.invocationReturnType signature :: live) scope
      (ctxArgs.zip signature.argumentTypes) [(ctxOpVal, cFrameHead)]
      [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)]
      (policy := policy) := by
    simpa [Completed.functionAssemble] using
      (Completed.FunctionBranchesRel.continuing
        (head := (ctxOpVal, cFrameHead)) (heads := [])
        (children := [(Entry.Value.argumentPacket ctxRetVals, cFrameArgs)])
        (rest := []) operatorContinues
        (by simpa only [operatorErase] using argumentsSource)
        (Completed.FunctionBranchesRel.nil (space := space)
          (dispatch := hostDispatch) (lookup := Completed.scopedLookup)
          (live := Completed.invocationReturnType signature :: live)
          (scope := scope) (requests := ctxArgs.zip signature.argumentTypes)
          (policy := policy)))
  have functionSource : Completed.FunctionRel space hostDispatch Completed.scopedLookup
      (Completed.invocationReturnType signature :: live) scope expected signature
      ctxOp ctxArgs cFrameSelected
      [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)]
      (policy := policy) :=
    .evaluated entry.arity_eq operatorSource functionBranches
  have callsSource : Completed.CallsRel space hostDispatch Completed.scopedLookup
      live scope (Completed.invocationReturnType signature)
      [(.expression .active (ctxOpVal :: ctxRetVals), cFrameArgs)] ctxFinalResults
      (policy := policy) := by
    simpa only [List.append_nil] using
      (Completed.CallsRel.cons callSource
        (Completed.CallsRel.nil (space := space) (dispatch := hostDispatch)
          (lookup := Completed.scopedLookup) (live := live) (scope := scope)
          (expected := Completed.invocationReturnType signature) (policy := policy)))
  have invocationsSource : Completed.InvocationsRel space hostDispatch
      Completed.scopedLookup live scope expected signature ctxOp ctxArgs
      [cFrameSelected] ctxFinalResults (policy := policy) := by
    simpa only [List.append_nil] using
      (Completed.InvocationsRel.cons functionSource callsSource
        (Completed.InvocationsRel.nil (space := space) (dispatch := hostDispatch)
          (lookup := Completed.scopedLookup) (live := live) (scope := scope)
          (expected := expected) (signature := signature) (operator := ctxOp)
          (arguments := ctxArgs) (policy := policy)))
  have entered : Entry.Rel policy.reentry (cFrame.read policy ctxVal).status
      (cFrame.read policy ctxVal).erase expected .interpret :=
    entry.entry_ready.entry_interpret entry.input_not_stopped
      entry.expected_not_atom entry.expected_not_expression
  have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup
      policy live scope (cFrame.read policy ctxVal).erase ctxOp.erase expected cFrame
      (.selected signature [cFrameSelected]) := by
    simpa only [entry.entry_ready.2.1, entry.operator_erase] using
      entry.contextual_selected
  simpa only [entry.entry_ready.2.1] using
    (Completed.AtomRel.function entered entry.read_shape selectedAtRead
      invocationsSource (completedSuccessPriority_rel
        (ctxFinalResults.map (Completed.readResult policy))))

/-- Local structural derivations earn both the complete selected source call
and its checked worker execution. The reached call may use the existing
absence constructor; the proof never assumes a whole-expression run. -/
theorem selected_of_derivations
    (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator opVal expected : Atom) (arguments retVals : List Atom)
    (ctxVal ctxOp ctxOpVal : Entry.Value)
    (ctxArgs ctxRetVals : List Entry.Value)
    (wB wBSelected wBHead wBArgs : Bindings)
    (cFrame cFrameSelected cFrameHead cFrameArgs : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom)
    (finalResults : ResultSet)
    (ctxFinalResults : List Completed.Result)
    (fuel opSteps argSteps callSteps readDepth : Nat)
    (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    [extension : ScopedAtomExtension]
    [extensionLaws : ScopedAtomExtensionLaws space dispatch hostDispatch policy wEmitted cEmitted]
    (readiness : Entry.Status)
    (entry : ScopedSelectedFunctionEntry space policy operator arguments opVal expected
      wB wBSelected fuel live scope ctxVal ctxOp ctxArgs cFrame cFrameSelected
      readiness signature candidates wStack wEmitted)
    (operatorDerivation :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
          .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
          .publish (.expression (operator :: arguments)) :: cStack
      ScopedAtomDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (fuel + 1)
        (signature.functionType :: arguments ++ (resultType :: live))
        (signature.functionType :: ctxArgs.map Entry.Value.erase ++ (resultType :: live))
        (scope ++ expectedApplicationScope
          (.expression ((ctxOp :: ctxArgs).map Entry.Value.erase)) expected)
        operator ctxOp signature.functionType wBSelected cFrameSelected
        (.heads signature.functionType arguments (fuel + 1) (resultType :: live) :: wCallStack)
        (.functionHeads (resultType :: live) scope
          (ctxArgs.zip signature.argumentTypes) :: cCallStack)
        opSteps [(opVal, wBHead)] [(ctxOpVal, cFrameHead)])
    (argumentsDerivation :
      let resultType := Completed.invocationReturnType signature
      let wCallStack : List RecursiveTasks.Frame :=
        .calls resultType (fuel + 2) live ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
          .filter :: wStack
      let cCallStack : List RecursiveTasks.Contextual.Continuation :=
        .calls live scope resultType ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
          .publish (.expression (operator :: arguments)) :: cStack
      ScopedArgsDerivation space dispatch hostDispatch policy wEmitted cEmitted scope
        (fuel + 1) argSteps (opVal :: resultType :: live)
        arguments signature.argumentTypes (ctxArgs.zip signature.argumentTypes)
        retVals ctxRetVals wBHead cFrameHead wBArgs cFrameArgs
        (.functionTail opVal ::
          .append (.heads signature.functionType arguments (fuel + 1) []
            (resultType :: live)) :: wCallStack)
        (.functionAssemble ctxOpVal ::
          .append (.functionBranches (resultType :: live) scope
            (ctxArgs.zip signature.argumentTypes) []) :: cCallStack))
    (callDerivation :
      let resultType := Completed.invocationReturnType signature
      let outAtom : Atom := .expression (opVal :: retVals)
      let ctxCall : Entry.Value := .expression .active (ctxOpVal :: ctxRetVals)
      let wDrainStack : List RecursiveTasks.Frame :=
        .append (.calls resultType (fuel + 2) [] live) ::
          .append (.bindingAlternatives (.expression (operator :: arguments))
            signature.functionType resultType (fuel + 2) [] live) ::
            .filter :: wStack
      let cDrainStack : List RecursiveTasks.Contextual.Continuation :=
        .append (.calls live scope resultType []) ::
          .append (.invocations live scope expected signature ctxOp ctxArgs []) ::
            .publish (.expression (operator :: arguments)) :: cStack
      ScopedOrdinaryCallDerivation space dispatch hostDispatch policy wEmitted cEmitted
        (fuel + 2) callSteps live scope outAtom ctxCall resultType wBArgs cFrameArgs
        wDrainStack cDrainStack finalResults ctxFinalResults)
    (returnedCovered : ∀ pair ∈ finalResults, pair.2.applyFullCovered pair.1 readDepth = true)
    (returnedStable : ∀ pair ∈ finalResults, pair.2.applyFull pair.1 readDepth = pair.1)
 :
    let expr := Atom.expression (operator :: arguments)
    let cSelected := completedSuccessPriority
      (ctxFinalResults.map (Completed.readResult policy))
    let cPublished := cSelected.map (Completed.publishResult policy expr)
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom expr expected wB (fuel + 4) live)
      (.atom live scope ctxVal expected cFrame)
      wStack cStack wEmitted cEmitted
      (opSteps + argSteps + callSteps + 20)
      (successPriority finalResults) cPublished := by
  have opRun := operatorDerivation.task_run
  have argsRun := argumentsDerivation.task_run
  have callRun := callDerivation.task_run
  have operatorResultRel : ScopedResultRel (opVal, wBHead) (ctxOpVal, cFrameHead) := by
    have related := opRun.results_rel
    cases related with
    | cons related _ => exact related
  have source := selectedSource_of_parts space hostDispatch policy
    operator opVal expected arguments ctxVal ctxOp ctxOpVal ctxArgs ctxRetVals
    wB wBSelected wBHead cFrame cFrameSelected cFrameHead cFrameArgs signature candidates
    ctxFinalResults fuel live scope wStack wEmitted readiness entry operatorResultRel
    operatorDerivation.to_completed_atomRel argumentsDerivation.to_completed_argumentsRel
    callDerivation.to_completed_callRel
  exact selectedWorker_of_runs space dispatch hostDispatch policy operator opVal expected
    arguments retVals ctxVal ctxOp ctxOpVal ctxArgs ctxRetVals wB wBSelected wBHead wBArgs
    cFrame cFrameSelected cFrameHead cFrameArgs signature candidates finalResults ctxFinalResults
    fuel opSteps argSteps callSteps readDepth live scope wStack cStack wEmitted cEmitted readiness
    entry opRun argsRun callRun returnedCovered returnedStable source

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition

