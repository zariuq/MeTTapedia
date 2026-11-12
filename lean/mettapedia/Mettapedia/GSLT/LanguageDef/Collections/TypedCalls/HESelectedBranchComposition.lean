import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationBranchComposition

/-!
# Selected HE expression entry and publication around arbitrary branch batches

The existing first-success selection square supplies the entry prefix. The
earned invocation block may produce any ordered result batch, including no
results or errors. Actual return readout and priority precede publication.
All worker continuations and emitted prefixes remain concrete parameters.

This composes a selected invocation region; it does not identify native
callback implementations with their source services.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchComposition

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Completed
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

theorem selected_from_blocks (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator expected : Atom) (arguments : List Atom) (ctxVal ctxOperator : Entry.Value)
    (ctxArguments : List Entry.Value) (wB wSelected : Bindings) (activation selectedFrame : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom) (fuel invocationSteps readDepth : Nat)
    (live : List Atom) (scope : List String) (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation) (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (readiness : Entry.Status) (results : ResultSet) (cResults : List Completed.Result)
    (entryReady : ScopedAtomEntryReady policy (.expression (operator :: arguments)) ctxVal activation)
    (readShape : activation.read policy ctxVal = .expression readiness (ctxOperator :: ctxArguments))
    (operatorErase : ctxOperator.erase = operator)
    (notStopped : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (candidateEq : invocationTypes
      ⟨space, .work (.expression (.expression (operator :: arguments)) expected wB (fuel + 3) live),
        .filter :: wStack, wEmitted⟩ wB operator expected = candidates)
    (selectionReady : FirstSuccessRecursiveStrategy.selectionReady
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB (fuel + 2) candidates live),
          .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB (fuel + 2) candidates = true)
    (workerSelected : FirstSuccessRecursiveStrategy.select
      (lookup := invocationTypes
        ⟨space, .work (.functions (.expression (operator :: arguments)) expected wB (fuel + 2) candidates live),
          .filter :: wStack, wEmitted⟩)
      space (.expression (operator :: arguments)) expected wB (fuel + 2) candidates = .selected signature [wSelected])
    (contextualSelected : Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (.expression (operator :: arguments)) operator expected activation (.selected signature [selectedFrame]))
    (invocationSource : Completed.InvocationsRel space hostDispatch Completed.scopedLookup live scope expected signature
      ctxOperator ctxArguments [selectedFrame] cResults (policy := policy))
    (invocationRun : ScopedTaskRun space dispatch hostDispatch policy
      (.bindingAlternatives (.expression (operator :: arguments)) signature.functionType (invocationReturnType signature)
        (fuel + 2) [wSelected] live)
      (.invocations live scope expected signature ctxOperator ctxArguments [selectedFrame])
      (.filter :: wStack) (.publish (.expression (operator :: arguments)) :: cStack)
      wEmitted cEmitted invocationSteps results cResults)
    (covered : ∀ pair ∈ results, pair.2.applyFullCovered pair.1 readDepth = true)
    (stable : ∀ pair ∈ results, pair.2.applyFull pair.1 readDepth = pair.1) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom (.expression (operator :: arguments)) expected wB (fuel + 4) live)
      (.atom live scope ctxVal expected activation)
      wStack cStack wEmitted cEmitted (invocationSteps + 4) (successPriority results)
      ((completedSuccessPriority (cResults.map (Completed.readResult policy))).map
        (Completed.publishResult policy (.expression (operator :: arguments)))) := by
  let expression := Atom.expression (operator :: arguments)
  have entered := entryReady.entry_interpret notStopped notAtom notExpression
  have selectedAtRead : Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (activation.read policy ctxVal).erase ctxOperator.erase expected activation (.selected signature [selectedFrame]) := by
    simpa only [entryReady.2.1, operatorErase] using contextualSelected
  have source : Completed.AtomRel space hostDispatch Completed.scopedLookup live scope ctxVal expected activation
      ((completedSuccessPriority (cResults.map (Completed.readResult policy))).map
        (Completed.publishResult policy expression)) (policy := policy) := by
    simpa only [entryReady.2.1, expression] using
      (Completed.AtomRel.function entered readShape selectedAtRead invocationSource
        (completedSuccessPriority_rel (cResults.map (Completed.readResult policy))))
  have entryBlock := scoped_selected_function_entry_run space dispatch hostDispatch policy operator arguments expected
    wB wSelected (fuel + 2) live scope ctxVal ctxOperator ctxArguments activation selectedFrame readiness signature candidates
    wStack cStack wEmitted cEmitted entryReady readShape operatorErase notStopped notAtom notExpression
    (by simpa only [show fuel + 2 + 1 = fuel + 3 by omega] using candidateEq)
    selectionReady workerSelected contextualSelected
  dsimp only at entryBlock
  have readRel := ScopedResultRel.forall2_materialized_readResult_stable policy invocationRun.results_rel readDepth covered stable
  have publishedRel := ScopedResultRel.forall2_publishResult policy expression (ScopedResultRel.forall2_successPriority readRel)
  have finishStep : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning results, .filter :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .returning (successPriority results), wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  refine ⟨by omega, publishedRel, ?_, RecursiveExecution.Contextual.atom_complete source cStack⟩
  intro budget
  rw [show (invocationSteps + 4) + budget = 3 + (invocationSteps + (budget + 1)) by omega,
    entryBlock.2.1 (invocationSteps + (budget + 1)), invocationRun.worker_run (budget + 1),
    (Checked.machine dispatch scopedTypes).run_succ_silent finishStep]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchComposition
