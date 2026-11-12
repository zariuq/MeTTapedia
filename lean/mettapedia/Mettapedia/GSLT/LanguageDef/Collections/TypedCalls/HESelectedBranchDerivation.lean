import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchComposition

/-!
# Local operator, branch and call evidence earns a whole selected expression

Entry is the existing first-success selection square. Operator execution,
the complete operator/argument branch spine and the ordinary calls spine are
local components. Their source judgments construct the enclosing expression
judgment, while their worker blocks construct its retained execution.
No whole-expression or whole-invocation run is an admission premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchDerivation

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Completed
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

theorem selected_from_components (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator expected : Atom) (arguments : List Atom) (ctxVal ctxOperator : Entry.Value)
    (ctxArguments : List Entry.Value) (wB wSelected : Bindings) (activation selectedFrame : Completed.Frame)
    (signature : SelectedTypePolicy) (candidates : List Atom) (fuel opSteps branchSteps callsSteps readDepth : Nat)
    (live : List Atom) (scope : List String) (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation) (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (readiness : Entry.Status) (heads rows results : ResultSet) (cHeads cRows cResults : List Completed.Result)
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
    (arity : ctxArguments.length = signature.argumentTypes.length)
    (operatorSource : Completed.AtomRel space hostDispatch Completed.scopedLookup
      (signature.functionType :: ctxArguments.map Entry.Value.erase ++ invocationReturnType signature :: live)
      (scope ++ expectedApplicationScope (.expression ((ctxOperator :: ctxArguments).map Entry.Value.erase)) expected)
      ctxOperator signature.functionType selectedFrame cHeads (policy := policy))
    (operatorRun : ScopedTaskRun space dispatch hostDispatch policy
      (.atom operator signature.functionType wSelected (fuel + 1)
        (signature.functionType :: arguments ++ invocationReturnType signature :: live))
      (.atom (signature.functionType :: ctxArguments.map Entry.Value.erase ++ invocationReturnType signature :: live)
        (scope ++ expectedApplicationScope (.expression ((ctxOperator :: ctxArguments).map Entry.Value.erase)) expected)
        ctxOperator signature.functionType selectedFrame)
      (.heads signature.functionType arguments (fuel + 1) (invocationReturnType signature :: live) ::
        .calls (invocationReturnType signature) (fuel + 2) live ::
        .append (.bindingAlternatives (.expression (operator :: arguments)) signature.functionType (invocationReturnType signature)
          (fuel + 2) [] live) :: .filter :: wStack)
      (.functionHeads (invocationReturnType signature :: live) scope (ctxArguments.zip signature.argumentTypes) ::
        .calls live scope (invocationReturnType signature) ::
        .append (.invocations live scope expected signature ctxOperator ctxArguments []) ::
        .publish (.expression (operator :: arguments)) :: cStack)
      wEmitted cEmitted opSteps heads cHeads)
    (branches : HEFunctionBranchComposition.Heads space dispatch hostDispatch policy wEmitted cEmitted
      signature.functionType arguments signature.argumentTypes (ctxArguments.zip signature.argumentTypes)
      (fuel + 1) (invocationReturnType signature :: live) scope heads cHeads
      (.calls (invocationReturnType signature) (fuel + 2) live ::
        .append (.bindingAlternatives (.expression (operator :: arguments)) signature.functionType (invocationReturnType signature)
          (fuel + 2) [] live) :: .filter :: wStack)
      (.calls live scope (invocationReturnType signature) ::
        .append (.invocations live scope expected signature ctxOperator ctxArguments []) ::
        .publish (.expression (operator :: arguments)) :: cStack)
      branchSteps rows cRows)
    (callsSource : Completed.CallsRel space hostDispatch Completed.scopedLookup live scope
      (invocationReturnType signature) cRows cResults (policy := policy))
    (callsRun : ScopedTaskRun space dispatch hostDispatch policy
      (.calls (invocationReturnType signature) (fuel + 2) rows live)
      (.calls live scope (invocationReturnType signature) cRows)
      (.append (.bindingAlternatives (.expression (operator :: arguments)) signature.functionType (invocationReturnType signature)
        (fuel + 2) [] live) :: .filter :: wStack)
      (.append (.invocations live scope expected signature ctxOperator ctxArguments []) ::
        .publish (.expression (operator :: arguments)) :: cStack)
      wEmitted cEmitted callsSteps results cResults)
    (covered : ∀ pair ∈ results, pair.2.applyFullCovered pair.1 readDepth = true)
    (stable : ∀ pair ∈ results, pair.2.applyFull pair.1 readDepth = pair.1) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.atom (.expression (operator :: arguments)) expected wB (fuel + 4) live)
      (.atom live scope ctxVal expected activation)
      wStack cStack wEmitted cEmitted (opSteps + branchSteps + callsSteps + 11) (successPriority results)
      ((completedSuccessPriority (cResults.map (Completed.readResult policy))).map
        (Completed.publishResult policy (.expression (operator :: arguments)))) := by
  let expression := Atom.expression (operator :: arguments)
  let debt := invocationReturnType signature
  let wRest : RecursiveTasks.Task := .bindingAlternatives expression signature.functionType debt (fuel + 2) [] live
  let cRest : RecursiveTasks.Contextual.Task := .invocations live scope expected signature ctxOperator ctxArguments []
  let wBase : List RecursiveTasks.Frame := .filter :: wStack
  let cBase : List RecursiveTasks.Contextual.Continuation := .publish expression :: cStack
  have functionSource : Completed.FunctionRel space hostDispatch Completed.scopedLookup (debt :: live) scope expected signature
      ctxOperator ctxArguments selectedFrame cRows (policy := policy) :=
    .evaluated arity operatorSource branches.to_source
  have functionRun := HEFunctionBranchComposition.function_of_parts space dispatch hostDispatch policy
    operator expected arguments ctxOperator ctxArguments signature wSelected selectedFrame fuel opSteps branchSteps
    (debt :: live) scope (.calls debt (fuel + 2) live :: .append wRest :: wBase)
    (.calls live scope debt :: .append cRest :: cBase) wEmitted cEmitted heads cHeads rows cRows
    arity operatorSource operatorRun branches
  have invocationSource : Completed.InvocationsRel space hostDispatch Completed.scopedLookup live scope expected signature
      ctxOperator ctxArguments [selectedFrame] cResults (policy := policy) := by
    simpa only [List.append_nil] using Completed.InvocationsRel.cons functionSource callsSource .nil
  have invocationRun := HEInvocationBranchComposition.invocation_of_parts space dispatch hostDispatch policy
    expression expected ctxOperator ctxArguments signature wSelected selectedFrame fuel
    (opSteps + branchSteps + 2) callsSteps live scope wBase cBase wEmitted cEmitted rows results cRows cResults
    functionSource callsSource functionRun callsRun
  have composed := HESelectedBranchComposition.selected_from_blocks space dispatch hostDispatch policy
    operator expected arguments ctxVal ctxOperator ctxArguments wB wSelected activation selectedFrame signature candidates
    fuel (opSteps + branchSteps + 2 + callsSteps + 5) readDepth live scope wStack cStack wEmitted cEmitted
    readiness results cResults entryReady readShape operatorErase notStopped notAtom notExpression candidateEq
    selectionReady workerSelected contextualSelected invocationSource invocationRun covered stable
  have count : (opSteps + branchSteps + 2 + callsSteps + 5) + 4 = opSteps + branchSteps + callsSteps + 11 := by omega
  simpa only [count] using composed

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchDerivation
