import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchComposition

/-!
# One selected activation with an arbitrary ordered call frontier

The function task produces a complete frontier of calls, each with its own
record. Its existing calls task executes that frontier, then the actual
empty activation tail drains back to the caller. This composes two earned
child blocks; neither the whole invocation nor a final successful answer is
assumed. Publication and result priority are later boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationBranchComposition

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Completed
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

theorem invocation_of_parts (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (expression expected : Atom) (operator : Entry.Value) (arguments : List Entry.Value)
    (signature : SelectedTypePolicy) (bindings : Bindings) (activation : Completed.Frame)
    (fuel functionSteps callsSteps : Nat) (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (rows results : ResultSet) (cRows cResults : List Completed.Result)
    (functionSource : Completed.FunctionRel space hostDispatch Completed.scopedLookup
      (invocationReturnType signature :: live) scope expected signature operator arguments activation cRows
      (policy := policy))
    (callsSource : Completed.CallsRel space hostDispatch Completed.scopedLookup live scope
      (invocationReturnType signature) cRows cResults (policy := policy))
    (functionRun : ScopedTaskRun space dispatch hostDispatch policy
      (.func expression signature.functionType bindings (fuel + 2) (invocationReturnType signature :: live))
      (.function (invocationReturnType signature :: live) scope expected signature operator arguments activation)
      (.calls (invocationReturnType signature) (fuel + 2) live ::
        .append (.bindingAlternatives expression signature.functionType (invocationReturnType signature)
          (fuel + 2) [] live) :: wStack)
      (.calls live scope (invocationReturnType signature) ::
        .append (.invocations live scope expected signature operator arguments []) :: cStack)
      wEmitted cEmitted functionSteps rows cRows)
    (callsRun : ScopedTaskRun space dispatch hostDispatch policy
      (.calls (invocationReturnType signature) (fuel + 2) rows live)
      (.calls live scope (invocationReturnType signature) cRows)
      (.append (.bindingAlternatives expression signature.functionType (invocationReturnType signature)
        (fuel + 2) [] live) :: wStack)
      (.append (.invocations live scope expected signature operator arguments []) :: cStack)
      wEmitted cEmitted callsSteps results cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.bindingAlternatives expression signature.functionType (invocationReturnType signature)
        (fuel + 2) [bindings] live)
      (.invocations live scope expected signature operator arguments [activation])
      wStack cStack wEmitted cEmitted (functionSteps + callsSteps + 5) results cResults := by
  let debt := invocationReturnType signature
  let rest : RecursiveTasks.Task := .bindingAlternatives expression signature.functionType debt (fuel + 2) [] live
  have source : Completed.InvocationsRel space hostDispatch Completed.scopedLookup live scope expected signature
      operator arguments [activation] cResults (policy := policy) := by
    simpa only [List.append_nil] using Completed.InvocationsRel.cons functionSource callsSource .nil
  have step0 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.bindingAlternatives expression signature.functionType debt (fuel + 2) [bindings] live), wStack, wEmitted⟩ =
      some (.silent ⟨space, .work (.func expression signature.functionType bindings (fuel + 2) (debt :: live)),
        .calls debt (fuel + 2) live :: .append rest :: wStack, wEmitted⟩) := rfl
  have step1 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning rows, .calls debt (fuel + 2) live :: .append rest :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .work (.calls debt (fuel + 2) rows live), .append rest :: wStack, wEmitted⟩) := rfl
  have step2 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning results, .append rest :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .work rest, .prepend results :: wStack, wEmitted⟩) := rfl
  have step3 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work rest, .prepend results :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .returning [], .prepend results :: wStack, wEmitted⟩) := rfl
  have step4 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning [], .prepend results :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .returning results, wStack, wEmitted⟩) := by
    simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
      RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
      FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
  refine ⟨by omega, callsRun.results_rel, ?_, RecursiveExecution.Contextual.invocations_complete source cStack⟩
  intro budget
  rw [show (functionSteps + callsSteps + 5) + budget =
      (functionSteps + ((callsSteps + (budget + 3)) + 1)) + 1 by omega,
    (Checked.machine dispatch scopedTypes).run_succ_silent step0,
    functionRun.worker_run ((callsSteps + (budget + 3)) + 1),
    (Checked.machine dispatch scopedTypes).run_succ_silent step1,
    callsRun.worker_run (budget + 3),
    show budget + 3 = ((budget + 1) + 1) + 1 by omega,
    (Checked.machine dispatch scopedTypes).run_succ_silent step2,
    (Checked.machine dispatch scopedTypes).run_succ_silent step3,
    (Checked.machine dispatch scopedTypes).run_succ_silent step4]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationBranchComposition
