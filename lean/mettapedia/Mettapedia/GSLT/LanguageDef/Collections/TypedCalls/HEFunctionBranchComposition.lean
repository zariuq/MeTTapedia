import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallComposition

/-!
# Ordered operator-result branches at retained HE caller stacks

Every operator result keeps its own reached binding record. A continuing
result runs the existing argument task and assembles every returned packet;
an empty/error result bypasses arguments without discarding later operator
results. The spine composes actual worker transitions with the existing
contextual source judgment. No whole-head execution is an input premise.

Child argument runs are local components at their exact saved stacks. Their
source judgments are retained independently. This is a composition theorem,
not native callback adequacy or a new evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchComposition

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Completed Spec.Type
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

inductive Heads (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (operatorType : Atom) (arguments types : List Atom) (requests : List Completed.ArgumentRequest)
    (fuel : Nat) (live : List Atom) (scope : List String) :
    ResultSet → List Completed.Result → List RecursiveTasks.Frame →
      List RecursiveTasks.Contextual.Continuation → Nat → ResultSet → List Completed.Result → Prop where
  | nil (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation) :
      Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
        [] [] wStack cStack 1 [] []
  | stopped (head : ResultPair) (cHead : Completed.Result) (heads : ResultSet) (cHeads : List Completed.Result)
      (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
      (steps : Nat) (rest : ResultSet) (cRest : List Completed.Result)
      (related : ScopedResultRel head cHead) (stopped : isEmptyOrError head.1 = true)
      (tail : Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
        heads cHeads (.prepend [head] :: wStack) (.prepend [cHead] :: cStack) steps rest cRest) :
      Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
        (head :: heads) (cHead :: cHeads) wStack cStack (steps + 3) (head :: rest) (cHead :: cRest)
  | continuing (head : ResultPair) (cHead : Completed.Result) (heads : ResultSet) (cHeads : List Completed.Result)
      (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
      (childSteps restSteps : Nat) (children rest : ResultSet) (cChildren cRest : List Completed.Result)
      (related : ScopedResultRel head cHead) (running : isEmptyOrError head.1 = false)
      (parsed : getFunctionArgTypes operatorType = some types)
      (childSource : Completed.ArgumentsRel space hostDispatch Completed.scopedLookup
        (cHead.1.erase :: live) scope requests cHead.2 cChildren (policy := policy))
      (childRun : ScopedTaskRun space dispatch hostDispatch policy
        (.args arguments types head.2 fuel (head.1 :: live))
        (.arguments (cHead.1.erase :: live) scope requests cHead.2)
        (.functionTail head.1 :: .append (.heads operatorType arguments fuel heads live) :: wStack)
        (.functionAssemble cHead.1 :: .append (.functionBranches live scope requests cHeads) :: cStack)
        wEmitted cEmitted childSteps children cChildren)
      (tail : Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
        heads cHeads (.prepend (RecursiveTasks.functionTail head.1 children) :: wStack)
        (.prepend (cChildren.map (Completed.functionAssemble cHead.1)) :: cStack) restSteps rest cRest) :
      Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
        (head :: heads) (cHead :: cHeads) wStack cStack (childSteps + restSteps + 4)
        (RecursiveTasks.functionTail head.1 children ++ rest) (cChildren.map (Completed.functionAssemble cHead.1) ++ cRest)

theorem Heads.input_relation {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy} {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {operatorType : Atom} {arguments types : List Atom} {requests : List Completed.ArgumentRequest}
    {fuel : Nat} {live : List Atom} {scope : List String} {heads : ResultSet} {cHeads : List Completed.Result}
    {wStack : List RecursiveTasks.Frame} {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {results : ResultSet} {cResults : List Completed.Result}
    (spine : Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
      heads cHeads wStack cStack steps results cResults) : List.Forall₂ ScopedResultRel heads cHeads := by
  induction spine with
  | nil => exact .nil
  | stopped _ _ _ _ _ _ _ _ _ related _ _ ih => exact .cons related ih
  | continuing _ _ _ _ _ _ _ _ _ _ _ _ related _ _ _ _ _ ih => exact .cons related ih

theorem Heads.to_source {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy} {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {operatorType : Atom} {arguments types : List Atom} {requests : List Completed.ArgumentRequest}
    {fuel : Nat} {live : List Atom} {scope : List String} {heads : ResultSet} {cHeads : List Completed.Result}
    {wStack : List RecursiveTasks.Frame} {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {results : ResultSet} {cResults : List Completed.Result}
    (spine : Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
      heads cHeads wStack cStack steps results cResults) :
    Completed.FunctionBranchesRel space hostDispatch Completed.scopedLookup live scope requests cHeads cResults
      (policy := policy) := by
  induction spine with
  | nil => exact .nil
  | stopped head cHead heads cHeads wStack cStack steps rest cRest related stopped tail ih =>
    apply Completed.FunctionBranchesRel.stopped ?_ ih
    rw [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError, ← related.1]
    exact stopped
  | continuing head cHead heads cHeads wStack cStack childSteps restSteps children rest cChildren cRest
      related running parsed childSource childRun tail ih =>
    apply Completed.FunctionBranchesRel.continuing ?_ childSource ih
    rw [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError, ← related.1]
    simp [running]

theorem Heads.task_run {space : Space} {dispatch : HE.GroundedDispatch}
    {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Policy} {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {operatorType : Atom} {arguments types : List Atom} {requests : List Completed.ArgumentRequest}
    {fuel : Nat} {live : List Atom} {scope : List String} {heads : ResultSet} {cHeads : List Completed.Result}
    {wStack : List RecursiveTasks.Frame} {cStack : List RecursiveTasks.Contextual.Continuation}
    {steps : Nat} {results : ResultSet} {cResults : List Completed.Result}
    (spine : Heads space dispatch hostDispatch policy wEmitted cEmitted operatorType arguments types requests fuel live scope
      heads cHeads wStack cStack steps results cResults) :
    ScopedTaskRun space dispatch hostDispatch policy (.heads operatorType arguments fuel heads live)
      (.functionBranches live scope requests cHeads) wStack cStack wEmitted cEmitted steps results cResults := by
  induction spine with
  | nil wStack cStack =>
    have stepped : (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.heads operatorType arguments fuel [] live), wStack, wEmitted⟩ =
        some (.silent ⟨space, .returning [], wStack, wEmitted⟩) := rfl
    refine ⟨by decide, .nil, ?_, .single .functionBranchesNil⟩
    intro budget
    rw [Nat.add_comm 1 budget, (Checked.machine dispatch scopedTypes).run_succ_silent stepped]
  | stopped head cHead heads cHeads wStack cStack steps rest cRest related stopped tail ih =>
    have source := (Heads.stopped head cHead heads cHeads wStack cStack steps rest cRest related stopped tail).to_source
    have step0 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.heads operatorType arguments fuel (head :: heads) live), wStack, wEmitted⟩ =
        some (.silent ⟨space, .returning [head], .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩) := by
      simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
        FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
        FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
        FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, stopped, Transition.relabel]
    have step1 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning [head], .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩ =
        some (.silent ⟨space, .work (.heads operatorType arguments fuel heads live), .prepend [head] :: wStack, wEmitted⟩) := rfl
    have step2 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning rest, .prepend [head] :: wStack, wEmitted⟩ =
        some (.silent ⟨space, .returning (head :: rest), wStack, wEmitted⟩) := rfl
    refine ⟨by omega, .cons related ih.results_rel, ?_, RecursiveExecution.Contextual.function_branches_complete source cStack⟩
    intro budget
    rw [show (steps + 3) + budget = ((steps + (budget + 1)) + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step0,
      (Checked.machine dispatch scopedTypes).run_succ_silent step1,
      ih.worker_run (budget + 1), (Checked.machine dispatch scopedTypes).run_succ_silent step2]
  | continuing head cHead heads cHeads wStack cStack childSteps restSteps children rest cChildren cRest
      related running parsed childSource childRun tail ih =>
    have source := (Heads.continuing head cHead heads cHeads wStack cStack childSteps restSteps children rest cChildren cRest
      related running parsed childSource childRun tail).to_source
    have step0 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .work (.heads operatorType arguments fuel (head :: heads) live), wStack, wEmitted⟩ =
        some (.silent ⟨space, .work (.args arguments types head.2 fuel (head.1 :: live)),
          .functionTail head.1 :: .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩) := by
      simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
        FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
        FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
        FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, running, parsed, Transition.relabel]
    have step1 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning children, .functionTail head.1 :: .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩ =
        some (.silent ⟨space, .returning (RecursiveTasks.functionTail head.1 children),
          .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩) := rfl
    have step2 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning (RecursiveTasks.functionTail head.1 children),
          .append (.heads operatorType arguments fuel heads live) :: wStack, wEmitted⟩ =
        some (.silent ⟨space, .work (.heads operatorType arguments fuel heads live),
          .prepend (RecursiveTasks.functionTail head.1 children) :: wStack, wEmitted⟩) := rfl
    have step3 : (Checked.machine dispatch scopedTypes).step
        ⟨space, .returning rest, .prepend (RecursiveTasks.functionTail head.1 children) :: wStack, wEmitted⟩ =
        some (.silent ⟨space, .returning (RecursiveTasks.functionTail head.1 children ++ rest), wStack, wEmitted⟩) := rfl
    refine ⟨by omega,
      ScopedResultRel.forall2_append (ScopedResultRel.forall2_functionTail related.1.symm childRun.results_rel) ih.results_rel,
      ?_, RecursiveExecution.Contextual.function_branches_complete source cStack⟩
    intro budget
    rw [show (childSteps + restSteps + 4) + budget = (childSteps + (((restSteps + (budget + 1)) + 1) + 1)) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent step0,
      childRun.worker_run (((restSteps + (budget + 1)) + 1) + 1),
      (Checked.machine dispatch scopedTypes).run_succ_silent step1,
      (Checked.machine dispatch scopedTypes).run_succ_silent step2,
      ih.worker_run (budget + 1), (Checked.machine dispatch scopedTypes).run_succ_silent step3]

/-- Operator execution and the complete branch spine compose at the actual
function task. Neither operator results nor argument packets are restricted
to singletons. Child execution keeps the concrete caller stack. -/
theorem function_of_parts (space : Space) (dispatch : HE.GroundedDispatch)
    (hostDispatch : Spec.Eval.GroundedDispatch) (policy : Policy)
    (operator expected : Atom) (arguments : List Atom) (ctxOperator : Entry.Value)
    (ctxArguments : List Entry.Value) (signature : SelectedTypePolicy)
    (bindings : Bindings) (activation : Completed.Frame) (fuel opSteps branchSteps : Nat)
    (live : List Atom) (scope : List String) (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation) (wEmitted : ResultSet) (cEmitted : List Completed.Result)
    (heads : ResultSet) (cHeads : List Completed.Result) (results : ResultSet) (cResults : List Completed.Result)
    (arity : ctxArguments.length = signature.argumentTypes.length)
    (operatorSource : Completed.AtomRel space hostDispatch Completed.scopedLookup
      (signature.functionType :: ctxArguments.map Entry.Value.erase ++ live)
      (scope ++ expectedApplicationScope (.expression ((ctxOperator :: ctxArguments).map Entry.Value.erase)) expected)
      ctxOperator signature.functionType activation cHeads (policy := policy))
    (operatorRun : ScopedTaskRun space dispatch hostDispatch policy
      (.atom operator signature.functionType bindings (fuel + 1) (signature.functionType :: arguments ++ live))
      (.atom (signature.functionType :: ctxArguments.map Entry.Value.erase ++ live)
        (scope ++ expectedApplicationScope (.expression ((ctxOperator :: ctxArguments).map Entry.Value.erase)) expected)
        ctxOperator signature.functionType activation)
      (.heads signature.functionType arguments (fuel + 1) live :: wStack)
      (.functionHeads live scope (ctxArguments.zip signature.argumentTypes) :: cStack)
      wEmitted cEmitted opSteps heads cHeads)
    (branches : Heads space dispatch hostDispatch policy wEmitted cEmitted signature.functionType arguments
      signature.argumentTypes (ctxArguments.zip signature.argumentTypes) (fuel + 1) live scope
      heads cHeads wStack cStack branchSteps results cResults) :
    ScopedTaskRun space dispatch hostDispatch policy
      (.func (.expression (operator :: arguments)) signature.functionType bindings (fuel + 2) live)
      (.function live scope expected signature ctxOperator ctxArguments activation)
      wStack cStack wEmitted cEmitted (opSteps + branchSteps + 2) results cResults := by
  have source : Completed.FunctionRel space hostDispatch Completed.scopedLookup live scope expected signature
      ctxOperator ctxArguments activation cResults (policy := policy) :=
    .evaluated arity operatorSource branches.to_source
  have branchRun := branches.task_run
  have step0 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.func (.expression (operator :: arguments)) signature.functionType bindings (fuel + 2) live), wStack, wEmitted⟩ =
      some (.silent ⟨space, .work (.atom operator signature.functionType bindings (fuel + 1)
        (signature.functionType :: arguments ++ live)), .heads signature.functionType arguments (fuel + 1) live :: wStack, wEmitted⟩) := rfl
  have step1 : (Checked.machine dispatch scopedTypes).step
      ⟨space, .returning heads, .heads signature.functionType arguments (fuel + 1) live :: wStack, wEmitted⟩ =
      some (.silent ⟨space, .work (.heads signature.functionType arguments (fuel + 1) heads live), wStack, wEmitted⟩) := rfl
  refine ⟨by omega, branchRun.results_rel, ?_, RecursiveExecution.Contextual.function_complete source cStack⟩
  intro budget
  rw [show (opSteps + branchSteps + 2) + budget = (opSteps + ((branchSteps + budget) + 1)) + 1 by omega,
    (Checked.machine dispatch scopedTypes).run_succ_silent step0,
    operatorRun.worker_run ((branchSteps + budget) + 1),
    (Checked.machine dispatch scopedTypes).run_succ_silent step1, branchRun.worker_run budget]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchComposition
