import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchDerivation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedCallCompositionControls

/-!
# A source-earned selected expression through the branch composition

The existing typed-constructor fixture supplies independent local source
derivations. The new operator-branch, invocation and publication blocks are
composed from those local derivations, with no whole-expression run premise.
The five-branch, nonempty-record fixtures are in `HEFunctionBranchControls`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchControls

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Completed
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication
open HESelectedCallComposition.Controls

theorem selected_constructor_from_local_branches (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation) (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedTaskRun space HE.GroundedDispatch.none host Policy.unmarked
      (.atom call Atom.undefinedType Bindings.empty 16 [])
      (.atom [] [] ctxCall Atom.undefinedType Completed.Frame.empty)
      wStack cStack wEmitted cEmitted 41 [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)] := by
  let wRest : RecursiveTasks.Task := .bindingAlternatives call signature.functionType returned 14 [] []
  let cRest : RecursiveTasks.Contextual.Task := .invocations [] [] Atom.undefinedType signature ctxOperator [ctxOperand] []
  let wBase : List RecursiveTasks.Frame := .filter :: wStack
  let cBase : List RecursiveTasks.Contextual.Continuation := .publish call :: cStack
  let wFunction : List RecursiveTasks.Frame := .calls returned 14 [] :: .append wRest :: wBase
  let cFunction : List RecursiveTasks.Contextual.Continuation := .calls [] [] returned :: .append cRest :: cBase
  let wOperator : List RecursiveTasks.Frame := .heads signature.functionType [operand] 13 [returned] :: wFunction
  let cOperator : List RecursiveTasks.Contextual.Continuation :=
    .functionHeads [returned] [] [(ctxOperand, formal)] :: cFunction
  let wArguments : List RecursiveTasks.Frame :=
    .functionTail operator :: .append (.heads signature.functionType [operand] 13 [] [returned]) :: wFunction
  let cArguments : List RecursiveTasks.Contextual.Continuation :=
    .functionAssemble ctxOperator :: .append (.functionBranches [returned] [] [(ctxOperand, formal)] []) :: cFunction
  have opDerivation := operatorDerivation (signature.functionType :: [operand] ++ [returned])
    (signature.functionType :: [ctxOperand].map Entry.Value.erase ++ [returned])
    ([] ++ expectedApplicationScope (.expression ((ctxOperator :: [ctxOperand]).map Entry.Value.erase)) Atom.undefinedType)
    wOperator cOperator wEmitted cEmitted
  have argDerivation := argumentsDerivation (operator :: returned :: []) [] wArguments cArguments wEmitted cEmitted
  have branches : HEFunctionBranchComposition.Heads space HE.GroundedDispatch.none host Policy.unmarked
      wEmitted cEmitted signature.functionType [operand] [formal] [(ctxOperand, formal)] 13 [returned] []
      [(operator, Bindings.empty)] [(ctxOperator, Completed.Frame.empty)] wFunction cFunction 14
      [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)] := by
    have built := HEFunctionBranchComposition.Heads.continuing
      (operatorType := signature.functionType) (arguments := [operand]) (types := [formal])
      (requests := [(ctxOperand, formal)]) (fuel := 13) (live := [returned]) (scope := [])
      (operator, Bindings.empty) (ctxOperator, Completed.Frame.empty) [] [] wFunction cFunction 9 1
      [(argumentPacket [operand], Bindings.empty)] [] [(Entry.Value.argumentPacket [ctxOperand], Completed.Frame.empty)] []
      ⟨eraseOperator.symm, actEmpty⟩ (by decide +kernel) (by rfl)
      (by simpa only [eraseOperator] using argDerivation.to_completed_argumentsRel)
      (by simpa only [eraseOperator] using argDerivation.task_run) (.nil _ _)
    simpa [RecursiveTasks.functionTail, argumentsSucceeded, argumentValues, unpackArguments, argumentPacket,
      Completed.functionAssemble, call, ctxCall, ctxOperator, ctxOperand, operator, operand, Entry.Value.erase] using built
  have calls : ScopedOrdinaryCallsDerivation space HE.GroundedDispatch.none host Policy.unmarked wEmitted cEmitted
      14 15 [] [] returned [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)]
      (.append wRest :: wBase) (.append cRest :: cBase) [(call, Bindings.empty)] [(ctxCall, Completed.Frame.empty)] := by
    apply ScopedOrdinaryCallsDerivation.cons 14 11 1 [] [] returned (call, Bindings.empty)
      (ctxCall, Completed.Frame.empty) [] [(call, Bindings.empty)] [] [] [(ctxCall, Completed.Frame.empty)] []
      (.append wRest :: wBase) (.append cRest :: cBase) ⟨eraseCall.symm, actEmpty⟩
    · exact callDerivation _ _ _ _
    · exact .nil _ _ _ _ _ _
  have admitted := entry wStack wEmitted
  have composed := HESelectedBranchDerivation.selected_from_components space HE.GroundedDispatch.none host Policy.unmarked
    operator Atom.undefinedType [operand] ctxCall ctxOperator [ctxOperand] Bindings.empty Bindings.empty
    Completed.Frame.empty Completed.Frame.empty signature [signature.functionType] 12 1 14 15 4
    [] [] wStack cStack wEmitted cEmitted .active [(operator, Bindings.empty)] [(call, Bindings.empty)] [(call, Bindings.empty)]
    [(ctxOperator, Completed.Frame.empty)] [(ctxCall, Completed.Frame.empty)] [(ctxCall, Completed.Frame.empty)]
    admitted.entry_ready admitted.read_shape admitted.operator_erase admitted.input_not_stopped
    admitted.expected_not_atom admitted.expected_not_expression admitted.candidate_eq admitted.selection_ready
    admitted.worker_selected admitted.contextual_selected admitted.arity_eq
    opDerivation.to_completed_atomRel opDerivation.task_run
    (by simpa [signature, Completed.invocationReturnType, Atom.expressionType, returned, call,
      wFunction, cFunction, wRest, cRest, wBase, cBase] using branches)
    calls.to_completed_callsRel calls.task_run
    (by decide +kernel) (by decide +kernel)
  simpa [signature, formal, returned, Completed.invocationReturnType, successPriority, completedSuccessPriority,
    Completed.readResult, Completed.Frame.read_empty, Completed.publishResult, Policy.unmarked, Entry.Value.publish,
    call, ctxCall, ctxOperator, ctxOperand, operator, operand, isErrorAtom, Entry.Value.erase, Entry.publish,
    Entry.Value.withStatus] using composed

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedBranchControls
