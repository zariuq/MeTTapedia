import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource

/-!
# Stateful selected-call source composition

A selected frame may differ from the incoming frame, operator evaluation
may reach another frame, and argument alternatives retain their own records.
This is a derived composition rule for the existing stateful source family,
not a second evaluator or a whole-expression correctness premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Mettapedia.Machines.OrderedProtocol.Completion

/-- Compose actual selection, operator, argument and call derivations.
The three child worlds and all three activation boundaries remain distinct. -/
theorem selected_of_parts {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (beforeWorld headWorld argumentsWorld afterWorld : World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (before selectedFrame headFrame : Frame) (readiness : Entry.Status)
    (operator head : Entry.Value) (arguments : List Entry.Value) (signature : SelectedTypePolicy)
    (packets raw selected : List Result)
    (entry : Entry.Rel policy.reentry (before.read policy value).status
      (before.read policy value).erase expected .interpret)
    (shape : before.read policy value = .expression readiness (operator :: arguments))
    (selection : environment.arguments.selection (environment.view beforeWorld label) environment.lookup policy live scope
      (before.read policy value).erase operator.erase expected before (.selected signature [selectedFrame]))
    (arity : arguments.length = signature.argumentTypes.length)
    (operatorRun : Stateful.AtomRel environment label beforeWorld
      (signature.functionType :: arguments.map Entry.Value.erase ++ invocationReturnType signature :: live)
      (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
      operator signature.functionType selectedFrame [(head, headFrame)] headWorld (policy := policy))
    (headContinues : ¬IsEmptyOrErrorRel head.erase)
    (argumentsRun : Stateful.ArgumentsRel environment label headWorld
      (head.erase :: invocationReturnType signature :: live) scope
      (arguments.zip signature.argumentTypes) headFrame packets argumentsWorld (policy := policy))
    (callsRun : Stateful.CallsRel environment label argumentsWorld live scope (invocationReturnType signature)
      (packets.map (functionAssemble head)) raw afterWorld (policy := policy))
    (priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      (raw.map (readResult policy)) selected) :
    Stateful.AtomRel environment label beforeWorld live scope value expected before
      (selected.map (publishResult policy (before.read policy value).erase)) afterWorld (policy := policy) := by
  have branches : Stateful.FunctionBranchesRel environment label headWorld
      (invocationReturnType signature :: live) scope (arguments.zip signature.argumentTypes)
      [(head, headFrame)] (packets.map (functionAssemble head)) argumentsWorld (policy := policy) := by
    simpa only [List.append_nil] using
      (Stateful.FunctionBranchesRel.continuing (head := (head, headFrame)) headContinues argumentsRun .nil)
  have functionRun : Stateful.FunctionRel environment label beforeWorld
      (invocationReturnType signature :: live) scope expected signature operator arguments selectedFrame
      (packets.map (functionAssemble head)) argumentsWorld (policy := policy) :=
    .evaluated arity operatorRun branches
  have invocations : Stateful.InvocationsRel environment label beforeWorld live scope expected signature
      operator arguments [selectedFrame] raw afterWorld (policy := policy) := by
    simpa only [List.append_nil] using Stateful.InvocationsRel.cons functionRun callsRun .nil
  exact .function entry shape selection invocations priority

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition
