import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedFunctionSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochFailureAuthorization

/-! A successful source closure call is realized by three actual occurrence
GSLT steps: return-to-application, source function dispatch and pattern entry.
The source machine makes one step; administrative target steps retain the
complete caller continuation and the source environment extension.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_lambda_return_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (reference body : OCaml.Code) (parameter : OCaml.MatchPattern)
    (capturedEnvironment : OCaml.Environment) (argument : OCaml.Value) (bindings : List OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned (.closure (.lambda reference) capturedEnvironment) (.function argument :: rest)) =
      .ok (some (.evaluate body (OCaml.extend capturedEnvironment bindings) rest)) ∧
    state? (patterns program) (.evaluate body (OCaml.extend capturedEnvironment bindings) rest) =
      some (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.lambda reference) capturedEnvironment), node "MlKFunction" [value argument, encodedRest]])
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declared, OCaml.enterBody, matched]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · have first := prepared_return_function_step program prepared table (.closure (.lambda reference) capturedEnvironment)
      argument rest encodedRest built signatures resolved
    obtain ⟨index, referenced, indexed, dispatch⟩ := prepared_lambda_dispatch_step program prepared table reference body parameter
      capturedEnvironment argument rest encodedRest built signatures declared resolved
    have entered := epoch_match_success_step program prepared table index parameter argument bindings body capturedEnvironment
      rest encodedRest built (prepared_plan_complete program prepared built) signatures indexed referenced resolved matched
    exact (Relation.ReflTransGen.single first).trans
      ((Relation.ReflTransGen.single dispatch).trans (Relation.ReflTransGen.single entered))

theorem prepared_recursive_return_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (group groupBody slot reference body : OCaml.Code)
    (definitions : List OCaml.Code) (parameter : OCaml.MatchPattern) (capturedEnvironment : OCaml.Environment)
    (argument : OCaml.Value) (bindings : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    let recursiveEnvironment := OCaml.recursiveEnvironment group definitions capturedEnvironment
    OCaml.machineStep program (.returned (.closure (.recursive group slot) capturedEnvironment) (.function argument :: rest)) =
      .ok (some (.evaluate body (OCaml.extend recursiveEnvironment bindings) rest)) ∧
    state? (patterns program) (.evaluate body (OCaml.extend recursiveEnvironment bindings) rest) =
      some (node "MlEvaluate" [code body, environment (OCaml.extend recursiveEnvironment bindings), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.recursive group slot) capturedEnvironment), node "MlKFunction" [value argument, encodedRest]])
      (node "MlEvaluate" [code body, environment (OCaml.extend recursiveEnvironment bindings), encodedRest]) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declaredGroup, declaredSlot, declaredFunction, OCaml.enterBody, matched]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · have first := prepared_return_function_step program prepared table (.closure (.recursive group slot) capturedEnvironment)
      argument rest encodedRest built signatures resolved
    obtain ⟨index, referenced, indexed, dispatch⟩ := prepared_recursive_dispatch_step program prepared table group groupBody slot
      reference body definitions parameter capturedEnvironment argument rest encodedRest built signatures declaredGroup declaredSlot declaredFunction resolved
    have entered := epoch_match_success_step program prepared table index parameter argument bindings body
      (OCaml.recursiveEnvironment group definitions capturedEnvironment) rest encodedRest built
      (prepared_plan_complete program prepared built) signatures indexed referenced resolved matched
    exact (Relation.ReflTransGen.single first).trans
      ((Relation.ReflTransGen.single dispatch).trans (Relation.ReflTransGen.single entered))

theorem prepared_let_return_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (body : OCaml.Code) (capturedEnvironment : OCaml.Environment) (argument : OCaml.Value)
    (bindings : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned argument (.letValue parameter body capturedEnvironment :: rest)) =
      .ok (some (.evaluate body (OCaml.extend capturedEnvironment bindings) rest)) ∧
    state? (patterns program) (.evaluate body (OCaml.extend capturedEnvironment bindings) rest) =
      some (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKLet" [patternId index, code body, environment capturedEnvironment, encodedRest]])
      (node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.enterBody, matched]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · have first := prepared_return_let_step program prepared table parameter (patternId index) argument body capturedEnvironment
      rest encodedRest built signatures referenced resolved
    have entered := epoch_match_success_step program prepared table index parameter argument bindings body capturedEnvironment
      rest encodedRest built (prepared_plan_complete program prepared built) signatures indexed referenced resolved matched
    exact (Relation.ReflTransGen.single first).trans (Relation.ReflTransGen.single entered)

#print axioms prepared_lambda_return_success_path
#print axioms prepared_recursive_return_success_path
#print axioms prepared_let_return_success_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
