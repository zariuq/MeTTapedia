import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEmptyArgumentCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootSearch

/-! Argument entry controls use the actual compiler and shared search.
Source order, nullary constructors and invalid formation remain distinct.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ArgumentControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

structure ControlResult where
  admitted : Bool
  searchComplete : Bool
  rightmostFirst : Bool
  reversedOrderRefused : Bool
  completeContinuation : Bool
  receiptRetained : Bool
  sourceStep : Bool
  deriving Repr

def selected (kind : OCaml.Build) (arguments : List OCaml.Code) : GeneralExecutionAdmission.Plan :=
  let generated := (compileInstruction? [] 19 (buildInstruction kind arguments)).toList
  GeneralExecutionAdmission.compile ⟨{baseLanguage with rewrites := generated}, [], provider⟩ permissions

def control (kind : OCaml.Build) : ControlResult := Id.run do
  let arguments := [2, 5, 9]
  let plan := selected kind arguments
  let actual : OCaml.Environment := [.literal (.integer 17)]
  let rest := node "MlKBoolean" [node "MlKDone"]
  let source := node "MlEvaluate" [code 19, environment actual, rest]
  let expected := node "MlEvaluate" [code 9, environment actual,
    node "MlKBuild" [build kind, codes ([5, 2].map code), environment actual, valueList [], rest]]
  let wrong := node "MlEvaluate" [code 2, environment actual,
    node "MlKBuild" [build kind, codes ([5, 9].map code), environment actual, valueList [], rest]]
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 300 (Complete.DeepRoot.start query)
  return {
    admitted := plan.complete
    searchComplete := searched.complete
    rightmostFirst := searched.publication.length == 1 && searched.publication.all (fun firing => firing.target == expected)
    reversedOrderRefused := !(searched.publication.any (fun firing => firing.target == wrong))
    completeContinuation := startArguments (build kind) arguments (environment actual) rest == expected
    receiptRetained := searched.publication.all (fun firing => decide (firing.captured = firing.completed) && firing.history.isEmpty)
    sourceStep := match OCaml.startArguments {code := #[], entry := 0} kind arguments actual [.booleanResult] with
      | .ok next => state? [] next == some expected
      | _ => false }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.admitted && result.searchComplete && result.rightmostFirst && result.reversedOrderRefused &&
    result.completeContinuation && result.receiptRetained && result.sourceStep

def nullary : Bool := Id.run do
  let kind : OCaml.Build := .variant 2 3
  let plan := selected kind []
  let source := node "MlEvaluate" [code 19, environment [], node "MlKDone"]
  let expected := node "MlBuildConfig" [build kind, valueList [], node "MlKDone"]
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 300 (Complete.DeepRoot.start query)
  return plan.complete && searched.complete && searched.publication.length == 1 &&
    searched.publication.all (fun firing => firing.target == expected && decide (firing.captured = firing.completed) && firing.history.isEmpty)

#eval control .tuple
#eval control (.variant 2 3)
#eval control (.primitive .subtract)
#guard (control .tuple).passed
#guard (control (.variant 2 3)).passed
#guard (control (.primitive .subtract)).passed
#guard nullary

example : OCaml.startArguments {code := #[], entry := 0} .tuple [] [] [] = .error (.invalidTupleArity 0) := rfl
example : OCaml.startArguments {code := #[], entry := 0} (.variant 2 3) [] [] [] = .error (.invalidConstructor 2 3 0) := rfl
example : OCaml.startArguments {code := #[], entry := 0, constructors := [⟨2, 3, 0⟩]} (.variant 2 3) [] [] [] =
    .ok (.returned (.variant 2 3 []) []) := rfl
example : startArguments (build (.variant 2 3)) [] (environment []) (node "MlKDone") =
    node "MlBuildConfig" [build (.variant 2 3), valueList [], node "MlKDone"] := rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ArgumentControls
