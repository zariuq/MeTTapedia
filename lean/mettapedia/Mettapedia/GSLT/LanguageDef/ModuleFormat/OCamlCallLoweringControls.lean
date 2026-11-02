import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRootFiringControls

/-! A reachable identity-function call takes one source machine transition
and three compiled root firings. The actual shared search traverses apply,
pattern-request and body-entry states before reaching the encoded successor.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.CallLoweringControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def sourceProgram : OCaml.Program := {
  code := #[.variable 0, .lambda .bind 0, .literal (.integer 7), .apply 1 2]
  entry := 3 }

def argument : OCaml.Value := .literal (.integer 7)
def sourceState : OCaml.MachineState := .returned (.closure (.lambda 1) []) [.function argument]
def successorState : OCaml.MachineState := .evaluate 0 [argument] []

def published (plan : GeneralExecutionAdmission.Plan) (source : Pattern) (ordinal : Nat)
    (expected : Pattern) : Bool := Id.run do
  let request : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩
  let searched := Complete.DeepRoot.run request 200 (Complete.DeepRoot.start request)
  return searched.complete && searched.publication.any (fun firing => firing.target == expected)

structure ControlResult where
  prepared : Bool
  planAdmitted : Bool
  sourceStateReached : Bool
  sourceSingleStep : Bool
  returnToApply : Bool
  applyToPatternRequest : Bool
  patternRequestToBody : Bool
  sourceSuccessorAgrees : Bool
  deriving Repr

def control : ControlResult := Id.run do
  match prepare sourceProgram with
  | .error _ => return ⟨false, false, false, false, false, false, false, false⟩
  | .ok prepared =>
    let selected := prepared.compiled.rewrites.zipIdx.filterMap fun (row, index) =>
      if ["ReturnFunction", "ml-function:1", "ml-pattern-one:0"].contains row.name then some index else none
    let executable := GeneralExecutionAdmission.compile ⟨prepared.compiled, [], provider⟩
      {permissions with ruleIndices := some selected}
    let returned := node "MlReturn" [value (.closure (.lambda 1) []), node "MlKFunction" [value argument, node "MlKDone"]]
    let applied := node "MlApply" [value (.closure (.lambda 1) []), value argument, node "MlKDone"]
    let requested := node "MlMatchOne" [patternId 0, value argument, code 0, environment [], node "MlKDone"]
    let entered := node "MlEvaluate" [code 0, environment [argument], node "MlKDone"]
    return {
      prepared := sourceProgram.checkScope && selected == [2, 31, 32]
      planAdmitted := executable.complete
      sourceStateReached := OCaml.run sourceProgram 4 (OCaml.begin sourceProgram) == .pending sourceState
      sourceSingleStep := match OCaml.machineStep sourceProgram sourceState with
        | .ok (some next) => next == successorState
        | _ => false
      returnToApply := published executable returned 0 applied
      applyToPatternRequest := published executable applied 1 requested
      patternRequestToBody := published executable requested 2 entered
      sourceSuccessorAgrees := state? prepared.patternPool successorState == some entered }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.prepared && result.planAdmitted && result.sourceStateReached && result.sourceSingleStep &&
    result.returnToApply && result.applyToPatternRequest && result.patternRequestToBody && result.sourceSuccessorAgrees

#eval control
#guard control.passed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.CallLoweringControls
