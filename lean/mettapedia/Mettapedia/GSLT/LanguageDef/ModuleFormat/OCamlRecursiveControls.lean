import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRecursiveInstantiation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCallLoweringControls

/-! A two-function group exercises slot-preserving dispatch through the
actual shared matcher. Other slots, missing slots and environments are
separating controls; the group remains ordinary indexed source code.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.RecursiveControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def program : OCaml.Program := {
  code := #[.variable 0, .lambda .bind 0, .literal (.integer 99), .lambda .wildcard 2,
    .variable 1, .literal (.integer 7), .apply 4 5, .letRecursive [1, 3] 6]
  entry := 7 }
def argument : OCaml.Value := .literal (.integer 7)

structure ControlResult where
  prepared : Bool
  admitted : Bool
  selectedRows : Bool
  sourceStep : Bool
  returnDispatch : Bool
  recursiveDispatch : Bool
  patternEntry : Bool
  sourceResult : Bool
  wrongSlotRefused : Bool
  missingSlotRefused : Bool
  deriving Repr

def noPublication (plan : GeneralExecutionAdmission.Plan) (source : Pattern) (ordinal : Nat) : Bool := Id.run do
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, ordinal⟩
  let result := Complete.DeepRoot.run query 300 (Complete.DeepRoot.start query)
  return result.complete && result.publication.isEmpty

def control (slot : Nat) : ControlResult := Id.run do
  match prepare program with
  | .error _ => return ⟨false, false, false, false, false, false, false, false, false, false⟩
  | .ok prepared =>
      let wanted := "ml-recursive:7:" ++ toString slot
      let patternIndex := slot
      let selected := prepared.compiled.rewrites.zipIdx.filterMap fun (row, index) =>
        if ["ReturnFunction", wanted, "ml-pattern-one:" ++ toString patternIndex].contains row.name then some index else none
      let plan := GeneralExecutionAdmission.compile ⟨prepared.compiled, [], provider⟩
        {permissions with ruleIndices := some selected}
      let function : OCaml.Value := .closure (.recursive 7 slot) []
      let source : OCaml.MachineState := .returned function [.function argument]
      let captured := OCaml.recursiveEnvironment 7 [1, 3] []
      let bindings := if slot == 0 then [argument] else []
      let body := if slot == 0 then 0 else 2
      let next : OCaml.MachineState := .evaluate body (OCaml.extend captured bindings) []
      let returned := node "MlReturn" [value function, node "MlKFunction" [value argument, node "MlKDone"]]
      let applied := node "MlApply" [value function, value argument, node "MlKDone"]
      let request := node "MlMatchOne" [patternId patternIndex, value argument, code body, environment captured, node "MlKDone"]
      let entered := node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), node "MlKDone"]
      return {
        prepared := program.checkScope
        admitted := plan.complete
        selectedRows := plan.rules.length == 3 &&
          (plan.rules[1]?).any (fun row => row.authored.name == wanted)
        sourceStep := match OCaml.machineStep program source with
          | .ok (some actual) => actual == next
          | _ => false
        returnDispatch := CallLoweringControls.published plan returned 0 applied
        recursiveDispatch := CallLoweringControls.published plan applied 1 request
        patternEntry := CallLoweringControls.published plan request 2 entered
        sourceResult := state? prepared.patternPool next == some entered
        wrongSlotRefused := noPublication plan
          (node "MlApply" [value (.closure (.recursive 7 (1 - slot)) []), value argument, node "MlKDone"]) 1
        missingSlotRefused := noPublication plan
          (node "MlApply" [value (.closure (.recursive 7 2) []), value argument, node "MlKDone"]) 1 }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.prepared && result.admitted && result.selectedRows && result.sourceStep && result.returnDispatch &&
    result.recursiveDispatch && result.patternEntry && result.sourceResult && result.wrongSlotRefused && result.missingSlotRefused

#eval control 0
#eval control 1
#guard (control 0).passed
#guard (control 1).passed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.RecursiveControls
