import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableFiring
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootSearch

/-! Indexed lookup controls run the actual selected compiler row. Duplicate
values do not change positions, and a short environment publishes nothing.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.VariableControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def items : OCaml.Environment := [.literal (.integer 7), .literal (.integer 8), .literal (.integer 7)]

def compiled (index : Nat) : GeneralExecutionAdmission.Plan :=
  let generated := (compileInstruction? [] 19 (.variable index)).toList
  GeneralExecutionAdmission.compile ⟨{baseLanguage with rewrites := baseLanguage.rewrites ++ generated}, [], provider⟩
    {permissions with ruleIndices := some [baseLanguage.rewrites.length]}

structure ControlResult where
  admitted : Bool
  sourcePositionRetained : Bool
  searchComplete : Bool
  targetExact : Bool
  wrongTargetRefused : Bool
  capturedAssignmentRetained : Bool
  premiseHistoryEmpty : Bool
  sourceLookup : Bool
  deriving Repr

def control (index : Nat) (environmentValues : OCaml.Environment) : ControlResult := Id.run do
  let plan := compiled index
  let rest := node "MlKDone"
  let source := node "MlEvaluate" [code 19, environment environmentValues, rest]
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 300 (Complete.DeepRoot.start query)
  let expected := environmentValues[index]?.map fun actual => node "MlReturn" [value actual, rest]
  return {
    admitted := plan.complete
    sourcePositionRetained := plan.rules.length == 1 &&
      (plan.rules[0]?).any (fun row => row.declarationIndex == baseLanguage.rewrites.length && row.authored.name == "ml-code:19")
    searchComplete := searched.complete
    targetExact := match expected with
      | some target => searched.publication.length == 1 && searched.publication.all (fun firing => firing.target == target)
      | none => searched.publication.isEmpty
    wrongTargetRefused := !(searched.publication.any (fun firing =>
      firing.target == node "MlReturn" [literal (.integer 99), rest]))
    capturedAssignmentRetained := searched.publication.all (fun firing => decide (firing.captured = firing.completed))
    premiseHistoryEmpty := searched.publication.all (fun firing => firing.history.isEmpty)
    sourceLookup := match expected, OCaml.evaluateInstruction {code := Array.replicate 19 (.literal .unit) |>.push (.variable index), entry := 19}
        19 environmentValues [] with
      | some target, .ok next => state? [] next == some target
      | none, .error (.unboundVariable actual) => actual == index
      | _, _ => false }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.admitted && result.sourcePositionRetained && result.searchComplete && result.targetExact &&
    result.wrongTargetRefused && result.capturedAssignmentRetained && result.premiseHistoryEmpty && result.sourceLookup

#eval control 0 items
#eval control 1 items
#eval control 2 items
#eval control 3 items
#guard (control 0 items).passed
#guard (control 1 items).passed
#guard (control 2 items).passed
#guard (control 3 items).passed
#guard (control 0 []).passed
#guard (control 2 (items.take 2)).passed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.VariableControls
