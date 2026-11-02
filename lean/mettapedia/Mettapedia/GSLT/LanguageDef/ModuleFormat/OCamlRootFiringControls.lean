import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnReadout
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootSearch

/-! Executable controls use the actual authored O0 module, its selected
occurrence-aware plan and the existing complete root search. The general
root-search theorems establish soundness and coverage separately.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.RootFiringControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

/-- Execution ordinal zero retains source declaration ordinal one. -/
def compiled : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨baseLanguage, [], provider⟩ {permissions with ruleIndices := some [1]}

def caller := GeneralPlanEnvironment.environment compiled
def actualArgument := value (.literal (.integer 7))
def actualFunction := code 1
def actualEnvironment := environment []
def actualContinuation := node "MlKDone"
def input := node "MlReturn" [actualArgument, node "MlKArgument"
  [actualFunction, actualEnvironment, actualContinuation]]
def output := node "MlEvaluate" [actualFunction, actualEnvironment,
  node "MlKFunction" [actualArgument, actualContinuation]]
def wrongOutput := node "MlEvaluate" [code 2, actualEnvironment,
  node "MlKFunction" [actualArgument, actualContinuation]]
def request : Complete.DeepRoot.Request := ⟨caller, [], .base "MlConfig", input, 0⟩

structure ControlResult where
  planAdmitted : Bool
  sourcePositionRetained : Bool
  occurrenceMetadataRetained : Bool
  searchComplete : Bool
  correctTargetPublished : Bool
  wrongTargetRefused : Bool
  capturedAssignmentRetained : Bool
  premiseHistoryEmpty : Bool
  deriving Repr

def control : ControlResult := Id.run do
  let searched := Complete.DeepRoot.run request 200 (Complete.DeepRoot.start request)
  return {
    planAdmitted := compiled.complete
    sourcePositionRetained := compiled.rules.length == 1 &&
      (compiled.rules[0]?).any (fun row => row.declarationIndex == 1 && row.authored.name == "ReturnArgument")
    occurrenceMetadataRetained := (compiled.rules[0]?).any (fun row => row.binding.spec.occurrences.length == 8)
    searchComplete := searched.complete
    correctTargetPublished := searched.publication.any (fun firing => firing.target == output)
    wrongTargetRefused := !(searched.publication.any (fun firing => firing.target == wrongOutput))
    capturedAssignmentRetained := searched.publication.all (fun firing => decide (firing.captured = firing.completed))
    premiseHistoryEmpty := searched.publication.all (fun firing => firing.history.isEmpty) }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.planAdmitted && result.sourcePositionRetained && result.occurrenceMetadataRetained &&
    result.searchComplete && result.correctTargetPublished && result.wrongTargetRefused &&
    result.capturedAssignmentRetained && result.premiseHistoryEmpty

#eval control
#guard control.passed

def branchControl (choice : Bool) : ControlResult := Id.run do
  let sourceIndex := if choice then 4 else 5
  let branchPlan := GeneralExecutionAdmission.compile ⟨baseLanguage, [], provider⟩
    {permissions with ruleIndices := some [sourceIndex]}
  let branchEnvironment := GeneralPlanEnvironment.environment branchPlan
  let source := node "MlReturn" [literal (.boolean choice), node "MlKBranch"
    [code 1, code 2, actualEnvironment, actualContinuation]]
  let expected := node "MlEvaluate" [code (if choice then 1 else 2), actualEnvironment, actualContinuation]
  let wrong := node "MlEvaluate" [code (if choice then 2 else 1), actualEnvironment, actualContinuation]
  let query : Complete.DeepRoot.Request := ⟨branchEnvironment, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 200 (Complete.DeepRoot.start query)
  return {
    planAdmitted := branchPlan.complete
    sourcePositionRetained := branchPlan.rules.length == 1 &&
      (branchPlan.rules[0]?).any (fun row => row.declarationIndex == sourceIndex)
    occurrenceMetadataRetained := (branchPlan.rules[0]?).any (fun row => row.binding.spec.occurrences.length == 7)
    searchComplete := searched.complete
    correctTargetPublished := searched.publication.any (fun firing => firing.target == expected)
    wrongTargetRefused := !(searched.publication.any (fun firing => firing.target == wrong))
    capturedAssignmentRetained := searched.publication.all (fun firing => decide (firing.captured = firing.completed))
    premiseHistoryEmpty := searched.publication.all (fun firing => firing.history.isEmpty) }

def nonBooleanRefused (choice : Bool) : Bool := Id.run do
  let branchPlan := GeneralExecutionAdmission.compile ⟨baseLanguage, [], provider⟩
    {permissions with ruleIndices := some [if choice then 4 else 5]}
  let source := node "MlReturn" [actualArgument, node "MlKBranch"
    [code 1, code 2, actualEnvironment, actualContinuation]]
  let query : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment branchPlan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 200 (Complete.DeepRoot.start query)
  return searched.complete && searched.publication.isEmpty

#eval branchControl true
#eval branchControl false
#guard (branchControl true).passed
#guard (branchControl false).passed
#guard nonBooleanRefused true
#guard nonBooleanRefused false

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.RootFiringControls
