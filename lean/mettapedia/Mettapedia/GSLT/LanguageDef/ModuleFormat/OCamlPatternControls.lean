import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternRuleReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRootFiringControls

/-! Nested source patterns exercise the actual compiled matcher, including
binding order, wildcard slots, exact arity and constructor identities.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.PatternControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def nestedPattern : OCaml.MatchPattern :=
  .tuple [.bind, .wildcard, .variant 0 1 [.cons .bind (.literal .nil)]]
def seven : OCaml.Value := .literal (.integer 7)
def nine : OCaml.Value := .literal (.integer 9)
def ignored : OCaml.Value := .literal (.boolean true)
def nestedValue : OCaml.Value := .tuple [seven, ignored, .variant 0 1 [.cons nine (.literal .nil)]]
def wrongConstructor : OCaml.Value := .tuple [seven, ignored, .variant 0 2 [.cons nine (.literal .nil)]]
def shortTuple : OCaml.Value := .tuple [seven, .variant 0 1 [.cons nine (.literal .nil)]]
def captures : PatternCaptures := [(0, seven), (1, ignored), (2, nine)]

theorem nested_source_match : OCaml.matchPattern nestedPattern nestedValue = some [seven, nine] := by rfl
theorem nested_source_wrong_tag : OCaml.matchPattern nestedPattern wrongConstructor = none := by decide_cbv
theorem nested_source_wrong_arity : OCaml.matchPattern nestedPattern shortTuple = none := by decide_cbv

theorem nested_compiled_coverage : ∃ assignment : Bindings,
    applyBindings assignment (patternAt nestedPattern 0).term = value nestedValue :=
  (pattern_instance_iff nestedPattern 0 nestedValue).mpr ⟨[seven, nine], nested_source_match⟩
theorem nested_compiled_wrong_tag : ¬ ∃ assignment : Bindings,
    applyBindings assignment (patternAt nestedPattern 0).term = value wrongConstructor :=
  (pattern_failure_iff nestedPattern 0 wrongConstructor).mp nested_source_wrong_tag
theorem nested_compiled_wrong_arity : ¬ ∃ assignment : Bindings,
    applyBindings assignment (patternAt nestedPattern 0).term = value shortTuple :=
  (pattern_failure_iff nestedPattern 0 shortTuple).mp nested_source_wrong_arity

#guard patternAfter nestedPattern 0 == 3
#guard applyBindings (captureBindings captures) (patternAt nestedPattern 0).term == value nestedValue
#guard (patternAt nestedPattern 0).bindings.map (applyBindings (captureBindings captures)) == [value seven, value nine]

structure ControlResult where
  admitted : Bool
  completed : Bool
  exactlyOneResult : Bool
  correctEnvironment : Bool
  wrongOrderRefused : Bool
  retainsReceipts : Bool
  deriving Repr

def compiledControl (clause : Bool) : ControlResult := Id.run do
  let rows := patternRules 0 nestedPattern
  let language := { baseLanguage with rewrites := rows }
  let plan := GeneralExecutionAdmission.compile ⟨language, [], provider⟩ permissions
  let captured : OCaml.Environment := [.literal (.integer 42)]
  let source := if clause then
    node "MlTryClause" [patternId 0, value nestedValue, code 0, node "MlClauseNil",
      environment captured, node "MlKDone"] else
    node "MlMatchOne" [patternId 0, value nestedValue, code 0, environment captured, node "MlKDone"]
  let expected := node "MlEvaluate" [code 0, environment (OCaml.extend captured [seven, nine]), node "MlKDone"]
  let wrong := node "MlEvaluate" [code 0, environment (OCaml.extend captured [nine, seven]), node "MlKDone"]
  let query : Complete.DeepRoot.Request :=
    ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, if clause then 1 else 0⟩
  let searched := Complete.DeepRoot.run query 500 (Complete.DeepRoot.start query)
  return {
    admitted := plan.complete
    completed := searched.complete
    exactlyOneResult := searched.publication.length == 1
    correctEnvironment := searched.publication.any (fun firing => firing.target == expected)
    wrongOrderRefused := !(searched.publication.any (fun firing => firing.target == wrong))
    retainsReceipts := searched.publication.all (fun firing =>
      decide (firing.captured = firing.completed) && firing.history.isEmpty) }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.admitted && result.completed && result.exactlyOneResult && result.correctEnvironment &&
    result.wrongOrderRefused && result.retainsReceipts

def compiledRefusal (actual : OCaml.Value) : Bool := Id.run do
  let language := { baseLanguage with rewrites := patternRules 0 nestedPattern }
  let plan := GeneralExecutionAdmission.compile ⟨language, [], provider⟩ permissions
  let source := node "MlMatchOne" [patternId 0, value actual, code 0, environment [], node "MlKDone"]
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 500 (Complete.DeepRoot.start query)
  return plan.complete && searched.complete && searched.publication.isEmpty

#eval compiledControl false
#eval compiledControl true
#guard (compiledControl false).passed
#guard (compiledControl true).passed
#guard compiledRefusal wrongConstructor
#guard compiledRefusal shortTuple

#print axioms nested_compiled_coverage
#print axioms nested_compiled_wrong_tag
#print axioms nested_compiled_wrong_arity

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.PatternControls
