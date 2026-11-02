import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBoolean
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnCons
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnGather
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCallLoweringControls

/-! The shared root search exercises structural returns with retained
continuations, distinct Boolean outcomes and ordered gathered values.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ReturnControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def tail := node "MlKDone"
def env := environment [.literal (.integer 42)]
def seven := value (.literal (.integer 7))
def nine := value (.literal (.integer 9))

structure Test where
  index : Nat
  source : Pattern
  expected : Pattern
  wrong : Pattern

def casesToCheck : List Test := [
  ⟨6, node "MlReturn" [literal (.boolean false), node "MlKAnd" [code 1, env, tail]],
    node "MlReturn" [literal (.boolean false), tail], node "MlEvaluate" [code 1, env, tail]⟩,
  ⟨7, node "MlReturn" [literal (.boolean true), node "MlKAnd" [code 1, env, tail]],
    node "MlEvaluate" [code 1, env, node "MlKBoolean" [tail]], node "MlReturn" [literal (.boolean true), tail]⟩,
  ⟨8, node "MlReturn" [literal (.boolean true), node "MlKOr" [code 1, env, tail]],
    node "MlReturn" [literal (.boolean true), tail], node "MlEvaluate" [code 1, env, tail]⟩,
  ⟨9, node "MlReturn" [literal (.boolean false), node "MlKOr" [code 1, env, tail]],
    node "MlEvaluate" [code 1, env, node "MlKBoolean" [tail]], node "MlReturn" [literal (.boolean false), tail]⟩,
  ⟨10, node "MlReturn" [literal (.boolean true), node "MlKBoolean" [tail]],
    node "MlReturn" [literal (.boolean true), tail], node "MlReturn" [literal (.boolean false), tail]⟩,
  ⟨11, node "MlReturn" [literal (.boolean false), node "MlKBoolean" [tail]],
    node "MlReturn" [literal (.boolean false), tail], node "MlReturn" [literal (.boolean true), tail]⟩,
  ⟨12, node "MlReturn" [seven, node "MlKConsTail" [code 1, env, tail]],
    node "MlEvaluate" [code 1, env, node "MlKConsHead" [seven, tail]],
    node "MlEvaluate" [code 2, env, node "MlKConsHead" [seven, tail]]⟩,
  ⟨13, node "MlReturn" [seven, node "MlKConsHead" [nine, tail]],
    node "MlReturn" [node "MlCons" [seven, nine], tail],
    node "MlReturn" [node "MlCons" [nine, seven], tail]⟩,
  ⟨14, node "MlReturn" [seven, node "MlKBuild" [node "MlBuildTuple", codes [code 1, code 2], env, values [nine], tail]],
    node "MlEvaluate" [code 1, env, node "MlKBuild" [node "MlBuildTuple", codes [code 2], env, values [seven, nine], tail]],
    node "MlEvaluate" [code 1, env, node "MlKBuild" [node "MlBuildTuple", codes [code 2], env, values [nine, seven], tail]]⟩,
  ⟨15, node "MlReturn" [seven, node "MlKBuild" [node "MlBuildTuple", codes [], env, values [nine], tail]],
    node "MlBuildConfig" [node "MlBuildTuple", values [seven, nine], tail],
    node "MlBuildConfig" [node "MlBuildTuple", values [nine, seven], tail]⟩,
  ⟨16, node "MlBuildConfig" [node "MlBuildTuple", values [seven, nine], tail],
    node "MlReturn" [node "MlTuple" [values [seven, nine]], tail],
    node "MlReturn" [node "MlTuple" [values [nine, seven]], tail]⟩,
  ⟨17, node "MlBuildConfig" [node "MlBuildVariant" [tag 0 1], values [seven], tail],
    node "MlReturn" [node "MlVariant" [tag 0 1, values [seven]], tail],
    node "MlReturn" [node "MlVariant" [tag 0 2, values [seven]], tail]⟩,
  ⟨18, node "MlBuildConfig" [node "MlBuildPrimitive" [primitive .add], values [seven, nine], tail],
    node "MlPrimitiveRequest" [primitive .add, values [seven, nine], tail],
    node "MlPrimitiveRequest" [primitive .subtract, values [seven, nine], tail]⟩,
  ⟨20, node "MlPrimitiveReturned" [node "MlPrimitiveValue" [seven], tail],
    node "MlReturn" [seven, tail], node "MlFault" [node "MlDivisionByZero"]⟩,
  ⟨21, node "MlPrimitiveReturned" [node "MlPrimitiveFault" [node "MlDivisionByZero"], tail],
    node "MlFault" [node "MlDivisionByZero"], node "MlReturn" [seven, tail]⟩,
  ⟨22, node "MlReturn" [seven, node "MlKMatch" [node "MlClauseCons" [patternId 0, code 1, node "MlClauseNil"], env, tail]],
    node "MlSelect" [node "MlClauseCons" [patternId 0, code 1, node "MlClauseNil"], seven, env, tail],
    node "MlSelect" [node "MlClauseNil", seven, env, tail]⟩,
  ⟨23, node "MlSelect" [node "MlClauseNil", seven, env, tail],
    node "MlFault" [node "MlMatchFailure"], node "MlDone" [seven]⟩,
  ⟨24, node "MlSelect" [node "MlClauseCons" [patternId 0, code 1, node "MlClauseNil"], seven, env, tail],
    node "MlTryClause" [patternId 0, seven, code 1, node "MlClauseNil", env, tail],
    node "MlTryClause" [patternId 1, seven, code 1, node "MlClauseNil", env, tail]⟩]

structure Result where
  admitted : Bool
  complete : Bool
  oneAnswer : Bool
  expected : Bool
  wrongRefused : Bool
  receipts : Bool
  deriving Repr

def runTest (test : Test) : Result := Id.run do
  let plan := GeneralExecutionAdmission.compile ⟨baseLanguage, [], provider⟩
    {permissions with ruleIndices := some [test.index]}
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", test.source, 0⟩
  let searched := Complete.DeepRoot.run query 400 (Complete.DeepRoot.start query)
  return ⟨plan.complete, searched.complete, searched.publication.length == 1,
    searched.publication.any (fun firing => firing.target == test.expected),
    !(searched.publication.any (fun firing => firing.target == test.wrong)),
    searched.publication.all (fun firing => decide (firing.captured = firing.completed) && firing.history.isEmpty)⟩

def Result.passed (result : Result) : Bool := result.admitted && result.complete && result.oneAnswer && result.expected &&
  result.wrongRefused && result.receipts

def nonBooleanRefused (index : Nat) : Bool := Id.run do
  let plan := GeneralExecutionAdmission.compile ⟨baseLanguage, [], provider⟩
    {permissions with ruleIndices := some [index]}
  let frame := if index == 6 || index == 7 then node "MlKAnd" [code 1, env, tail] else
    if index == 8 || index == 9 then node "MlKOr" [code 1, env, tail] else node "MlKBoolean" [tail]
  let source := node "MlReturn" [seven, frame]
  let query : Complete.DeepRoot.Request := ⟨GeneralPlanEnvironment.environment plan, [], .base "MlConfig", source, 0⟩
  let searched := Complete.DeepRoot.run query 400 (Complete.DeepRoot.start query)
  return plan.complete && searched.complete && searched.publication.isEmpty

#eval casesToCheck.map (fun test => (test.index, runTest test))
#guard casesToCheck.all (fun test => (runTest test).passed)
#guard [6, 7, 8, 9, 10, 11].all nonBooleanRefused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ReturnControls
