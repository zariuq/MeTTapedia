import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClassPatternFailure

/-! The class runner commits a successful pattern and settles on a failed
one. A zero-work page keeps searching and cannot authorize failure.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ClassFailureControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines

def parameter : OCaml.MatchPattern := .literal (.integer 7)
def program : OCaml.Program := {code := #[.literal .unit, .lambda parameter 0], entry := 1}

structure ControlResult where
  prepared : Bool
  completePlan : Bool
  fullPatternRows : Bool
  correctPhase : Bool
  correctState : Bool
  correctHistory : Bool
  pendingCannotFail : Bool
  sourceAgrees : Bool
  deriving Repr

def control (clause matched : Bool) : ControlResult := Id.run do
  match prepare program with
  | .error _ => return ⟨false, false, false, false, false, false, false, false⟩
  | .ok prepared =>
    let compiled := plan prepared
    let argument : OCaml.Value := .literal (.integer (if matched then 7 else 8))
    let source := if clause then
      node "MlTryClause" [patternId 0, value argument, code 0, node "MlClauseNil", environment [], node "MlKDone"] else
      node "MlMatchOne" [patternId 0, value argument, code 0, environment [], node "MlKDone"]
    let expected := node "MlEvaluate" [code 0, environment [], node "MlKDone"]
    let search := Complete.Classes.search compiled [] (.base "MlConfig")
    let first := ResumableSearchRunner.Machine.begin search source
    let after := ResumableSearchRunner.Machine.tick search first 100
    let pending := ResumableSearchRunner.Machine.tick search first 0
    return {
      prepared := program.checkScope
      completePlan := compiled.complete
      fullPatternRows := compiled.rules.any (fun row => row.authored.name == "ml-pattern-one:0") &&
        compiled.rules.any (fun row => row.authored.name == "ml-pattern-clause:0")
      correctPhase := decide (after.phase = if matched then .running else .done)
      correctState := after.state == if matched then expected else source
      correctHistory := if matched then after.receipts.length == 1 && after.states.length == 2 else
        after.receipts.isEmpty && after.states == [source]
      pendingCannotFail := decide (pending.phase = .running) && pending.state == source && pending.receipts.isEmpty
      sourceAgrees := if matched then (OCaml.matchPattern parameter argument).isSome else
        (OCaml.matchPattern parameter argument).isNone }

def ControlResult.passed (result : ControlResult) : Bool :=
  result.prepared && result.completePlan && result.fullPatternRows && result.correctPhase &&
    result.correctState && result.correctHistory && result.pendingCannotFail && result.sourceAgrees

#eval control false true
#eval control false false
#eval control true true
#eval control true false
#guard (control false true).passed
#guard (control false false).passed
#guard (control true true).passed
#guard (control true false).passed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ClassFailureControls
