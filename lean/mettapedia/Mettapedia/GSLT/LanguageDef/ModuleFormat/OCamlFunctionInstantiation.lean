import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternRuleCoverage

/-! Lambda dispatch connects existing indexed function rules to pattern
requests. A successful request enters the same source body/environment.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def functionBindings (captured : OCaml.Environment) (argument : OCaml.Value) (continuation : Pattern) : Bindings :=
  [("ml:environment", environment captured), ("ml:argument", value argument), ("ml:continuation", continuation)]

theorem function_lambda_rows (program : OCaml.Program) {pool : List OCaml.MatchPattern}
    (reference body : OCaml.Code) {parameter : OCaml.MatchPattern} {patternCode : Pattern}
    (resolved : patternReference? pool parameter = some patternCode) :
    functionRules? program pool reference (.lambda parameter body) = some [rule ("ml-function:" ++ toString reference)
      (node "MlApply" [node "MlClosure" [node "MlLambdaFunction" [code reference], hole "environment"],
        hole "argument", hole "continuation"])
      (node "MlMatchOne" [patternCode, hole "argument", code body, hole "environment", hole "continuation"])] := by
  simp only [functionRules?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem function_lambda_instance (program : OCaml.Program) {pool : List OCaml.MatchPattern}
    (reference body : OCaml.Code) {parameter : OCaml.MatchPattern} {patternCode : Pattern}
    (resolved : patternReference? pool parameter = some patternCode)
    (captured : OCaml.Environment) (argument : OCaml.Value) (continuation : Pattern) :
    ∃ row, functionRules? program pool reference (.lambda parameter body) = some [row] ∧
      applyBindings (functionBindings captured argument continuation) row.left =
        node "MlApply" [value (.closure (.lambda reference) captured), value argument, continuation] ∧
      applyBindings (functionBindings captured argument continuation) row.right =
        node "MlMatchOne" [patternCode, value argument, code body, environment captured, continuation] := by
  refine ⟨_, function_lambda_rows program reference body resolved, ?_, ?_⟩
  · simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code]
    simp [functionBindings, hole, applyBindings, value]
  · simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code, patternReference?_fixed _ resolved]
    simp [functionBindings, hole, applyBindings]

theorem enter_body_encoding {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern}
    {argument : OCaml.Value} {bindings : List OCaml.Value} (body : OCaml.Code)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation) {encodedContinuation : Pattern}
    (resolved : continuation? pool continuation = some encodedContinuation)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    state? pool (OCaml.enterBody parameter argument body captured continuation) =
      some (node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedContinuation]) := by
  simp only [OCaml.enterBody, matched, state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem lambda_source_success (program : OCaml.Program) (reference body : OCaml.Code)
    (parameter : OCaml.MatchPattern) (captured : OCaml.Environment) (argument : OCaml.Value)
    (bindings : List OCaml.Value) (continuation : OCaml.Continuation)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned (.closure (.lambda reference) captured) (.function argument :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend captured bindings) continuation)) := by
  simp only [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declared, OCaml.enterBody, matched,
    Except.map]

theorem lambda_pattern_lowering (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference body index : OCaml.Code) (parameter : OCaml.MatchPattern) (captured : OCaml.Environment)
    (argument : OCaml.Value) (bindings : List OCaml.Value) (continuation : OCaml.Continuation)
    (encodedContinuation : Pattern)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (parameterResolved : patternReference? pool parameter = some (patternId index))
    (continuationResolved : continuation? pool continuation = some encodedContinuation)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned (.closure (.lambda reference) captured) (.function argument :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend captured bindings) continuation)) ∧
    ∃ functionRow assignment,
      functionRules? program pool reference (.lambda parameter body) = some [functionRow] ∧
      applyBindings (functionBindings captured argument encodedContinuation) functionRow.left =
        node "MlApply" [value (.closure (.lambda reference) captured), value argument, encodedContinuation] ∧
      applyBindings (functionBindings captured argument encodedContinuation) functionRow.right =
        applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).left ∧
      state? pool (.evaluate body (OCaml.extend captured bindings) continuation) =
        some (applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).right) := by
  refine ⟨lambda_source_success program reference body parameter captured argument bindings continuation declared matched, ?_⟩
  obtain ⟨functionRow, rows, input, request⟩ := function_lambda_instance program reference body parameterResolved
    captured argument encodedContinuation
  obtain ⟨assignment, patternInput, patternOutput⟩ := match_one_rule_complete parameter index argument bindings body
    captured encodedContinuation matched
  refine ⟨functionRow, assignment, rows, input, request.trans patternInput.symm, ?_⟩
  rw [patternOutput]
  simpa only [OCaml.enterBody, matched] using
    enter_body_encoding body captured continuation continuationResolved matched

#print axioms function_lambda_instance
#print axioms enter_body_encoding
#print axioms lambda_source_success
#print axioms lambda_pattern_lowering

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
