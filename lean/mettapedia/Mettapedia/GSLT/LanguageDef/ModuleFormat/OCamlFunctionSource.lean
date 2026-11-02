import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternSource

/-! A generated function dispatch followed by a successful pattern rule
reflects to the independent source application, including recursive slots.
No source declaration is inferred from a target code number alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem function_rule_readback (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program pool reference instruction = some rows) (member : row ∈ rows)
    (actualFunction argument : OCaml.Value) (continuation : Pattern) (assignment : Bindings)
    (input : applyBindings assignment row.left = node "MlApply" [value actualFunction, value argument, continuation]) :
    ∃ parameter body patternCode sourceEnvironment,
      patternReference? pool parameter = some patternCode ∧
      applyBindings assignment row.right =
        node "MlMatchOne" [patternCode, value argument, code body, environment sourceEnvironment, continuation] ∧
      ∀ rest : OCaml.Continuation,
        OCaml.applyClosure program actualFunction argument rest = .ok (OCaml.enterBody parameter argument body sourceEnvironment rest) := by
  cases instruction with
  | lambda parameter body =>
      cases resolved : patternReference? pool parameter with
      | none => simp [functionRules?, resolved] at compiled
      | some patternCode =>
          obtain ⟨sourceEnvironment, functionSame, output⟩ := lambda_row_readback program pool reference body parameter patternCode
            rows row resolved compiled member actualFunction argument continuation assignment input
          refine ⟨parameter, body, patternCode, sourceEnvironment, resolved, output, ?_⟩
          intro rest
          rw [functionSame]
          simp only [OCaml.applyClosure, declared]
  | letRecursive definitions groupBody =>
      obtain ⟨slot, functionReference, parameter, body, patternCode, indexed, lambdaDeclared, resolved, rowSame⟩ :=
        recursive_rule_origin program pool reference groupBody definitions rows row compiled member
      rw [rowSame] at input
      obtain ⟨sourceEnvironment, functionSame, output⟩ := recursive_row_readback reference slot body definitions parameter pool
        patternCode resolved actualFunction argument continuation assignment input
      refine ⟨parameter, body, patternCode, OCaml.recursiveEnvironment reference definitions sourceEnvironment,
        resolved, rowSame ▸ output, ?_⟩
      intro rest
      rw [functionSame]
      simp only [OCaml.applyClosure, declared, indexed, lambdaDeclared]
      rfl
  | _ =>
      simp only [functionRules?] at compiled
      cases Option.some.inj compiled
      cases member

theorem function_then_pattern_source (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (declared : program.instruction? reference = some instruction)
    (compiled : functionRules? program pool reference instruction = some rows) (member : row ∈ rows)
    (actualFunction argument : OCaml.Value) (continuation : OCaml.Continuation) (encodedContinuation : Pattern)
    (functionAssignment : Bindings)
    (resolved : continuation? pool continuation = some encodedContinuation)
    (input : applyBindings functionAssignment row.left =
      node "MlApply" [value actualFunction, value argument, encodedContinuation]) :
    ∃ parameter body patternCode sourceEnvironment,
      patternReference? pool parameter = some patternCode ∧
      applyBindings functionAssignment row.right =
        node "MlMatchOne" [patternCode, value argument, code body, environment sourceEnvironment, encodedContinuation] ∧
      ∀ (index : Nat) (patternAssignment : Bindings) (target : Pattern),
        patternCode = patternId index →
        applyBindings patternAssignment ((patternRules index parameter)[0]'(by simp [patternRules])).left =
          applyBindings functionAssignment row.right →
        applyBindings patternAssignment ((patternRules index parameter)[0]'(by simp [patternRules])).right = target →
        ∃ next, OCaml.machineStep program (.returned actualFunction (.function argument :: continuation)) = .ok (some next) ∧
          state? pool next = some target := by
  obtain ⟨parameter, body, patternCode, sourceEnvironment, referenced, output, application⟩ :=
    function_rule_readback program pool reference instruction rows row declared compiled member actualFunction argument
      encodedContinuation functionAssignment input
  refine ⟨parameter, body, patternCode, sourceEnvironment, referenced, output, ?_⟩
  intro index patternAssignment target same patternInput patternOutput
  rw [output, same] at patternInput
  obtain ⟨boundValues, matched, targetSame⟩ := match_one_rule_readback parameter index argument body sourceEnvironment
    encodedContinuation patternAssignment patternInput
  refine ⟨.evaluate body (OCaml.extend sourceEnvironment boundValues) continuation, ?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.returnValue, application, OCaml.enterBody, matched, Except.map]
  · rw [← patternOutput, targetSame]
    simpa only [OCaml.enterBody, matched] using enter_body_encoding body sourceEnvironment continuation resolved matched

#print axioms function_rule_readback
#print axioms function_then_pattern_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
