import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPool

/-! Direct source instructions perform one structural machine transition.
Variable lookup and argument construction retain their separate lookup and
administrative paths. No source instruction is silently reclassified.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def DirectInstruction : OCaml.Instruction → Prop
  | .variable _ | .tuple _ | .variant _ _ _ | .primitive _ _ => False
  | _ => True

theorem direct_instruction_left (pool : List OCaml.MatchPattern) (reference : OCaml.Code) (instruction : OCaml.Instruction)
    (row : RewriteRule) (direct : DirectInstruction instruction)
    (formed : compileInstruction? pool reference instruction = some row) :
    row.left = node "MlEvaluate" [code reference, hole "environment", hole "continuation"] := by
  cases instruction with
  | «variable» | tuple | variant | primitive => cases direct
  | letValue parameter argument body =>
      cases resolved : patternReference? pool parameter <;>
        simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.pure_def, Option.some.injEq, reduceCtorEq] at formed
      cases formed
      rfl
  | matchValue scrutinee clauses =>
      cases resolved : clauseList? pool clauses <;>
        simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.pure_def, Option.some.injEq, reduceCtorEq] at formed
      cases formed
      rfl
  | _ =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      rfl

theorem instruction_result_instantiated {pool : List OCaml.MatchPattern} {reference : OCaml.Code}
    {instruction : OCaml.Instruction} {row : RewriteRule} {captured rest target : Pattern}
    (formed : compileInstruction? pool reference instruction = some row)
    (result : instructionResult? pool reference instruction captured rest = some target) :
    applyBindings (instructionBindings captured rest) row.right = target := by
  simp only [instructionResult?, formed, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at result
  exact result

theorem direct_instruction_source (program : OCaml.Program) (reference : OCaml.Code) (instruction : OCaml.Instruction)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (direct : DirectInstruction instruction)
    (declared : program.instruction? reference = some instruction)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ next target, OCaml.machineStep program (.evaluate reference captured rest) = .ok (some next) ∧
      state? (patterns program) next = some target ∧
      instructionResult? (patterns program) reference instruction (environment captured) encodedRest = some target := by
  cases instruction with
  | «variable» | tuple | variant | primitive => cases direct
  | literal datum =>
      refine ⟨.returned (.literal datum) rest, node "MlReturn" [literal datum, encodedRest], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact literal_instruction _ _ _ _ _
  | lambda parameter body =>
      refine ⟨.returned (.closure (.lambda reference) captured) rest,
        node "MlReturn" [value (.closure (.lambda reference) captured), encodedRest], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact lambda_instruction _ _ _ _ _ _
  | apply function argument =>
      refine ⟨.evaluate argument captured (.argument function captured :: rest),
        node "MlEvaluate" [code argument, environment captured, node "MlKArgument" [code function, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact application_instruction _ _ _ _ _ _
  | letRecursive definitions body =>
      refine ⟨.evaluate body (OCaml.recursiveEnvironment reference definitions captured) rest,
        node "MlEvaluate" [code body, recursiveEnvironment reference definitions (environment captured), encodedRest], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, resolved, recursive_environment, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact recursive_instruction _ _ _ _ _ _
  | branch condition yes no =>
      refine ⟨.evaluate condition captured (.branch yes no captured :: rest),
        node "MlEvaluate" [code condition, environment captured, node "MlKBranch" [code yes, code no, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact branch_instruction _ _ _ _ _ _ _
  | andThen left right =>
      refine ⟨.evaluate left captured (.andThen right captured :: rest),
        node "MlEvaluate" [code left, environment captured, node "MlKAnd" [code right, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact and_instruction _ _ _ _ _ _
  | orElse left right =>
      refine ⟨.evaluate left captured (.orElse right captured :: rest),
        node "MlEvaluate" [code left, environment captured, node "MlKOr" [code right, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact or_instruction _ _ _ _ _ _
  | cons head tail =>
      refine ⟨.evaluate tail captured (.consTail head captured :: rest),
        node "MlEvaluate" [code tail, environment captured, node "MlKConsTail" [code head, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact cons_instruction _ _ _ _ _ _
  | letValue parameter argument body =>
      obtain ⟨parameterCode, referenced⟩ := patternReference?_exists (let_pattern_member declared)
      refine ⟨.evaluate argument captured (.letValue parameter body captured :: rest),
        node "MlEvaluate" [code argument, environment captured, node "MlKLet" [parameterCode, code body, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, referenced, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact let_instruction _ _ _ referenced _ _
  | matchValue scrutinee clauses =>
      obtain ⟨clauseCode, referenced⟩ := program_clauses_resolve declared
      refine ⟨.evaluate scrutinee captured (.matchValue clauses captured :: rest),
        node "MlEvaluate" [code scrutinee, environment captured, node "MlKMatch" [clauseCode, environment captured, encodedRest]], ?_, ?_, ?_⟩
      · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map]; rfl
      · simp only [state?, continuation?, frame?, referenced, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      · exact match_instruction _ _ referenced _ _

#print axioms direct_instruction_source

theorem direct_instruction_plan_step {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {reference : OCaml.Code} {instruction : OCaml.Instruction}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (declared : program.instruction? reference = some instruction)
    (direct : DirectInstruction instruction)
    (formed : compileInstruction? (patterns program) reference instruction = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ next target trace captured,
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) = .ok (some next) ∧
      state? (patterns program) next = some target ∧
      GeneralPremise.RootFiring
        (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
        (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured [] target := by
  obtain ⟨next, target, sourceStep, targetEncoded, result⟩ :=
    direct_instruction_source program reference instruction capturedEnvironment rest encodedRest direct declared resolved
  have input : applyBindings (instructionBindings (environment capturedEnvironment) encodedRest) row.authored.left =
      node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest] := by
    rw [direct_instruction_left (patterns program) reference instruction row.authored direct formed]
    simp only [apply_node, List.map_cons, List.map_nil, apply_code, apply_environment_hole, apply_continuation_hole]
  have output := instruction_result_instantiated formed result
  have sourceEncoded : state? (patterns program) (.evaluate reference capturedEnvironment rest) =
      some (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) := by
    simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨trace, captured, firing⟩ := instruction_plan_coverage position terms types formed sourceEncoded targetEncoded input output
  exact ⟨next, target, trace, captured, sourceStep, targetEncoded, firing⟩

#print axioms direct_instruction_plan_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
