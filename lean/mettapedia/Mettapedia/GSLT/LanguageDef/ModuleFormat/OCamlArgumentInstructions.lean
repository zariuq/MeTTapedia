import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDirectInstructions

/-! Nonempty argument lists enter the source and emitted gather machines in
the same right-to-left order. Empty lists retain their separate build step;
in particular a nullary constructor is not an empty tuple.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def buildInstruction (kind : OCaml.Build) (arguments : List OCaml.Code) : OCaml.Instruction :=
  match kind with
  | .tuple => .tuple arguments
  | .variant typeId constructor => .variant typeId constructor arguments
  | .primitive operator => .primitive operator arguments

theorem build_instruction_left (pool : List OCaml.MatchPattern) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (row : RewriteRule)
    (formed : compileInstruction? pool reference (buildInstruction kind arguments) = some row) :
    row.left = node "MlEvaluate" [code reference, hole "environment", hole "continuation"] := by
  cases kind <;>
    simp only [buildInstruction, compileInstruction?, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at formed <;> cases formed <;> rfl

theorem build_instruction_result (pool : List OCaml.MatchPattern) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (captured rest : Pattern) :
    instructionResult? pool reference (buildInstruction kind arguments) captured rest =
      some (startArguments (build kind) arguments captured rest) := by
  cases kind with
  | tuple => exact tuple_instruction pool reference arguments captured rest
  | variant typeId constructor => exact variant_instruction pool reference typeId constructor arguments captured rest
  | primitive operator => exact primitive_instruction pool reference operator arguments captured rest

theorem start_arguments_nonempty_encoding (pool : List OCaml.MatchPattern) (kind : OCaml.Build)
    (arguments : List OCaml.Code) (last : OCaml.Code) (later : List OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (reversed : arguments.reverse = last :: later)
    (resolved : continuation? pool rest = some encodedRest) :
    state? pool (.evaluate last captured (.gather kind later captured [] :: rest)) =
      some (startArguments (build kind) arguments (environment captured) encodedRest) := by
  simp only [startArguments, reversed, state?, continuation?, frame?, resolved,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, valueList, values, linked, List.foldr_nil]

theorem build_instruction_source (program : OCaml.Program) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (last : OCaml.Code) (later : List OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (declared : program.instruction? reference = some (buildInstruction kind arguments))
    (reversed : arguments.reverse = last :: later) :
    OCaml.machineStep program (.evaluate reference captured rest) =
      .ok (some (.evaluate last captured (.gather kind later captured [] :: rest))) := by
  cases kind <;>
    simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, buildInstruction,
      OCaml.startArguments, reversed, Except.map]

theorem build_instruction_plan_step {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {reference : OCaml.Code} {kind : OCaml.Build} {arguments : List OCaml.Code}
    {last : OCaml.Code} {later : List OCaml.Code} {capturedEnvironment : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (reversed : arguments.reverse = last :: later)
    (formed : compileInstruction? (patterns program) reference (buildInstruction kind arguments) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured []
      (startArguments (build kind) arguments (environment capturedEnvironment) encodedRest) := by
  have input : applyBindings (instructionBindings (environment capturedEnvironment) encodedRest) row.authored.left =
      node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest] := by
    rw [build_instruction_left (patterns program) reference kind arguments row.authored formed]
    simp only [apply_node, List.map_cons, List.map_nil, apply_code, apply_environment_hole, apply_continuation_hole]
  have output := instruction_result_instantiated formed
    (build_instruction_result (patterns program) reference kind arguments (environment capturedEnvironment) encodedRest)
  apply instruction_plan_coverage (pool := patterns program)
    (sourceState := .evaluate reference capturedEnvironment rest)
    (targetState := .evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest))
    position terms types formed
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · exact start_arguments_nonempty_encoding (patterns program) kind arguments last later capturedEnvironment rest encodedRest reversed resolved
  · exact input
  · exact output

#print axioms build_instruction_source
#print axioms build_instruction_plan_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
