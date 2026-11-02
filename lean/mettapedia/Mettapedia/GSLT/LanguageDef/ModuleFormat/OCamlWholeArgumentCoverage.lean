import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlArgumentInstructions

/-! Nonempty tuple, variant and primitive instructions obtain their actual
selected row from a complete prepared plan. The emitted target encodes the
source gather state, retaining every unevaluated argument and continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_build_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (last : OCaml.Code) (later : List OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (buildInstruction kind arguments))
    (reversed : arguments.reverse = last :: later)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ ordinal target trace captured,
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) =
        .ok (some (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest))) ∧
      state? (patterns program) (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest)) = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
        (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured [] target := by
  obtain ⟨ordinal, row, selected, formed, _⟩ :=
    whole_plan_instruction program prepared reference (buildInstruction kind arguments) built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨trace, captured, firing⟩ := build_instruction_plan_step selected terms types reversed formed resolved
  exact ⟨ordinal, _, trace, captured,
    build_instruction_source program reference kind arguments last later capturedEnvironment rest declared reversed,
    start_arguments_nonempty_encoding (patterns program) kind arguments last later capturedEnvironment rest encodedRest reversed resolved,
    firing⟩

theorem reachable_whole_build_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (kind : OCaml.Build) (arguments : List OCaml.Code) (last : OCaml.Code) (later : List OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (buildInstruction kind arguments))
    (reversed : arguments.reverse = last :: later)
    (reachable : OCaml.MachinePath program (OCaml.begin program) (.evaluate reference capturedEnvironment rest)) :
    ∃ source ordinal target trace captured,
      state? (patterns program) (.evaluate reference capturedEnvironment rest) = some source ∧
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) =
        .ok (some (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest))) ∧
      state? (patterns program) (.evaluate last capturedEnvironment (.gather kind later capturedEnvironment [] :: rest)) = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
        source ordinal trace captured captured [] target := by
  have covered := machine_path_covered program _ _ (initial_covered program) reachable
  obtain ⟨encodedRest, resolved⟩ := continuation?_exists (patterns program) rest covered
  obtain ⟨ordinal, target, trace, captured, step, encoded, firing⟩ :=
    whole_build_instruction program prepared reference kind arguments last later capturedEnvironment rest encodedRest
      built complete declared reversed resolved
  refine ⟨node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest], ordinal, target,
    trace, captured, ?_, step, encoded, firing⟩
  simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms whole_build_instruction
#print axioms reachable_whole_build_instruction

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
