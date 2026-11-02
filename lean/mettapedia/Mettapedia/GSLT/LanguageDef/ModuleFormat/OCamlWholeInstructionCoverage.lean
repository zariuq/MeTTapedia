import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholePlanRows
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDirectInstructions
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCoveragePreservation

/-! Complete prepared plans supply their own instruction rows and actual
root firings for direct instructions and indexed variable lookup. Reachable
states supply continuation encodings through the source invariant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_direct_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest : Pattern) (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some instruction) (direct : DirectInstruction instruction)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ ordinal next target trace captured,
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) = .ok (some next) ∧
      state? (patterns program) next = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
        (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured [] target := by
  obtain ⟨ordinal, row, selected, formed, _⟩ := whole_plan_instruction program prepared reference instruction built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨next, target, trace, captured, step, encoded, firing⟩ := direct_instruction_plan_step selected terms types declared direct formed resolved
  exact ⟨ordinal, next, target, trace, captured, step, encoded, firing⟩

theorem whole_variable_instruction (program : OCaml.Program) (prepared : Prepared) (reference index : Nat)
    (items : OCaml.Environment) (actual : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (.variable index)) (found : items[index]? = some actual)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ ordinal trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment items, encodedRest]) ordinal trace captured captured []
      (node "MlReturn" [value actual, encodedRest]) := by
  obtain ⟨ordinal, row, selected, formed, _⟩ := whole_plan_instruction program prepared reference (.variable index) built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  obtain ⟨_, trace, captured, firing⟩ := variable_plan_step selected terms types declared found formed resolved
  exact ⟨ordinal, trace, captured, firing⟩

theorem reachable_whole_direct_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some instruction) (direct : DirectInstruction instruction)
    (reachable : OCaml.MachinePath program (OCaml.begin program) (.evaluate reference capturedEnvironment rest)) :
    ∃ source ordinal next target trace captured,
      state? (patterns program) (.evaluate reference capturedEnvironment rest) = some source ∧
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) = .ok (some next) ∧
      state? (patterns program) next = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
        source ordinal trace captured captured [] target := by
  have covered := machine_path_covered program _ _ (initial_covered program) reachable
  obtain ⟨encodedRest, resolved⟩ := continuation?_exists (patterns program) rest covered
  obtain ⟨ordinal, next, target, trace, captured, step, encoded, firing⟩ :=
    whole_direct_instruction program prepared reference instruction capturedEnvironment rest encodedRest built complete declared direct resolved
  refine ⟨node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest], ordinal, next, target,
    trace, captured, ?_, step, encoded, firing⟩
  simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms whole_direct_instruction
#print axioms whole_variable_instruction
#print axioms reachable_whole_direct_instruction

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
