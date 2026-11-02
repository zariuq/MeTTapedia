import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEmptyArgumentCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSourceEntry
import Mettapedia.OSLF.MeTTaIL.GeneralRootStep

/-! Every successful independent source evaluation step has an actual prepared
GSLT successor. Instruction selection and admission follow from preparation;
variable lookup, direct instructions and empty/nonempty builders are covered.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

private theorem build_entry_can_fire {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    (program : OCaml.Program) (reference : OCaml.Code) (kind : OCaml.Build) (arguments : List OCaml.Code)
    (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms) (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (formed : compileInstruction? (patterns program) reference (buildInstruction kind arguments) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ target trace captured, GeneralPremise.RootFiring
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured [] target := by
  cases reversed : arguments.reverse with
  | nil =>
    have empty := List.reverse_eq_nil_iff.mp reversed
    subst arguments
    obtain ⟨trace, captured, firing⟩ := empty_build_instruction_plan_step (capturedEnvironment := capturedEnvironment) position terms types formed resolved
    exact ⟨_, trace, captured, firing⟩
  | cons last later =>
    obtain ⟨trace, captured, firing⟩ := build_instruction_plan_step (program := program) (capturedEnvironment := capturedEnvironment) position terms types reversed formed resolved
    exact ⟨_, trace, captured, firing⟩

theorem prepared_evaluation_can_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (reference : OCaml.Code) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (encodedRest : Pattern) (next : OCaml.MachineState)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (sourceStep : OCaml.machineStep program (.evaluate reference capturedEnvironment rest) = .ok (some next)) :
    ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) target := by
  cases declared : program.instruction? reference with
  | none => simp [OCaml.machineStep, OCaml.evaluateInstruction, declared, Except.map] at sourceStep
  | some instruction =>
    obtain ⟨ordinal, row, selected, formed, _⟩ := whole_plan_instruction program prepared reference instruction built declared
      (prepared_plan_complete program prepared built)
    have position : (epochPlan prepared table).rules[ordinal]? = some row := by
      rw [epoch_rules prepared table signatures]
      exact selected
    obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
    have possible : ∃ target trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
        (node "MlEvaluate" [code reference, environment capturedEnvironment, encodedRest]) ordinal trace captured captured [] target := by
      cases instruction with
      | «variable» index =>
        cases found : capturedEnvironment[index]? with
        | none => simp [OCaml.machineStep, OCaml.evaluateInstruction, declared, found, Except.map] at sourceStep
        | some actual =>
          obtain ⟨_, trace, captured, firing⟩ := variable_plan_step position terms types declared found formed resolved
          exact ⟨_, trace, captured, firing⟩
      | tuple fields =>
        exact build_entry_can_fire program reference .tuple fields capturedEnvironment rest encodedRest
          position terms types formed resolved
      | variant typeId constructor fields =>
        exact build_entry_can_fire program reference (.variant typeId constructor) fields capturedEnvironment rest encodedRest
          position terms types formed resolved
      | primitive operator arguments =>
        exact build_entry_can_fire program reference (.primitive operator) arguments capturedEnvironment rest encodedRest
          position terms types formed resolved
      | _ =>
        obtain ⟨_, target, trace, captured, _, _, firing⟩ := direct_instruction_plan_step position terms types declared (by trivial) formed resolved
        exact ⟨target, trace, captured, firing⟩
    obtain ⟨target, _, _, firing⟩ := possible
    exact ⟨target, GeneralOccurrenceSemantics.root_firing_semantic_step rfl firing⟩

#print axioms prepared_evaluation_can_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
