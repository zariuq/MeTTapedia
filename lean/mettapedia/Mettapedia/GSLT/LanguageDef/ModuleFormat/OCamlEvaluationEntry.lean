import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionFiringReadout
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlArgumentReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint

/-! Direct and argument-building instructions enter the control-point relation.
The source machine step remains independent of the emitted rule instance;
nullary construction retains its pending administrative build phase.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem direct_evaluation_entry {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (sourceEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (formed : compileInstruction? (patterns program) reference instruction = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (direct : DirectInstruction instruction) (declared : program.instruction? reference = some instruction)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (sourceStep : OCaml.machineStep program (.evaluate reference sourceEnvironment rest) = .ok (some next))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment sourceEnvironment, encodedRest]) ordinal trace captured completed history target) :
    ControlPoint program next target 0 := by
  obtain ⟨actual, expected, step, encoded, result⟩ :=
    direct_instruction_source program reference instruction sourceEnvironment rest encodedRest direct declared resolved
  have sameSource : actual = next := Option.some.inj (Except.ok.inj (step.symm.trans sourceStep))
  subst actual
  have input : applyBindings (instructionBindings (environment sourceEnvironment) encodedRest) row.authored.left =
      node "MlEvaluate" [code reference, environment sourceEnvironment, encodedRest] := by
    rw [direct_instruction_left (patterns program) reference instruction row.authored direct formed]
    simp only [apply_node, List.map_cons, List.map_nil, apply_code, apply_environment_hole, apply_continuation_hole]
  have same := instruction_firing_target position formed zero input (instruction_result_instantiated formed result) firing
  rw [same]
  exact .state encoded

theorem build_evaluation_entry {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} (program : OCaml.Program)
    (reference : OCaml.Code) (kind : OCaml.Build) (arguments : List OCaml.Code) (sourceEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest target : Pattern) (next : OCaml.MachineState)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (formed : compileInstruction? (patterns program) reference (buildInstruction kind arguments) = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (declared : program.instruction? reference = some (buildInstruction kind arguments))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (sourceStep : OCaml.machineStep program (.evaluate reference sourceEnvironment rest) = .ok (some next))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, environment sourceEnvironment, encodedRest]) ordinal trace captured completed history target) :
    ∃ rank, ControlPoint program next target rank := by
  obtain ⟨_, _, input, output⟩ := instruction_firing_readout position formed zero firing
  have same : target = startArguments (build kind) arguments (environment sourceEnvironment) encodedRest :=
    output.symm.trans (build_instruction_readback (patterns program) reference kind arguments row.authored
      (GeneralFirstOrderProjection.ordinary captured) (environment sourceEnvironment) encodedRest formed input)
  rw [same]
  have source : OCaml.startArguments program kind arguments sourceEnvironment rest = .ok next := by
    have evaluate : OCaml.evaluateInstruction program reference sourceEnvironment rest =
        OCaml.startArguments program kind arguments sourceEnvironment rest := by
      cases kind <;> simp only [OCaml.evaluateInstruction, declared, buildInstruction]
    simp only [OCaml.machineStep, evaluate] at sourceStep
    cases stepped : OCaml.startArguments program kind arguments sourceEnvironment rest <;>
      simp_all only [Except.map, Except.ok.injEq, Option.some.injEq, reduceCtorEq]
  cases reversed : arguments.reverse with
  | nil =>
    have empty : arguments = [] := List.reverse_eq_nil_iff.mp reversed
    subst arguments
    have finished : OCaml.finishBuild program kind [] rest = .ok next := source
    exact ⟨3, .build resolved finished⟩
  | cons last later =>
    have actual : next = .evaluate last sourceEnvironment (.gather kind later sourceEnvironment [] :: rest) := by
      simp only [OCaml.startArguments, reversed, Except.ok.injEq] at source
      exact source.symm
    rw [actual]
    exact ⟨0, .state (start_arguments_nonempty_encoding (patterns program) kind arguments last later
      sourceEnvironment rest encodedRest reversed resolved)⟩

#print axioms direct_evaluation_entry
#print axioms build_evaluation_entry

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
