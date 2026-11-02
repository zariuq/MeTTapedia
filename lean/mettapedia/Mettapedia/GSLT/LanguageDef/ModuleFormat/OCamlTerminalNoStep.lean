import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledRowOrigin

/-! Encoded source values and faults admit no further prepared firing,
including through equation-saturated or canonically committed execution.
This conclusion uses the actual compiled declarations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem prepared_terminal_no_firing (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (result : OCaml.Result) (config : Pattern)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (encoded : state? (patterns program) (.halted result) = some config) :
    ¬ GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      config ordinal trace captured completed history target := by
  intro firing
  cases result with
  | ok actual =>
    have same : config = node "MlDone" [value actual] := Option.some.inj encoded.symm
    subst config
    rcases enabled_prepared_row_origin program prepared table "MlDone" _ built position firing with
      ⟨index, _, member⟩ | instruction | function | pattern | clause
    · have empty : kernelCandidates "MlDone" = [] := by decide +kernel
      rw [empty] at member
      cases member
    · simp at instruction
    · simp at function
    · simp at pattern
    · simp at clause
  | error error =>
    have same : config = node "MlFault" [fault error] := Option.some.inj encoded.symm
    subst config
    rcases enabled_prepared_row_origin program prepared table "MlFault" _ built position firing with
      ⟨index, _, member⟩ | instruction | function | pattern | clause
    · have empty : kernelCandidates "MlFault" = [] := by decide +kernel
      rw [empty] at member
      cases member
    · simp at instruction
    · simp at function
    · simp at pattern
    · simp at clause

theorem prepared_terminal_no_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (result : OCaml.Result) (config target : Pattern)
    (built : prepare program = .ok prepared) (encoded : state? (patterns program) (.halted result) = some config) :
    ¬ (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step config target := by
  intro step
  obtain ⟨receipt, valid, same⟩ := Complete.Run.valid_of_step (epochPlan prepared table) [] (.base "MlConfig")
    (epoch_compiled_equations_empty program prepared table built) step
  obtain ⟨position, firing⟩ := GeneralRuleJobs.rootOnly_receipt (plan := epochPlan prepared table) rfl valid
  exact prepared_terminal_no_firing program prepared table result config built position encoded firing

theorem prepared_terminal_no_normalized_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (result : OCaml.Result) (config target : Pattern)
    (built : prepare program = .ok prepared) (encoded : state? (patterns program) (.halted result) = some config) :
    ¬ Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target := by
  rintro ⟨raw, step, _⟩
  exact prepared_terminal_no_step program prepared table result config raw built encoded step

#print axioms prepared_terminal_no_firing
#print axioms prepared_terminal_no_step
#print axioms prepared_terminal_no_normalized_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
