import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeVariableExact

/-! Prepared source programs supply their own admission evidence to
provider replacement and actual shared matcher execution. No caller needs
to assert plan completeness at these source-facing entries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_epoch_complete (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    (epochPlan prepared table).complete = true :=
  epoch_complete prepared table signatures (prepared_plan_complete program prepared built) closed

theorem prepared_initial_epoch_complete (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) : (epochPlan prepared provider).complete = true :=
  prepared_epoch_complete program prepared provider built rfl (initial_provider_checked prepared)

theorem prepared_failure_append_complete (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (argument : OCaml.Value)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    (epochPlan prepared (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument])).complete = true :=
  epoch_failure_append_complete program prepared table index argument built signatures (prepared_plan_complete program prepared built) closed

theorem prepared_reachable_direct_instruction (program : OCaml.Program) (prepared : Prepared) (reference : OCaml.Code)
    (instruction : OCaml.Instruction) (capturedEnvironment : OCaml.Environment) (rest : OCaml.Continuation)
    (built : prepare program = .ok prepared) (declared : program.instruction? reference = some instruction)
    (direct : DirectInstruction instruction)
    (reachable : OCaml.MachinePath program (OCaml.begin program) (.evaluate reference capturedEnvironment rest)) :
    ∃ source ordinal next target trace captured,
      state? (patterns program) (.evaluate reference capturedEnvironment rest) = some source ∧
      OCaml.machineStep program (.evaluate reference capturedEnvironment rest) = .ok (some next) ∧
      state? (patterns program) next = some target ∧
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (plan prepared)) [] (.base "MlConfig")
        source ordinal trace captured captured [] target :=
  reachable_whole_direct_instruction program prepared reference instruction capturedEnvironment rest built
    (prepared_plan_complete program prepared built) declared direct reachable

theorem prepared_variable_exact (program : OCaml.Program) (prepared : Prepared) (reference index : Nat)
    (items : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (declared : program.instruction? reference = some (.variable index))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧
      compileInstruction? (patterns program) reference (.variable index) = some row.authored ∧
      ∀ target, (∃ work firing, firing ∈ (Complete.DeepRoot.run
        ⟨GeneralPlanEnvironment.environment (plan prepared), [], .base "MlConfig",
          node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩ work
        (Complete.DeepRoot.start
          ⟨GeneralPlanEnvironment.environment (plan prepared), [], .base "MlConfig",
            node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩)).publication ∧ firing.target = target) ↔
        ∃ actual, items[index]? = some actual ∧ target = node "MlReturn" [value actual, encodedRest] :=
  whole_variable_exact program prepared reference index items rest encodedRest built
    (prepared_plan_complete program prepared built) declared resolved

#print axioms prepared_epoch_complete
#print axioms prepared_initial_epoch_complete
#print axioms prepared_failure_append_complete
#print axioms prepared_reachable_direct_instruction
#print axioms prepared_variable_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
