import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlWholeInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableSearch

/-! Complete prepared plans provide the actual lookup row; its native
publications are exactly indexed source lookup, with no target invention.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem whole_variable_exact (program : OCaml.Program) (prepared : Prepared) (reference index : Nat)
    (items : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (declared : program.instruction? reference = some (.variable index))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (plan prepared).rules[ordinal]? = some row ∧
      compileInstruction? (patterns program) reference (.variable index) = some row.authored ∧
      ∀ target, (∃ work firing, firing ∈ (Complete.DeepRoot.run
        ⟨GeneralPlanEnvironment.environment (plan prepared), [], .base "MlConfig",
          node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩ work
        (Complete.DeepRoot.start
          ⟨GeneralPlanEnvironment.environment (plan prepared), [], .base "MlConfig",
            node "MlEvaluate" [code reference, environment items, encodedRest], ordinal⟩)).publication ∧ firing.target = target) ↔
        ∃ actual, items[index]? = some actual ∧ target = node "MlReturn" [value actual, encodedRest] := by
  obtain ⟨ordinal, row, selected, formed, _⟩ :=
    whole_plan_instruction program prepared reference (.variable index) built declared complete
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  exact ⟨ordinal, row, selected, formed, fun _ => variable_search_iff selected terms types declared formed resolved⟩

#print axioms whole_variable_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
