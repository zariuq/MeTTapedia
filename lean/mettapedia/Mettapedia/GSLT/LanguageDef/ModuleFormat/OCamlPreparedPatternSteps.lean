import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage

/-! Exact positive pattern entry in every prepared provider epoch. The
source program supplies its own actual selected row and admission proof;
every publication recovers the source bindings and full continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_pattern_entry_exact (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (epochPlan prepared table).rules[ordinal]? = some row ∧
      row.authored = (patternRules index parameter)[0]'(by simp [patternRules]) ∧
      ∀ target, (∃ trace captured completed history,
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
          (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
          ordinal trace captured completed history target) ↔
        ∃ bindings, OCaml.matchPattern parameter argument = some bindings ∧
          target = node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment bindings), encodedRest] := by
  obtain ⟨ordinal, row, selected, same⟩ := epoch_pattern_row program prepared table index parameter
    ((patternRules index parameter)[0]'(by simp [patternRules])) built (prepared_plan_complete program prepared built)
    signatures indexed (List.getElem_mem _)
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  exact ⟨ordinal, row, selected, same, fun _ => match_one_plan_iff selected terms types same referenced resolved⟩

theorem prepared_pattern_failure_no_positive_firing (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (capturedEnvironment : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (failed : OCaml.matchPattern parameter argument = none) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (epochPlan prepared table).rules[ordinal]? = some row ∧
      row.authored = (patternRules index parameter)[0]'(by simp [patternRules]) ∧
      ¬ ∃ target trace captured completed history,
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
          (node "MlMatchOne" [patternId index, value argument, code body, environment capturedEnvironment, encodedRest])
          ordinal trace captured completed history target := by
  obtain ⟨ordinal, row, selected, same, exactTarget⟩ := prepared_pattern_entry_exact program prepared table index parameter
    argument body capturedEnvironment rest encodedRest built signatures indexed referenced resolved
  refine ⟨ordinal, row, selected, same, ?_⟩
  rintro ⟨target, trace, captured, completed, history, firing⟩
  obtain ⟨bindings, matched, _⟩ := (exactTarget target).mp ⟨trace, captured, completed, history, firing⟩
  rw [failed] at matched
  cases matched

#print axioms prepared_pattern_entry_exact
#print axioms prepared_pattern_failure_no_positive_firing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
