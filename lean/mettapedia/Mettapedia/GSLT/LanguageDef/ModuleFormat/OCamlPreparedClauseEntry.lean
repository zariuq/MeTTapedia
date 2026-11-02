import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClausePlanCoverage

/-! A selected clause-entry publication is exactly a successful match of
that source clause. Its later-clause cursor, bindings and continuation are
read from the actual prepared row and provider epoch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_clause_entry_exact (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment)
    (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (epochPlan prepared table).rules[ordinal]? = some row ∧
      row.authored = (patternRules index parameter)[1]'(by simp [patternRules]) ∧
      ∀ target, (∃ trace assignment completed history,
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
          (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest])
          ordinal trace assignment completed history target) ↔
        ∃ bindings, OCaml.matchPattern parameter argument = some bindings ∧
          target = node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedRest] := by
  obtain ⟨ordinal, row, selected, same⟩ := epoch_pattern_row program prepared table index parameter
    ((patternRules index parameter)[1]'(by simp [patternRules])) built (prepared_plan_complete program prepared built)
    signatures indexed (List.getElem_mem _)
  obtain ⟨_, _, terms, types, _⟩ := prepare_readback program prepared built
  exact ⟨ordinal, row, selected, same, fun _ => try_clause_plan_iff selected terms types same referenced clauseResolved resolved⟩

theorem prepared_failed_clause_has_no_positive_entry (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment)
    (clauses : List OCaml.Clause) (later : Pattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (failed : OCaml.matchPattern parameter argument = none) :
    ∃ (ordinal : Nat) (row : GeneralExecutionAdmission.RulePlan), (epochPlan prepared table).rules[ordinal]? = some row ∧
      row.authored = (patternRules index parameter)[1]'(by simp [patternRules]) ∧
      ¬ ∃ target trace assignment completed history,
        GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
          (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest])
          ordinal trace assignment completed history target := by
  obtain ⟨ordinal, row, selected, same, actual⟩ := prepared_clause_entry_exact program prepared table index parameter
    argument body captured clauses later rest encodedRest built signatures indexed referenced clauseResolved resolved
  refine ⟨ordinal, row, selected, same, ?_⟩
  rintro ⟨target, trace, assignment, completed, history, firing⟩
  obtain ⟨bindings, matched, _⟩ := (actual target).mp ⟨trace, assignment, completed, history, firing⟩
  rw [failed] at matched
  cases matched

#print axioms prepared_clause_entry_exact
#print axioms prepared_failed_clause_has_no_positive_entry

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
