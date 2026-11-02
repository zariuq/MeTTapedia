import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedBaseSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectionRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClauseDispatch

/-! Actual prepared GSLT steps enter an ordered clause list, test its
first clause and fault at its empty boundary. Skipping a failed clause
remains an explicit provider-authorized step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_return_match_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKMatch" [encodedClauses, environment captured, encodedRest]])
      (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.returned argument (.matchValue clauses captured :: rest)) =
      some (node "MlReturn" [value argument, node "MlKMatch" [encodedClauses, environment captured, encodedRest]]) := by
    simp only [state?, continuation?, frame?, clauseResolved, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 22
    (baseLanguage.rewrites[22]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact state?_closed _ _ _ encoded
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact select_request_open _ grammar _ (patterns program) clauses encodedClauses argument captured rest encodedRest clauseResolved resolved
  · exact return_match_instance (value argument) encodedClauses (environment captured) encodedRest

theorem prepared_select_empty_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (argument : OCaml.Value) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlSelect" [node "MlClauseNil", value argument, environment captured, encodedRest])
      (node "MlFault" [fault .matchFailure]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have encoded : state? (patterns program) (.halted (.error .matchFailure)) = some (node "MlFault" [fault .matchFailure]) := rfl
  apply prepared_pure_base_step program prepared table built signatures 23
    (baseLanguage.rewrites[23]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact select_request_closed (patterns program) [] _ argument captured rest encodedRest (clauseList?_nil _) resolved
  · exact select_request_open _ grammar _ (patterns program) [] _ argument captured rest encodedRest (clauseList?_nil _) resolved
  · exact state?_open _ grammar _ [] _ _ _ encoded
  · exact select_empty_instance (value argument) (environment captured) encodedRest

theorem prepared_select_first_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clause : OCaml.Clause) (clauses : List OCaml.Clause)
    (patternCode later : Pattern) (argument : OCaml.Value) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (referenced : patternReference? (patterns program) clause.pattern = some patternCode)
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlSelect" [node "MlClauseCons" [patternCode, code clause.body, later], value argument, environment captured, encodedRest])
      (node "MlTryClause" [patternCode, value argument, code clause.body, later, environment captured, encodedRest]) := by
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have listed : clauseList? (patterns program) (clause :: clauses) = some (node "MlClauseCons" [patternCode, code clause.body, later]) := by
    rw [clauseList?_cons]
    simp only [referenced, clauseResolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  apply prepared_pure_base_step program prepared table built signatures 24
    (baseLanguage.rewrites[24]'(by decide +kernel)) (by exact List.getElem?_eq_getElem (by decide +kernel))
  · exact select_request_closed (patterns program) (clause :: clauses) _ argument captured rest encodedRest listed resolved
  · exact select_request_open _ grammar _ (patterns program) (clause :: clauses) _ argument captured rest encodedRest listed resolved
  · exact clause_request_open _ grammar _ referenced argument clause.body clauses later clauseResolved captured rest encodedRest resolved
  · exact select_clause_instance patternCode (code clause.body) later (value argument) (environment captured) encodedRest

#print axioms prepared_return_match_step
#print axioms prepared_select_empty_step
#print axioms prepared_select_first_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
