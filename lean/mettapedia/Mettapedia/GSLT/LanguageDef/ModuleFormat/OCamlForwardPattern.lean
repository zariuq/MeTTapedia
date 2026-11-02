import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternControlStep

/-! Successful pattern and clause requests enable their actual prepared row
at the retained pool occurrence, including repeated identical patterns.
No first-occurrence lookup premise replaces that occurrence identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_match_success_step_any_index (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern) (bindings : List OCaml.Value)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some parameter) (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      (node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedRest]) := by
  obtain ⟨assignment, input, output⟩ := match_one_rule_complete parameter index argument bindings body captured encodedRest matched
  have sourcePoint : ControlPoint program (OCaml.enterBody parameter argument body captured rest)
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) 1 := .matchOne indexed resolved
  have targetPoint : ControlPoint program (.evaluate body (OCaml.extend captured bindings) rest)
      (node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedRest]) 0 :=
    .state (by simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
  exact prepared_pattern_control_step program prepared table index parameter _ assignment built signatures indexed
    (List.getElem_mem _) sourcePoint targetPoint input output

theorem prepared_clause_success_step_any_index (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (clause : OCaml.Clause) (clauses : List OCaml.Clause) (later : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (bindings : List OCaml.Value) (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some clause.pattern) (listed : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern clause.pattern argument = some bindings) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
      (node "MlEvaluate" [code clause.body, environment (OCaml.extend captured bindings), encodedRest]) := by
  obtain ⟨assignment, input, output⟩ := try_clause_rule_complete clause.pattern index argument bindings clause.body later captured encodedRest matched
  have selected : OCaml.returnValue program argument (.matchValue (clause :: clauses) captured :: rest) =
      .ok (.evaluate clause.body (OCaml.extend captured bindings) rest) := by
    simp only [OCaml.returnValue, OCaml.selectClause, matched]
    rfl
  have sourcePoint : ControlPoint program (.evaluate clause.body (OCaml.extend captured bindings) rest)
      (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
      (2 * clauses.length + 2) := .clause indexed listed resolved selected
  have targetPoint : ControlPoint program (.evaluate clause.body (OCaml.extend captured bindings) rest)
      (node "MlEvaluate" [code clause.body, environment (OCaml.extend captured bindings), encodedRest]) 0 :=
    .state (by simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
  exact prepared_pattern_control_step program prepared table index clause.pattern _ assignment built signatures indexed
    (List.getElem_mem _) sourcePoint targetPoint input output

#print axioms prepared_match_success_step_any_index
#print axioms prepared_clause_success_step_any_index

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
