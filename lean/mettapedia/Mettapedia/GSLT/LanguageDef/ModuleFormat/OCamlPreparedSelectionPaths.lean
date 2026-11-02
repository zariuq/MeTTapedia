import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSelectionSteps
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochClauseAuthorization

/-! Ordered first-clause success and the empty-match fault compose through
the actual selection cursor. Later clauses are retained as source data;
failure-based skipping remains separately authorized by provider evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_first_clause_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clause : OCaml.Clause) (clauses : List OCaml.Clause)
    (index : Nat) (later : Pattern) (argument : OCaml.Value) (bindings : List OCaml.Value)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (indexed : (patterns program)[index]? = some clause.pattern)
    (referenced : patternReference? (patterns program) clause.pattern = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (matched : OCaml.matchPattern clause.pattern argument = some bindings) :
    OCaml.machineStep program (.returned argument (.matchValue (clause :: clauses) captured :: rest)) =
      .ok (some (.evaluate clause.body (OCaml.extend captured bindings) rest)) ∧
    state? (patterns program) (.evaluate clause.body (OCaml.extend captured bindings) rest) =
      some (node "MlEvaluate" [code clause.body, environment (OCaml.extend captured bindings), encodedRest]) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKMatch" [node "MlClauseCons" [patternId index, code clause.body, later],
        environment captured, encodedRest]])
      (node "MlEvaluate" [code clause.body, environment (OCaml.extend captured bindings), encodedRest]) := by
  have listed : clauseList? (patterns program) (clause :: clauses) = some (node "MlClauseCons" [patternId index, code clause.body, later]) := by
    rw [clauseList?_cons]
    simp only [referenced, clauseResolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  refine ⟨?_, ?_, ?_⟩
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.selectClause, matched]
    rfl
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · have entered := prepared_return_match_step program prepared table (clause :: clauses) _ argument captured rest encodedRest
      built signatures listed resolved
    have selected := prepared_select_first_step program prepared table clause clauses (patternId index) later argument captured rest
      encodedRest built signatures referenced clauseResolved resolved
    have finished := epoch_clause_success_step program prepared table index clause.pattern argument bindings clause.body captured clauses
      later rest encodedRest built (prepared_plan_complete program prepared built) signatures indexed referenced clauseResolved resolved matched
    exact (Relation.ReflTransGen.single entered).trans
      ((Relation.ReflTransGen.single selected).trans (Relation.ReflTransGen.single finished))

theorem prepared_empty_match_fault_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (argument : OCaml.Value) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.returned argument (.matchValue [] captured :: rest)) = .ok (some (.halted (.error .matchFailure))) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKMatch" [node "MlClauseNil", environment captured, encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  constructor
  · simp [OCaml.machineStep, OCaml.returnValue, OCaml.selectClause]
    rfl
  · exact (Relation.ReflTransGen.single (prepared_return_match_step program prepared table [] _ argument captured rest encodedRest
      built signatures (clauseList?_nil _) resolved)).trans
      (Relation.ReflTransGen.single (prepared_select_empty_step program prepared table argument captured rest encodedRest built signatures resolved))

#print axioms prepared_first_clause_success_path
#print axioms prepared_empty_match_fault_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
