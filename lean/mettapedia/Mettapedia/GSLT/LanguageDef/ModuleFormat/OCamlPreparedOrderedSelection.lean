import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedClauseFailure
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedSelectionPaths

/-! Ordered selection reaches exactly the source's first successful
clause, once the source-authorized failure answers for preceding clauses
are available. This composes actual prepared cursor/query/pattern steps;
it does not replace service installation or whole-controller iteration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem clause_list_cons_readback {pool : List OCaml.MatchPattern} {clause : OCaml.Clause}
    {clauses : List OCaml.Clause} {encoded : Pattern}
    (resolved : clauseList? pool (clause :: clauses) = some encoded) :
    ∃ index later, patternReference? pool clause.pattern = some (patternId index) ∧
      pool[index]? = some clause.pattern ∧ clauseList? pool clauses = some later ∧
      encoded = node "MlClauseCons" [patternId index, code clause.body, later] := by
  rw [clauseList?_cons] at resolved
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at resolved
  obtain ⟨patternCode, referenced, later, rest, same⟩ := resolved
  obtain ⟨index, found, rfl⟩ := Option.map_eq_some_iff.mp referenced
  exact ⟨index, later, by simp only [patternReference?, found, Option.map_some],
    OCaml.patternIndex?_sound clause.pattern pool index found, rest, same.symm⟩

theorem prepared_select_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (body : OCaml.Code) (bindings : List OCaml.Value) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : ∀ clause ∈ clauses, ∀ index,
      patternReference? (patterns program) clause.pattern = some (patternId index) →
      OCaml.matchPattern clause.pattern argument = none → failureRow index argument ∈ table.rows)
    (selected : OCaml.selectClause clauses argument = some (body, bindings)) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest])
      (node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedRest]) := by
  induction clauses generalizing encodedClauses with
  | nil => simp only [OCaml.selectClause] at selected; cases selected
  | cons clause clauses ih =>
    obtain ⟨index, later, referenced, indexed, laterResolved, same⟩ := clause_list_cons_readback clauseResolved
    subst encodedClauses
    have begin := prepared_select_first_step program prepared table clause clauses (patternId index) later argument captured rest
      encodedRest built signatures referenced laterResolved resolved
    cases matched : OCaml.matchPattern clause.pattern argument with
    | some actualBindings =>
      have same : (clause.body, actualBindings) = (body, bindings) := by
        exact Option.some.inj (by simpa only [OCaml.selectClause, matched] using selected)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      have entry := epoch_clause_success_step program prepared table index clause.pattern argument actualBindings clause.body captured clauses
        later rest encodedRest built (prepared_plan_complete program prepared built) signatures indexed referenced laterResolved resolved matched
      exact (Relation.ReflTransGen.single begin).trans (Relation.ReflTransGen.single entry)
    | none =>
      have skip := prepared_clause_failure_step program prepared table index clause.pattern argument clause.body clauses later captured
        rest encodedRest built signatures referenced laterResolved resolved (cached clause List.mem_cons_self index referenced matched)
      have tail := ih later laterResolved
        (fun next member => cached next (List.mem_cons_of_mem _ member))
        (by simpa only [OCaml.selectClause, matched] using selected)
      exact (Relation.ReflTransGen.single begin).trans ((Relation.ReflTransGen.single skip).trans tail)

theorem prepared_ordered_match_success_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (body : OCaml.Code) (bindings : List OCaml.Value) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : ∀ clause ∈ clauses, ∀ index,
      patternReference? (patterns program) clause.pattern = some (patternId index) →
      OCaml.matchPattern clause.pattern argument = none → failureRow index argument ∈ table.rows)
    (selected : OCaml.selectClause clauses argument = some (body, bindings)) :
    OCaml.machineStep program (.returned argument (.matchValue clauses captured :: rest)) =
      .ok (some (.evaluate body (OCaml.extend captured bindings) rest)) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKMatch" [encodedClauses, environment captured, encodedRest]])
      (node "MlEvaluate" [code body, environment (OCaml.extend captured bindings), encodedRest]) := by
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue, selected]
    rfl
  · exact (Relation.ReflTransGen.single (prepared_return_match_step program prepared table clauses encodedClauses argument captured
      rest encodedRest built signatures clauseResolved resolved)).trans
      (prepared_select_success_path program prepared table clauses encodedClauses argument body bindings captured rest encodedRest
        built signatures clauseResolved resolved cached selected)

#print axioms clause_list_cons_readback
#print axioms prepared_select_success_path
#print axioms prepared_ordered_match_success_path

theorem prepared_select_failure_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : ∀ clause ∈ clauses, ∀ index,
      patternReference? (patterns program) clause.pattern = some (patternId index) →
      OCaml.matchPattern clause.pattern argument = none → failureRow index argument ∈ table.rows)
    (failed : OCaml.selectClause clauses argument = none) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest])
      (node "MlFault" [fault .matchFailure]) := by
  induction clauses generalizing encodedClauses with
  | nil =>
    have same : encodedClauses = node "MlClauseNil" := Option.some.inj ((clauseList?_nil _).symm.trans clauseResolved) |>.symm
    subst encodedClauses
    exact .single (prepared_select_empty_step program prepared table argument captured rest encodedRest built signatures resolved)
  | cons clause clauses ih =>
    obtain ⟨index, later, referenced, _, laterResolved, same⟩ := clause_list_cons_readback clauseResolved
    subst encodedClauses
    cases matched : OCaml.matchPattern clause.pattern argument with
    | some bindings => simp only [OCaml.selectClause, matched] at failed; cases failed
    | none =>
      have begin := prepared_select_first_step program prepared table clause clauses (patternId index) later argument captured rest
        encodedRest built signatures referenced laterResolved resolved
      have skip := prepared_clause_failure_step program prepared table index clause.pattern argument clause.body clauses later captured
        rest encodedRest built signatures referenced laterResolved resolved (cached clause List.mem_cons_self index referenced matched)
      have tail := ih later laterResolved
        (fun next member => cached next (List.mem_cons_of_mem _ member))
        (by simpa only [OCaml.selectClause, matched] using failed)
      exact (Relation.ReflTransGen.single begin).trans ((Relation.ReflTransGen.single skip).trans tail)

theorem prepared_ordered_match_failure_path (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some encodedClauses)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : ∀ clause ∈ clauses, ∀ index,
      patternReference? (patterns program) clause.pattern = some (patternId index) →
      OCaml.matchPattern clause.pattern argument = none → failureRow index argument ∈ table.rows)
    (failed : OCaml.selectClause clauses argument = none) :
    OCaml.machineStep program (.returned argument (.matchValue clauses captured :: rest)) =
      .ok (some (.halted (.error .matchFailure))) ∧
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlReturn" [value argument, node "MlKMatch" [encodedClauses, environment captured, encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  constructor
  · simp only [OCaml.machineStep, OCaml.returnValue, failed]
    rfl
  · exact (Relation.ReflTransGen.single (prepared_return_match_step program prepared table clauses encodedClauses argument captured
      rest encodedRest built signatures clauseResolved resolved)).trans
      (prepared_select_failure_path program prepared table clauses encodedClauses argument captured rest encodedRest
        built signatures clauseResolved resolved cached failed)

#print axioms prepared_select_failure_path
#print axioms prepared_ordered_match_failure_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
