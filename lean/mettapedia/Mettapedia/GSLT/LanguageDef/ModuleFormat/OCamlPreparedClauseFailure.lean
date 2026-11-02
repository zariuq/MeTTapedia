import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlIndexedRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectionRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! A cached, independently authorized pattern failure advances the actual
ordered clause cursor. Later clauses, environment and continuation survive
the provider query unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem prepared_clause_failure_step_any_index (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat)
    (argument : OCaml.Value) (body : OCaml.Code) (clauses : List OCaml.Clause) (later : Pattern)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest])
      (node "MlSelect" [later, value argument, environment captured, encodedRest]) := by
  let authored := baseLanguage.rewrites[26]'(by decide +kernel)
  have atBase : baseLanguage.rewrites[26]? = some authored := List.getElem?_eq_getElem (by decide +kernel)
  have computed : (baseLanguage.rewrites[26]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlTryClause" [.fvar "pattern", .fvar "value", .fvar "body", .fvar "later", .fvar "environment", .fvar "rest"],
        node "MlSelect" [.fvar "later", .fvar "value", .fvar "environment", .fvar "rest"],
        [.relationQuery "ml-pattern-failure" [.fvar "pattern", .fvar "value"]]) := by decide +kernel
  rw [atBase] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premise := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premise
  let assignment : Bindings := [("pattern", patternId index), ("value", value argument), ("body", code body),
    ("later", later), ("environment", environment captured), ("rest", encodedRest)]
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have sourceTyped := clause_index_request_open _ grammar (epochPlan prepared table).snapshot.free (patterns program) index argument body clauses
    later clauseResolved captured rest encodedRest resolved
  have emptyTyped := clause_index_request_open baseLanguage rfl FreeTypeContext.empty (patterns program) index argument body clauses
    later clauseResolved captured rest encodedRest resolved
  have closed : (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest]).freeFvarNames = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name present
    obtain ⟨_, impossible⟩ := emptyTyped.1.freeType_of_mem_freeFvarNames_of_isObjectPattern emptyTyped.2.2.1 present
    cases impossible
  obtain ⟨rowIndex, present⟩ := List.mem_iff_getElem?.mp cached
  have signature : GeneralPremise.signature? table "ml-pattern-failure" 2 =
      some ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ := by
    unfold GeneralPremise.signature?
    rw [signatures]
    decide +kernel
  apply prepared_input_query_base_step program prepared table built signatures 26 authored atBase _ _ assignment
    "ml-pattern-failure" [.fvar "pattern", .fvar "value"] rowIndex
    ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ premise
  · rw [right, left]
    simp [node, Pattern.freeFvarNames]
  · intro schema member
    rcases List.mem_cons.mp member with rfl | member
    · exact .metavariable _
    · cases List.mem_singleton.mp member
      exact .metavariable _
  · rw [left]
    simp [node, Pattern.freeFvarNames]
  · exact closed
  · exact sourceTyped
  · exact select_request_open _ grammar _ (patterns program) clauses later argument captured rest encodedRest clauseResolved resolved
  · rw [left]
    simp [assignment, apply_node, applyBindings]
  · rw [right]
    simp [assignment, apply_node, applyBindings]
  · simpa [assignment, applyBindings, failureRow] using present
  · exact signature
  · rfl
  · simpa [assignment, applyBindings, failureRow] using
      GeneralPremise.checkRow_sound (failure_row_checked _ grammar (epochPlan prepared table).snapshot.free index argument)

theorem prepared_clause_failure_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (clauses : List OCaml.Clause) (later : Pattern)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (_referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest])
      (node "MlSelect" [later, value argument, environment captured, encodedRest]) :=
  prepared_clause_failure_step_any_index program prepared table index argument body clauses later captured rest encodedRest built signatures clauseResolved resolved cached

theorem prepared_authorized_clause_failure (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (clause : OCaml.Clause)
    (argument : OCaml.Value) (clauses : List OCaml.Clause) (later : Pattern) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (meaning : ProviderMeaning (patterns program) table)
    (indexed : (patterns program)[index]? = some clause.pattern)
    (referenced : patternReference? (patterns program) clause.pattern = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    OCaml.matchPattern clause.pattern argument = none ∧
    OCaml.selectClause (clause :: clauses) argument = OCaml.selectClause clauses argument ∧
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlTryClause" [patternId index, value argument, code clause.body, later, environment captured, encodedRest])
      (node "MlSelect" [later, value argument, environment captured, encodedRest]) := by
  have failed := meaning.2 index clause.pattern argument indexed cached
  refine ⟨failed, ?_, prepared_clause_failure_step program prepared table index clause.pattern argument clause.body clauses later
    captured rest encodedRest built signatures referenced clauseResolved resolved cached⟩
  simp only [OCaml.selectClause, failed]

#print axioms prepared_clause_failure_step
#print axioms prepared_clause_failure_step_any_index
#print axioms prepared_authorized_clause_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
