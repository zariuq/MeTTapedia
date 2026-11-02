import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlIndexedRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedInputQueries
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! A cached failed source pattern authorizes the actual MatchOneFailure
query step to the language fault. The failed body is never entered.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem prepared_match_failure_step_any_index (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      (node "MlFault" [fault .matchFailure]) := by
  let authored := baseLanguage.rewrites[25]'(by decide +kernel)
  have atBase : baseLanguage.rewrites[25]? = some authored := List.getElem?_eq_getElem (by decide +kernel)
  have computed : (baseLanguage.rewrites[25]?).map (fun row => (row.left, row.right, row.premises)) =
      some (node "MlMatchOne" [.fvar "pattern", .fvar "value", .fvar "body", .fvar "environment", .fvar "rest"],
        node "MlFault" [fault .matchFailure],
        [.relationQuery "ml-pattern-failure" [.fvar "pattern", .fvar "value"]]) := by decide +kernel
  rw [atBase] at computed
  have fields := Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premise := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premise
  let assignment : Bindings := [("pattern", patternId index), ("value", value argument), ("body", code body),
    ("environment", environment captured), ("rest", encodedRest)]
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms :=
    (prepare_readback program prepared built).2.2.1
  have sourceTyped := match_index_request_open _ grammar (epochPlan prepared table).snapshot.free (patterns program) index argument body captured rest encodedRest resolved
  have emptyTyped := match_index_request_open baseLanguage rfl FreeTypeContext.empty (patterns program) index argument body captured rest encodedRest resolved
  have closed : (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]).freeFvarNames = [] := by
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
  apply prepared_input_query_base_step program prepared table built signatures 25 authored atBase _ _ assignment
    "ml-pattern-failure" [.fvar "pattern", .fvar "value"] rowIndex
    ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ premise
  · rw [right, left]
    simp [node, fault, Pattern.freeFvarNames]
  · intro schema member
    rcases List.mem_cons.mp member with rfl | member
    · exact .metavariable _
    · cases List.mem_singleton.mp member
      exact .metavariable _
  · rw [left]
    simp [node, Pattern.freeFvarNames]
  · exact closed
  · exact sourceTyped
  · exact state?_open _ grammar _ [] (patterns program) (.halted (.error .matchFailure)) _ rfl
  · rw [left]
    simp [assignment, apply_node, applyBindings]
  · rw [right]
    simp only [fault, apply_node, List.map_cons, List.map_nil]
  · simpa [assignment, applyBindings, failureRow] using present
  · exact signature
  · rfl
  · simpa [assignment, applyBindings, failureRow] using
      GeneralPremise.checkRow_sound (failure_row_checked _ grammar (epochPlan prepared table).snapshot.free index argument)

theorem prepared_match_failure_step (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (_referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      (node "MlFault" [fault .matchFailure]) :=
  prepared_match_failure_step_any_index program prepared table index argument body captured rest encodedRest built signatures resolved cached

theorem prepared_authorized_match_failure (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern)
    (argument : OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (meaning : ProviderMeaning (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (cached : failureRow index argument ∈ table.rows) :
    OCaml.enterBody parameter argument body captured rest = .halted (.error .matchFailure) ∧
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest])
      (node "MlFault" [fault .matchFailure]) :=
  ⟨cached_failure_authorized (patterns program) table index parameter argument body captured rest meaning.2 indexed cached,
    prepared_match_failure_step program prepared table index parameter argument body captured rest encodedRest
      built signatures referenced resolved cached⟩

#print axioms prepared_match_failure_step
#print axioms prepared_match_failure_step_any_index
#print axioms prepared_authorized_match_failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
