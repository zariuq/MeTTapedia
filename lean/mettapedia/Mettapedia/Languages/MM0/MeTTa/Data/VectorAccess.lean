import Mettapedia.Languages.MM0.MeTTa.Data.ListAccess

/-!
# Saved-vector reads in the retained MM0 source

The declared prefix bounds a read. Inside that prefix the native query must
return exactly one occurrence: missing and duplicate rows are malformed.
These theorems execute the pinned vector branch and expose its current store
reading. Relating those readings to checked proof conclusions additionally
requires the vector's scope and publication invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.VectorAccess

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Store (natural indexedQuery)

def vectorValue (handle : Handle) (size : Nat) : Atom :=
  .expression [.symbol "MM0:Vector", handleValue handle, natural size]

/-- Observation of a native query, retaining multiplicity. -/
def queryAnswer : List Atom → Atom
  | [value] => ListAccess.optionValue (some value)
  | _ => .symbol "MM0:Malformed"

private def environment (handle : Handle) (size index : Nat) : Subst :=
  [("index", natural index), ("items", vectorValue handle size)]

private def vectorEnvironment (handle : Handle) (size index : Nat) : Subst :=
  ("size", natural size) :: ("space", handleValue handle) :: environment handle size index

theorem vector_clause (handle : Handle) (size index : Nat) :
    clauses program "mm0:data-at" [vectorValue handle size, natural index] =
      [.evaluate (environment handle size index) dataAtEquation.body] := by
  rw [clauses_use_only_the_named_equations, data_at_equation_is_unique]
  simp [data_at_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private def cases : SpaceSemantics.Cases :=
  match dataAtEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def vectorBody : Atom := (cases[1]'(by decide)).2

private def listBody : Atom := (cases[0]'(by decide)).2

private def foundBody : Atom :=
  match vectorBody with
  | .expression [_, _, .expression [_, _, _, body], _] => body
  | _ => .expression []

private def foundCases : SpaceSemantics.Cases :=
  match foundBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private theorem body_is_case :
    dataAtEquation.body = .expression [.symbol "case", .var "items",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:L", .var "values"], listBody),
      (.expression [.symbol "MM0:Vector", .var "space", .var "size"], vectorBody)] := by decide

private theorem vector_body_shape :
    vectorBody = .expression [.symbol "if", .expression [.symbol "<", .var "index", .var "size"],
      .expression [.symbol "let", .var "found", .expression [.symbol "collapse",
        .expression [.symbol "match", .var "space",
          .expression [.var "index", .var "value"], .var "value"]], foundBody], .symbol "None"] := by
  decide

private theorem found_body_shape :
    foundBody = .expression [.symbol "case", .var "found",
      .expression (foundCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem found_cases_shape :
    foundCases = [(.expression [.var "value"], .expression [.symbol "Some", .var "value"]),
      (.var "bad", .symbol "MM0:Malformed")] := by decide

private theorem found_body_returns (state : State) (handle : Handle) (size index : Nat)
    (answers : List Atom) :
    PureReturns program (("found", .expression answers) :: vectorEnvironment handle size index)
      state foundBody state (queryAnswer answers) := by
  let bindings := ("found", .expression answers) :: vectorEnvironment handle size index
  rw [found_body_shape]
  cases answers with
  | nil =>
      let bound := ("bad", .expression []) :: bindings
      apply case_returns program bindings bound state state state (.var "found")
        (.expression []) (.symbol "MM0:Malformed") _ _ foundCases (read_cases_encoded foundCases)
      · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
      · simp [found_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, bindings, vectorEnvironment,
          environment, Subst.lookup, bound]
      · exact symbol_returns program bound state "MM0:Malformed"
  | cons first rest =>
      cases rest with
      | nil =>
          let bound := ("value", first) :: bindings
          apply case_returns program bindings bound state state state (.var "found")
            (.expression [first]) (.expression [.symbol "Some", .var "value"]) _ _ foundCases
            (read_cases_encoded foundCases)
          · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
          · simp [found_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, bindings, vectorEnvironment,
              environment, Subst.lookup, bound]
          · simpa [bound, applySubst, Subst.lookup, queryAnswer, ListAccess.optionValue] using
              unary_constructor_returns program bound state "Some" "value" some_is_data_constructor (by decide)
      | cons second rest =>
          let bound := ("bad", .expression (first :: second :: rest)) :: bindings
          apply case_returns program bindings bound state state state (.var "found")
            (.expression (first :: second :: rest)) (.symbol "MM0:Malformed") _ _ foundCases
            (read_cases_encoded foundCases)
          · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
          · simp [found_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, bindings, vectorEnvironment,
              environment, Subst.lookup, bound]
          · exact symbol_returns program bound state "MM0:Malformed"

private theorem vector_condition_returns (state : State) (handle : Handle) (size index : Nat) :
    PureReturns program (vectorEnvironment handle size index) state
      (.expression [.symbol "<", .var "index", .var "size"]) state (boolean (index < size)) := by
  apply native_variable_call_returns program (vectorEnvironment handle size index) state state "<"
    ["index", "size"] _ (by decide) (by decide) _ (by decide)
  simp [vectorEnvironment, environment, applySubst, Subst.lookup, natural, StdLib.apply]

theorem vector_body_returns (state : State) (handle : Handle) (rows : List Atom) (size index : Nat)
    (represented : state.read handle = some rows) :
    PureReturns program (environment handle size index) state dataAtEquation.body state
      (if index < size then queryAnswer (indexedQuery rows index) else .symbol "None") := by
  rw [body_is_case]
  let bindings := environment handle size index
  let bound := vectorEnvironment handle size index
  apply case_returns program bindings bound state state state (.var "items") (vectorValue handle size)
    vectorBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "items"
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, vectorValue, bindings, bound, environment,
      vectorEnvironment, matchAtom, Subst.lookup]
  · rw [vector_body_shape]
    apply if_returns program bound state state state _ _ _ _ _
      (vector_condition_returns state handle size index)
    by_cases bounded : index < size
    · simp only [boolean, bounded, ↓reduceIte]
      let answers := indexedQuery rows index
      let found := ("found", .expression answers) :: bound
      apply let_returns program bound found state state state (.var "found") _ _ (.expression answers) _
      · apply match_collapse_returns program bound state state "space"
          (.expression [.var "index", .var "value"]) (.var "value") answers
        simp [bound, vectorEnvironment, environment, applySubst, Subst.lookup,
          applySubst.applySubstList, StdLib.apply, represented, indexedQuery, answers]
      · simp [SpaceSemantics.matchValue, matchAtom, bound, vectorEnvironment, environment,
          Subst.lookup, found]
      · exact found_body_returns state handle size index answers
    · simpa [boolean, bounded] using symbol_returns program bound state "None"

theorem vector_returns (bindings : Subst) (state : State) (handle : Handle) (rows : List Atom)
    (size index : Nat) (itemsName indexName : String)
    (represented : state.read handle = some rows)
    (itemsCaptured : applySubst bindings (.var itemsName) = vectorValue handle size)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:data-at", .var itemsName, .var indexName]) state
      (if index < size then queryAnswer (indexedQuery rows index) else .symbol "None") := by
  apply authored_variable_call_returns program bindings (environment handle size index) state state
    "mm0:data-at" [itemsName, indexName] dataAtEquation.body _
    (by decide) (by decide) (by decide) _ (vector_body_returns state handle rows size index represented)
    (by decide)
  simpa [itemsCaptured, indexCaptured] using vector_clause handle size index

theorem vector_literal_returns (state : State) (handle : Handle) (rows : List Atom) (size index : Nat)
    (represented : state.read handle = some rows) :
    PureReturns program [] state
      (.expression [.symbol "mm0:data-at", vectorValue handle size, natural index]) state
      (if index < size then queryAnswer (indexedQuery rows index) else .symbol "None") := by
  let result := if index < size then queryAnswer (indexedQuery rows index) else .symbol "None"
  apply call_returns program [] state state "mm0:data-at" [vectorValue handle size, natural index]
    result (by decide) _ (by decide)
  have entered := authored_function_arguments_return program [] (environment handle size index)
    state state "mm0:data-at" [vectorValue handle size, natural index] 2 dataAtEquation.body result
    (by decide) (by decide) (vector_clause handle size index)
    (vector_body_returns state handle rows size index represented)
  have last := evaluated_argument_answers program [] state state state (.function "mm0:data-at")
    (natural index) (natural index) [result] [] [vectorValue handle size] 1 (by decide +kernel)
    (grounded_returns program [] state (.int index)) entered
  exact raw_argument_answers program [] state state "mm0:data-at" (vectorValue handle size)
    [natural index] [] 0 [result] (by decide)
    (by simpa only [applySubst_nil, List.nil_append, Nat.zero_add] using last)

theorem vector_has_sufficient_fuel (state : State) (handle : Handle) (rows : List Atom)
    (size index : Nat) (represented : state.read handle = some rows) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:data-at", vectorValue handle size, natural index]) =
      .complete state [if index < size then queryAnswer (indexedQuery rows index) else .symbol "None"] [] [] :=
  pure_returns_has_sufficient_fuel program [] state state _ _
    (vector_literal_returns state handle rows size index represented)

theorem represented_row_returns_its_value (state : State) (handle : Handle) (index : Nat) (value : Atom)
    (represented : Store.Represents state handle [(index, value)]) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:data-at", vectorValue handle (index + 1), natural index]) =
      .complete state [ListAccess.optionValue (some value)] [] [] := by
  simpa [Store.one_stored_value, queryAnswer] using
    vector_has_sufficient_fuel state handle (Store.rows [(index, value)]) (index + 1) index represented

theorem duplicate_occurrences_are_malformed (state : State) (handle : Handle) (index : Nat) (value : Atom)
    (represented : Store.Represents state handle [(index, value), (index, value)]) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:data-at", vectorValue handle (index + 1), natural index]) =
      .complete state [.symbol "MM0:Malformed"] [] [] := by
  simpa [Store.duplicate_rows_are_visible, queryAnswer] using
    vector_has_sufficient_fuel state handle (Store.rows [(index, value), (index, value)])
      (index + 1) index represented

theorem missing_row_inside_prefix_is_malformed (state : State) (handle : Handle) (index : Nat)
    (empty : state.read handle = some []) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:data-at", vectorValue handle (index + 1), natural index]) =
      .complete state [.symbol "MM0:Malformed"] [] [] := by
  simpa [indexedQuery, SpaceSemantics.query, queryAnswer] using
    vector_has_sufficient_fuel state handle [] (index + 1) index empty

theorem entries_beyond_prefix_are_not_reused (state : State) (handle : Handle) (index : Nat) (value : Atom)
    (represented : Store.Represents state handle [(index, value)]) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:data-at", vectorValue handle index, natural index]) =
      .complete state [.symbol "None"] [] [] := by
  simpa using vector_has_sufficient_fuel state handle (Store.rows [(index, value)]) index index represented

end Mettapedia.Languages.MM0.MeTTa.VectorAccess
