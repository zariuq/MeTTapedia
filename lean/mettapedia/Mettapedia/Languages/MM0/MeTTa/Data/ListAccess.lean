import Mettapedia.Languages.MM0.MeTTa.Program
import Mettapedia.Languages.MM0.MeTTa.Data.Store
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Direct list access in the retained MM0 source

The source function checks its bound and uses native container access. Its
execution is related to ordinary list lookup, without expanding a hypothesis
read into proof-certificate nodes. Captured list entries are returned as data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ListAccess

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)

def listValue (values : List Atom) : Atom :=
  .expression [.symbol "MM0:L", .expression values]

/-- MM0's internal substitution list, distinct from native containers. -/
def linkedValue : List Atom → Atom
  | [] => .symbol "LNil"
  | first :: rest => .expression [.symbol "LCons", first, linkedValue rest]

def optionValue : Option Atom → Atom
  | none => .symbol "None"
  | some value => .expression [.symbol "Some", value]

private def environment (values : List Atom) (index : Nat) : Subst :=
  [("index", natural index), ("items", listValue values)]

private def listEnvironment (values : List Atom) (index : Nat) : Subst :=
  ("values", .expression values) :: environment values index

theorem data_at_list_clause (values : List Atom) (index : Nat) :
    clauses program "mm0:data-at" [listValue values, natural index] =
      [.evaluate (environment values index) dataAtEquation.body] := by
  rw [clauses_use_only_the_named_equations, data_at_equation_is_unique]
  simp [data_at_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private def cases : SpaceSemantics.Cases :=
  match dataAtEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def listBody : Atom := (cases[0]'(by decide)).2

private theorem body_is_case :
    dataAtEquation.body = .expression [.symbol "case", .var "items",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by
  decide

private theorem cases_head :
    cases = (.expression [.symbol "MM0:L", .var "values"], listBody) :: cases.tail := by
  decide

private theorem list_body_shape :
    listBody = .expression [.symbol "if",
      .expression [.symbol "<", .var "index", .expression [.symbol "size-atom", .var "values"]],
      .expression [.symbol "let", .var "value",
        .expression [.symbol "index-atom", .var "values", .var "index"],
        .expression [.symbol "Some", .var "value"]], .symbol "None"] := by
  decide

private theorem selected_list_case (values : List Atom) (index : Nat) :
    SpaceSemantics.selectCase (environment values index) (listValue values) cases =
      some (("values", .expression values) :: environment values index, listBody) := by
  have matched : SpaceSemantics.matchValue (environment values index)
      (.expression [.symbol "MM0:L", .var "values"]) (listValue values) =
      some (("values", .expression values) :: environment values index) := by
    simp [SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, listValue,
      environment, matchAtom, Subst.lookup]
  rw [cases_head, SpaceSemantics.selectCase, matched]

private theorem list_condition_returns (state : State) (values : List Atom) (index : Nat) :
    PureReturns program (listEnvironment values index) state
      (.expression [.symbol "<", .var "index",
        .expression [.symbol "size-atom", .var "values"]]) state
      (boolean (index < values.length)) := by
  let bindings := listEnvironment values index
  have size : PureReturns program bindings state
      (.expression [.symbol "size-atom", .var "values"]) state (natural values.length) := by
    apply native_variable_call_returns program bindings state state "size-atom" ["values"]
      (natural values.length) (by decide) (by decide) _ (by decide)
    simp [bindings, listEnvironment, environment, applySubst, Subst.lookup,
      StdLib.apply, natural]
  apply call_returns program bindings state state "<" _ _ (by decide) _ (by decide)
  have native := native_function_arguments_return program bindings state state "<"
    [natural index, natural values.length] 2 (boolean (index < values.length))
    (by decide) (by decide) (by simp [StdLib.apply, natural, boolean])
  have last := evaluated_argument_returns program bindings state state state (.function "<")
    _ (natural values.length) (boolean (index < values.length)) [] [natural index] 1
    (by decide) size native
  have first : PureReturns program bindings state (.var "index") state (natural index) := by
    simpa [bindings, listEnvironment, environment, applySubst, Subst.lookup] using
      variable_returns program bindings state "index"
  exact evaluated_argument_returns program bindings state state state (.function "<")
    (.var "index") (natural index) (boolean (index < values.length)) _ [] 0
    (by decide) first last

private theorem list_found_returns (state : State) (values : List Atom) (index : Nat)
    (bounded : index < values.length) :
    PureReturns program (listEnvironment values index) state
      (.expression [.symbol "let", .var "value",
        .expression [.symbol "index-atom", .var "values", .var "index"],
        .expression [.symbol "Some", .var "value"]]) state
      (optionValue (values[index]?)) := by
  let bindings := listEnvironment values index
  let value := values[index]
  have accessed : PureReturns program bindings state
      (.expression [.symbol "index-atom", .var "values", .var "index"]) state value := by
    apply native_variable_call_returns program bindings state state "index-atom" ["values", "index"]
      value (by decide) (by decide) _ (by decide)
    simp [bindings, listEnvironment, environment, applySubst, Subst.lookup,
      StdLib.apply, natural, value, List.getElem?_eq_getElem bounded]
  have matched : SpaceSemantics.matchValue bindings (.var "value") value =
      some (("value", value) :: bindings) := by
    simp [SpaceSemantics.matchValue, matchAtom, bindings, listEnvironment, environment, Subst.lookup]
  have wrapped := unary_constructor_returns program (("value", value) :: bindings) state "Some" "value"
    some_is_data_constructor (by decide)
  have wrappedResult : PureReturns program (("value", value) :: bindings) state
      (.expression [.symbol "Some", .var "value"]) state (optionValue (values[index]?)) := by
    simpa [optionValue, List.getElem?_eq_getElem bounded, applySubst, Subst.lookup] using wrapped
  exact let_returns program bindings _ state state state (.var "value") _ _ value _
    accessed matched wrappedResult

theorem data_at_list_body_returns (state : State) (values : List Atom) (index : Nat) :
    PureReturns program (environment values index) state dataAtEquation.body state
      (optionValue (values[index]?)) := by
  rw [body_is_case]
  apply case_returns program (environment values index) (listEnvironment values index)
    state state state (.var "items") (listValue values) listBody _ _ cases
    (read_cases_encoded cases)
  · simpa [environment, applySubst, Subst.lookup] using
      variable_returns program (environment values index) state "items"
  · exact selected_list_case values index
  · rw [list_body_shape]
    apply if_returns program (listEnvironment values index) state state state _ _ _ _ _
      (list_condition_returns state values index)
    by_cases bounded : index < values.length
    · simpa [boolean, bounded] using list_found_returns state values index bounded
    · have absent : values[index]? = none := List.getElem?_eq_none (by omega)
      simpa [boolean, bounded, absent, optionValue] using
        symbol_returns program (listEnvironment values index) state "None"

theorem data_at_list_returns (bindings : Subst) (state : State) (values : List Atom) (index : Nat)
    (itemsName indexName : String)
    (items : applySubst bindings (.var itemsName) = listValue values)
    (number : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:data-at", .var itemsName, .var indexName]) state
      (optionValue (values[index]?)) := by
  apply authored_variable_call_returns program bindings (environment values index) state state
    "mm0:data-at" [itemsName, indexName] dataAtEquation.body _
    (by decide) (by decide) (by decide)
    _ (data_at_list_body_returns state values index) (by decide)
  simpa [items, number] using data_at_list_clause values index

def viewValue : List Atom → Atom
  | [] => .symbol "List:Nil"
  | first :: rest => .expression [.symbol "List:Cons", first, listValue rest]

theorem list_variables_return (bindings : Subst) (state : State) (names : List String) :
    PureReturns program bindings state
      (.expression [.symbol "MM0:L", .expression (names.map Atom.var)]) state
      (listValue (names.map fun name => applySubst bindings (.var name))) := by
  apply data_call_returns program bindings state state "MM0:L" _ _ list_is_data_constructor _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol "MM0:L") (.symbol "MM0:L") _ _ [] 0 rfl
    (symbol_returns program bindings state "MM0:L")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression (names.map Atom.var)) _ _ [] [.symbol "MM0:L"] 1 rfl
    (tuple_variables_return program bindings state names)
  exact data_arguments_values_return program bindings state _ 2

private def viewEnvironment (values : List Atom) : Subst := [("items", .expression values)]

private def viewCases : SpaceSemantics.Cases :=
  match listViewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def nonemptyViewBody : Atom := (viewCases[1]'(by decide)).2

private theorem view_body_shape :
    listViewEquation.body = .expression [.symbol "case", .var "items",
      .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem view_cases_shape :
    viewCases = [(.expression [], .symbol "List:Nil"),
      (.expression [.symbol "cons", .var "first", .var "rest"], nonemptyViewBody)] := by decide

private theorem nonempty_view_body_shape :
    nonemptyViewBody = .expression [.symbol "List:Cons", .var "first",
      .expression [.symbol "MM0:L", .var "rest"]] := by decide

theorem view_clause (values : List Atom) :
    clauses program "mm0:list-view" [listValue values] =
      [.evaluate (viewEnvironment values) listViewEquation.body] := by
  rw [clauses_use_only_the_named_equations, list_view_equation_is_unique]
  simp [list_view_formals, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]

theorem view_body_returns (state : State) (values : List Atom) :
    PureReturns program (viewEnvironment values) state listViewEquation.body state (viewValue values) := by
  rw [view_body_shape]
  have input : PureReturns program (viewEnvironment values) state (.var "items") state (.expression values) := by
    simpa [viewEnvironment, applySubst, Subst.lookup] using
      variable_returns program (viewEnvironment values) state "items"
  cases values with
  | nil =>
      apply case_returns program (viewEnvironment []) (viewEnvironment []) state state state
        (.var "items") (.expression []) (.symbol "List:Nil") _ _ viewCases
        (read_cases_encoded viewCases) input
      · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · exact symbol_returns program _ state "List:Nil"
  | cons first rest =>
      let bindings := viewEnvironment (first :: rest)
      let bound := ("rest", .expression rest) :: ("first", first) :: bindings
      apply case_returns program bindings bound state state state (.var "items") (.expression (first :: rest))
        nonemptyViewBody _ _ viewCases (read_cases_encoded viewCases) input
      · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, bound, bindings, viewEnvironment, Subst.lookup]
      · rw [nonempty_view_body_shape]
        apply binary_constructor_returns program bound state state state "List:Cons"
          (.var "first") (.expression [.symbol "MM0:L", .var "rest"]) first (listValue rest)
          list_cons_is_data_constructor (by decide)
        · simpa [bound, bindings, viewEnvironment, applySubst, Subst.lookup] using
            variable_returns program bound state "first"
        · simpa [bound, listValue, applySubst, Subst.lookup] using
            unary_constructor_returns program bound state "MM0:L" "rest" list_is_data_constructor (by decide)

theorem view_captured_returns (bindings : Subst) (state : State) (name : String) (values : List Atom)
    (captured : applySubst bindings (.var name) = listValue values) :
    PureReturns program bindings state (.expression [.symbol "mm0:list-view", .var name]) state
      (viewValue values) := by
  apply authored_variable_call_returns program bindings (viewEnvironment values) state state
    "mm0:list-view" [name] listViewEquation.body _ (by decide) (by decide) (by decide)
    _ (view_body_returns state values) (by decide)
  simpa [captured] using view_clause values

private def consEquation : SpaceSemantics.Equation := dataSource.program.equations[4]'(by decide)

private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("tail", listValue rest), ("first", first)]

private def consCases : SpaceSemantics.Cases :=
  match consEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def consBody : Atom := (consCases[0]'(by decide)).2

private theorem cons_unique :
    program.equations.filter (fun entry => entry.head == "mm0:list-cons") = [consEquation] := by decide

private theorem cons_formals : consEquation.arguments = [.var "first", .var "tail"] := by decide

private theorem cons_body_shape :
    consEquation.body = .expression [.symbol "case", .expression [.var "first", .var "tail"],
      .expression (consCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cons_cases_head :
    consCases = (.expression [.var "item", .expression [.symbol "MM0:L", .var "rest"]], consBody) ::
      consCases.tail := by decide

private theorem cons_selected_body_shape :
    consBody = .expression [.symbol "let", .var "items",
      .expression [.symbol "cons", .var "item", .var "rest"],
      .expression [.symbol "MM0:L", .var "items"]] := by decide

private theorem cons_clause (first : Atom) (rest : List Atom) :
    clauses program "mm0:list-cons" [first, listValue rest] =
      [.evaluate (consEnvironment first rest) consEquation.body] := by
  rw [clauses_use_only_the_named_equations, cons_unique]
  simp [cons_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, consEnvironment]

theorem cons_body_returns (state : State) (first : Atom) (rest : List Atom) :
    PureReturns program (consEnvironment first rest) state consEquation.body state
      (listValue (first :: rest)) := by
  let bindings := consEnvironment first rest
  let bound := ("rest", .expression rest) :: ("item", first) :: bindings
  rw [cons_body_shape]
  apply case_returns program bindings bound state state state (.expression [.var "first", .var "tail"])
    (.expression [first, listValue rest]) consBody _ _ consCases (read_cases_encoded consCases)
  · simpa [bindings, consEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["first", "tail"]
  · rw [cons_cases_head]
    simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, listValue, bound, bindings, consEnvironment]
  · rw [cons_selected_body_shape]
    let wrapped := ("items", .expression (first :: rest)) :: bound
    apply let_returns program bound wrapped state state state (.var "items") _ _
      (.expression (first :: rest)) _
    · apply native_variable_call_returns program bound state state "cons" ["item", "rest"] _
        (by decide) (by decide) _ (by decide)
      simp [StdLib.apply, bound, bindings, consEnvironment, applySubst, Subst.lookup]
    · simp [SpaceSemantics.matchValue, matchAtom, wrapped, bound, bindings, consEnvironment, Subst.lookup]
    · simpa [wrapped, listValue, applySubst, Subst.lookup] using
        unary_constructor_returns program wrapped state "MM0:L" "items" list_is_data_constructor (by decide)

theorem cons_captured_returns (bindings : Subst) (state : State) (first : Atom) (rest : List Atom)
    (firstName restName : String)
    (capturedFirst : applySubst bindings (.var firstName) = first)
    (capturedRest : applySubst bindings (.var restName) = listValue rest) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:list-cons", .var firstName, .var restName]) state
      (listValue (first :: rest)) := by
  apply authored_variable_call_returns program bindings (consEnvironment first rest) state state
    "mm0:list-cons" [firstName, restName] consEquation.body _ (by decide) (by decide) (by decide)
    _ (cons_body_returns state first rest) (by decide)
  simpa [capturedFirst, capturedRest] using cons_clause first rest

private def appendEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 144)[143]'(by decide +kernel)

private def appendViewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 145)[144]'(by decide +kernel)

private def appendEnvironment (left right : List Atom) : Subst :=
  [("right", listValue right), ("left", listValue left)]

private def appendViewEnvironment (left right : List Atom) : Subst :=
  [("right", listValue right), ("valueInput", viewValue left)]

private def appendCases : SpaceSemantics.Cases :=
  match appendViewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def appendConsBody : Atom := (appendCases[1]'(by decide)).2

private theorem append_unique :
    program.equations.filter (fun entry => entry.head == "mm0:list-append") = [appendEquation] := by decide

private theorem append_view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:append-view") = [appendViewEquation] := by decide

private theorem append_formals : appendEquation.arguments = [.var "left", .var "right"] := by decide

private theorem append_view_formals :
    appendViewEquation.arguments = [.var "valueInput", .var "right"] := by decide

private theorem append_body_shape :
    appendEquation.body = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "left"],
      .expression [.symbol "mm0:append-view", .var "view", .var "right"]] := by decide

private theorem append_view_body_shape :
    appendViewEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (appendCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem append_cases_shape :
    appendCases = [(.symbol "List:Nil", .var "right"),
      (.expression [.symbol "List:Cons", .var "first", .var "rest"], appendConsBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem append_cons_body_shape :
    appendConsBody = .expression [.symbol "let", .var "combined",
      .expression [.symbol "mm0:list-append", .var "rest", .var "right"],
      .expression [.symbol "mm0:list-cons", .var "first", .var "combined"]] := by decide

private theorem append_clause (left right : List Atom) :
    clauses program "mm0:list-append" [listValue left, listValue right] =
      [.evaluate (appendEnvironment left right) appendEquation.body] := by
  rw [clauses_use_only_the_named_equations, append_unique]
  simp [append_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, appendEnvironment]

private theorem append_view_clause (left right : List Atom) :
    clauses program "mm0:append-view" [viewValue left, listValue right] =
      [.evaluate (appendViewEnvironment left right) appendViewEquation.body] := by
  rw [clauses_use_only_the_named_equations, append_view_unique]
  simp [append_view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, appendViewEnvironment]

theorem append_body_returns (state : State) (left right : List Atom) :
    PureReturns program (appendEnvironment left right) state appendEquation.body state
      (listValue (left ++ right)) := by
  induction left with
  | nil =>
      let bindings := appendEnvironment [] right
      let viewed := ("view", viewValue []) :: bindings
      rw [append_body_shape]
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact view_captured_returns bindings state "left" [] (by rfl)
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, appendEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (appendViewEnvironment [] right) state state
          "mm0:append-view" ["view", "right"] appendViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, appendEnvironment, applySubst, Subst.lookup] using append_view_clause [] right
        · rw [append_view_body_shape]
          let inner := appendViewEnvironment [] right
          apply case_returns program inner inner state state state (.var "valueInput")
            (viewValue []) (.var "right") _ _ appendCases (read_cases_encoded appendCases)
          · simpa [inner, appendViewEnvironment, applySubst, Subst.lookup] using
              variable_returns program inner state "valueInput"
          · simp [append_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · simpa [inner, appendViewEnvironment, applySubst, Subst.lookup] using
              variable_returns program inner state "right"
  | cons first rest recursive =>
      let bindings := appendEnvironment (first :: rest) right
      let viewed := ("view", viewValue (first :: rest)) :: bindings
      rw [append_body_shape]
      apply let_returns program bindings viewed state state state (.var "view") _ _
        (viewValue (first :: rest)) _
      · exact view_captured_returns bindings state "left" (first :: rest) (by rfl)
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, appendEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (appendViewEnvironment (first :: rest) right)
          state state "mm0:append-view" ["view", "right"] appendViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, appendEnvironment, applySubst, Subst.lookup] using
            append_view_clause (first :: rest) right
        · rw [append_view_body_shape]
          let inner := appendViewEnvironment (first :: rest) right
          let bound := ("rest", listValue rest) :: ("first", first) :: inner
          apply case_returns program inner bound state state state (.var "valueInput")
            (viewValue (first :: rest)) appendConsBody _ _ appendCases (read_cases_encoded appendCases)
          · simpa [inner, appendViewEnvironment, applySubst, Subst.lookup] using
              variable_returns program inner state "valueInput"
          · simp [append_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, bound, inner,
              appendViewEnvironment, Subst.lookup]
          · rw [append_cons_body_shape]
            let combined := ("combined", listValue (rest ++ right)) :: bound
            apply let_returns program bound combined state state state (.var "combined") _ _
              (listValue (rest ++ right)) _
            · apply authored_variable_call_returns program bound (appendEnvironment rest right) state state
                "mm0:list-append" ["rest", "right"] appendEquation.body _
                (by decide) (by decide) (by decide) _ recursive (by decide)
              simpa [bound, inner, appendViewEnvironment, applySubst, Subst.lookup] using append_clause rest right
            · simp [SpaceSemantics.matchValue, matchAtom, combined, bound, inner, appendViewEnvironment, Subst.lookup]
            · simpa using cons_captured_returns combined state first (rest ++ right) "first" "combined"
                (by simp [combined, bound, inner, appendViewEnvironment, applySubst, Subst.lookup]) (by rfl)

theorem append_captured_returns (bindings : Subst) (state : State) (left right : List Atom)
    (leftName rightName : String)
    (capturedLeft : applySubst bindings (.var leftName) = listValue left)
    (capturedRight : applySubst bindings (.var rightName) = listValue right) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:list-append", .var leftName, .var rightName]) state
      (listValue (left ++ right)) := by
  apply authored_variable_call_returns program bindings (appendEnvironment left right) state state
    "mm0:list-append" [leftName, rightName] appendEquation.body _
    (by decide) (by decide) (by decide) _ (append_body_returns state left right) (by decide)
  simpa [capturedLeft, capturedRight] using append_clause left right

end Mettapedia.Languages.MM0.MeTTa.ListAccess
