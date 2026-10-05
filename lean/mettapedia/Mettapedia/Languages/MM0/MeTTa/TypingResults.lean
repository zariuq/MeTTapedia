import Mettapedia.Languages.MM0.MeTTa.Data
import Mettapedia.Languages.MM0.MeTTa.Scalar

/-!
# Typing results from the retained MM0 source

Context lookup returns a binder; declaration lookup returns a term's
unapplied arguments and result sort. These paths execute the retained result
handlers, including missing entries. They do not authorize the tables or
establish the recursive, cached inference operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TypingResults

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open Store (natural)
open Kernel (Preterm Binder Context TermDecl)
open ListAccess (optionValue)

private def binderCode (value : Option Binder) : Atom := optionValue (value.map Data.binder)

private def declarationCode (value : Option TermDecl) : Atom := optionValue (value.map Data.declaration)

private def environment (value : Atom) : Subst := [("valueInput", value)]

private def binderEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 134)[133]'(by decide +kernel)

private def declarationEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 135)[134]'(by decide +kernel)

private theorem binder_unique :
    program.equations.filter (fun equation => equation.head == "mm0:infer-binder") =
      [binderEquation] := by decide

private theorem declaration_unique :
    program.equations.filter (fun equation => equation.head == "mm0:infer-declaration") =
      [declarationEquation] := by decide

private theorem binder_formals : binderEquation.arguments = [.var "valueInput"] := by decide

private theorem declaration_formals : declarationEquation.arguments = [.var "valueInput"] := by decide

private def binderCases : SourceProgram.Cases :=
  match binderEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def declarationCases : SourceProgram.Cases :=
  match declarationEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def boundBody : Atom := (binderCases[1]'(by decide)).2
private def regularBody : Atom := (binderCases[2]'(by decide)).2

private theorem binder_body_shape :
    binderEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
      .expression (binderCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem declaration_body_shape :
    declarationEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
      .expression (declarationCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem binder_cases_shape :
    binderCases = [(.expression [.symbol "None"], .symbol "None"),
      (.expression [.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Bound", .var "sort"]]]], boundBody),
      (.expression [.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]]]], regularBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem declaration_cases_shape :
    declarationCases = [(.expression [.symbol "None"], .symbol "None"),
      (.expression [.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:TermDecl", .var "arguments", .var "sort", .var "dependencies"]]]],
        .expression [.symbol "MM0:Inferred", .var "arguments", .var "sort"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem bound_body_shape :
    boundBody = .expression [.symbol "let", .var "items",
      .expression [.symbol "MM0:L", .expression []],
      .expression [.symbol "MM0:Inferred", .var "items", .var "sort"]] := by decide

private theorem regular_body_shape :
    regularBody = .expression [.symbol "let", .var "items2",
      .expression [.symbol "MM0:L", .expression []],
      .expression [.symbol "MM0:Inferred", .var "items2", .var "sort"]] := by decide

private theorem binder_clause (value : Option Binder) :
    clauses program "mm0:infer-binder" [binderCode value] =
      [.evaluate (environment (binderCode value)) binderEquation.body] := by
  rw [clauses_use_only_the_named_equations, binder_unique]
  simp [binder_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem declaration_clause (value : Option TermDecl) :
    clauses program "mm0:infer-declaration" [declarationCode value] =
      [.evaluate (environment (declarationCode value)) declarationEquation.body] := by
  rw [clauses_use_only_the_named_equations, declaration_unique]
  simp [declaration_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem empty_arguments_returns (bindings : Subst) (state : State) (itemsName : String)
    (sort : Nat) (captured : applySubst bindings (.var "sort") = natural sort)
    (fresh : Subst.lookup bindings itemsName = none) :
    PureReturns program bindings state
      (.expression [.symbol "let", .var itemsName, .expression [.symbol "MM0:L", .expression []],
        .expression [.symbol "MM0:Inferred", .var itemsName, .var "sort"]]) state
      (Data.inferred (some ([], sort))) := by
  let bound := (itemsName, Data.context []) :: bindings
  apply let_returns program bindings bound state state state (.var itemsName) _ _ (Data.context []) _
  · exact empty_constructor_returns program bindings state "MM0:L" list_is_data_constructor (by decide)
  · simp [SourceProgram.matchValue, matchAtom, fresh, bound]
  · have different : itemsName ≠ "sort" := by
      intro same
      subst itemsName
      have absent : applySubst bindings (.var "sort") = .var "sort" := by
        simp [applySubst, fresh]
      rw [absent] at captured
      cases captured
    have sortCaptured : applySubst bound (.var "sort") = natural sort := by
      simpa [bound, applySubst, Subst.lookup, different] using captured
    have itemsCaptured : applySubst bound (.var itemsName) = Data.context [] := by
      simp [bound, applySubst, Subst.lookup]
    simpa only [Data.inferred, List.map_cons, List.map_nil, sortCaptured, itemsCaptured] using
      constructor_variables_return program bound state "MM0:Inferred" [itemsName, "sort"]
        inferred_is_data_constructor (by decide)

theorem binder_body_returns (state : State) (value : Option Binder) :
    PureReturns program (environment (binderCode value)) state binderEquation.body state
      (Data.inferred (value.map fun binder => ([], binder.sort))) := by
  rw [binder_body_shape]
  have input : PureReturns program (environment (binderCode value)) state
      (.expression [.var "valueInput"]) state (.expression [binderCode value]) := by
    simpa [environment, applySubst, Subst.lookup] using
      tuple_variables_return program (environment (binderCode value)) state ["valueInput"]
  cases value with
  | none =>
      apply case_returns program (environment (binderCode none)) (environment (binderCode none))
        state state state _ (.expression [.symbol "None"]) (.symbol "None") _ _ binderCases
        (read_cases_encoded binderCases) input
      · simp [binder_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom]
      · exact symbol_returns program _ state "None"
  | some value =>
      cases value with
      | bound sort =>
          let bindings := environment (binderCode (some (.bound sort)))
          let bound := ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state _
            (.expression [binderCode (some (.bound sort))]) boundBody _ _ binderCases
            (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
              SourceProgram.matchValue.matchValues, matchAtom, binderCode, optionValue,
              Data.binder, ListAccess.listValue, bound, bindings, environment, Subst.lookup]
          · rw [bound_body_shape]
            exact empty_arguments_returns bound state "items" sort
              (by simp [bound, applySubst, Subst.lookup])
              (by simp [bound, bindings, environment, Subst.lookup])
      | regular sort dependencies =>
          let bindings := environment (binderCode (some (.regular sort dependencies)))
          let bound := ("dependencies", Data.dependencies dependencies) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state _
            (.expression [binderCode (some (.regular sort dependencies))]) regularBody _ _ binderCases
            (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
              SourceProgram.matchValue.matchValues, matchAtom, binderCode, optionValue,
              Data.binder, ListAccess.listValue, bound, bindings, environment, Subst.lookup]
          · rw [regular_body_shape]
            exact empty_arguments_returns bound state "items2" sort
              (by simp [bound, applySubst, Subst.lookup])
              (by simp [bound, bindings, environment, Subst.lookup])

theorem binder_captured_returns (bindings : Subst) (state : State) (name : String)
    (value : Option Binder) (captured : applySubst bindings (.var name) = binderCode value) :
    PureReturns program bindings state (.expression [.symbol "mm0:infer-binder", .var name]) state
      (Data.inferred (value.map fun binder => ([], binder.sort))) := by
  apply authored_variable_call_returns program bindings (environment (binderCode value)) state state
    "mm0:infer-binder" [name] binderEquation.body _ (by decide) (by decide) (by decide)
    _ (binder_body_returns state value) (by decide)
  simpa [captured] using binder_clause value

theorem declaration_body_returns (state : State) (value : Option TermDecl) :
    PureReturns program (environment (declarationCode value)) state declarationEquation.body state
      (Data.inferred (value.map fun declaration => (declaration.arguments, declaration.resultSort))) := by
  rw [declaration_body_shape]
  have input : PureReturns program (environment (declarationCode value)) state
      (.expression [.var "valueInput"]) state (.expression [declarationCode value]) := by
    simpa [environment, applySubst, Subst.lookup] using
      tuple_variables_return program (environment (declarationCode value)) state ["valueInput"]
  cases value with
  | none =>
      apply case_returns program (environment (declarationCode none)) (environment (declarationCode none))
        state state state _ (.expression [.symbol "None"]) (.symbol "None") _ _ declarationCases
        (read_cases_encoded declarationCases) input
      · simp [declaration_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom]
      · exact symbol_returns program _ state "None"
  | some declaration =>
      let bindings := environment (declarationCode (some declaration))
      let bound := ("dependencies", Data.dependencies declaration.dependencies) ::
        ("sort", natural declaration.resultSort) :: ("arguments", Data.context declaration.arguments) :: bindings
      apply case_returns program bindings bound state state state _
        (.expression [declarationCode (some declaration)])
        (.expression [.symbol "MM0:Inferred", .var "arguments", .var "sort"]) _ _ declarationCases
        (read_cases_encoded declarationCases) input
      · simp [declaration_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, declarationCode, optionValue,
          Data.declaration, ListAccess.listValue, bound, bindings, environment, Subst.lookup]
      · simpa [Data.inferred, bound, applySubst, Subst.lookup] using
          constructor_variables_return program bound state "MM0:Inferred" ["arguments", "sort"]
            inferred_is_data_constructor (by decide)

theorem declaration_captured_returns (bindings : Subst) (state : State) (name : String)
    (value : Option TermDecl) (captured : applySubst bindings (.var name) = declarationCode value) :
    PureReturns program bindings state (.expression [.symbol "mm0:infer-declaration", .var name]) state
      (Data.inferred (value.map fun declaration => (declaration.arguments, declaration.resultSort))) := by
  apply authored_variable_call_returns program bindings (environment (declarationCode value)) state state
    "mm0:infer-declaration" [name] declarationEquation.body _ (by decide) (by decide) (by decide)
    _ (declaration_body_returns state value) (by decide)
  simpa [captured] using declaration_clause value

private def equalEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 143)[142]'(by decide +kernel)

private def boundEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 140)[139]'(by decide +kernel)

private def equalEnvironment (same : Bool) (rest : Context) (result : Nat) : Subst :=
  [("result", natural result), ("rest", Data.context rest), ("conditionInput", boolean same)]

private def boundEnvironment (actual : Option Nat) (expected : Nat) (rest : Context) (result : Nat) : Subst :=
  [("result", natural result), ("rest", Data.context rest), ("expected", natural expected),
    ("valueInput", optionValue (actual.map natural))]

private def equalCases : SourceProgram.Cases :=
  match equalEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def boundCases : SourceProgram.Cases :=
  match boundEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def boundFoundBody : Atom := (boundCases[1]'(by decide)).2

private theorem equal_body_shape :
    equalEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (equalCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem equal_cases_shape :
    equalCases = [(boolean true, .expression [.symbol "MM0:Inferred", .var "rest", .var "result"]),
      (boolean false, .symbol "None"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem bound_handler_body_shape :
    boundEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (boundCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem bound_cases_shape :
    boundCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "sort"], boundFoundBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem bound_found_body_shape :
    boundFoundBody = .expression [.symbol "let", .var "equal",
      .expression [.symbol "mm0:nat-eq", .var "sort", .var "expected"],
      .expression [.symbol "mm0:infer-sort-equal", .var "equal", .var "rest", .var "result"]] := by decide

private theorem equal_clause (same : Bool) (rest : Context) (result : Nat) :
    clauses program "mm0:infer-sort-equal" [boolean same, Data.context rest, natural result] =
      [.evaluate (equalEnvironment same rest result) equalEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun equation => equation.head == "mm0:infer-sort-equal") =
      [equalEquation] := by decide
  have formals : equalEquation.arguments = [.var "conditionInput", .var "rest", .var "result"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, equalEnvironment, Subst.lookup]

theorem equal_body_returns (state : State) (same : Bool) (rest : Context) (result : Nat) :
    PureReturns program (equalEnvironment same rest result) state equalEquation.body state
      (Data.inferred (if same then some (rest, result) else none)) := by
  rw [equal_body_shape]
  have input : PureReturns program (equalEnvironment same rest result) state
      (.var "conditionInput") state (boolean same) := by
    simpa [equalEnvironment, applySubst, Subst.lookup] using
      variable_returns program (equalEnvironment same rest result) state "conditionInput"
  cases same with
  | true =>
      apply case_returns program (equalEnvironment true rest result) (equalEnvironment true rest result)
        state state state (.var "conditionInput") (boolean true)
        (.expression [.symbol "MM0:Inferred", .var "rest", .var "result"]) _ _ equalCases
        (read_cases_encoded equalCases) input
      · simp [equal_cases_shape, boolean, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · simpa [Data.inferred, equalEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program (equalEnvironment true rest result) state
            "MM0:Inferred" ["rest", "result"] inferred_is_data_constructor (by decide)
  | false =>
      apply case_returns program (equalEnvironment false rest result) (equalEnvironment false rest result)
        state state state (.var "conditionInput") (boolean false) (.symbol "None") _ _ equalCases
        (read_cases_encoded equalCases) input
      · simp [equal_cases_shape, boolean, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program _ state "None"

theorem equal_captured_returns (bindings : Subst) (state : State)
    (sameName restName resultName : String) (same : Bool) (rest : Context) (result : Nat)
    (capturedSame : applySubst bindings (.var sameName) = boolean same)
    (capturedRest : applySubst bindings (.var restName) = Data.context rest)
    (capturedResult : applySubst bindings (.var resultName) = natural result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-sort-equal", .var sameName, .var restName, .var resultName]) state
      (Data.inferred (if same then some (rest, result) else none)) := by
  apply authored_variable_call_returns program bindings (equalEnvironment same rest result) state state
    "mm0:infer-sort-equal" [sameName, restName, resultName] equalEquation.body _
    (by decide) (by decide) (by decide) _ (equal_body_returns state same rest result) (by decide)
  simpa [capturedSame, capturedRest, capturedResult] using equal_clause same rest result

private theorem bound_clause (actual : Option Nat) (expected : Nat) (rest : Context) (result : Nat) :
    clauses program "mm0:infer-bound-sort"
      [optionValue (actual.map natural), natural expected, Data.context rest, natural result] =
      [.evaluate (boundEnvironment actual expected rest result) boundEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun equation => equation.head == "mm0:infer-bound-sort") =
      [boundEquation] := by decide
  have formals : boundEquation.arguments =
      [.var "valueInput", .var "expected", .var "rest", .var "result"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, boundEnvironment, Subst.lookup]

theorem bound_body_returns (state : State) (actual : Option Nat) (expected : Nat)
    (rest : Context) (result : Nat) :
    PureReturns program (boundEnvironment actual expected rest result) state boundEquation.body state
      (Data.inferred (if actual = some expected then some (rest, result) else none)) := by
  rw [bound_handler_body_shape]
  have input : PureReturns program (boundEnvironment actual expected rest result) state
      (.var "valueInput") state (optionValue (actual.map natural)) := by
    simpa [boundEnvironment, applySubst, Subst.lookup] using
      variable_returns program (boundEnvironment actual expected rest result) state "valueInput"
  cases actual with
  | none =>
      apply case_returns program (boundEnvironment none expected rest result)
        (boundEnvironment none expected rest result) state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ boundCases (read_cases_encoded boundCases) input
      · simp [bound_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program _ state "None"
  | some actual =>
      let bindings := boundEnvironment (some actual) expected rest result
      let bound := ("sort", natural actual) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (optionValue (some (natural actual))) boundFoundBody _ _ boundCases
        (read_cases_encoded boundCases) input
      · simp [bound_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, optionValue, bound, bindings,
          boundEnvironment, Subst.lookup]
      · rw [bound_found_body_shape]
        let compared := ("equal", boolean (decide (actual = expected))) :: bound
        apply let_returns program bound compared state state state (.var "equal") _ _
          (boolean (decide (actual = expected))) _
        · exact Scalar.equality_captured_returns bound state "sort" "expected" actual expected
            (by simp [bound, applySubst, Subst.lookup])
            (by simp [bound, bindings, boundEnvironment, applySubst, Subst.lookup])
        · simp [SourceProgram.matchValue, matchAtom, compared, bound, bindings, boundEnvironment, Subst.lookup]
        · simpa using equal_captured_returns compared state "equal" "rest" "result"
            (decide (actual = expected)) rest result
            (by simp [compared, applySubst, Subst.lookup])
            (by simp [compared, bound, bindings, boundEnvironment, applySubst, Subst.lookup])
            (by simp [compared, bound, bindings, boundEnvironment, applySubst, Subst.lookup])

theorem bound_captured_returns (bindings : Subst) (state : State)
    (actualName expectedName restName resultName : String)
    (actual : Option Nat) (expected : Nat) (rest : Context) (result : Nat)
    (capturedActual : applySubst bindings (.var actualName) = optionValue (actual.map natural))
    (capturedExpected : applySubst bindings (.var expectedName) = natural expected)
    (capturedRest : applySubst bindings (.var restName) = Data.context rest)
    (capturedResult : applySubst bindings (.var resultName) = natural result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-bound-sort", .var actualName, .var expectedName,
        .var restName, .var resultName]) state
      (Data.inferred (if actual = some expected then some (rest, result) else none)) := by
  apply authored_variable_call_returns program bindings (boundEnvironment actual expected rest result)
    state state "mm0:infer-bound-sort" [actualName, expectedName, restName, resultName] boundEquation.body _
    (by decide) (by decide) (by decide) _ (bound_body_returns state actual expected rest result) (by decide)
  simpa [capturedActual, capturedExpected, capturedRest, capturedResult] using
    bound_clause actual expected rest result

private def saturatedEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 142)[141]'(by decide +kernel)

private def regularEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 141)[140]'(by decide +kernel)

private def saturatedEnvironment (remaining : Context) (actual expected : Nat) (rest : Context)
    (result : Nat) : Subst :=
  [("result", natural result), ("rest", Data.context rest), ("expected", natural expected),
    ("sort", natural actual), ("valueInput", ListAccess.viewValue (remaining.map Data.binder))]

private def regularEnvironment (actual : Option Kernel.ExpressionType) (expected : Nat)
    (rest : Context) (result : Nat) : Subst :=
  [("result", natural result), ("rest", Data.context rest), ("expected", natural expected),
    ("valueInput", Data.inferred actual)]

private def saturatedCases : SourceProgram.Cases :=
  match saturatedEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def regularCases : SourceProgram.Cases :=
  match regularEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def saturatedEmptyBody : Atom := (saturatedCases[0]'(by decide)).2
private def regularFoundBody : Atom := (regularCases[1]'(by decide)).2

private theorem saturated_body_shape :
    saturatedEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (saturatedCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem saturated_cases_shape :
    saturatedCases = [(.symbol "List:Nil", saturatedEmptyBody),
      (.expression [.symbol "List:Cons", .var "first", .var "tail"], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem saturated_empty_body_shape :
    saturatedEmptyBody = .expression [.symbol "let", .var "equal",
      .expression [.symbol "mm0:nat-eq", .var "sort", .var "expected"],
      .expression [.symbol "mm0:infer-sort-equal", .var "equal", .var "rest", .var "result"]] := by decide

private theorem regular_handler_body_shape :
    regularEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (regularCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem regular_cases_shape :
    regularCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "MM0:Inferred", .var "remaining", .var "sort"], regularFoundBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem regular_found_body_shape :
    regularFoundBody = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "remaining"],
      .expression [.symbol "mm0:infer-saturated", .var "view", .var "sort", .var "expected",
        .var "rest", .var "result"]] := by decide

private theorem saturated_clause (remaining : Context) (actual expected : Nat) (rest : Context)
    (result : Nat) :
    clauses program "mm0:infer-saturated"
      [ListAccess.viewValue (remaining.map Data.binder), natural actual, natural expected,
        Data.context rest, natural result] =
      [.evaluate (saturatedEnvironment remaining actual expected rest result) saturatedEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun equation => equation.head == "mm0:infer-saturated") =
      [saturatedEquation] := by decide
  have formals : saturatedEquation.arguments =
      [.var "valueInput", .var "sort", .var "expected", .var "rest", .var "result"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, saturatedEnvironment, Subst.lookup]

theorem saturated_body_returns (state : State) (remaining : Context) (actual expected : Nat)
    (rest : Context) (result : Nat) :
    PureReturns program (saturatedEnvironment remaining actual expected rest result) state
      saturatedEquation.body state
      (Data.inferred (if (remaining, actual) = ([], expected) then some (rest, result) else none)) := by
  rw [saturated_body_shape]
  have input : PureReturns program (saturatedEnvironment remaining actual expected rest result) state
      (.var "valueInput") state (ListAccess.viewValue (remaining.map Data.binder)) := by
    simpa [saturatedEnvironment, applySubst, Subst.lookup] using
      variable_returns program (saturatedEnvironment remaining actual expected rest result) state "valueInput"
  cases remaining with
  | nil =>
      let bindings := saturatedEnvironment [] actual expected rest result
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "List:Nil") saturatedEmptyBody _ _ saturatedCases (read_cases_encoded saturatedCases) input
      · simp [saturated_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · rw [saturated_empty_body_shape]
        let compared := ("equal", boolean (decide (actual = expected))) :: bindings
        apply let_returns program bindings compared state state state (.var "equal") _ _
          (boolean (decide (actual = expected))) _
        · exact Scalar.equality_captured_returns bindings state "sort" "expected" actual expected
            (by simp [bindings, saturatedEnvironment, applySubst, Subst.lookup])
            (by simp [bindings, saturatedEnvironment, applySubst, Subst.lookup])
        · simp [SourceProgram.matchValue, matchAtom, compared, bindings, saturatedEnvironment, Subst.lookup]
        · simpa using equal_captured_returns compared state "equal" "rest" "result"
            (decide (actual = expected)) rest result
            (by simp [compared, applySubst, Subst.lookup])
            (by simp [compared, bindings, saturatedEnvironment, applySubst, Subst.lookup])
            (by simp [compared, bindings, saturatedEnvironment, applySubst, Subst.lookup])
  | cons first tail =>
      let bindings := saturatedEnvironment (first :: tail) actual expected rest result
      let bound := ("tail", Data.context tail) :: ("first", Data.binder first) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (ListAccess.viewValue ((first :: tail).map Data.binder)) (.symbol "None") _ _ saturatedCases
        (read_cases_encoded saturatedCases) input
      · simp [saturated_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, ListAccess.viewValue, Data.context,
          bound, bindings, saturatedEnvironment, Subst.lookup]
      · simpa [Data.inferred] using symbol_returns program bound state "None"

theorem saturated_captured_returns (bindings : Subst) (state : State)
    (viewName actualName expectedName restName resultName : String)
    (remaining : Context) (actual expected : Nat) (rest : Context) (result : Nat)
    (capturedView : applySubst bindings (.var viewName) = ListAccess.viewValue (remaining.map Data.binder))
    (capturedActual : applySubst bindings (.var actualName) = natural actual)
    (capturedExpected : applySubst bindings (.var expectedName) = natural expected)
    (capturedRest : applySubst bindings (.var restName) = Data.context rest)
    (capturedResult : applySubst bindings (.var resultName) = natural result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-saturated", .var viewName, .var actualName, .var expectedName,
        .var restName, .var resultName]) state
      (Data.inferred (if (remaining, actual) = ([], expected) then some (rest, result) else none)) := by
  apply authored_variable_call_returns program bindings
    (saturatedEnvironment remaining actual expected rest result) state state "mm0:infer-saturated"
    [viewName, actualName, expectedName, restName, resultName] saturatedEquation.body _
    (by decide) (by decide) (by decide) _
    (saturated_body_returns state remaining actual expected rest result) (by decide)
  simpa [capturedView, capturedActual, capturedExpected, capturedRest, capturedResult] using
    saturated_clause remaining actual expected rest result

private theorem regular_clause (actual : Option Kernel.ExpressionType) (expected : Nat)
    (rest : Context) (result : Nat) :
    clauses program "mm0:infer-regular-type" [Data.inferred actual, natural expected, Data.context rest,
      natural result] = [.evaluate (regularEnvironment actual expected rest result) regularEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun equation => equation.head == "mm0:infer-regular-type") =
      [regularEquation] := by decide
  have formals : regularEquation.arguments =
      [.var "valueInput", .var "expected", .var "rest", .var "result"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, regularEnvironment, Subst.lookup]

theorem regular_body_returns (state : State) (actual : Option Kernel.ExpressionType) (expected : Nat)
    (rest : Context) (result : Nat) :
    PureReturns program (regularEnvironment actual expected rest result) state regularEquation.body state
      (Data.inferred (if actual = some ([], expected) then some (rest, result) else none)) := by
  rw [regular_handler_body_shape]
  have input : PureReturns program (regularEnvironment actual expected rest result) state
      (.var "valueInput") state (Data.inferred actual) := by
    simpa [regularEnvironment, applySubst, Subst.lookup] using
      variable_returns program (regularEnvironment actual expected rest result) state "valueInput"
  cases actual with
  | none =>
      apply case_returns program (regularEnvironment none expected rest result)
        (regularEnvironment none expected rest result) state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ regularCases (read_cases_encoded regularCases) input
      · simp [regular_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program _ state "None"
  | some type =>
      rcases type with ⟨remaining, sort⟩
      let bindings := regularEnvironment (some (remaining, sort)) expected rest result
      let bound := ("sort", natural sort) :: ("remaining", Data.context remaining) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.inferred (some (remaining, sort))) regularFoundBody _ _ regularCases
        (read_cases_encoded regularCases) input
      · simp [regular_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, matchAtom, Data.inferred, bound, bindings,
          regularEnvironment, Subst.lookup]
      · rw [regular_found_body_shape]
        let viewed := ("view", ListAccess.viewValue (remaining.map Data.binder)) :: bound
        apply let_returns program bound viewed state state state (.var "view") _ _
          (ListAccess.viewValue (remaining.map Data.binder)) _
        · exact ListAccess.view_captured_returns bound state "remaining" (remaining.map Data.binder)
            (by simp [bound, Data.context, applySubst, Subst.lookup])
        · simp [SourceProgram.matchValue, matchAtom, viewed, bound, bindings, regularEnvironment, Subst.lookup]
        · simpa only [Option.some.injEq] using
            saturated_captured_returns viewed state "view" "sort" "expected" "rest" "result"
              remaining sort expected rest result
              (by simp [viewed, applySubst, Subst.lookup])
              (by simp [viewed, bound, applySubst, Subst.lookup])
              (by simp [viewed, bound, bindings, regularEnvironment, applySubst, Subst.lookup])
              (by simp [viewed, bound, bindings, regularEnvironment, applySubst, Subst.lookup])
              (by simp [viewed, bound, bindings, regularEnvironment, applySubst, Subst.lookup])

theorem regular_captured_returns (bindings : Subst) (state : State)
    (actualName expectedName restName resultName : String)
    (actual : Option Kernel.ExpressionType) (expected : Nat) (rest : Context) (result : Nat)
    (capturedActual : applySubst bindings (.var actualName) = Data.inferred actual)
    (capturedExpected : applySubst bindings (.var expectedName) = natural expected)
    (capturedRest : applySubst bindings (.var restName) = Data.context rest)
    (capturedResult : applySubst bindings (.var resultName) = natural result) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-regular-type", .var actualName, .var expectedName,
        .var restName, .var resultName]) state
      (Data.inferred (if actual = some ([], expected) then some (rest, result) else none)) := by
  apply authored_variable_call_returns program bindings (regularEnvironment actual expected rest result)
    state state "mm0:infer-regular-type" [actualName, expectedName, restName, resultName] regularEquation.body _
    (by decide) (by decide) (by decide) _ (regular_body_returns state actual expected rest result) (by decide)
  simpa [capturedActual, capturedExpected, capturedRest, capturedResult] using
    regular_clause actual expected rest result

end Mettapedia.Languages.MM0.MeTTa.TypingResults
