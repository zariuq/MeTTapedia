import Mettapedia.Languages.MM0.MeTTa.Data

/-!
# Native containers converted to MM0 substitution images

The retained source converts one ordinary list into its internal linked image
list. Elements are captured data: a callable-looking element is not evaluated.
Order, repetitions and empty lists are preserved, with no store changes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SubstitutionValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State)
open ListAccess (listValue linkedValue viewValue)

private def equation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 63)[62]'(by decide)
private def viewEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 64)[63]'(by decide)
private def environment (values : List Atom) : Subst := [("values", listValue values)]
private def viewEnvironment (values : List Atom) : Subst := [("valueInput", viewValue values)]
private def cases : SourceProgram.Cases :=
  match viewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := (cases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:substitution-values") = [equation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:substitution-values-view") = [viewEquation] := by decide
private theorem formals : equation.arguments = [.var "values"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "values"],
      .expression [.symbol "mm0:substitution-values-view", .var "view"]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"], .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem cases_shape : cases = [(.expression [.symbol "List:Nil"], .symbol "LNil"),
    (.expression [.expression [.symbol "List:Cons", .var "first", .var "rest"]], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "substitutionValuesResult", .expression [.symbol "mm0:substitution-values", .var "rest"],
      .expression [.symbol "LCons", .var "first", .var "substitutionValuesResult"]] := by decide

private theorem clause (values : List Atom) : clauses program "mm0:substitution-values" [listValue values] =
    [.evaluate (environment values) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (values : List Atom) : clauses program "mm0:substitution-values-view" [viewValue values] =
    [.evaluate (viewEnvironment values) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]

private theorem call_from_body (bindings : Subst) (state : State) (values : List Atom) (name : String)
    (captured : applySubst bindings (.var name) = listValue values)
    (computed : PureReturns program (environment values) state equation.body state (linkedValue values)) :
    PureReturns program bindings state (.expression [.symbol "mm0:substitution-values", .var name]) state (linkedValue values) := by
  apply authored_variable_call_returns program bindings (environment values) state state
    "mm0:substitution-values" [name] equation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [captured] using clause values

theorem body_returns (state : State) (values : List Atom) :
    PureReturns program (environment values) state equation.body state (linkedValue values) := by
  induction values with
  | nil =>
      rw [body_shape]
      let bindings := environment []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "values" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment []) state state
          "mm0:substitution-values-view" ["view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause []
        · rw [view_body_shape]
          let callee := viewEnvironment []
          apply case_returns program callee callee state state state (.expression [.var "valueInput"])
            (.expression [viewValue []]) (.symbol "LNil") _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program callee state ["valueInput"]
          · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, viewValue]
          · exact symbol_returns program callee state "LNil"
  | cons first rest ih =>
      rw [body_shape]
      let bindings := environment (first :: rest)
      let viewed := ("view", viewValue (first :: rest)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue (first :: rest)) _
      · exact ListAccess.view_captured_returns bindings state "values" (first :: rest) rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment (first :: rest)) state state
          "mm0:substitution-values-view" ["view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause (first :: rest)
        · rw [view_body_shape]
          let callee := viewEnvironment (first :: rest)
          let bound := ("rest", listValue rest) :: ("first", first) :: callee
          apply case_returns program callee bound state state state (.expression [.var "valueInput"])
            (.expression [viewValue (first :: rest)]) consBody _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program callee state ["valueInput"]
          · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, listValue, bound, callee, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let converted := ("substitutionValuesResult", linkedValue rest) :: bound
            apply let_returns program bound converted state state state (.var "substitutionValuesResult") _ _ (linkedValue rest) _
            · exact call_from_body bound state rest "rest" rfl ih
            · simp [SourceProgram.matchValue, matchAtom, converted, bound, callee, viewEnvironment, Subst.lookup]
            · simpa [converted, bound, callee, viewEnvironment, applySubst, Subst.lookup, linkedValue] using
                constructor_variables_return program converted state "LCons" ["first", "substitutionValuesResult"] (by decide +kernel) (by decide)

theorem captured_returns (bindings : Subst) (state : State) (values : List Atom) (name : String)
    (captured : applySubst bindings (.var name) = listValue values) :
    PureReturns program bindings state (.expression [.symbol "mm0:substitution-values", .var name]) state (linkedValue values) :=
  call_from_body bindings state values name captured (body_returns state values)

/-! ## Dummy variable images -/

private def imagesEquation : SourceProgram.Equation := (kernelSource.program.equations.take 73)[72]'(by decide)
private def imagesViewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 74)[73]'(by decide)
private def imagesEnvironment (images : List Nat) : Subst := [("images", listValue (images.map Store.natural))]
private def imagesViewEnvironment (images : List Nat) : Subst := [("valueInput", viewValue (images.map Store.natural))]
private def imagesCases : SourceProgram.Cases :=
  match imagesViewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def imagesConsBody : Atom := (imagesCases[1]'(by decide)).2
private theorem images_unique : program.equations.filter (fun e => e.head == "mm0:variable-images") = [imagesEquation] := by decide
private theorem images_view_unique : program.equations.filter (fun e => e.head == "mm0:variable-images-view") = [imagesViewEquation] := by decide
private theorem images_formals : imagesEquation.arguments = [.var "images"] := by decide
private theorem images_view_formals : imagesViewEquation.arguments = [.var "valueInput"] := by decide
private theorem images_body_shape : imagesEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "images"],
      .expression [.symbol "mm0:variable-images-view", .var "view"]] := by decide
private theorem images_view_body_shape : imagesViewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"],
      .expression (imagesCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem images_cases_shape : imagesCases = [(.expression [.symbol "List:Nil"], listValue []),
    (.expression [.expression [.symbol "List:Cons", .var "first", .var "rest"]], imagesConsBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem images_cons_body_shape : imagesConsBody =
    .expression [.symbol "let", .var "var", .expression [.symbol "MM0:Var", .var "first"],
      .expression [.symbol "let", .var "variableImagesResult", .expression [.symbol "mm0:variable-images", .var "rest"],
        .expression [.symbol "mm0:list-cons", .var "var", .var "variableImagesResult"]]] := by decide
private theorem images_clause (images : List Nat) :
    clauses program "mm0:variable-images" [listValue (images.map Store.natural)] =
      [.evaluate (imagesEnvironment images) imagesEquation.body] := by
  rw [clauses_use_only_the_named_equations, images_unique]
  simp [images_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, imagesEnvironment]
private theorem images_view_clause (images : List Nat) :
    clauses program "mm0:variable-images-view" [viewValue (images.map Store.natural)] =
      [.evaluate (imagesViewEnvironment images) imagesViewEquation.body] := by
  rw [clauses_use_only_the_named_equations, images_view_unique]
  simp [images_view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, imagesViewEnvironment]
private theorem images_call_from_body (bindings : Subst) (state : State) (images : List Nat) (name : String)
    (captured : applySubst bindings (.var name) = listValue (images.map Store.natural))
    (computed : PureReturns program (imagesEnvironment images) state imagesEquation.body state
      (listValue (images.map fun i => Data.preterm (.var i)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:variable-images", .var name]) state
      (listValue (images.map fun i => Data.preterm (.var i))) := by
  apply authored_variable_call_returns program bindings (imagesEnvironment images) state state
    "mm0:variable-images" [name] imagesEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [captured] using images_clause images

theorem variable_images_body_returns (state : State) (images : List Nat) :
    PureReturns program (imagesEnvironment images) state imagesEquation.body state
      (listValue (images.map fun i => Data.preterm (.var i))) := by
  induction images with
  | nil =>
      rw [images_body_shape]
      let bindings := imagesEnvironment []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "images" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, imagesEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (imagesViewEnvironment []) state state
          "mm0:variable-images-view" ["view"] imagesViewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, imagesEnvironment, applySubst, Subst.lookup] using images_view_clause []
        · rw [images_view_body_shape]
          let callee := imagesViewEnvironment []
          apply case_returns program callee callee state state state (.expression [.var "valueInput"])
            (.expression [viewValue []]) (listValue []) _ _ imagesCases (read_cases_encoded imagesCases)
          · simpa [callee, imagesViewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program callee state ["valueInput"]
          · simp [images_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, viewValue]
          · exact empty_constructor_returns program callee state "MM0:L" (by decide +kernel) (by decide)
  | cons first rest ih =>
      rw [images_body_shape]
      let bindings := imagesEnvironment (first :: rest)
      let viewed := ("view", viewValue ((first :: rest).map Store.natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((first :: rest).map Store.natural)) _
      · exact ListAccess.view_captured_returns bindings state "images" ((first :: rest).map Store.natural) rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, imagesEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (imagesViewEnvironment (first :: rest)) state state
          "mm0:variable-images-view" ["view"] imagesViewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, imagesEnvironment, applySubst, Subst.lookup] using images_view_clause (first :: rest)
        · rw [images_view_body_shape]
          let callee := imagesViewEnvironment (first :: rest)
          let bound := ("rest", listValue (rest.map Store.natural)) :: ("first", Store.natural first) :: callee
          apply case_returns program callee bound state state state (.expression [.var "valueInput"])
            (.expression [viewValue ((first :: rest).map Store.natural)]) imagesConsBody _ _ imagesCases (read_cases_encoded imagesCases)
          · simpa [callee, imagesViewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program callee state ["valueInput"]
          · simp [images_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, listValue, bound, callee, imagesViewEnvironment, Subst.lookup]
          · rw [images_cons_body_shape]
            let withVariable := ("var", Data.preterm (.var first)) :: bound
            apply let_returns program bound withVariable state state state (.var "var") _ _ (Data.preterm (.var first)) _
            · simpa [Data.preterm, withVariable, bound, applySubst, Subst.lookup] using
                unary_constructor_returns program bound state "MM0:Var" "first" (by decide +kernel) (by decide)
            · simp [SourceProgram.matchValue, matchAtom, withVariable, bound, callee, imagesViewEnvironment, Subst.lookup]
            · let converted := ("variableImagesResult", listValue (rest.map fun i => Data.preterm (.var i))) :: withVariable
              apply let_returns program withVariable converted state state state (.var "variableImagesResult") _ _
                (listValue (rest.map fun i => Data.preterm (.var i))) _
              · exact images_call_from_body withVariable state rest "rest" rfl ih
              · simp [SourceProgram.matchValue, matchAtom, converted, withVariable, bound, callee, imagesViewEnvironment, Subst.lookup]
              · exact ListAccess.cons_captured_returns converted state (Data.preterm (.var first))
                  (rest.map fun i => Data.preterm (.var i)) "var" "variableImagesResult" rfl rfl

theorem variable_images_captured_returns (bindings : Subst) (state : State) (images : List Nat) (name : String)
    (captured : applySubst bindings (.var name) = listValue (images.map Store.natural)) :
    PureReturns program bindings state (.expression [.symbol "mm0:variable-images", .var name]) state
      (listValue (images.map fun i => Data.preterm (.var i))) :=
  images_call_from_body bindings state images name captured (variable_images_body_returns state images)

end Mettapedia.Languages.MM0.MeTTa.SubstitutionValues
