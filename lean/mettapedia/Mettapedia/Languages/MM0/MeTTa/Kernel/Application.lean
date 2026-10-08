import Mettapedia.Languages.MM0.MeTTa.Data.Data

/-!
# Ordered argument application in the retained MM0 source

The source folds the supplied argument list into applications. Order and
repeated arguments are retained, and no inference or proof search is involved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Application

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Kernel (Preterm)
open ListAccess (listValue viewValue)

private def argumentsValue (arguments : List Preterm) : Atom := listValue (arguments.map Data.preterm)
private def equation : SpaceSemantics.Equation := (kernelSource.program.equations.take 156)[155]'(by decide +kernel)
private def viewEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 157)[156]'(by decide +kernel)
private def environment (function : Preterm) (arguments : List Preterm) : Subst :=
  [("arguments", argumentsValue arguments), ("function", Data.preterm function)]
private def viewEnvironment (function : Preterm) (arguments : List Preterm) : Subst :=
  [("valueInput", viewValue (arguments.map Data.preterm)), ("function", Data.preterm function)]
private def cases : SpaceSemantics.Cases :=
  match viewEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := (cases[1]'(by decide)).2
private theorem unique : program.equations.filter (fun e => e.head == "mm0:apply-args") = [equation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:apply-args-view") = [viewEquation] := by decide
private theorem formals : equation.arguments = [.var "function", .var "arguments"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "function", .var "valueInput"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "arguments"],
      .expression [.symbol "mm0:apply-args-view", .var "function", .var "view"]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun e => .expression [e.1,e.2])] := by decide
private theorem cases_shape : cases = [(.symbol "List:Nil", .var "function"),
    (.expression [.symbol "List:Cons", .var "argument", .var "arguments"], consBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "app", .expression [.symbol "MM0:App", .var "function", .var "argument"],
      .expression [.symbol "mm0:apply-args", .var "app", .var "arguments"]] := by decide
private theorem clause (function : Preterm) (arguments : List Preterm) :
    clauses program "mm0:apply-args" [Data.preterm function, argumentsValue arguments] =
      [.evaluate (environment function arguments) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]
private theorem view_clause (function : Preterm) (arguments : List Preterm) :
    clauses program "mm0:apply-args-view" [Data.preterm function, viewValue (arguments.map Data.preterm)] =
      [.evaluate (viewEnvironment function arguments) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]
private theorem call_from_body (bindings : Subst) (state : State) (function : Preterm) (arguments : List Preterm)
    (functionName argumentsName : String)
    (capturedFunction : applySubst bindings (.var functionName) = Data.preterm function)
    (capturedArguments : applySubst bindings (.var argumentsName) = argumentsValue arguments)
    (computed : PureReturns program (environment function arguments) state equation.body state (Data.preterm (Preterm.applyArgs function arguments))) :
    PureReturns program bindings state (.expression [.symbol "mm0:apply-args", .var functionName, .var argumentsName]) state
      (Data.preterm (Preterm.applyArgs function arguments)) := by
  apply authored_variable_call_returns program bindings (environment function arguments) state state
    "mm0:apply-args" [functionName, argumentsName] equation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedFunction, capturedArguments] using clause function arguments

theorem body_returns (state : State) (function : Preterm) (arguments : List Preterm) :
    PureReturns program (environment function arguments) state equation.body state (Data.preterm (Preterm.applyArgs function arguments)) := by
  induction arguments generalizing function with
  | nil =>
      rw [body_shape]
      let bindings := environment function []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "arguments" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment function []) state state
          "mm0:apply-args-view" ["function", "view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause function []
        · rw [view_body_shape]
          let callee := viewEnvironment function []
          apply case_returns program callee callee state state state (.var "valueInput") (viewValue []) (.var "function") _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · simpa [Preterm.applyArgs, callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "function"
  | cons first rest ih =>
      rw [body_shape]
      let bindings := environment function (first :: rest)
      let viewed := ("view", viewValue ((first :: rest).map Data.preterm)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((first :: rest).map Data.preterm)) _
      · exact ListAccess.view_captured_returns bindings state "arguments" ((first :: rest).map Data.preterm) rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment function (first :: rest)) state state
          "mm0:apply-args-view" ["function", "view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause function (first :: rest)
        · rw [view_body_shape]
          let callee := viewEnvironment function (first :: rest)
          let bound := ("arguments", argumentsValue rest) :: ("argument", Data.preterm first) :: callee
          apply case_returns program callee bound state state state (.var "valueInput") (viewValue ((first :: rest).map Data.preterm)) consBody _ _ cases (read_cases_encoded cases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, viewValue, bound, argumentsValue, callee, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let applied := ("app", Data.preterm (.app function first)) :: bound
            apply let_returns program bound applied state state state (.var "app") _ _ (Data.preterm (.app function first)) _
            · simpa [Data.preterm, bound, callee, viewEnvironment, applySubst, Subst.lookup] using
                constructor_variables_return program bound state "MM0:App" ["function", "argument"] (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, applied, bound, callee, viewEnvironment, Subst.lookup]
            · exact call_from_body applied state (.app function first) rest "app" "arguments" rfl rfl (ih _)

theorem captured_returns (bindings : Subst) (state : State) (function : Preterm) (arguments : List Preterm)
    (functionName argumentsName : String)
    (capturedFunction : applySubst bindings (.var functionName) = Data.preterm function)
    (capturedArguments : applySubst bindings (.var argumentsName) = listValue (arguments.map Data.preterm)) :
    PureReturns program bindings state (.expression [.symbol "mm0:apply-args", .var functionName, .var argumentsName]) state
      (Data.preterm (Preterm.applyArgs function arguments)) :=
  call_from_body bindings state function arguments functionName argumentsName capturedFunction capturedArguments (body_returns state function arguments)

end Mettapedia.Languages.MM0.MeTTa.Application
