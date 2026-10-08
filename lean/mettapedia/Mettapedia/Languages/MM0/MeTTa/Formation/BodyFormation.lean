import Mettapedia.Languages.MM0.MeTTa.Formation.DummyFormation
import Mettapedia.Languages.MM0.MeTTa.Kernel.Inference
import Mettapedia.Languages.MM0.MeTTa.Kernel.FreeVariables
import Mettapedia.Languages.MM0.MeTTa.Kernel.Dependencies
import Mettapedia.Languages.MM0.MeTTa.Kernel.NaturalDifference
import Mettapedia.Languages.MM0.MeTTa.Kernel.Unfolding
import Mettapedia.Languages.MM0.Presentation.FreeVariablesData

/-!
# Definition-body formation in the retained MM0 source

The source extends the preceding context with dummy binders, checks the
body type, and excludes residual free variables outside the declared return
dependencies. The component executions below use equations projected from
the digest-checked program. A failed dummy or typing check stops before the
later source calls. Successful type inference may populate its cache while
preserving the term table and the remaining stores.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.MeTTa.BodyFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Context Preterm Binder TermDecl SortInfo)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open Support (indicesValue resultValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open Presentation.ComputationalFreeVariables (subtract)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []

namespace DummyContext

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 79)[78]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 80)[79]'(by decide)
private def cases := casesOf viewEquation.body
private def consBody := (cases[1]'(by decide)).2
private def environment (dummies : List Nat) : Subst := [("sorts", indicesValue dummies)]

private theorem unique :
    program.equations.filter (fun e => e.head == "mm0:dummy-context") = [equation] := by decide
private theorem view_unique :
    program.equations.filter (fun e => e.head == "mm0:dummy-context-view") = [viewEquation] := by decide
private theorem formals : equation.arguments = [.var "sorts"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput"] := by decide
private theorem shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "sorts"],
      .expression [.symbol "mm0:dummy-context-view", .var "view"]] := by decide
private theorem view_shape : viewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"],
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (.expression [.symbol "List:Nil"], .expression [.symbol "MM0:L", .expression []]),
    (.expression [.expression [.symbol "List:Cons", .var "sort", .var "rest"]], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_shape : consBody =
    .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
      .expression [.symbol "let", .var "dummyContextResult", .expression [.symbol "mm0:dummy-context", .var "rest"],
        .expression [.symbol "mm0:list-cons", .var "items", .var "dummyContextResult"]]] := by decide

private theorem clause (dummies : List Nat) :
    clauses program "mm0:dummy-context" [indicesValue dummies] =
      [.evaluate (environment dummies) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem view_clause (dummies : List Nat) :
    clauses program "mm0:dummy-context-view" [viewValue (dummies.map natural)] =
      [.evaluate [("valueInput", viewValue (dummies.map natural))] viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup]

theorem body_returns (state : State) (dummies : List Nat) :
    PureReturns program (environment dummies) state equation.body state
      (Data.context (dummies.map Binder.bound)) := by
  induction dummies with
  | nil =>
      rw [shape]
      let bindings := environment []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "sorts" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed [("valueInput", viewValue [])] state state
          "mm0:dummy-context-view" ["view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause []
        · rw [view_shape]
          apply case_returns program [("valueInput", viewValue [])] [("valueInput", viewValue [])] state state state
            (.expression [.var "valueInput"]) (.expression [viewValue []])
            (.expression [.symbol "MM0:L", .expression []]) _ _ cases (read_cases_encoded _)
          · simpa [applySubst, Subst.lookup] using
              tuple_variables_return program [("valueInput", viewValue [])] state ["valueInput"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
          · exact empty_constructor_returns program _ state "MM0:L" list_is_data_constructor (by decide)
  | cons sort dummies recursive =>
      rw [shape]
      let bindings := environment (sort :: dummies)
      let viewed := ("view", viewValue ((sort :: dummies).map natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((sort :: dummies).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "sorts" _ rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · let callee : Subst := [("valueInput", viewValue ((sort :: dummies).map natural))]
        apply authored_variable_call_returns program viewed callee state state
          "mm0:dummy-context-view" ["view"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [callee, viewed, bindings, environment, applySubst, Subst.lookup] using view_clause (sort :: dummies)
        · rw [view_shape]
          let bound := ("rest", indicesValue dummies) :: ("sort", natural sort) :: callee
          apply case_returns program callee bound state state state (.expression [.var "valueInput"])
            (.expression [viewValue ((sort :: dummies).map natural)]) consBody _ _ cases (read_cases_encoded _)
          · simpa [callee, applySubst, Subst.lookup] using
              tuple_variables_return program callee state ["valueInput"]
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, callee, bound, indicesValue, Subst.lookup]
          · rw [cons_shape]
            let withBinder := ("items", Data.binder (.bound sort)) :: bound
            apply let_returns program bound withBinder state state state (.var "items") _ _ (Data.binder (.bound sort)) _
            · apply unary_constructor_of_returns program bound state state "MM0:L" _ _
                list_is_data_constructor (by decide)
              simpa [bound, callee, applySubst, Subst.lookup] using
                unary_constructor_returns program bound state "MM0:Bound" "sort" (by decide) (by decide)
            · simp [SpaceSemantics.matchValue, matchAtom, withBinder, bound, callee, Subst.lookup]
            · let completed := ("dummyContextResult", Data.context (dummies.map Binder.bound)) :: withBinder
              apply let_returns program withBinder completed state state state (.var "dummyContextResult") _ _
                (Data.context (dummies.map Binder.bound)) _
              · apply authored_variable_call_returns program withBinder (environment dummies) state state
                  "mm0:dummy-context" ["rest"] equation.body _ (by decide) (by decide) (by decide) _ recursive (by decide)
                simpa [withBinder, bound, callee, applySubst, Subst.lookup] using clause dummies
              · simp [SpaceSemantics.matchValue, matchAtom, completed, withBinder, bound, callee, Subst.lookup]
              · simpa [Data.context] using ListAccess.cons_captured_returns completed state
                  (Data.binder (.bound sort)) ((dummies.map Binder.bound).map Data.binder)
                  "items" "dummyContextResult" rfl rfl

theorem captured_returns (bindings : Subst) (state : State) (dummies : List Nat) (name : String)
    (captured : applySubst bindings (.var name) = indicesValue dummies) :
    PureReturns program bindings state (.expression [.symbol "mm0:dummy-context", .var name]) state
      (Data.context (dummies.map Binder.bound)) := by
  apply authored_variable_call_returns program bindings (environment dummies) state state
    "mm0:dummy-context" [name] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns state dummies) (by decide)
  simpa [captured] using clause dummies

end DummyContext

namespace FreeResult

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 182)[181]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 183)[182]'(by decide)
private def cases := casesOf equation.body
private def viewCases := casesOf viewEquation.body
private def someBody := (cases[1]'(by decide)).2
private def environment (result : Option (List Nat)) (deps : Finset Nat) : Subst :=
  [("deps", Data.dependencies deps), ("valueInput", resultValue result)]
private def viewEnvironment (indices : List Nat) : Subst :=
  [("valueInput", viewValue (indices.map natural))]

private theorem unique :
    program.equations.filter (fun e => e.head == "mm0:body-free") = [equation] := by decide
private theorem view_unique :
    program.equations.filter (fun e => e.head == "mm0:body-free-view") = [viewEquation] := by decide
private theorem formals : equation.arguments = [.var "valueInput", .var "deps"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput"] := by decide
private theorem shape : equation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (.symbol "None", boolean false),
    (.expression [.symbol "Some", .var "free"], someBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem some_shape : someBody =
    .expression [.symbol "let", .var "view",
      .expression [.symbol "let", .var "natDifferenceResult", .expression [.symbol "mm0:nat-difference", .var "free", .var "deps"],
        .expression [.symbol "mm0:list-view", .var "natDifferenceResult"]],
      .expression [.symbol "mm0:body-free-view", .var "view"]] := by decide
private theorem view_shape : viewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"], .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem view_cases : viewCases = [
    (.expression [.symbol "List:Nil"], boolean true),
    (.expression [.expression [.symbol "List:Cons", .var "first", .var "rest"]], boolean false),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem clause (result : Option (List Nat)) (deps : Finset Nat) :
    clauses program "mm0:body-free" [resultValue result, Data.dependencies deps] =
      [.evaluate (environment result deps) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]
private theorem view_clause (indices : List Nat) :
    clauses program "mm0:body-free-view" [viewValue (indices.map natural)] =
      [.evaluate (viewEnvironment indices) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, viewEnvironment]

private theorem view_body_returns (state : State) (indices : List Nat) :
    PureReturns program (viewEnvironment indices) state viewEquation.body state
      (boolean (decide (indices = []))) := by
  rw [view_shape]
  cases indices with
  | nil =>
      apply case_returns program (viewEnvironment []) (viewEnvironment []) state state state
        (.expression [.var "valueInput"]) (.expression [viewValue []]) (boolean true)
        _ _ viewCases (read_cases_encoded _)
      · simpa [viewEnvironment, applySubst, Subst.lookup] using
          tuple_variables_return program (viewEnvironment []) state ["valueInput"]
      · simp [view_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
      · exact grounded_returns program _ state (.bool true)
  | cons first rest =>
      let bindings := viewEnvironment (first :: rest)
      let bound := ("rest", indicesValue rest) :: ("first", natural first) :: bindings
      apply case_returns program bindings bound state state state
        (.expression [.var "valueInput"]) (.expression [viewValue ((first :: rest).map natural)]) (boolean false)
        _ _ viewCases (read_cases_encoded _)
      · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using
          tuple_variables_return program bindings state ["valueInput"]
      · simp [view_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, bound, bindings,
          viewEnvironment, indicesValue, Subst.lookup]
      · exact grounded_returns program _ state (.bool false)

theorem subtract_empty_iff_subset (indices : List Nat) (deps : Finset Nat) :
    subtract indices (deps.sort (· ≤ ·)) = [] ↔ indices.toFinset ⊆ deps := by
  rw [← List.toFinset_eq_empty_iff, Presentation.ComputationalFreeVariables.subtract_meaning,
    Finset.sort_toFinset, Finset.sdiff_eq_empty_iff_subset]

theorem body_returns (state : State) (result : Option (List Nat)) (deps : Finset Nat) :
    PureReturns program (environment result deps) state equation.body state
      (boolean (result.any fun indices => decide (indices.toFinset ⊆ deps))) := by
  rw [shape]
  cases result with
  | none =>
      apply case_returns program (environment none deps) (environment none deps) state state state
        (.var "valueInput") (.symbol "None") (boolean false) _ _ cases (read_cases_encoded _)
      · exact variable_returns program _ state "valueInput"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program _ state (.bool false)
  | some indices =>
      let bindings := environment (some indices) deps
      let bound := ("free", indicesValue indices) :: bindings
      apply case_returns program bindings bound state state state
        (.var "valueInput") (resultValue (some indices)) someBody _ _ cases (read_cases_encoded _)
      · exact variable_returns program _ state "valueInput"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, environment, Subst.lookup]
      · rw [some_shape]
        let remaining := subtract indices (deps.sort (· ≤ ·))
        let viewed := ("view", viewValue (remaining.map natural)) :: bound
        apply let_returns program bound viewed state state state (.var "view") _ _ (viewValue (remaining.map natural)) _
        · let computed := ("natDifferenceResult", indicesValue remaining) :: bound
          apply let_returns program bound computed state state state (.var "natDifferenceResult") _ _
            (indicesValue remaining) _
          · exact NaturalDifference.captured_returns bound state indices (deps.sort (· ≤ ·)) "free" "deps" rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, computed, bound, bindings, environment, Subst.lookup]
          · exact ListAccess.view_captured_returns computed state "natDifferenceResult" (remaining.map natural) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bound, bindings, environment, Subst.lookup]
        · have same : decide (remaining = []) = decide (indices.toFinset ⊆ deps) :=
            decide_eq_decide.mpr (subtract_empty_iff_subset indices deps)
          simp only [Option.any_some]
          rw [← same]
          apply authored_variable_call_returns program viewed (viewEnvironment remaining) state state
            "mm0:body-free-view" ["view"] viewEquation.body _
            (by decide) (by decide) (by decide) _ (view_body_returns state remaining) (by decide)
          simpa [viewed, bound, bindings, environment, applySubst, Subst.lookup] using view_clause remaining

theorem captured_returns (bindings : Subst) (state : State) (result : Option (List Nat))
    (deps : Finset Nat) (resultName depsName : String)
    (capturedResult : applySubst bindings (.var resultName) = resultValue result)
    (capturedDeps : applySubst bindings (.var depsName) = Data.dependencies deps) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:body-free", .var resultName, .var depsName]) state
      (boolean (result.any fun indices => decide (indices.toFinset ⊆ deps))) := by
  apply authored_variable_call_returns program bindings (environment result deps) state state
    "mm0:body-free" [resultName, depsName] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns state result deps) (by decide)
  simpa [capturedResult, capturedDeps] using clause result deps

end FreeResult

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 114)[113]'(by decide)
private def dummiesEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 184)[183]'(by decide)
private def contextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 185)[184]'(by decide)
private def typedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 186)[185]'(by decide)
private def cases := casesOf equation.body
private def dummiesCases := casesOf dummiesEquation.body
private def typedCases := casesOf typedEquation.body
private def presentBody := (cases[0]'(by decide)).2
private def checkedDummiesBody := (dummiesCases[1]'(by decide)).2
private def checkedTypeBody := (typedCases[1]'(by decide)).2
private def environment (sorts terms : Atom) (declaration : TermDecl) (body : Kernel.Definition.Body) : Subst :=
  [("valueInputValue", Unfolding.bodyValue body), ("valueInput", Data.declaration declaration),
    ("table", terms), ("sorts", sorts)]
private def dummiesEnvironment (checked : Bool) (terms : Atom) (declaration : TermDecl)
    (body : Kernel.Definition.Body) : Subst :=
  [("expression", Data.preterm body.expression), ("dummies", indicesValue body.dummies),
    ("deps", Data.dependencies declaration.dependencies), ("sort", natural declaration.resultSort),
    ("context", Data.context declaration.arguments), ("table", terms), ("conditionInput", boolean checked)]
private def contextEnvironment (terms : Atom) (context : Context) (sort : Nat) (deps : Finset Nat)
    (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("deps", Data.dependencies deps),
    ("sort", natural sort), ("context", Data.context context), ("table", terms)]
private def typedEnvironment (checked : Bool) (terms : Atom) (context : Context)
    (deps : Finset Nat) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("deps", Data.dependencies deps),
    ("context", Data.context context), ("table", terms), ("conditionInput", boolean checked)]

private theorem unique :
    program.equations.filter (fun e => e.head == "mm0:form-body") = [equation] := by decide
private theorem dummies_unique :
    program.equations.filter (fun e => e.head == "mm0:body-dummies") = [dummiesEquation] := by decide
private theorem context_unique :
    program.equations.filter (fun e => e.head == "mm0:body-context") = [contextEquation] := by decide
private theorem typed_unique :
    program.equations.filter (fun e => e.head == "mm0:body-typed") = [typedEquation] := by decide
private theorem formals : equation.arguments =
    [.var "sorts", .var "table", .var "valueInput", .var "valueInputValue"] := by decide
private theorem dummies_formals : dummiesEquation.arguments =
    [.var "conditionInput", .var "table", .var "context", .var "sort", .var "deps", .var "dummies", .var "expression"] := by decide
private theorem context_formals : contextEquation.arguments =
    [.var "table", .var "context", .var "sort", .var "deps", .var "expression"] := by decide
private theorem typed_formals : typedEquation.arguments =
    [.var "conditionInput", .var "table", .var "context", .var "deps", .var "expression"] := by decide
private theorem shape : equation.body =
    .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (.expression [listValue [.symbol "MM0:TermDecl", .var "context", .var "sort", .var "deps"],
      listValue [.symbol "MM0:Definition", .var "dummies", .var "expression"]], presentBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem present_shape : presentBody =
    .expression [.symbol "let", .var "formDummiesResult", .expression [.symbol "mm0:form-dummies", .var "sorts", .var "dummies"],
      .expression [.symbol "mm0:body-dummies", .var "formDummiesResult", .var "table", .var "context", .var "sort", .var "deps", .var "dummies", .var "expression"]] := by decide
private theorem dummies_shape : dummiesEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (dummiesCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem dummies_cases : dummiesCases = [
    (boolean false, boolean false), (boolean true, checkedDummiesBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem checked_dummies_shape : checkedDummiesBody =
    .expression [.symbol "let", .var "combined",
      .expression [.symbol "let", .var "dummyContextResult", .expression [.symbol "mm0:dummy-context", .var "dummies"],
        .expression [.symbol "mm0:list-append", .var "context", .var "dummyContextResult"]],
      .expression [.symbol "mm0:body-context", .var "table", .var "combined", .var "sort", .var "deps", .var "expression"]] := by decide
private theorem context_shape : contextEquation.body =
    .expression [.symbol "let", .var "equal",
      .expression [.symbol "let", .var "inferred", .expression [.symbol "mm0:infer", .var "table", .var "context", .var "expression"],
        .expression [.symbol "let", .var "inferred2",
          .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []],
            .expression [.symbol "MM0:Inferred", .var "items", .var "sort"]],
          .expression [.symbol "mm0:data-eq", .var "inferred", .var "inferred2"]]],
      .expression [.symbol "mm0:body-typed", .var "equal", .var "table", .var "context", .var "deps", .var "expression"]] := by decide
private theorem typed_shape : typedEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (typedCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem typed_cases : typedCases = [
    (boolean false, boolean false), (boolean true, checkedTypeBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem checked_type_shape : checkedTypeBody =
    .expression [.symbol "let", .var "freeVariablesResult", .expression [.symbol "mm0:free-variables", .var "table", .var "context", .var "expression"],
      .expression [.symbol "mm0:body-free", .var "freeVariablesResult", .var "deps"]] := by decide

private theorem clause (sorts terms : Atom) (declaration : TermDecl) (body : Kernel.Definition.Body) :
    clauses program "mm0:form-body" [sorts, terms, Data.declaration declaration, Unfolding.bodyValue body] =
      [.evaluate (environment sorts terms declaration body) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]
private theorem dummies_clause (checked : Bool) (terms : Atom) (declaration : TermDecl)
    (body : Kernel.Definition.Body) :
    clauses program "mm0:body-dummies" [boolean checked, terms, Data.context declaration.arguments,
      natural declaration.resultSort, Data.dependencies declaration.dependencies, indicesValue body.dummies, Data.preterm body.expression] =
      [.evaluate (dummiesEnvironment checked terms declaration body) dummiesEquation.body] := by
  rw [clauses_use_only_the_named_equations, dummies_unique]
  simp [dummies_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, dummiesEnvironment]
private theorem context_clause (terms : Atom) (context : Context) (sort : Nat) (deps : Finset Nat)
    (expression : Preterm) :
    clauses program "mm0:body-context" [terms, Data.context context, natural sort, Data.dependencies deps, Data.preterm expression] =
      [.evaluate (contextEnvironment terms context sort deps expression) contextEquation.body] := by
  rw [clauses_use_only_the_named_equations, context_unique]
  simp [context_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, contextEnvironment]
private theorem typed_clause (checked : Bool) (terms : Atom) (context : Context) (deps : Finset Nat)
    (expression : Preterm) :
    clauses program "mm0:body-typed" [boolean checked, terms, Data.context context, Data.dependencies deps, Data.preterm expression] =
      [.evaluate (typedEnvironment checked terms context deps expression) typedEquation.body] := by
  rw [clauses_use_only_the_named_equations, typed_unique]
  simp [typed_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, typedEnvironment]

/-- A completed negative type comparison stops without calling the free-variable
traversal. This statement needs no coherent inference cache. -/
theorem typed_false_body_returns (state : State) (terms : Atom) (context : Context)
    (deps : Finset Nat) (expression : Preterm) :
    PureReturns program (typedEnvironment false terms context deps expression) state typedEquation.body state (boolean false) := by
  rw [typed_shape]
  apply case_returns program (typedEnvironment false terms context deps expression)
    (typedEnvironment false terms context deps expression) state state state (.var "conditionInput") (boolean false) (boolean false)
    _ _ typedCases (read_cases_encoded _)
  · exact variable_returns program _ state "conditionInput"
  · simp [typed_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · exact grounded_returns program _ state (.bool false)

/-- A rejected dummy-sort check stops before constructing or checking a body
context. The source state, including a missing or incoherent cache, is retained. -/
theorem dummies_false_body_returns (state : State) (terms : Atom) (declaration : TermDecl)
    (body : Kernel.Definition.Body) :
    PureReturns program (dummiesEnvironment false terms declaration body) state dummiesEquation.body state (boolean false) := by
  rw [dummies_shape]
  apply case_returns program (dummiesEnvironment false terms declaration body)
    (dummiesEnvironment false terms declaration body) state state state (.var "conditionInput") (boolean false) (boolean false)
    _ _ dummiesCases (read_cases_encoded _)
  · exact variable_returns program _ state "conditionInput"
  · simp [dummies_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · exact grounded_returns program _ state (.bool false)

private theorem typed_captured_of_body (bindings : Subst) (before after : State) (checked : Bool)
    (terms : Atom) (context : Context) (deps : Finset Nat) (expression : Preterm) (answer : Atom)
    (checkedName termsName contextName depsName expressionName : String)
    (capturedChecked : applySubst bindings (.var checkedName) = boolean checked)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedDeps : applySubst bindings (.var depsName) = Data.dependencies deps)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression)
    (computed : PureReturns program (typedEnvironment checked terms context deps expression) before typedEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:body-typed", .var checkedName, .var termsName, .var contextName, .var depsName, .var expressionName]) after answer := by
  apply authored_variable_call_returns program bindings (typedEnvironment checked terms context deps expression)
    before after "mm0:body-typed" [checkedName, termsName, contextName, depsName, expressionName] typedEquation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedChecked, capturedTerms, capturedContext, capturedDeps, capturedExpression] using
    typed_clause checked terms context deps expression

private theorem typed_true_body_of_free_path (before after : State) (terms : Atom) (context : Context)
    (deps : Finset Nat) (expression : Preterm) (result : Option (List Nat))
    (freePath : ∀ bindings termsName contextName expressionName,
      applySubst bindings (.var termsName) = terms →
      applySubst bindings (.var contextName) = Data.context context →
      applySubst bindings (.var expressionName) = Data.preterm expression →
      PureReturns program bindings before
        (.expression [.symbol "mm0:free-variables", .var termsName, .var contextName, .var expressionName]) after (resultValue result)) :
    PureReturns program (typedEnvironment true terms context deps expression) before typedEquation.body after
      (boolean (result.any fun indices => decide (indices.toFinset ⊆ deps))) := by
  rw [typed_shape]
  let bindings := typedEnvironment true terms context deps expression
  apply case_returns program bindings bindings before before after (.var "conditionInput") (boolean true) checkedTypeBody
    _ _ typedCases (read_cases_encoded _)
  · exact variable_returns program _ before "conditionInput"
  · simp [typed_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · rw [checked_type_shape]
    let computed := ("freeVariablesResult", resultValue result) :: bindings
    apply let_returns program bindings computed before after after (.var "freeVariablesResult") _ _ (resultValue result) _
    · exact freePath bindings "table" "context" "expression" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, computed, bindings, typedEnvironment, Subst.lookup]
    · exact FreeResult.captured_returns computed after result deps "freeVariablesResult" "deps" rfl rfl

private theorem context_body_of_paths (before inferredState after : State) (terms : Atom)
    (context : Context) (sort : Nat) (deps : Finset Nat) (expression : Preterm)
    (inferred : Option Kernel.ExpressionType) (answer : Atom)
    (inferPath : ∀ bindings termsName contextName expressionName,
      applySubst bindings (.var termsName) = terms →
      applySubst bindings (.var contextName) = Data.context context →
      applySubst bindings (.var expressionName) = Data.preterm expression →
      PureReturns program bindings before
        (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
        inferredState (Data.inferred inferred))
    (handled : PureReturns program (typedEnvironment (decide (inferred = some ([], sort))) terms context deps expression)
      inferredState typedEquation.body after answer) :
    PureReturns program (contextEnvironment terms context sort deps expression) before contextEquation.body after answer := by
  rw [context_shape]
  let bindings := contextEnvironment terms context sort deps expression
  let compared := ("equal", boolean (decide (inferred = some ([], sort)))) :: bindings
  apply let_returns program bindings compared before inferredState after (.var "equal") _ _
    (boolean (decide (inferred = some ([], sort)))) _
  · let withInferred := ("inferred", Data.inferred inferred) :: bindings
    apply let_returns program bindings withInferred before inferredState inferredState (.var "inferred") _ _
      (Data.inferred inferred) _
    · exact inferPath bindings "table" "context" "expression" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withInferred, bindings, contextEnvironment, Subst.lookup]
    · let expected := ("inferred2", Data.inferred (some ([], sort))) :: withInferred
      apply let_returns program withInferred expected inferredState inferredState inferredState (.var "inferred2") _ _
        (Data.inferred (some ([], sort))) _
      · let withItems := ("items", Data.context []) :: withInferred
        apply let_returns program withInferred withItems inferredState inferredState inferredState (.var "items") _ _
          (Data.context []) _
        · exact empty_constructor_returns program withInferred inferredState "MM0:L" list_is_data_constructor (by decide)
        · simp [SpaceSemantics.matchValue, matchAtom, withItems, withInferred, bindings, contextEnvironment, Subst.lookup]
        · simpa [withItems, withInferred, bindings, contextEnvironment, Data.inferred, applySubst, Subst.lookup] using
            constructor_variables_return program withItems inferredState "MM0:Inferred" ["items", "sort"]
              inferred_is_data_constructor (by decide)
      · simp [SpaceSemantics.matchValue, matchAtom, expected, withInferred, bindings, contextEnvironment, Subst.lookup]
      · simpa only [Data.inferred_injective.eq_iff] using Scalar.data_equality_captured_returns expected inferredState
          (Data.inferred inferred) (Data.inferred (some ([], sort))) "inferred" "inferred2" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, compared, bindings, contextEnvironment, Subst.lookup]
  · exact typed_captured_of_body compared inferredState after _ terms context deps expression answer
      "equal" "table" "context" "deps" "expression" rfl rfl rfl rfl rfl handled

private theorem context_captured_of_body (bindings : Subst) (before after : State) (terms : Atom)
    (context : Context) (sort : Nat) (deps : Finset Nat) (expression : Preterm) (answer : Atom)
    (termsName contextName sortName depsName expressionName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedSort : applySubst bindings (.var sortName) = natural sort)
    (capturedDeps : applySubst bindings (.var depsName) = Data.dependencies deps)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression)
    (computed : PureReturns program (contextEnvironment terms context sort deps expression) before contextEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:body-context", .var termsName, .var contextName, .var sortName, .var depsName, .var expressionName]) after answer := by
  apply authored_variable_call_returns program bindings (contextEnvironment terms context sort deps expression) before after
    "mm0:body-context" [termsName, contextName, sortName, depsName, expressionName] contextEquation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTerms, capturedContext, capturedSort, capturedDeps, capturedExpression] using
    context_clause terms context sort deps expression

private theorem dummies_true_body_of_context_path (before after : State) (terms : Atom)
    (declaration : TermDecl) (body : Kernel.Definition.Body) (answer : Atom)
    (computed : PureReturns program
      (contextEnvironment terms (body.context declaration) declaration.resultSort declaration.dependencies body.expression)
      before contextEquation.body after answer) :
    PureReturns program (dummiesEnvironment true terms declaration body) before dummiesEquation.body after answer := by
  rw [dummies_shape]
  let bindings := dummiesEnvironment true terms declaration body
  apply case_returns program bindings bindings before before after (.var "conditionInput") (boolean true) checkedDummiesBody
    _ _ dummiesCases (read_cases_encoded _)
  · exact variable_returns program _ before "conditionInput"
  · simp [dummies_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · rw [checked_dummies_shape]
    let combined := ("combined", Data.context (body.context declaration)) :: bindings
    apply let_returns program bindings combined before before after (.var "combined") _ _
      (Data.context (body.context declaration)) _
    · let dummyContext := ("dummyContextResult", Data.context (body.dummies.map Binder.bound)) :: bindings
      apply let_returns program bindings dummyContext before before before (.var "dummyContextResult") _ _
        (Data.context (body.dummies.map Binder.bound)) _
      · exact DummyContext.captured_returns bindings before body.dummies "dummies" rfl
      · simp [SpaceSemantics.matchValue, matchAtom, dummyContext, bindings, dummiesEnvironment, Subst.lookup]
      · simpa [Kernel.Definition.Body.context, Data.context] using ListAccess.append_captured_returns dummyContext before
          (declaration.arguments.map Data.binder) ((body.dummies.map Binder.bound).map Data.binder)
          "context" "dummyContextResult" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, combined, bindings, dummiesEnvironment, Subst.lookup]
    · exact context_captured_of_body combined before after terms (body.context declaration) declaration.resultSort
        declaration.dependencies body.expression answer "table" "combined" "sort" "deps" "expression"
        rfl rfl rfl rfl rfl computed

private theorem dummies_captured_of_body (bindings : Subst) (before after : State) (checked : Bool)
    (terms : Atom) (declaration : TermDecl) (body : Kernel.Definition.Body) (answer : Atom)
    (checkedName termsName contextName sortName depsName dummiesName expressionName : String)
    (capturedChecked : applySubst bindings (.var checkedName) = boolean checked)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context declaration.arguments)
    (capturedSort : applySubst bindings (.var sortName) = natural declaration.resultSort)
    (capturedDeps : applySubst bindings (.var depsName) = Data.dependencies declaration.dependencies)
    (capturedDummies : applySubst bindings (.var dummiesName) = indicesValue body.dummies)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm body.expression)
    (computed : PureReturns program (dummiesEnvironment checked terms declaration body) before dummiesEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:body-dummies", .var checkedName, .var termsName, .var contextName, .var sortName,
        .var depsName, .var dummiesName, .var expressionName]) after answer := by
  apply authored_variable_call_returns program bindings (dummiesEnvironment checked terms declaration body) before after
    "mm0:body-dummies" [checkedName, termsName, contextName, sortName, depsName, dummiesName, expressionName] dummiesEquation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedChecked, capturedTerms, capturedContext, capturedSort, capturedDeps, capturedDummies, capturedExpression] using
    dummies_clause checked terms declaration body

private theorem body_of_dummies_path (before after : State) (sorts : Handle) (sortEntries : List (Nat × SortInfo))
    (terms : Atom) (declaration : TermDecl) (body : Kernel.Definition.Body) (answer : Atom)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : before.read sorts = some (SortFormation.rows sortEntries))
    (computed : PureReturns program (dummiesEnvironment (Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies)
      terms declaration body) before dummiesEquation.body after answer) :
    PureReturns program (environment (tableValue sorts) terms declaration body) before equation.body after answer := by
  rw [shape]
  let bindings := environment (tableValue sorts) terms declaration body
  let bound := ("expression", Data.preterm body.expression) :: ("dummies", indicesValue body.dummies) ::
    ("deps", Data.dependencies declaration.dependencies) :: ("sort", natural declaration.resultSort) ::
    ("context", Data.context declaration.arguments) :: bindings
  apply case_returns program bindings bound before before after (.expression [.var "valueInput", .var "valueInputValue"])
    (.expression [Data.declaration declaration, Unfolding.bodyValue body]) presentBody _ _ cases (read_cases_encoded _)
  · simpa [bindings, environment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
  · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Unfolding.bodyValue, Data.declaration,
      indicesValue, listValue, bound, bindings, environment, Subst.lookup]
  · rw [present_shape]
    let checked := ("formDummiesResult", boolean (Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies)) :: bound
    apply let_returns program bound checked before before after (.var "formDummiesResult") _ _
      (boolean (Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies)) _
    · exact DummyFormation.captured_returns bound before sorts sortEntries body.dummies "sorts" "dummies"
        uniqueSorts allocatedSorts rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, environment, Subst.lookup]
    · exact dummies_captured_of_body checked before after _ terms declaration body answer
        "formDummiesResult" "table" "context" "sort" "deps" "dummies" "expression"
        rfl rfl rfl rfl rfl rfl rfl computed

private theorem captured_of_body (bindings : Subst) (before after : State) (sorts terms : Atom)
    (declaration : TermDecl) (body : Kernel.Definition.Body) (answer : Atom)
    (sortsName termsName declarationName bodyName : String)
    (capturedSorts : applySubst bindings (.var sortsName) = sorts)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDeclaration : applySubst bindings (.var declarationName) = Data.declaration declaration)
    (capturedBody : applySubst bindings (.var bodyName) = Unfolding.bodyValue body)
    (computed : PureReturns program (environment sorts terms declaration body) before equation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:form-body", .var sortsName, .var termsName, .var declarationName, .var bodyName]) after answer := by
  apply authored_variable_call_returns program bindings (environment sorts terms declaration body) before after
    "mm0:form-body" [sortsName, termsName, declarationName, bodyName] equation.body answer
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedSorts, capturedTerms, capturedDeclaration, capturedBody] using clause sorts terms declaration body

/-- A bad dummy sort is an immediate completed refusal of body admission,
without inspecting or requiring the term table or the inference cache. -/
theorem rejected_dummies_returns (bindings : Subst) (state : State) (sorts : Handle)
    (sortEntries : List (Nat × SortInfo)) (terms : Atom) (declaration : TermDecl) (body : Kernel.Definition.Body)
    (sortsName termsName declarationName bodyName : String)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (rejected : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies = false)
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue sorts)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDeclaration : applySubst bindings (.var declarationName) = Data.declaration declaration)
    (capturedBody : applySubst bindings (.var bodyName) = Unfolding.bodyValue body) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:form-body", .var sortsName, .var termsName, .var declarationName, .var bodyName]) state (boolean false) := by
  apply captured_of_body bindings state state (tableValue sorts) terms declaration body (boolean false)
    sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
  apply body_of_dummies_path state state sorts sortEntries terms declaration body (boolean false) uniqueSorts allocatedSorts
  simpa only [rejected] using dummies_false_body_returns state terms declaration body

theorem rejected_dummies_kernel_refusal (sorts : Kernel.SortSignature) (signature : Kernel.TermSignature)
    (declaration : TermDecl) (body : Kernel.Definition.Body)
    (rejected : Kernel.Definition.checkDummySorts sorts body.dummies = false) :
    Kernel.Definition.checkBody sorts signature declaration body = false := by
  simp [Kernel.Definition.checkBody, rejected]

/-- A completed wrong-sort, function-valued or unknown inferred type refuses
before the free-variable traversal. Inference's cache publication is retained. -/
theorem rejected_type_returns (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state)
    (allowedDummies : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies = true)
    (wrongType : Preterm.infer (signatureOf entries) (body.context declaration) body.expression ≠ some ([], declaration.resultSort)) :
    ∃ after,
      (∀ bindings sortsName termsName declarationName bodyName,
        applySubst bindings (.var sortsName) = tableValue sorts →
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var declarationName) = Data.declaration declaration →
        applySubst bindings (.var bodyName) = Unfolding.bodyValue body →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-body", .var sortsName, .var termsName, .var declarationName, .var bodyName]) after (boolean false)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf body.expression) state after := by
  obtain ⟨after, inferred, readyAfter, frame⟩ := Inference.returns handle cache entries uniqueTerms separate
    (body.context declaration) body.expression state allocatedTerms ready
  refine ⟨after, ?_, readyAfter, frame⟩
  intro bindings sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
  apply captured_of_body bindings state after (tableValue sorts) (tableValue handle) declaration body (boolean false)
    sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
  apply body_of_dummies_path state after sorts sortEntries (tableValue handle) declaration body (boolean false) uniqueSorts allocatedSorts
  rw [allowedDummies]
  apply dummies_true_body_of_context_path state after (tableValue handle) declaration body (boolean false)
  apply context_body_of_paths state after after (tableValue handle) (body.context declaration) declaration.resultSort
    declaration.dependencies body.expression (Preterm.infer (signatureOf entries) (body.context declaration) body.expression)
    (boolean false) inferred
  simpa only [wrongType, decide_false] using
    typed_false_body_returns after (tableValue handle) (body.context declaration) declaration.dependencies body.expression

theorem free_predicate_meaning (signature : Kernel.TermSignature) (context : Context)
    (expression : Preterm) (deps : Finset Nat) :
    (Presentation.ComputationalFreeVariables.indices? signature context expression).any
      (fun indices => decide (indices.toFinset ⊆ deps)) =
    (match Preterm.freeVariables? signature context expression with
      | none => false | some free => decide (free ⊆ deps)) := by
  have meaning := Presentation.ComputationalFreeVariables.indices_meaning signature context expression
  cases computed : Presentation.ComputationalFreeVariables.indices? signature context expression with
  | none =>
      have actual : Preterm.freeVariables? signature context expression = none := by
        simpa only [computed, Option.map_none] using meaning.symm
      simp only [actual, Option.any_none]
  | some indices =>
      have actual : Preterm.freeVariables? signature context expression = some indices.toFinset := by
        simpa only [computed, Option.map_some] using meaning.symm
      simp only [actual, Option.any_some]

def request : Atom :=
  .expression [.symbol "mm0:form-body", .var "sorts", .var "table", .var "valueInput", .var "valueInputValue"]

def requestConfiguration (state : State) (sorts terms : Handle) (declaration : TermDecl)
    (body : Kernel.Definition.Body) : Configuration :=
  { state, control := .evaluate (environment (tableValue sorts) (tableValue terms) declaration body) request }

/-- Immediate refusal has finite fuel, remains stable with more fuel, and leaves
all stores and cells unchanged even if no inference cache exists. -/
theorem rejected_dummies_sufficient_fuel (sorts terms : Handle) (sortEntries : List (Nat × SortInfo))
    (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (rejected : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies = false) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state sorts terms declaration body) =
      .complete state [boolean false] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue sorts) (tableValue terms) declaration body) state state request (boolean false)
    (rejected_dummies_returns _ state sorts sortEntries (tableValue terms) declaration body
      "sorts" "table" "valueInput" "valueInputValue" uniqueSorts allocatedSorts rejected rfl rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem rejected_type_sufficient_fuel (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state)
    (allowedDummies : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies = true)
    (wrongType : Preterm.infer (signatureOf entries) (body.context declaration) body.expression ≠ some ([], declaration.resultSort)) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state sorts handle declaration body) =
        .complete after [boolean false] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf body.expression) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := rejected_type_returns sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready allowedDummies wrongType
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue sorts) (tableValue handle) declaration body) state after request (boolean false)
    (path _ "sorts" "table" "valueInput" "valueInputValue" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem rejected_type_kernel_refusal (sorts : Kernel.SortSignature) (signature : Kernel.TermSignature)
    (declaration : TermDecl) (body : Kernel.Definition.Body)
    (wrongType : Preterm.infer signature (body.context declaration) body.expression ≠ some ([], declaration.resultSort)) :
    Kernel.Definition.checkBody sorts signature declaration body = false := by
  simp [Kernel.Definition.checkBody, wrongType]

namespace Controls

theorem all_declared_occurrences_accepted (state : State) :
    PureReturns program [("result", resultValue (some [0, 0, 1])), ("deps", Data.dependencies {0, 1})] state
      (.expression [.symbol "mm0:body-free", .var "result", .var "deps"]) state (boolean true) :=
  FreeResult.captured_returns _ state (some [0, 0, 1]) {0, 1} "result" "deps" rfl rfl

theorem undeclared_occurrence_refused (state : State) :
    PureReturns program [("result", resultValue (some [0, 1])), ("deps", Data.dependencies {0})] state
      (.expression [.symbol "mm0:body-free", .var "result", .var "deps"]) state (boolean false) :=
  FreeResult.captured_returns _ state (some [0, 1]) {0} "result" "deps" rfl rfl

theorem undefined_free_set_refused (state : State) :
    PureReturns program [("result", resultValue none), ("deps", Data.dependencies {0})] state
      (.expression [.symbol "mm0:body-free", .var "result", .var "deps"]) state (boolean false) :=
  FreeResult.captured_returns _ state none {0} "result" "deps" rfl rfl

end Controls

/-- Actual source acceptance forces the independent dummy-sort admission
premise, without requiring any term-table or inference-cache representation. -/
theorem acceptance_requires_dummy_sorts (sorts terms : Handle) (sortEntries : List (Nat × SortInfo))
    (declaration : TermDecl) (body : Kernel.Definition.Body) (state after : State) (fuel : Nat)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (accepted : run program fuel (requestConfiguration state sorts terms declaration body) = .complete after [boolean true] [] []) :
    Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies = true := by
  cases checked : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies with
  | true => rfl
  | false =>
      obtain ⟨referenceFuel, completed⟩ := rejected_dummies_sufficient_fuel sorts terms sortEntries declaration body state
        uniqueSorts allocatedSorts checked
      have reference := completed 0
      simp only [Nat.add_zero] at reference
      have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] reference accepted
      have impossible := List.singleton_inj.mp same.2.1
      cases impossible

theorem acceptance_requires_admissible_dummy_sorts (sorts terms : Handle) (sortEntries : List (Nat × SortInfo))
    (declaration : TermDecl) (body : Kernel.Definition.Body) (state after : State) (fuel : Nat)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (accepted : run program fuel (requestConfiguration state sorts terms declaration body) = .complete after [boolean true] [] []) :
    ∀ sort ∈ body.dummies, ∃ info, SortFormation.signature sortEntries sort = some info ∧
      info.strict = false ∧ info.free = false :=
  (Kernel.Definition.checkDummySorts_iff _ _).mp
    (acceptance_requires_dummy_sorts sorts terms sortEntries declaration body state after fuel uniqueSorts allocatedSorts accepted)

/-- Source acceptance forces the kernel's exact saturated result type. This
uses the preceding term table and coherent inference cache, rather than a
hypothesis asserting the desired body-typing result. -/
theorem acceptance_requires_type (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body)
    (state after : State) (fuel : Nat)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state)
    (accepted : run program fuel (requestConfiguration state sorts handle declaration body) = .complete after [boolean true] [] []) :
    Preterm.HasType (signatureOf entries) (body.context declaration) body.expression [] declaration.resultSort := by
  apply (Preterm.infer_eq_some_iff _ _ _ _ _).mp
  by_contra wrongType
  have allowedDummies := acceptance_requires_dummy_sorts sorts handle sortEntries declaration body state after fuel
    uniqueSorts allocatedSorts accepted
  obtain ⟨refused, referenceFuel, completed, _, _⟩ := rejected_type_sufficient_fuel sorts handle cache sortEntries entries
    declaration body state uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready allowedDummies wrongType
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  have same := completed_result_unique program referenceFuel fuel _ refused after _ [] [] _ [] [] reference accepted
  have impossible := List.singleton_inj.mp same.2.1
  cases impossible

/-- Universal execution of the retained body-admission path. Dummy and type
checks short-circuit; successful inference and argument checks retain only
permitted cache publications in the preceding signature. -/
theorem returns (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after,
      (∀ bindings sortsName termsName declarationName bodyName,
        applySubst bindings (.var sortsName) = tableValue sorts →
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var declarationName) = Data.declaration declaration →
        applySubst bindings (.var bodyName) = Unfolding.bodyValue body →
        PureReturns program bindings state
          (.expression [.symbol "mm0:form-body", .var sortsName, .var termsName, .var declarationName, .var bodyName]) after
          (boolean (Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf body.expression + 1) state after := by
  cases allowedDummies : Kernel.Definition.checkDummySorts (SortFormation.signature sortEntries) body.dummies with
  | false =>
      refine ⟨state, ?_, ready, InferenceCache.Frame.refl cache (tableValue handle) _ state⟩
      intro bindings sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
      simpa only [Kernel.Definition.checkBody, allowedDummies, Bool.false_and] using
        rejected_dummies_returns bindings state sorts sortEntries (tableValue handle) declaration body
          sortsName termsName declarationName bodyName uniqueSorts allocatedSorts allowedDummies
          capturedSorts capturedTerms capturedDeclaration capturedBody
  | true =>
      obtain ⟨middle, inferPath, readyMiddle, frameInfer⟩ := Inference.returns handle cache entries uniqueTerms separate
        (body.context declaration) body.expression state allocatedTerms ready
      by_cases hasType : Preterm.infer (signatureOf entries) (body.context declaration) body.expression = some ([], declaration.resultSort)
      · have middleAllocated : middle.read handle = some (declarationRows entries) := by
          rw [frameInfer.other handle separate]
          exact allocatedTerms
        obtain ⟨after, freePath, readyAfter, frameFree⟩ := FreeVariables.returns handle cache entries uniqueTerms separate
          (body.context declaration) body.expression middle middleAllocated readyMiddle
        refine ⟨after, ?_, readyAfter, (frameInfer.weaken (by omega)).trans frameFree⟩
        intro bindings sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
        have bodyAnswer : Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body =
            (Presentation.ComputationalFreeVariables.indices? (signatureOf entries) (body.context declaration) body.expression).any
              (fun indices => decide (indices.toFinset ⊆ declaration.dependencies)) := by
          rw [Kernel.Definition.checkBody, allowedDummies, hasType]
          simp only [decide_true, Bool.true_and]
          exact (free_predicate_meaning (signatureOf entries) (body.context declaration)
            body.expression declaration.dependencies).symm
        rw [bodyAnswer]
        apply captured_of_body bindings state after (tableValue sorts) (tableValue handle) declaration body _
          sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
        apply body_of_dummies_path state after sorts sortEntries (tableValue handle) declaration body _ uniqueSorts allocatedSorts
        rw [allowedDummies]
        apply dummies_true_body_of_context_path state after (tableValue handle) declaration body
        apply context_body_of_paths state middle after (tableValue handle) (body.context declaration) declaration.resultSort
          declaration.dependencies body.expression (Preterm.infer (signatureOf entries) (body.context declaration) body.expression)
          _ inferPath
        simpa only [hasType, decide_true] using typed_true_body_of_free_path middle after (tableValue handle)
          (body.context declaration) declaration.dependencies body.expression
          (Presentation.ComputationalFreeVariables.indices? (signatureOf entries) (body.context declaration) body.expression) freePath
      · refine ⟨middle, ?_, readyMiddle, frameInfer.weaken (by omega)⟩
        intro bindings sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
        have bodyAnswer : Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body = false :=
          rejected_type_kernel_refusal _ _ declaration body hasType
        rw [bodyAnswer]
        apply captured_of_body bindings state middle (tableValue sorts) (tableValue handle) declaration body (boolean false)
          sortsName termsName declarationName bodyName capturedSorts capturedTerms capturedDeclaration capturedBody
        apply body_of_dummies_path state middle sorts sortEntries (tableValue handle) declaration body (boolean false) uniqueSorts allocatedSorts
        rw [allowedDummies]
        apply dummies_true_body_of_context_path state middle (tableValue handle) declaration body (boolean false)
        apply context_body_of_paths state middle middle (tableValue handle) (body.context declaration) declaration.resultSort
          declaration.dependencies body.expression (Preterm.infer (signatureOf entries) (body.context declaration) body.expression)
          (boolean false) inferPath
        simpa only [hasType, decide_false] using typed_false_body_returns middle (tableValue handle)
          (body.context declaration) declaration.dependencies body.expression

theorem sufficient_fuel (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state sorts handle declaration body) =
        .complete after [boolean (Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf body.expression + 1) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue sorts) (tableValue handle) declaration body) state after request _
    (path _ "sorts" "table" "valueInput" "valueInputValue" rfl rfl rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) (answer : Bool) :
    Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts handle declaration body) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ := sufficient_fuel sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem admissible_iff_source_accepts (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    Kernel.Definition.AdmissibleBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts handle declaration body) = .complete after [boolean true] [] [] :=
  (Kernel.Definition.checkBody_iff _ _ _ _).symm.trans
    (result_iff_source_returns sorts handle cache sortEntries entries declaration body state
      uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready true)

theorem refused_iff_source_refuses (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ Kernel.Definition.AdmissibleBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body) ↔
      ∃ after fuel, run program fuel (requestConfiguration state sorts handle declaration body) = .complete after [boolean false] [] [] := by
  rw [← Kernel.Definition.checkBody_iff]
  exact (Bool.eq_false_iff).symm.trans (result_iff_source_returns sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready false)

theorem admissible_iff_gslt_path (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body) (state : State)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    Kernel.Definition.AdmissibleBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state sorts handle declaration body)
        (finished after [boolean true] [] []) := by
  rw [admissible_iff_source_accepts sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_frame (sorts handle cache : Handle) (sortEntries : List (Nat × SortInfo))
    (entries : List ServiceInferenceCache.Row) (declaration : TermDecl) (body : Kernel.Definition.Body)
    (state after : State) (fuel : Nat) (answers : List Atom)
    (uniqueSorts : ∀ key, (sortEntries.filter fun entry => entry.1 = key).length ≤ 1)
    (uniqueTerms : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (allocatedSorts : state.read sorts = some (SortFormation.rows sortEntries))
    (allocatedTerms : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state)
    (returned : run program fuel (requestConfiguration state sorts handle declaration body) = .complete after answers [] []) :
    answers = [boolean (Kernel.Definition.checkBody (SortFormation.signature sortEntries) (signatureOf entries) declaration body)] ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf body.expression + 1) state after := by
  obtain ⟨reference, referenceFuel, completed, readyReference, frame⟩ := sufficient_fuel sorts handle cache sortEntries entries declaration body state
    uniqueSorts uniqueTerms separate allocatedSorts allocatedTerms ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨same.2.1.symm, readyReference, frame⟩

end Mettapedia.Languages.MM0.MeTTa.BodyFormation
