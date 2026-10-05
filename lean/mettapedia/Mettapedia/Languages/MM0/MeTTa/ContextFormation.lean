import Mettapedia.Languages.MM0.MeTTa.SortFormation

/-!
# Ordered context admission in the retained MM0 source

The source checks dependencies in the preceding context. These execution
proofs cover both successful and refused formation, leave every store and
cell unchanged, and use the independent kernel's context judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ContextFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open NamedSpaces (Handle)
open Kernel (Binder Context SortInfo)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open TableAccess (tableValue)

private def indexEquation : SourceProgram.Equation := (kernelSource.program.equations.take 87)[86]'(by decide)
private def itemEquation : SourceProgram.Equation := (kernelSource.program.equations.take 88)[87]'(by decide)
private def indicesEquation : SourceProgram.Equation := (kernelSource.program.equations.take 89)[88]'(by decide)
private def viewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 90)[89]'(by decide)
private def nextEquation : SourceProgram.Equation := (kernelSource.program.equations.take 91)[90]'(by decide)

private def casesOf (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def itemCases := casesOf itemEquation.body
private def viewCases := casesOf viewEquation.body
private def nextCases := casesOf nextEquation.body
private def consBody := (viewCases[1]'(by decide)).2

private def indexEnvironment (context : Context) (index : Nat) : Subst :=
  [("index", natural index), ("context", Data.context context)]
private def itemEnvironment (item : Option Binder) : Subst :=
  [("valueInput", optionValue (item.map Data.binder))]
private def indicesEnvironment (context : Context) (indices : List Nat) : Subst :=
  [("indices", listValue (indices.map natural)), ("context", Data.context context)]
private def viewEnvironment (context : Context) (indices : List Nat) : Subst :=
  [("context", Data.context context), ("valueInput", viewValue (indices.map natural))]
private def nextEnvironment (answer : Bool) (context : Context) (indices : List Nat) : Subst :=
  [("indices", listValue (indices.map natural)), ("context", Data.context context), ("conditionInput", boolean answer)]

private theorem item_unique : program.equations.filter (fun e => e.head == "mm0:form-bound-item") = [itemEquation] := by decide
private theorem index_unique : program.equations.filter (fun e => e.head == "mm0:form-bound-index") = [indexEquation] := by decide
private theorem indices_unique : program.equations.filter (fun e => e.head == "mm0:form-bound-indices") = [indicesEquation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:form-bound-view") = [viewEquation] := by decide
private theorem next_unique : program.equations.filter (fun e => e.head == "mm0:form-bound-next") = [nextEquation] := by decide
private theorem item_formals : itemEquation.arguments = [.var "valueInput"] := by decide
private theorem index_formals : indexEquation.arguments = [.var "context", .var "index"] := by decide
private theorem indices_formals : indicesEquation.arguments = [.var "context", .var "indices"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "context"] := by decide
private theorem next_formals : nextEquation.arguments = [.var "conditionInput", .var "context", .var "indices"] := by decide

private theorem item_shape : itemEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
    .expression (itemCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem item_cases : itemCases = [
    (.expression [.symbol "None"], boolean false),
    (.expression [.expression [.symbol "Some", listValue [.symbol "MM0:Bound", .var "sort"]]], boolean true),
    (.expression [.expression [.symbol "Some", listValue [.symbol "MM0:Regular", .var "sort", .var "deps"]]], boolean false),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem index_shape : indexEquation.body = .expression [.symbol "let", .var "entry",
    .expression [.symbol "mm0:data-at", .var "context", .var "index"],
    .expression [.symbol "mm0:form-bound-item", .var "entry"]] := by decide
private theorem indices_shape : indicesEquation.body = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "indices"],
    .expression [.symbol "mm0:form-bound-view", .var "view", .var "context"]] := by decide
private theorem view_shape : viewEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem view_cases : viewCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "index", .var "indices"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_shape : consBody = .expression [.symbol "let", .var "formBoundIndexResult",
    .expression [.symbol "mm0:form-bound-index", .var "context", .var "index"],
    .expression [.symbol "mm0:form-bound-next", .var "formBoundIndexResult", .var "context", .var "indices"]] := by decide
private theorem next_shape : nextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (nextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem next_cases : nextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:form-bound-indices", .var "context", .var "indices"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem item_body_returns (item : Option Binder) (state : State) :
    PureReturns program (itemEnvironment item) state itemEquation.body state
      (boolean (match item with | some (.bound _) => true | _ => false)) := by
  rw [item_shape]
  have input : PureReturns program (itemEnvironment item) state (.expression [.var "valueInput"]) state
      (.expression [optionValue (item.map Data.binder)]) := by
    simpa [itemEnvironment, applySubst, Subst.lookup] using tuple_variables_return program (itemEnvironment item) state ["valueInput"]
  cases item with
  | none =>
      apply case_returns program (itemEnvironment none) (itemEnvironment none) state state state _ _ (boolean false) _ _ itemCases (read_cases_encoded _) input
      · simp [item_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, itemEnvironment, optionValue]
      · exact grounded_returns program _ state (.bool false)
  | some item =>
      cases item with
      | bound sort =>
          let bindings := ("sort", natural sort) :: itemEnvironment (some (.bound sort))
          apply case_returns program _ bindings state state state _ _ (boolean true) _ _ itemCases (read_cases_encoded _) input
          · simp [item_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
              bindings, itemEnvironment, Data.binder, optionValue, listValue, Subst.lookup]
          · exact grounded_returns program _ state (.bool true)
      | regular sort deps =>
          let bindings := ("deps", Data.dependencies deps) :: ("sort", natural sort) :: itemEnvironment (some (.regular sort deps))
          apply case_returns program _ bindings state state state _ _ (boolean false) _ _ itemCases (read_cases_encoded _) input
          · simp [item_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
              bindings, itemEnvironment, Data.binder, optionValue, listValue, Subst.lookup]
          · exact grounded_returns program _ state (.bool false)

theorem index_body_returns (context : Context) (index : Nat) (state : State) :
    PureReturns program (indexEnvironment context index) state indexEquation.body state (boolean (Kernel.Context.isBound context index)) := by
  rw [index_shape]
  let bindings := indexEnvironment context index
  let found := ("entry", optionValue ((context[index]?).map Data.binder)) :: bindings
  apply let_returns program bindings found state state state (.var "entry") _ _ (optionValue ((context[index]?).map Data.binder)) _
  · simpa only [Data.context, List.getElem?_map] using ListAccess.data_at_list_returns bindings state (context.map Data.binder) index
      "context" "index" rfl rfl
  · simp [SourceProgram.matchValue, matchAtom, found, bindings, indexEnvironment, Subst.lookup]
  · apply authored_variable_call_returns program found (itemEnvironment (context[index]?)) state state "mm0:form-bound-item"
      ["entry"] itemEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
    · rw [clauses_use_only_the_named_equations, item_unique]
      simp [item_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, found, applySubst, Subst.lookup, itemEnvironment]
    · exact item_body_returns (context[index]?) state

theorem index_captured_returns (bindings : Subst) (state : State) (context : Context) (index : Nat)
    (contextName indexName : String)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-bound-index", .var contextName, .var indexName]) state
      (boolean (Kernel.Context.isBound context index)) := by
  apply authored_variable_call_returns program bindings (indexEnvironment context index) state state "mm0:form-bound-index"
    [contextName, indexName] indexEquation.body _ (by decide) (by decide) (by decide) _ (index_body_returns context index state) (by decide)
  rw [clauses_use_only_the_named_equations, index_unique]
  simp [capturedContext, capturedIndex, index_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, indexEnvironment]

private theorem indices_call_from_body (bindings : Subst) (state : State) (context : Context) (indices : List Nat)
    (contextName indicesName : String)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedIndices : applySubst bindings (.var indicesName) = listValue (indices.map natural))
    (computed : PureReturns program (indicesEnvironment context indices) state indicesEquation.body state
      (boolean (indices.all (Kernel.Context.isBound context)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-bound-indices", .var contextName, .var indicesName]) state
      (boolean (indices.all (Kernel.Context.isBound context))) := by
  apply authored_variable_call_returns program bindings (indicesEnvironment context indices) state state "mm0:form-bound-indices"
    [contextName, indicesName] indicesEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, indices_unique]
  simp [capturedContext, capturedIndices, indices_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, indicesEnvironment]

private theorem next_returns (answer : Bool) (context : Context) (indices : List Nat) (state : State)
    (computed : PureReturns program (indicesEnvironment context indices) state indicesEquation.body state
      (boolean (indices.all (Kernel.Context.isBound context)))) :
    PureReturns program (nextEnvironment answer context indices) state nextEquation.body state
      (boolean (answer && indices.all (Kernel.Context.isBound context))) := by
  rw [next_shape]
  cases answer with
  | false =>
      apply case_returns program (nextEnvironment false context indices) (nextEnvironment false context indices) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ nextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [next_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      apply case_returns program (nextEnvironment true context indices) (nextEnvironment true context indices) state state state
        (.var "conditionInput") (boolean true) (.expression [.symbol "mm0:form-bound-indices", .var "context", .var "indices"])
        _ _ nextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [next_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact indices_call_from_body _ state context indices "context" "indices" rfl rfl computed

theorem indices_body_returns (context : Context) (indices : List Nat) (state : State) :
    PureReturns program (indicesEnvironment context indices) state indicesEquation.body state
      (boolean (indices.all (Kernel.Context.isBound context))) := by
  induction indices with
  | nil =>
      rw [indices_shape]
      let bindings := indicesEnvironment context []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "indices" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, indicesEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment context []) state state "mm0:form-bound-view"
          ["view", "context"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, view_unique]
          simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
            viewed, bindings, indicesEnvironment, applySubst, Subst.lookup, viewEnvironment]
        · rw [view_shape]
          apply case_returns program (viewEnvironment context []) (viewEnvironment context []) state state state
            (.var "valueInput") (viewValue []) (boolean true) _ _ viewCases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [view_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, viewValue]
          · exact grounded_returns program _ state (.bool true)
  | cons index indices recursive =>
      rw [indices_shape]
      let bindings := indicesEnvironment context (index :: indices)
      let viewed := ("view", viewValue ((index :: indices).map natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((index :: indices).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "indices" _ rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, indicesEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment context (index :: indices)) state state "mm0:form-bound-view"
          ["view", "context"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, view_unique]
          simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
            viewed, bindings, indicesEnvironment, applySubst, Subst.lookup, viewEnvironment]
        · rw [view_shape]
          let callee := viewEnvironment context (index :: indices)
          let bound := ("indices", listValue (indices.map natural)) :: ("index", natural index) :: callee
          apply case_returns program callee bound state state state (.var "valueInput") (viewValue ((index :: indices).map natural))
            consBody _ _ viewCases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [view_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, callee, bound, viewEnvironment, Subst.lookup]
          · rw [cons_shape]
            let answer := Kernel.Context.isBound context index
            let checked := ("formBoundIndexResult", boolean answer) :: bound
            apply let_returns program bound checked state state state (.var "formBoundIndexResult") _ _ (boolean answer) _
            · exact index_captured_returns bound state context index "context" "index" rfl rfl
            · simp [SourceProgram.matchValue, matchAtom, checked, bound, callee, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program checked (nextEnvironment answer context indices) state state "mm0:form-bound-next"
                ["formBoundIndexResult", "context", "indices"] nextEquation.body _ (by decide) (by decide) (by decide) _
                (next_returns answer context indices state recursive) (by decide)
              rw [clauses_use_only_the_named_equations, next_unique]
              simp [next_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
                checked, bound, callee, viewEnvironment, applySubst, Subst.lookup, nextEnvironment]

theorem indices_captured_returns (bindings : Subst) (state : State) (context : Context) (indices : List Nat)
    (contextName indicesName : String)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedIndices : applySubst bindings (.var indicesName) = listValue (indices.map natural)) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-bound-indices", .var contextName, .var indicesName]) state
      (boolean (indices.all (Kernel.Context.isBound context))) :=
  indices_call_from_body bindings state context indices contextName indicesName capturedContext capturedIndices
    (indices_body_returns context indices state)

private def binderEquation : SourceProgram.Equation := (kernelSource.program.equations.take 94)[93]'(by decide)
private def depsEquation : SourceProgram.Equation := (kernelSource.program.equations.take 95)[94]'(by decide)
private def binderCases := casesOf binderEquation.body
private def depsCases := casesOf depsEquation.body
private def regularBody := (binderCases[1]'(by decide)).2
private def binderEnvironment (handle : Handle) (context : Context) (binder : Binder) : Subst :=
  [("valueInput", Data.binder binder), ("context", Data.context context), ("sorts", tableValue handle)]
private def depsEnvironment (answer : Bool) (context : Context) (deps : Finset Nat) : Subst :=
  [("deps", Data.dependencies deps), ("context", Data.context context), ("conditionInput", boolean answer)]
private theorem binder_unique : program.equations.filter (fun e => e.head == "mm0:form-binder") = [binderEquation] := by decide
private theorem deps_unique : program.equations.filter (fun e => e.head == "mm0:form-binder-deps") = [depsEquation] := by decide
private theorem binder_formals : binderEquation.arguments = [.var "sorts", .var "context", .var "valueInput"] := by decide
private theorem deps_formals : depsEquation.arguments = [.var "conditionInput", .var "context", .var "deps"] := by decide
private theorem binder_shape : binderEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (binderCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem binder_cases : binderCases = [
    (listValue [.symbol "MM0:Bound", .var "sort"], .expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Bound"]),
    (listValue [.symbol "MM0:Regular", .var "sort", .var "deps"], regularBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem regular_shape : regularBody = .expression [.symbol "let", .var "formSortResult",
    .expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Regular"],
    .expression [.symbol "mm0:form-binder-deps", .var "formSortResult", .var "context", .var "deps"]] := by decide
private theorem deps_shape : depsEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (depsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem deps_cases : depsCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:form-bound-indices", .var "context", .var "deps"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

theorem dependency_check (context : Context) (deps : Finset Nat) :
    (deps.sort (· ≤ ·)).all (Kernel.Context.isBound context) =
      decide (∀ index ∈ deps, Kernel.Context.isBound context index = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true]

private theorem regular_check (sorts : Kernel.SortSignature) (context : Context) (sort : Nat) (deps : Finset Nat) :
    Kernel.Context.checkBinder sorts context (.regular sort deps) =
      (SortFormation.flag (sorts sort) .regular && (deps.sort (· ≤ ·)).all (Kernel.Context.isBound context)) := by
  rw [dependency_check]
  cases known : sorts sort <;> simp [Kernel.Context.checkBinder, SortFormation.flag, known]

private theorem deps_body_returns (answer : Bool) (context : Context) (deps : Finset Nat) (state : State) :
    PureReturns program (depsEnvironment answer context deps) state depsEquation.body state
      (boolean (answer && (deps.sort (· ≤ ·)).all (Kernel.Context.isBound context))) := by
  rw [deps_shape]
  cases answer with
  | false =>
      apply case_returns program (depsEnvironment false context deps) (depsEnvironment false context deps) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ depsCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [deps_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      apply case_returns program (depsEnvironment true context deps) (depsEnvironment true context deps) state state state
        (.var "conditionInput") (boolean true) (.expression [.symbol "mm0:form-bound-indices", .var "context", .var "deps"])
        _ _ depsCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [deps_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact indices_captured_returns _ state context (deps.sort (· ≤ ·)) "context" "deps" rfl rfl

theorem binder_body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (binder : Binder) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (binderEnvironment handle context binder) state binderEquation.body state
      (boolean (Kernel.Context.checkBinder (SortFormation.signature entries) context binder)) := by
  rw [binder_shape]
  cases binder with
  | bound sort =>
      let bindings := binderEnvironment handle context (.bound sort)
      let bound := ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (Data.binder (.bound sort))
        (.expression [.symbol "mm0:form-sort", .var "sorts", .var "sort", .symbol "Bound"]) _ _ binderCases (read_cases_encoded _)
      · exact variable_returns program _ state "valueInput"
      · simp [binder_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
          Data.binder, listValue, bindings, bound, binderEnvironment, Subst.lookup]
      · rw [← SortFormation.bound_flag]
        exact SortFormation.sort_use_returns bound state handle entries sort .bound "sorts" "sort" unique allocated rfl rfl
  | regular sort deps =>
      let bindings := binderEnvironment handle context (.regular sort deps)
      let bound := ("deps", Data.dependencies deps) :: ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (Data.binder (.regular sort deps))
        regularBody _ _ binderCases (read_cases_encoded _)
      · exact variable_returns program _ state "valueInput"
      · simp [binder_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
          Data.binder, listValue, bindings, bound, binderEnvironment, Subst.lookup]
      · rw [regular_shape, regular_check]
        let answer := SortFormation.flag (SortFormation.signature entries sort) .regular
        let checked := ("formSortResult", boolean answer) :: bound
        apply let_returns program bound checked state state state (.var "formSortResult") _ _ (boolean answer) _
        · exact SortFormation.sort_use_returns bound state handle entries sort .regular "sorts" "sort" unique allocated rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, checked, bound, bindings, binderEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program checked (depsEnvironment answer context deps) state state "mm0:form-binder-deps"
            ["formSortResult", "context", "deps"] depsEquation.body _ (by decide) (by decide) (by decide) _
            (deps_body_returns answer context deps state) (by decide)
          rw [clauses_use_only_the_named_equations, deps_unique]
          simp [deps_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
            checked, bound, bindings, binderEnvironment, applySubst, Subst.lookup, depsEnvironment]

theorem binder_captured_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (context : Context) (binder : Binder) (sortsName contextName binderName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedBinder : applySubst bindings (.var binderName) = Data.binder binder) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-binder", .var sortsName, .var contextName, .var binderName]) state
      (boolean (Kernel.Context.checkBinder (SortFormation.signature entries) context binder)) := by
  apply authored_variable_call_returns program bindings (binderEnvironment handle context binder) state state "mm0:form-binder"
    [sortsName, contextName, binderName] binderEquation.body _ (by decide) (by decide) (by decide) _
    (binder_body_returns handle entries context binder state unique allocated) (by decide)
  rw [clauses_use_only_the_named_equations, binder_unique]
  simp [capturedSorts, capturedContext, capturedBinder, binder_formals, SourceProgram.matchValue,
    SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, binderEnvironment]

private def fromEquation : SourceProgram.Equation := (kernelSource.program.equations.take 96)[95]'(by decide)
private def contextViewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 97)[96]'(by decide)
private def contextNextEquation : SourceProgram.Equation := (kernelSource.program.equations.take 98)[97]'(by decide)
private def contextEquation : SourceProgram.Equation := (kernelSource.program.equations.take 99)[98]'(by decide)
private def contextViewCases := casesOf contextViewEquation.body
private def contextNextCases := casesOf contextNextEquation.body
private def contextConsBody := (contextViewCases[1]'(by decide)).2
private def extendBody := (contextNextCases[1]'(by decide)).2
private def fromEnvironment (handle : Handle) (initial remaining : Context) : Subst :=
  [("remaining", Data.context remaining), ("initial", Data.context initial), ("sorts", tableValue handle)]
private def contextViewEnvironment (handle : Handle) (initial remaining : Context) : Subst :=
  [("initial", Data.context initial), ("sorts", tableValue handle), ("valueInput", viewValue (remaining.map Data.binder))]
private def contextNextEnvironment (answer : Bool) (handle : Handle) (initial : Context) (binder : Binder) (remaining : Context) : Subst :=
  [("remaining", Data.context remaining), ("binder", Data.binder binder), ("initial", Data.context initial),
    ("sorts", tableValue handle), ("conditionInput", boolean answer)]
private def contextEnvironment (handle : Handle) (context : Context) : Subst :=
  [("context", Data.context context), ("sorts", tableValue handle)]
private theorem from_unique : program.equations.filter (fun e => e.head == "mm0:form-context-from") = [fromEquation] := by decide
private theorem context_view_unique : program.equations.filter (fun e => e.head == "mm0:form-context-view") = [contextViewEquation] := by decide
private theorem context_next_unique : program.equations.filter (fun e => e.head == "mm0:form-context-next") = [contextNextEquation] := by decide
private theorem context_unique : program.equations.filter (fun e => e.head == "mm0:form-context") = [contextEquation] := by decide
private theorem from_formals : fromEquation.arguments = [.var "sorts", .var "initial", .var "remaining"] := by decide
private theorem context_view_formals : contextViewEquation.arguments = [.var "valueInput", .var "sorts", .var "initial"] := by decide
private theorem context_next_formals : contextNextEquation.arguments =
    [.var "conditionInput", .var "sorts", .var "initial", .var "binder", .var "remaining"] := by decide
private theorem context_formals : contextEquation.arguments = [.var "sorts", .var "context"] := by decide
private theorem from_shape : fromEquation.body = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "remaining"],
    .expression [.symbol "mm0:form-context-view", .var "view", .var "sorts", .var "initial"]] := by decide
private theorem context_view_shape : contextViewEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (contextViewCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_view_cases : contextViewCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "binder", .var "remaining"], contextConsBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem context_cons_shape : contextConsBody = .expression [.symbol "let", .var "formBinderResult",
    .expression [.symbol "mm0:form-binder", .var "sorts", .var "initial", .var "binder"],
    .expression [.symbol "mm0:form-context-next", .var "formBinderResult", .var "sorts", .var "initial", .var "binder", .var "remaining"]] := by decide
private theorem context_next_shape : contextNextEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (contextNextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_next_cases : contextNextCases = [(boolean false, boolean false), (boolean true, extendBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem extend_shape : extendBody = .expression [.symbol "let", .var "combined",
    .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression [.var "binder"]],
      .expression [.symbol "mm0:list-append", .var "initial", .var "items"]],
    .expression [.symbol "mm0:form-context-from", .var "sorts", .var "combined", .var "remaining"]] := by decide
private theorem context_shape : contextEquation.body = .expression [.symbol "let", .var "items",
    .expression [.symbol "MM0:L", .expression []],
    .expression [.symbol "mm0:form-context-from", .var "sorts", .var "items", .var "context"]] := by decide

private theorem from_call_from_body (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (initial remaining : Context) (sortsName initialName remainingName : String)
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedInitial : applySubst bindings (.var initialName) = Data.context initial)
    (capturedRemaining : applySubst bindings (.var remainingName) = Data.context remaining)
    (computed : PureReturns program (fromEnvironment handle initial remaining) state fromEquation.body state
      (boolean (Kernel.Context.checkFrom (SortFormation.signature entries) initial remaining))) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-context-from", .var sortsName, .var initialName, .var remainingName]) state
      (boolean (Kernel.Context.checkFrom (SortFormation.signature entries) initial remaining)) := by
  apply authored_variable_call_returns program bindings (fromEnvironment handle initial remaining) state state "mm0:form-context-from"
    [sortsName, initialName, remainingName] fromEquation.body _ (by decide) (by decide) (by decide) _ computed (by decide)
  rw [clauses_use_only_the_named_equations, from_unique]
  simp [capturedSorts, capturedInitial, capturedRemaining, from_formals, SourceProgram.matchValue,
    SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, fromEnvironment]

private theorem context_next_returns (answer : Bool) (handle : Handle) (entries : List (Nat × SortInfo))
    (initial : Context) (binder : Binder) (remaining : Context) (state : State)
    (computed : PureReturns program (fromEnvironment handle (initial ++ [binder]) remaining) state fromEquation.body state
      (boolean (Kernel.Context.checkFrom (SortFormation.signature entries) (initial ++ [binder]) remaining))) :
    PureReturns program (contextNextEnvironment answer handle initial binder remaining) state contextNextEquation.body state
      (boolean (answer && Kernel.Context.checkFrom (SortFormation.signature entries) (initial ++ [binder]) remaining)) := by
  rw [context_next_shape]
  cases answer with
  | false =>
      apply case_returns program (contextNextEnvironment false handle initial binder remaining)
        (contextNextEnvironment false handle initial binder remaining) state state state
        (.var "conditionInput") (boolean false) (boolean false) _ _ contextNextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [context_next_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)
  | true =>
      let bindings := contextNextEnvironment true handle initial binder remaining
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) extendBody
        _ _ contextNextCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [context_next_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · rw [extend_shape]
        let combined := ("combined", Data.context (initial ++ [binder])) :: bindings
        apply let_returns program bindings combined state state state (.var "combined") _ _ (Data.context (initial ++ [binder])) _
        · let withItems := ("items", listValue [Data.binder binder]) :: bindings
          apply let_returns program bindings withItems state state state (.var "items") _ _ (listValue [Data.binder binder]) _
          · exact ListAccess.list_variables_return bindings state ["binder"]
          · simp [SourceProgram.matchValue, matchAtom, withItems, bindings, contextNextEnvironment, Subst.lookup]
          · simpa [Data.context, List.map_append] using ListAccess.append_captured_returns withItems state
              (initial.map Data.binder) [Data.binder binder] "initial" "items" rfl rfl
        · simp [SourceProgram.matchValue, matchAtom, combined, bindings, contextNextEnvironment, Subst.lookup]
        · exact from_call_from_body combined state handle entries (initial ++ [binder]) remaining
            "sorts" "combined" "remaining" rfl rfl rfl computed

theorem from_body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (initial remaining : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (fromEnvironment handle initial remaining) state fromEquation.body state
      (boolean (Kernel.Context.checkFrom (SortFormation.signature entries) initial remaining)) := by
  induction remaining generalizing initial with
  | nil =>
      rw [from_shape]
      let bindings := fromEnvironment handle initial []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "remaining" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, fromEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (contextViewEnvironment handle initial []) state state "mm0:form-context-view"
          ["view", "sorts", "initial"] contextViewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, context_view_unique]
          simp [context_view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
            viewed, bindings, fromEnvironment, applySubst, Subst.lookup, contextViewEnvironment]
        · rw [context_view_shape]
          apply case_returns program (contextViewEnvironment handle initial []) (contextViewEnvironment handle initial []) state state state
            (.var "valueInput") (viewValue []) (boolean true) _ _ contextViewCases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [context_view_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, viewValue]
          · exact grounded_returns program _ state (.bool true)
  | cons binder remaining recursive =>
      rw [from_shape]
      let bindings := fromEnvironment handle initial (binder :: remaining)
      let viewed := ("view", viewValue ((binder :: remaining).map Data.binder)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((binder :: remaining).map Data.binder)) _
      · exact ListAccess.view_captured_returns bindings state "remaining" _ rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, fromEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (contextViewEnvironment handle initial (binder :: remaining)) state state "mm0:form-context-view"
          ["view", "sorts", "initial"] contextViewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · rw [clauses_use_only_the_named_equations, context_view_unique]
          simp [context_view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
            viewed, bindings, fromEnvironment, applySubst, Subst.lookup, contextViewEnvironment]
        · rw [context_view_shape]
          let callee := contextViewEnvironment handle initial (binder :: remaining)
          let bound := ("remaining", Data.context remaining) :: ("binder", Data.binder binder) :: callee
          apply case_returns program callee bound state state state (.var "valueInput") (viewValue ((binder :: remaining).map Data.binder))
            contextConsBody _ _ contextViewCases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [context_view_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, Data.context, callee, bound, contextViewEnvironment, Subst.lookup]
          · rw [context_cons_shape]
            let answer := Kernel.Context.checkBinder (SortFormation.signature entries) initial binder
            let checked := ("formBinderResult", boolean answer) :: bound
            apply let_returns program bound checked state state state (.var "formBinderResult") _ _ (boolean answer) _
            · exact binder_captured_returns bound state handle entries initial binder "sorts" "initial" "binder" unique allocated rfl rfl rfl
            · simp [SourceProgram.matchValue, matchAtom, checked, bound, callee, contextViewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program checked (contextNextEnvironment answer handle initial binder remaining) state state "mm0:form-context-next"
                ["formBinderResult", "sorts", "initial", "binder", "remaining"] contextNextEquation.body _ (by decide) (by decide) (by decide) _
                (context_next_returns answer handle entries initial binder remaining state (recursive (initial ++ [binder]))) (by decide)
              rw [clauses_use_only_the_named_equations, context_next_unique]
              simp [context_next_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom,
                checked, bound, callee, contextViewEnvironment, applySubst, Subst.lookup, contextNextEnvironment]

theorem from_captured_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (initial remaining : Context) (sortsName initialName remainingName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedInitial : applySubst bindings (.var initialName) = Data.context initial)
    (capturedRemaining : applySubst bindings (.var remainingName) = Data.context remaining) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-context-from", .var sortsName, .var initialName, .var remainingName]) state
      (boolean (Kernel.Context.checkFrom (SortFormation.signature entries) initial remaining)) :=
  from_call_from_body bindings state handle entries initial remaining sortsName initialName remainingName capturedSorts capturedInitial
    capturedRemaining (from_body_returns handle entries initial remaining state unique allocated)

theorem context_body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    PureReturns program (contextEnvironment handle context) state contextEquation.body state
      (boolean (Kernel.Context.check (SortFormation.signature entries) context)) := by
  rw [context_shape]
  let bindings := contextEnvironment handle context
  let empty := ("items", Data.context []) :: bindings
  apply let_returns program bindings empty state state state (.var "items") _ _ (Data.context []) _
  · exact ListAccess.list_variables_return bindings state []
  · simp [SourceProgram.matchValue, matchAtom, empty, bindings, contextEnvironment, Subst.lookup]
  · exact from_captured_returns empty state handle entries [] context "sorts" "items" "context" unique allocated rfl rfl rfl

theorem context_captured_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (context : Context) (sortsName contextName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-context", .var sortsName, .var contextName]) state
      (boolean (Kernel.Context.check (SortFormation.signature entries) context)) := by
  apply authored_variable_call_returns program bindings (contextEnvironment handle context) state state "mm0:form-context"
    [sortsName, contextName] contextEquation.body _ (by decide) (by decide) (by decide) _
    (context_body_returns handle entries context state unique allocated) (by decide)
  rw [clauses_use_only_the_named_equations, context_unique]
  simp [capturedSorts, capturedContext, context_formals, SourceProgram.matchValue,
    SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, contextEnvironment]

theorem strict_bound_refuses (sorts : Kernel.SortSignature) (initial : Context) (sort : Nat) (info : SortInfo)
    (known : sorts sort = some info) (strict : info.strict = true) :
    ¬ Kernel.Context.AdmitsBinder sorts initial (.bound sort) := by
  intro admitted
  cases admitted with
  | bound declared notStrict =>
      have same := Option.some.inj (known.symm.trans declared)
      subst info
      simp [strict] at notStrict

theorem forward_dependency_refuses (sorts : Kernel.SortSignature) (initial : Context) (sort : Nat)
    (deps : Finset Nat) (index : Nat) (used : index ∈ deps) (future : initial.length ≤ index) :
    ¬ Kernel.Context.AdmitsBinder sorts initial (.regular sort deps) := by
  intro admitted
  cases admitted with
  | regular _ dependencies =>
      obtain ⟨_, known⟩ := dependencies index used
      rw [List.getElem?_eq_none future] at known
      cases known

def requestConfiguration (state : State) (handle : Handle) (context : Context) : Configuration :=
  { state := state, control := .evaluate (contextEnvironment handle context)
      (.expression [.symbol "mm0:form-context", .var "sorts", .var "context"]) }

theorem sufficient_fuel (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state handle context) =
      .complete state [boolean (Kernel.Context.check (SortFormation.signature entries) context)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (contextEnvironment handle context) state state _ _
    (context_captured_returns (contextEnvironment handle context) state handle entries context "sorts" "context" unique allocated rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (answer : Bool) :
    Kernel.Context.check (SortFormation.signature entries) context = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context) = .complete after [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries context state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨state, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem formed_iff_source_accepts (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    Kernel.Context.WellFormed (SortFormation.signature entries) context ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context) = .complete after [boolean true] [] [] :=
  (Kernel.Context.check_iff (SortFormation.signature entries) context).symm.trans
    (result_iff_source_returns handle entries context state unique allocated true)

theorem refused_iff_source_refuses (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    (¬ Kernel.Context.WellFormed (SortFormation.signature entries) context) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context) = .complete after [boolean false] [] [] := by
  rw [← Kernel.Context.check_iff]
  exact (Bool.eq_false_iff).symm.trans (result_iff_source_returns handle entries context state unique allocated false)

theorem formed_iff_gslt_path (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) :
    Kernel.Context.WellFormed (SortFormation.signature entries) context ↔
      ∃ after, (theory program).MultiStep (requestConfiguration state handle context) (finished after [boolean true] [] []) := by
  rw [formed_iff_source_accepts handle entries context state unique allocated]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem completed_state_unchanged (handle : Handle) (entries : List (Nat × SortInfo)) (context : Context) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (SortFormation.rows entries)) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration state handle context) = .complete after answers [] []) : after = state := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel handle entries context state unique allocated
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  exact (completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] referenceCompleted returned).1.symm

end Mettapedia.Languages.MM0.MeTTa.ContextFormation
