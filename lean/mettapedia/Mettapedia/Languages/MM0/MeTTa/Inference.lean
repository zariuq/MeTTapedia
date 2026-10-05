import Mettapedia.Languages.MM0.MeTTa.BoundTyping
import Mettapedia.Languages.MM0.MeTTa.TypingResults
import Mettapedia.Languages.MM0.MeTTa.TableAccess
import Mettapedia.Languages.MM0.MeTTa.InferenceCache

/-!
# Inference paths in the retained MM0 program

These paths join context/declaration lookup, the source result handlers and
the concrete cache. Term-table readings are stated explicitly: a cache handle
does not establish a frozen signature. The recursive application branch is
separate from the leaf paths below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Inference

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State)
open NamedSpaces (Handle)
open Kernel (Preterm Context)
open Store (natural)
open ListAccess (optionValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def equation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 133)[132]'(by decide +kernel)

private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:infer-uncached") = [equation] := by decide

private theorem formals :
    equation.arguments = [.var "table", .var "context", .var "expression"] := by decide

private def environment (terms : Atom) (context : Context) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("context", Data.context context), ("table", terms)]

private def cases : SourceProgram.Cases :=
  match equation.body with
  | .expression [_, _, .expression entries] => (readCases entries).getD []
  | _ => []

private def variableBody : Atom := (cases[0]'(by decide)).2
private def termBody : Atom := (cases[1]'(by decide)).2
private def applicationBody : Atom := (cases[2]'(by decide)).2

private theorem body_shape :
    equation.body = .expression [.symbol "case", .var "expression",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:Var", .var "index"], variableBody),
      (.expression [.symbol "MM0:Term", .var "index"], termBody),
      (.expression [.symbol "MM0:App", .var "function", .var "argument"], applicationBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem variable_body_shape :
    variableBody = .expression [.symbol "let", .var "entry",
      .expression [.symbol "mm0:data-at", .var "context", .var "index"],
      .expression [.symbol "mm0:infer-binder", .var "entry"]] := by decide

private theorem term_body_shape :
    termBody = .expression [.symbol "let", .var "declaration",
      .expression [.symbol "mm0:declaration", .var "table", .var "index"],
      .expression [.symbol "mm0:infer-declaration", .var "declaration"]] := by decide

private theorem clause (terms : Atom) (context : Context) (expression : Preterm) :
    clauses program "mm0:infer-uncached" [terms, Data.context context, Data.preterm expression] =
      [.evaluate (environment terms context expression) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

theorem uncached_variable_body_returns (state : State) (signature : Kernel.TermSignature)
    (terms : Atom) (context : Context) (index : Nat) :
    PureReturns program (environment terms context (.var index)) state equation.body state
      (Data.inferred (Preterm.infer signature context (.var index))) := by
  let bindings := environment terms context (.var index)
  let bound := ("index", natural index) :: bindings
  rw [body_shape]
  apply case_returns program bindings bound state state state (.var "expression")
    (Data.preterm (.var index)) variableBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings state "expression"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings,
      environment, Subst.lookup]
  · rw [variable_body_shape]
    let entry := ("entry", optionValue (context[index]?.map Data.binder)) :: bound
    apply let_returns program bound entry state state state (.var "entry") _ _
      (optionValue (context[index]?.map Data.binder)) _
    · simpa [Data.context, List.getElem?_map] using
        ListAccess.data_at_list_returns bound state (context.map Data.binder) index "context" "index"
          (by simp [bound, bindings, environment, applySubst, Subst.lookup, Data.context])
          (by simp [bound, applySubst, Subst.lookup])
    · simp [SourceProgram.matchValue, matchAtom, entry, bound, bindings, environment, Subst.lookup]
    · have handled := TypingResults.binder_captured_returns entry state "entry" context[index]?
          (by rfl)
      cases found : context[index]? with
      | none => simpa [Preterm.infer, found] using handled
      | some binder => simpa [Preterm.infer, found] using handled

theorem uncached_term_body_returns (state : State) (handle : Handle)
    (entries : List ServiceInferenceCache.Row) (context : Context) (index : Nat)
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (allocated : state.read handle = some (declarationRows entries)) :
    PureReturns program (environment (tableValue handle) context (.term index)) state equation.body state
      (Data.inferred (Preterm.infer (signatureOf entries) context (.term index))) := by
  let bindings := environment (tableValue handle) context (.term index)
  let bound := ("index", natural index) :: bindings
  rw [body_shape]
  apply case_returns program bindings bound state state state (.var "expression")
    (Data.preterm (.term index)) termBody _ _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings state "expression"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings,
      environment, Subst.lookup]
  · rw [term_body_shape]
    let declaration := ("declaration", optionValue ((signatureOf entries index).map Data.declaration)) :: bound
    apply let_returns program bound declaration state state state (.var "declaration") _ _
      (optionValue ((signatureOf entries index).map Data.declaration)) _
    · exact TableAccess.declaration_signature_returns bound state handle entries index "table" "index"
        uniqueRows allocated
        (by simp [bound, bindings, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
    · simp [SourceProgram.matchValue, matchAtom, declaration, bound, bindings, environment, Subst.lookup]
    · have handled := TypingResults.declaration_captured_returns declaration state "declaration"
          (signatureOf entries index) (by rfl)
      cases found : signatureOf entries index with
      | none => simpa [Preterm.infer, found] using handled
      | some value => simpa [Preterm.infer, found] using handled

theorem uncached_variable_captured_returns (bindings : Subst) (state : State)
    (signature : Kernel.TermSignature) (terms : Atom) (context : Context) (index : Nat)
    (termsName contextName expressionName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm (.var index)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-uncached", .var termsName, .var contextName, .var expressionName])
      state (Data.inferred (Preterm.infer signature context (.var index))) := by
  apply authored_variable_call_returns program bindings (environment terms context (.var index)) state state
    "mm0:infer-uncached" [termsName, contextName, expressionName] equation.body _
    (by decide) (by decide) (by decide) _
    (uncached_variable_body_returns state signature terms context index) (by decide)
  simpa [capturedTerms, capturedContext, capturedExpression] using clause terms context (.var index)

theorem uncached_term_captured_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List ServiceInferenceCache.Row) (context : Context) (index : Nat)
    (termsName contextName expressionName : String)
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (allocated : state.read handle = some (declarationRows entries))
    (capturedTerms : applySubst bindings (.var termsName) = tableValue handle)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm (.term index)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer-uncached", .var termsName, .var contextName, .var expressionName])
      state (Data.inferred (Preterm.infer (signatureOf entries) context (.term index))) := by
  apply authored_variable_call_returns program bindings (environment (tableValue handle) context (.term index))
    state state "mm0:infer-uncached" [termsName, contextName, expressionName] equation.body _
    (by decide) (by decide) (by decide) _
    (uncached_term_body_returns state handle entries context index uniqueRows allocated) (by decide)
  simpa [capturedTerms, capturedContext, capturedExpression] using
    clause (tableValue handle) context (.term index)

/-- The complete cached variable path, including misses, publication,
context-sensitive hits and missing-variable refusals. -/
theorem variable_returns (state : State) (signature : Kernel.TermSignature) (handle cache : Handle)
    (context : Context) (index : Nat)
    (ready : InferenceCache.Ready signature (tableValue handle) cache state) :
    ∃ after,
      (∀ bindings termsName contextName expressionName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionName) = Data.preterm (.var index) →
        PureReturns program bindings state
          (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
          after (Data.inferred (Preterm.infer signature context (.var index)))) ∧
      InferenceCache.Ready signature (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf (Preterm.var index)) state after := by
  apply InferenceCache.settle signature (tableValue handle) cache (TableAccess.table_literal handle)
    (context, .var index) state ready
  exact ⟨state, 0,
    fun bindings termsName contextName expressionName => uncached_variable_captured_returns bindings state
      signature (tableValue handle) context index termsName contextName expressionName,
    ready, InferenceCache.Frame.refl cache (tableValue handle) 0 state, by simp⟩

/-- The complete cached term-symbol path on the current admitted signature. -/
theorem term_returns (state : State) (handle cache : Handle)
    (entries : List ServiceInferenceCache.Row) (context : Context) (index : Nat)
    (uniqueRows : ServiceInferenceCache.Unique entries)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after,
      (∀ bindings termsName contextName expressionName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionName) = Data.preterm (.term index) →
        PureReturns program bindings state
          (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
          after (Data.inferred (Preterm.infer (signatureOf entries) context (.term index)))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf (Preterm.term index)) state after := by
  apply InferenceCache.settle (signatureOf entries) (tableValue handle) cache (TableAccess.table_literal handle)
    (context, .term index) state ready
  exact ⟨state, 0,
    fun bindings termsName contextName expressionName => uncached_term_captured_returns bindings state
      handle entries context index termsName contextName expressionName uniqueRows allocated,
    ready, InferenceCache.Frame.refl cache (tableValue handle) 0 state, by simp⟩

/-! ## Application: retained argument and function handlers -/

private def argumentsEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 137)[136]'(by decide +kernel)

private def functionEquation : SourceProgram.Equation :=
  (kernelSource.program.equations.take 136)[135]'(by decide +kernel)

private def argumentsEnvironment (terms : Atom) (context arguments : Context)
    (result : Nat) (argument : Preterm) : Subst :=
  [("argument", Data.preterm argument), ("context", Data.context context), ("table", terms),
    ("result", natural result), ("valueInput", ListAccess.viewValue (arguments.map Data.binder))]

private def functionEnvironment (terms : Atom) (context : Context)
    (inferred : Option Kernel.ExpressionType) (argument : Preterm) : Subst :=
  [("argument", Data.preterm argument), ("context", Data.context context), ("table", terms),
    ("valueInput", Data.inferred inferred)]

private def argumentsCases : SourceProgram.Cases :=
  match argumentsEquation.body with
  | .expression [_, _, .expression entries] => (readCases entries).getD []
  | _ => []

private def functionCases : SourceProgram.Cases :=
  match functionEquation.body with
  | .expression [_, _, .expression entries] => (readCases entries).getD []
  | _ => []

private def boundBody : Atom := (argumentsCases[1]'(by decide)).2
private def regularBody : Atom := (argumentsCases[2]'(by decide)).2
private def functionBody : Atom := (functionCases[1]'(by decide)).2

private theorem arguments_body_shape :
    argumentsEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (argumentsCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem arguments_cases_shape :
    argumentsCases = [(.symbol "List:Nil", .symbol "None"),
      (.expression [.symbol "List:Cons", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Bound", .var "sort"]], .var "rest"], boundBody),
      (.expression [.symbol "List:Cons", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]], .var "rest"], regularBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem bound_body_shape :
    boundBody = .expression [.symbol "let", .var "boundSortResult",
      .expression [.symbol "mm0:bound-sort", .var "context", .var "argument"],
      .expression [.symbol "mm0:infer-bound-sort", .var "boundSortResult", .var "sort",
        .var "rest", .var "result"]] := by decide

private theorem regular_body_shape :
    regularBody = .expression [.symbol "let", .var "inferred",
      .expression [.symbol "mm0:infer", .var "table", .var "context", .var "argument"],
      .expression [.symbol "mm0:infer-regular-type", .var "inferred", .var "sort", .var "rest",
        .var "result"]] := by decide

private theorem function_body_shape :
    functionEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (functionCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem function_cases_shape :
    functionCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "MM0:Inferred", .var "arguments", .var "result"], functionBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem function_found_body_shape :
    functionBody = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "arguments"],
      .expression [.symbol "mm0:infer-arguments", .var "view", .var "result", .var "table",
        .var "context", .var "argument"]] := by decide

private theorem application_body_shape :
    applicationBody = .expression [.symbol "let", .var "inferred",
      .expression [.symbol "mm0:infer", .var "table", .var "context", .var "function"],
      .expression [.symbol "mm0:infer-function", .var "inferred", .var "table", .var "context",
        .var "argument"]] := by decide

private theorem arguments_clause (terms : Atom) (context arguments : Context) (result : Nat)
    (argument : Preterm) :
    clauses program "mm0:infer-arguments"
      [ListAccess.viewValue (arguments.map Data.binder), natural result, terms,
        Data.context context, Data.preterm argument] =
      [.evaluate (argumentsEnvironment terms context arguments result argument) argumentsEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun entry => entry.head == "mm0:infer-arguments") =
      [argumentsEquation] := by decide
  have formals : argumentsEquation.arguments =
      [.var "valueInput", .var "result", .var "table", .var "context", .var "argument"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, argumentsEnvironment, Subst.lookup]

private theorem function_clause (terms : Atom) (context : Context)
    (inferred : Option Kernel.ExpressionType) (argument : Preterm) :
    clauses program "mm0:infer-function"
      [Data.inferred inferred, terms, Data.context context, Data.preterm argument] =
      [.evaluate (functionEnvironment terms context inferred argument) functionEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun entry => entry.head == "mm0:infer-function") =
      [functionEquation] := by decide
  have formals : functionEquation.arguments =
      [.var "valueInput", .var "table", .var "context", .var "argument"] := by decide
  rw [unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, functionEnvironment, Subst.lookup]

private theorem arguments_nil_body_returns (state : State) (terms : Atom) (context : Context)
    (result : Nat) (argument : Preterm) :
    PureReturns program (argumentsEnvironment terms context [] result argument) state
      argumentsEquation.body state (.symbol "None") := by
  rw [arguments_body_shape]
  let bindings := argumentsEnvironment terms context [] result argument
  apply case_returns program bindings bindings state state state (.var "valueInput")
    (.symbol "List:Nil") (.symbol "None") _ _ argumentsCases (read_cases_encoded argumentsCases)
  · simpa [bindings, argumentsEnvironment, applySubst, Subst.lookup, ListAccess.viewValue] using
      SourceExecution.variable_returns program bindings state "valueInput"
  · simp [arguments_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem arguments_bound_body_returns (state : State) (terms : Atom) (context rest : Context)
    (expected result : Nat) (argument : Preterm) :
    PureReturns program (argumentsEnvironment terms context (.bound expected :: rest) result argument)
      state argumentsEquation.body state
      (Data.inferred (if Preterm.boundSort? context argument = some expected then some (rest, result) else none)) := by
  rw [arguments_body_shape]
  let bindings := argumentsEnvironment terms context (.bound expected :: rest) result argument
  let bound := ("rest", Data.context rest) :: ("sort", natural expected) :: bindings
  apply case_returns program bindings bound state state state (.var "valueInput")
    (ListAccess.viewValue ((.bound expected :: rest).map Data.binder)) boundBody _ _ argumentsCases
    (read_cases_encoded argumentsCases)
  · simpa [bindings, argumentsEnvironment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings state "valueInput"
  · simp [arguments_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, ListAccess.viewValue,
      ListAccess.listValue, Data.binder, Data.context, bound, bindings, argumentsEnvironment, Subst.lookup]
  · rw [bound_body_shape]
    let computed := ("boundSortResult", optionValue ((Preterm.boundSort? context argument).map natural)) :: bound
    apply let_returns program bound computed state state state (.var "boundSortResult") _ _
      (optionValue ((Preterm.boundSort? context argument).map natural)) _
    · exact BoundTyping.bound_sort_captured_returns bound state context argument "context" "argument"
        (by simp [bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])
    · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, argumentsEnvironment, Subst.lookup]
    · exact TypingResults.bound_captured_returns computed state "boundSortResult" "sort" "rest" "result"
        (Preterm.boundSort? context argument) expected rest result
        (by rfl) (by rfl) (by rfl)
        (by simp [computed, bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])

private theorem arguments_regular_body_returns (before after : State) (signature : Kernel.TermSignature)
    (terms : Atom) (context rest : Context) (expected result : Nat) (dependencies : Finset Nat)
    (argument : Preterm)
    (child : ∀ bindings,
      applySubst bindings (.var "table") = terms →
      applySubst bindings (.var "context") = Data.context context →
      applySubst bindings (.var "argument") = Data.preterm argument →
      PureReturns program bindings before
        (.expression [.symbol "mm0:infer", .var "table", .var "context", .var "argument"])
        after (Data.inferred (Preterm.infer signature context argument))) :
    PureReturns program
      (argumentsEnvironment terms context (.regular expected dependencies :: rest) result argument)
      before argumentsEquation.body after
      (Data.inferred (if Preterm.infer signature context argument = some ([], expected)
        then some (rest, result) else none)) := by
  rw [arguments_body_shape]
  let bindings := argumentsEnvironment terms context (.regular expected dependencies :: rest) result argument
  let bound := ("rest", Data.context rest) :: ("dependencies", Data.dependencies dependencies) ::
    ("sort", natural expected) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput")
    (ListAccess.viewValue ((.regular expected dependencies :: rest).map Data.binder)) regularBody _ _
    argumentsCases (read_cases_encoded argumentsCases)
  · simpa [bindings, argumentsEnvironment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings before "valueInput"
  · simp [arguments_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, ListAccess.viewValue,
      ListAccess.listValue, Data.binder, Data.context, bound, bindings, argumentsEnvironment, Subst.lookup]
  · rw [regular_body_shape]
    let computed := ("inferred", Data.inferred (Preterm.infer signature context argument)) :: bound
    apply let_returns program bound computed before after after (.var "inferred") _ _
      (Data.inferred (Preterm.infer signature context argument)) _
    · exact child bound
        (by simp [bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])
        (by simp [bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])
    · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, argumentsEnvironment, Subst.lookup]
    · exact TypingResults.regular_captured_returns computed after "inferred" "sort" "rest" "result"
        (Preterm.infer signature context argument) expected rest result (by rfl)
        (by simp [computed, bound, applySubst, Subst.lookup]) (by rfl)
        (by simp [computed, bound, bindings, argumentsEnvironment, applySubst, Subst.lookup])

private theorem arguments_captured_returns (bindings : Subst) (before after : State)
    (terms : Atom) (context arguments : Context) (result : Nat) (argument : Preterm) (answer : Atom)
    (capturedView : applySubst bindings (.var "view") = ListAccess.viewValue (arguments.map Data.binder))
    (capturedResult : applySubst bindings (.var "result") = natural result)
    (capturedTerms : applySubst bindings (.var "table") = terms)
    (capturedContext : applySubst bindings (.var "context") = Data.context context)
    (capturedArgument : applySubst bindings (.var "argument") = Data.preterm argument)
    (body : PureReturns program (argumentsEnvironment terms context arguments result argument)
      before argumentsEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:infer-arguments", .var "view", .var "result", .var "table",
        .var "context", .var "argument"]) after answer := by
  apply authored_variable_call_returns program bindings
    (argumentsEnvironment terms context arguments result argument) before after "mm0:infer-arguments"
    ["view", "result", "table", "context", "argument"] argumentsEquation.body answer
    (by decide) (by decide) (by decide) _ body (by decide)
  simpa [capturedView, capturedResult, capturedTerms, capturedContext, capturedArgument] using
    arguments_clause terms context arguments result argument

private theorem function_none_body_returns (state : State) (terms : Atom)
    (context : Context) (argument : Preterm) :
    PureReturns program (functionEnvironment terms context none argument) state functionEquation.body
      state (.symbol "None") := by
  rw [function_body_shape]
  let bindings := functionEnvironment terms context none argument
  apply case_returns program bindings bindings state state state (.var "valueInput")
    (.symbol "None") (.symbol "None") _ _ functionCases (read_cases_encoded functionCases)
  · simpa [bindings, functionEnvironment, Data.inferred, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings state "valueInput"
  · simp [function_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
  · exact symbol_returns program bindings state "None"

private theorem function_some_body_returns (before after : State) (terms : Atom)
    (context arguments : Context) (result : Nat) (argument : Preterm) (answer : Atom)
    (body : PureReturns program (argumentsEnvironment terms context arguments result argument)
      before argumentsEquation.body after answer) :
    PureReturns program (functionEnvironment terms context (some (arguments, result)) argument)
      before functionEquation.body after answer := by
  rw [function_body_shape]
  let bindings := functionEnvironment terms context (some (arguments, result)) argument
  let bound := ("result", natural result) :: ("arguments", Data.context arguments) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput")
    (Data.inferred (some (arguments, result))) functionBody answer _ functionCases
    (read_cases_encoded functionCases)
  · simpa [bindings, functionEnvironment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings before "valueInput"
  · simp [function_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Data.inferred, bound,
      bindings, functionEnvironment, Subst.lookup]
  · rw [function_found_body_shape]
    let viewed := ("view", ListAccess.viewValue (arguments.map Data.binder)) :: bound
    apply let_returns program bound viewed before before after (.var "view") _ _
      (ListAccess.viewValue (arguments.map Data.binder)) answer
    · exact ListAccess.view_captured_returns bound before "arguments" (arguments.map Data.binder) (by rfl)
    · simp [SourceProgram.matchValue, matchAtom, viewed, bound, bindings, functionEnvironment, Subst.lookup]
    · exact arguments_captured_returns viewed before after terms context arguments result argument answer
        (by rfl) (by simp [viewed, bound, applySubst, Subst.lookup])
        (by simp [viewed, bound, bindings, functionEnvironment, applySubst, Subst.lookup])
        (by simp [viewed, bound, bindings, functionEnvironment, applySubst, Subst.lookup])
        (by simp [viewed, bound, bindings, functionEnvironment, applySubst, Subst.lookup]) body

private theorem function_captured_returns (bindings : Subst) (before after : State)
    (terms : Atom) (context : Context) (inferred : Option Kernel.ExpressionType)
    (argument : Preterm) (answer : Atom)
    (capturedInferred : applySubst bindings (.var "inferred") = Data.inferred inferred)
    (capturedTerms : applySubst bindings (.var "table") = terms)
    (capturedContext : applySubst bindings (.var "context") = Data.context context)
    (capturedArgument : applySubst bindings (.var "argument") = Data.preterm argument)
    (body : PureReturns program (functionEnvironment terms context inferred argument)
      before functionEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:infer-function", .var "inferred", .var "table", .var "context",
        .var "argument"]) after answer := by
  apply authored_variable_call_returns program bindings (functionEnvironment terms context inferred argument)
    before after "mm0:infer-function" ["inferred", "table", "context", "argument"] functionEquation.body
    answer (by decide) (by decide) (by decide) _ body (by decide)
  simpa [capturedInferred, capturedTerms, capturedContext, capturedArgument] using
    function_clause terms context inferred argument

private theorem uncached_application_body_returns (before middle after : State)
    (terms : Atom) (context : Context) (function argument : Preterm)
    (inferred : Option Kernel.ExpressionType) (answer : Atom)
    (child : ∀ bindings,
      applySubst bindings (.var "table") = terms →
      applySubst bindings (.var "context") = Data.context context →
      applySubst bindings (.var "function") = Data.preterm function →
      PureReturns program bindings before
        (.expression [.symbol "mm0:infer", .var "table", .var "context", .var "function"])
        middle (Data.inferred inferred))
    (handled : PureReturns program (functionEnvironment terms context inferred argument)
      middle functionEquation.body after answer) :
    PureReturns program (environment terms context (.app function argument)) before equation.body
      after answer := by
  rw [body_shape]
  let bindings := environment terms context (.app function argument)
  let bound := ("argument", Data.preterm argument) :: ("function", Data.preterm function) :: bindings
  apply case_returns program bindings bound before before after (.var "expression")
    (Data.preterm (.app function argument)) applicationBody answer _ cases (read_cases_encoded cases)
  · simpa [bindings, environment, applySubst, Subst.lookup] using
      SourceExecution.variable_returns program bindings before "expression"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Data.preterm, bound,
      bindings, environment, Subst.lookup]
  · rw [application_body_shape]
    let computed := ("inferred", Data.inferred inferred) :: bound
    apply let_returns program bound computed before middle after (.var "inferred") _ _
      (Data.inferred inferred) answer
    · exact child bound
        (by simp [bound, bindings, environment, applySubst, Subst.lookup])
        (by simp [bound, bindings, environment, applySubst, Subst.lookup])
        (by rfl)
    · simp [SourceProgram.matchValue, matchAtom, computed, bound, bindings, environment, Subst.lookup]
    · exact function_captured_returns computed middle after terms context inferred argument answer
        (by rfl) (by simp [computed, bound, bindings, environment, applySubst, Subst.lookup])
        (by simp [computed, bound, bindings, environment, applySubst, Subst.lookup])
        (by simp [computed, bound, applySubst, Subst.lookup]) handled

private theorem uncached_captured_of_body (bindings : Subst) (before after : State)
    (terms : Atom) (context : Context) (expression : Preterm) (answer : Atom)
    (termsName contextName expressionName : String)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression)
    (body : PureReturns program (environment terms context expression) before equation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:infer-uncached", .var termsName, .var contextName, .var expressionName])
      after answer := by
  apply authored_variable_call_returns program bindings (environment terms context expression) before after
    "mm0:infer-uncached" [termsName, contextName, expressionName] equation.body answer
    (by decide) (by decide) (by decide) _ body (by decide)
  simpa [capturedTerms, capturedContext, capturedExpression] using clause terms context expression

/-- Every expression runs through the retained recursive inference code and
returns the kernel's answer. Cache coherence is preserved, the term table
stays frozen, and the recursive child contract is discharged by structural
induction rather than assumed. -/
theorem returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after,
      (∀ bindings termsName contextName expressionName,
        applySubst bindings (.var termsName) = tableValue handle →
        applySubst bindings (.var contextName) = Data.context context →
        applySubst bindings (.var expressionName) = Data.preterm expression →
        PureReturns program bindings state
          (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
          after (Data.inferred (Preterm.infer (signatureOf entries) context expression))) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) state after := by
  induction expression generalizing state with
  | var index => exact variable_returns state (signatureOf entries) handle cache context index ready
  | term index => exact term_returns state handle cache entries context index uniqueRows allocated ready
  | app function argument ihFunction ihArgument =>
      apply InferenceCache.settle (signatureOf entries) (tableValue handle) cache
        (TableAccess.table_literal handle) (context, .app function argument) state ready
      obtain ⟨middle, functionPath, readyMiddle, frameFunction⟩ := ihFunction state allocated ready
      have middleAllocated : middle.read handle = some (declarationRows entries) := by
        rw [frameFunction.other handle separate]
        exact allocated
      let bound := max (sizeOf function) (sizeOf argument)
      have smaller : bound < sizeOf (Preterm.app function argument) := by
        change max (sizeOf function) (sizeOf argument) < 1 + sizeOf function + sizeOf argument
        omega
      have functionFrame : InferenceCache.Frame cache (tableValue handle) bound state middle :=
        frameFunction.weaken (Nat.le_max_left _ _)
      have pathFunction (bindings : Subst)
          (capturedTerms : applySubst bindings (.var "table") = tableValue handle)
          (capturedContext : applySubst bindings (.var "context") = Data.context context)
          (capturedFunction : applySubst bindings (.var "function") = Data.preterm function) :=
        functionPath bindings "table" "context" "function" capturedTerms capturedContext capturedFunction
      have lift (after : State) (inferred : Option Kernel.ExpressionType)
          (same : Preterm.infer (signatureOf entries) context function = inferred)
          (handled : PureReturns program (functionEnvironment (tableValue handle) context inferred argument)
            middle functionEquation.body after
            (Data.inferred (Preterm.infer (signatureOf entries) context (.app function argument))))
          (readyAfter : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after)
          (frame : InferenceCache.Frame cache (tableValue handle) bound state after) :
          ∃ after bound,
            (∀ bindings termsName contextName expressionName,
              applySubst bindings (.var termsName) = tableValue handle →
              applySubst bindings (.var contextName) = Data.context context →
              applySubst bindings (.var expressionName) = Data.preterm (.app function argument) →
              PureReturns program bindings state
                (.expression [.symbol "mm0:infer-uncached", .var termsName, .var contextName,
                  .var expressionName]) after
                (InferenceCache.observation (signatureOf entries) (context, .app function argument))) ∧
            InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
            InferenceCache.Frame cache (tableValue handle) bound state after ∧
            bound < sizeOf (Preterm.app function argument) := by
        refine ⟨after, bound, ?_, readyAfter, frame, smaller⟩
        intro bindings termsName contextName expressionName capturedTerms capturedContext capturedExpression
        apply uncached_captured_of_body bindings state after (tableValue handle) context
          (.app function argument) _ termsName contextName expressionName capturedTerms capturedContext capturedExpression
        apply uncached_application_body_returns state middle after (tableValue handle) context function argument
          inferred _ _ handled
        intro bindings capturedTerms capturedContext capturedFunction
        simpa only [same] using pathFunction bindings capturedTerms capturedContext capturedFunction
      cases inferredFunction : Preterm.infer (signatureOf entries) context function with
      | none =>
          have refused : Preterm.infer (signatureOf entries) context (.app function argument) = none := by
            simp [Preterm.infer, inferredFunction]
          exact lift middle none inferredFunction
            (by simpa only [refused, Data.inferred] using
              function_none_body_returns middle (tableValue handle) context argument)
            readyMiddle functionFrame
      | some inferred =>
          rcases inferred with ⟨arguments, result⟩
          cases arguments with
          | nil =>
              have refused : Preterm.infer (signatureOf entries) context (.app function argument) = none := by
                simp [Preterm.infer, inferredFunction]
              exact lift middle (some ([], result)) inferredFunction
                (by simpa only [refused, Data.inferred] using
                  (function_some_body_returns middle middle (tableValue handle) context [] result argument
                    (.symbol "None") (arguments_nil_body_returns middle (tableValue handle) context result argument)))
                readyMiddle functionFrame
          | cons binder rest =>
              cases binder with
              | bound expected =>
                  have answer : Preterm.infer (signatureOf entries) context (.app function argument) =
                      if Preterm.boundSort? context argument = some expected then some (rest, result) else none := by
                    simp [Preterm.infer, inferredFunction]
                  exact lift middle (some (.bound expected :: rest, result)) inferredFunction
                    (by simpa only [answer] using
                      (function_some_body_returns middle middle (tableValue handle) context
                        (.bound expected :: rest) result argument _
                        (arguments_bound_body_returns middle (tableValue handle) context rest expected result argument)))
                    readyMiddle functionFrame
              | regular expected dependencies =>
                  obtain ⟨after, argumentPath, readyAfter, frameArgument⟩ :=
                    ihArgument middle middleAllocated readyMiddle
                  have answer : Preterm.infer (signatureOf entries) context (.app function argument) =
                      if Preterm.infer (signatureOf entries) context argument = some ([], expected)
                      then some (rest, result) else none := by
                    simp [Preterm.infer, inferredFunction]
                  apply lift after (some (.regular expected dependencies :: rest, result)) inferredFunction _
                    readyAfter (functionFrame.trans (frameArgument.weaken (Nat.le_max_right _ _)))
                  rw [answer]
                  apply function_some_body_returns middle after (tableValue handle) context
                    (.regular expected dependencies :: rest) result argument
                  apply arguments_regular_body_returns middle after (signatureOf entries) (tableValue handle)
                    context rest expected result dependencies argument
                  intro bindings capturedTerms capturedContext capturedArgument
                  exact argumentPath bindings "table" "context" "argument" capturedTerms capturedContext capturedArgument

def request : Atom :=
  .expression [.symbol "mm0:infer", .var "table", .var "context", .var "expression"]

def requestConfiguration (state : State) (handle : Handle) (context : Context)
    (expression : Preterm) : Configuration :=
  { state, control := .evaluate (environment (tableValue handle) context expression) request }

theorem sufficient_fuel (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration state handle context expression) =
        .complete after [Data.inferred (Preterm.infer (signatureOf entries) context expression)] [] []) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) (sizeOf expression) state after := by
  obtain ⟨after, path, readyAfter, frame⟩ := returns handle cache entries uniqueRows separate context expression
    state allocated ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (environment (tableValue handle) context expression) state after request _
    (path _ "table" "context" "expression" rfl rfl rfl)
  exact ⟨after, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

/-- Preservation and reflection of completed inference, including `None`.
Fuel exhaustion and native faults are not completed refusals. -/
theorem result_iff_source_returns (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state)
    (answer : Option Kernel.ExpressionType) :
    Preterm.infer (signatureOf entries) context expression = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context expression) =
        .complete after [Data.inferred answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _, _⟩ :=
    sufficient_fuel handle cache entries uniqueRows separate context expression state allocated ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, accepted⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] []
      referenceCompleted accepted
    exact Data.inferred_injective (List.singleton_inj.mp same.2.1)

theorem typing_iff_source_accepts (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context remaining : Context) (expression : Preterm) (sort : Nat) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    Preterm.HasType (signatureOf entries) context expression remaining sort ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context expression) =
        .complete after [Data.inferred (some (remaining, sort))] [] [] :=
  (Preterm.infer_eq_some_iff (signatureOf entries) context expression remaining sort).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate context expression state
      allocated ready (some (remaining, sort)))

theorem refusal_iff_source_returns_none (handle cache : Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (context : Context) (expression : Preterm) (state : State)
    (allocated : state.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state) :
    (¬ ∃ remaining sort, Preterm.HasType (signatureOf entries) context expression remaining sort) ↔
      ∃ after fuel, run program fuel (requestConfiguration state handle context expression) =
        .complete after [.symbol "None"] [] [] :=
  (Preterm.infer_none_iff (signatureOf entries) context expression).symm.trans
    (result_iff_source_returns handle cache entries uniqueRows separate context expression state
      allocated ready none)

namespace Controls

private def emptyState (cache : Handle) : State :=
  { core := [], next := 2, spaces := fun _ => [],
    cells := fun name => if name = InferenceCache.cell then some (SourcePrimitives.handleValue cache) else none }

def initial : State := emptyState (.privateSpace 1)

private theorem initial_ready :
    InferenceCache.Ready (signatureOf []) (tableValue (.privateSpace 0)) (.privateSpace 1) initial := by
  refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;>
    simp [initial, emptyState, NamedSpaces.Store.read]

private theorem initial_allocated :
    initial.read (.privateSpace 0) = some (declarationRows []) := by
  simp [initial, emptyState, NamedSpaces.Store.read, declarationRows, Store.rows]

/-- A bound function slot accepts its bound variable. -/
theorem bound_variable_typed :
    ∃ after fuel, run program fuel
      (requestConfiguration initial (.privateSpace 0) [.bound 7] (.var 0)) =
        .complete after [Data.inferred (some ([], 7))] [] [] := by
  apply (result_iff_source_returns (.privateSpace 0) (.privateSpace 1) []
    (by intro index; simp) (by decide) [.bound 7] (.var 0) initial initial_allocated
    (by simpa [signatureOf] using initial_ready) (some ([], 7))).mp
  rfl

/-- A context does not manufacture an entry for a missing variable. -/
theorem missing_variable_refused :
    ∃ after fuel, run program fuel (requestConfiguration initial (.privateSpace 0) [] (.var 0)) =
      .complete after [.symbol "None"] [] [] := by
  apply (result_iff_source_returns (.privateSpace 0) (.privateSpace 1) []
    (by intro index; simp) (by decide) [] (.var 0) initial initial_allocated initial_ready none).mp
  rfl

end Controls

end Mettapedia.Languages.MM0.MeTTa.Inference
