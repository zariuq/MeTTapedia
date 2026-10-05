import Mettapedia.Languages.MM0.MeTTa.ConversionResults
import Mettapedia.Languages.MM0.MeTTa.BinderChecking

/-!
# Conversion argument guards in the retained MM0 source

Congruence checks each child's sort and both endpoints against the declared
binder. These source components preserve the actual evaluation order, arity
checks and completed refusals. Conversion's structural witness/list theorem
supplies their recursive child and remaining-argument executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ConversionArguments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open Kernel (Binder)
open Store (natural)
open ListAccess (listValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)

private def sortEquation : SourceProgram.Equation := (kernelSource.program.equations.take 34)[33]'(by decide)
private def checkedEquation : SourceProgram.Equation := (kernelSource.program.equations.take 35)[34]'(by decide)
private def argumentEquation : SourceProgram.Equation := (kernelSource.program.equations.take 33)[32]'(by decide)
private def listEquation : SourceProgram.Equation := (kernelSource.program.equations.take 31)[30]'(by decide)
private def viewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 32)[31]'(by decide)
private def listEnvironment (terms definitions : Atom) (context : Kernel.Context) (children : List Atom) (binders : Kernel.Context) : Subst :=
  [("formal", Data.context binders), ("children", listValue children), ("context", Data.context context), ("definitions", definitions), ("table", terms)]
private def viewEnvironment (terms definitions : Atom) (context : Kernel.Context) (children : List Atom) (binders : Kernel.Context) : Subst :=
  [("context", Data.context context), ("definitions", definitions), ("table", terms),
    ("valueInputValue", ListAccess.viewValue (binders.map Data.binder)), ("valueInput", ListAccess.viewValue children)]
private def argumentEnvironment (result : Option Kernel.ConversionResult) (terms definitions : Atom)
    (context : Kernel.Context) (children : Atom) (binder : Binder) (binders : Kernel.Context) : Subst :=
  [("binders", Data.context binders), ("binder", Data.binder binder), ("children", children),
    ("context", Data.context context), ("definitions", definitions), ("table", terms),
    ("valueInput", ConversionResults.resultValue result)]
private def sortEnvironment (binder : Binder) : Subst := [("valueInput", Data.binder binder)]
private def checkedEnvironment (sortOK leftOK rightOK : Bool) (terms definitions context children binders left right : Atom) : Subst :=
  [("right", right), ("left", left), ("binders", binders), ("children", children), ("context", context),
    ("definitions", definitions), ("table", terms), ("right-okInput", boolean rightOK),
    ("left-okInput", boolean leftOK), ("sort-okInput", boolean sortOK)]
private def sourceCases (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def sortCases := sourceCases sortEquation.body
private def checkedCases := sourceCases checkedEquation.body
private def argumentCases := sourceCases argumentEquation.body
private def convertedBody : Atom := (argumentCases[1]'(by decide)).2
private def viewCases := sourceCases viewEquation.body
private def emptyBody : Atom := (viewCases[0]'(by decide)).2
private def consBody : Atom := (viewCases[3]'(by decide)).2
private theorem list_unique : program.equations.filter (fun e => e.head == "mm0:conversion-arguments") = [listEquation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:conversion-arguments-view") = [viewEquation] := by decide
private theorem list_formals : listEquation.arguments = [.var "table", .var "definitions", .var "context", .var "children", .var "formal"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "valueInputValue", .var "table", .var "definitions", .var "context"] := by decide
private theorem list_body_shape : listEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "children"],
      .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "formal"],
        .expression [.symbol "mm0:conversion-arguments-view", .var "view", .var "view2", .var "table", .var "definitions", .var "context"]]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
      .expression (viewCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem view_cases_shape : viewCases = [(.expression [.symbol "List:Nil", .symbol "List:Nil"], emptyBody),
    (.expression [.symbol "List:Nil", .expression [.symbol "List:Cons", .var "binder", .var "binders"]], .symbol "None"),
    (.expression [.expression [.symbol "List:Cons", .var "child", .var "children"], .symbol "List:Nil"], .symbol "None"),
    (.expression [.expression [.symbol "List:Cons", .var "child", .var "children"], .expression [.symbol "List:Cons", .var "binder", .var "binders"]], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem empty_body_shape : emptyBody =
    .expression [.symbol "let", .var "items", listValue [], .expression [.symbol "let", .var "items2", listValue [],
      .expression [.symbol "MM0:ConvertedArgs", .var "items", .var "items2"]]] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "converted", .expression [.symbol "mm0:conversion", .var "table", .var "definitions", .var "context", .var "child"],
      .expression [.symbol "mm0:conversion-argument", .var "converted", .var "table", .var "definitions", .var "context", .var "children", .var "binder", .var "binders"]] := by decide
private def continuationBody : Atom := (checkedCases[0]'(by decide)).2
private theorem sort_unique : program.equations.filter (fun e => e.head == "mm0:conversion-binder-sort") = [sortEquation] := by decide
private theorem checked_unique : program.equations.filter (fun e => e.head == "mm0:conversion-argument-checked") = [checkedEquation] := by decide
private theorem argument_unique : program.equations.filter (fun e => e.head == "mm0:conversion-argument") = [argumentEquation] := by decide
private theorem argument_formals : argumentEquation.arguments = [.var "valueInput", .var "table", .var "definitions", .var "context",
    .var "children", .var "binder", .var "binders"] := by decide
private theorem argument_body_shape : argumentEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (argumentCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem argument_cases_shape : argumentCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Converted", .var "left", .var "right", .var "sort"], convertedBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem converted_body_shape : convertedBody =
    .expression [.symbol "let", .var "equal", .expression [.symbol "let", .var "conversionBinderSortResult",
      .expression [.symbol "mm0:conversion-binder-sort", .var "binder"],
      .expression [.symbol "mm0:data-eq", .var "sort", .var "conversionBinderSortResult"]],
      .expression [.symbol "let", .var "binderFits", .expression [.symbol "mm0:check-binder", .var "table", .var "context", .var "left", .var "binder"],
        .expression [.symbol "let", .var "binderFits2", .expression [.symbol "mm0:check-binder", .var "table", .var "context", .var "right", .var "binder"],
          .expression [.symbol "mm0:conversion-argument-checked", .var "equal", .var "binderFits", .var "binderFits2", .var "table",
            .var "definitions", .var "context", .var "children", .var "binders", .var "left", .var "right"]]]] := by decide
private theorem sort_formals : sortEquation.arguments = [.var "valueInput"] := by decide
private theorem checked_formals : checkedEquation.arguments = [.var "sort-okInput", .var "left-okInput", .var "right-okInput", .var "table", .var "definitions",
    .var "context", .var "children", .var "binders", .var "left", .var "right"] := by decide
private theorem sort_body_shape : sortEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"], .expression (sortCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem sort_cases_shape : sortCases = [(.expression [listValue [.symbol "MM0:Bound", .var "sort"]], .var "sort"),
    (.expression [listValue [.symbol "MM0:Regular", .var "sort", .var "dependencies"]], .var "sort"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem checked_body_shape : checkedEquation.body =
    .expression [.symbol "case", .expression [.var "sort-okInput", .var "left-okInput", .var "right-okInput"],
      .expression (checkedCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem checked_cases_shape : checkedCases = [(.expression [boolean true, boolean true, boolean true], continuationBody),
    (.expression [.var "sort-ok", .var "left-ok", .var "right-ok"], .symbol "None"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem continuation_body_shape : continuationBody =
    .expression [.symbol "let", .var "conversionArgumentsResult", .expression [.symbol "mm0:conversion-arguments", .var "table", .var "definitions", .var "context", .var "children", .var "binders"],
      .expression [.symbol "mm0:conversion-argument-tail", .var "conversionArgumentsResult", .var "left", .var "right"]] := by decide
private theorem sort_clause (binder : Binder) :
    clauses program "mm0:conversion-binder-sort" [Data.binder binder] = [.evaluate (sortEnvironment binder) sortEquation.body] := by
  rw [clauses_use_only_the_named_equations, sort_unique]
  simp [sort_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, sortEnvironment]
private theorem checked_clause (sortOK leftOK rightOK : Bool) (terms definitions context children binders left right : Atom) :
    clauses program "mm0:conversion-argument-checked" [boolean sortOK, boolean leftOK, boolean rightOK, terms, definitions, context, children, binders, left, right] =
      [.evaluate (checkedEnvironment sortOK leftOK rightOK terms definitions context children binders left right) checkedEquation.body] := by
  rw [clauses_use_only_the_named_equations, checked_unique]
  simp [checked_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, checkedEnvironment]
private theorem argument_clause (result : Option Kernel.ConversionResult) (terms definitions : Atom)
    (context : Kernel.Context) (children : Atom) (binder : Binder) (binders : Kernel.Context) :
    clauses program "mm0:conversion-argument" [ConversionResults.resultValue result, terms, definitions, Data.context context, children, Data.binder binder, Data.context binders] =
      [.evaluate (argumentEnvironment result terms definitions context children binder binders) argumentEquation.body] := by
  rw [clauses_use_only_the_named_equations, argument_unique]
  simp [argument_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, argumentEnvironment]
private theorem list_clause (terms definitions : Atom) (context : Kernel.Context) (children : List Atom) (binders : Kernel.Context) :
    clauses program "mm0:conversion-arguments" [terms, definitions, Data.context context, listValue children, Data.context binders] =
      [.evaluate (listEnvironment terms definitions context children binders) listEquation.body] := by
  rw [clauses_use_only_the_named_equations, list_unique]
  simp [list_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, listEnvironment]
private theorem view_clause (terms definitions : Atom) (context : Kernel.Context) (children : List Atom) (binders : Kernel.Context) :
    clauses program "mm0:conversion-arguments-view" [ListAccess.viewValue children, ListAccess.viewValue (binders.map Data.binder), terms, definitions, Data.context context] =
      [.evaluate (viewEnvironment terms definitions context children binders) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]

theorem sort_body_returns (state : State) (binder : Binder) :
    PureReturns program (sortEnvironment binder) state sortEquation.body state (natural binder.sort) := by
  rw [sort_body_shape]
  cases binder with
  | bound sort =>
      let bindings := sortEnvironment (.bound sort)
      let bound := ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.expression [.var "valueInput"]) (.expression [Data.binder (.bound sort)]) (.var "sort") _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, sortEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [sort_cases_shape, Data.binder, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, bound, bindings, sortEnvironment, Subst.lookup]
      · simpa [Binder.sort, bound, applySubst, Subst.lookup] using variable_returns program bound state "sort"
  | regular sort dependencies =>
      let bindings := sortEnvironment (.regular sort dependencies)
      let bound := ("dependencies", Data.dependencies dependencies) :: ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.expression [.var "valueInput"]) (.expression [Data.binder (.regular sort dependencies)]) (.var "sort") _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, sortEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [sort_cases_shape, Data.binder, listValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, bound, bindings, sortEnvironment, Subst.lookup]
      · simpa [Binder.sort, bound, applySubst, Subst.lookup] using variable_returns program bound state "sort"

theorem sort_captured_returns (bindings : Subst) (state : State) (binder : Binder) (name : String)
    (captured : applySubst bindings (.var name) = Data.binder binder) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-binder-sort", .var name]) state (natural binder.sort) := by
  apply authored_variable_call_returns program bindings (sortEnvironment binder) state state
    "mm0:conversion-binder-sort" [name] sortEquation.body _ (by decide) (by decide) (by decide) _ (sort_body_returns state binder) (by decide)
  simpa [captured] using sort_clause binder

theorem failed_guard_body_returns (state : State) (sortOK leftOK rightOK : Bool)
    (terms definitions context children binders left right : Atom)
    (failed : sortOK = false ∨ leftOK = false ∨ rightOK = false) :
    PureReturns program (checkedEnvironment sortOK leftOK rightOK terms definitions context children binders left right)
      state checkedEquation.body state (.symbol "None") := by
  rw [checked_body_shape]
  let bindings := checkedEnvironment sortOK leftOK rightOK terms definitions context children binders left right
  let bound := ("right-ok", boolean rightOK) :: ("left-ok", boolean leftOK) :: ("sort-ok", boolean sortOK) :: bindings
  apply case_returns program bindings bound state state state (.expression [.var "sort-okInput", .var "left-okInput", .var "right-okInput"])
    (.expression [boolean sortOK, boolean leftOK, boolean rightOK]) (.symbol "None") _ _ checkedCases (read_cases_encoded checkedCases)
  · simpa [bindings, checkedEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["sort-okInput", "left-okInput", "right-okInput"]
  · cases sortOK <;> cases leftOK <;> cases rightOK
    all_goals simp_all [checked_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, boolean, bound, bindings, checkedEnvironment, Subst.lookup]
  · exact symbol_returns program bound state "None"

theorem failed_guard_captured_returns (bindings : Subst) (state : State) (sortOK leftOK rightOK : Bool)
    (terms definitions context children binders left right : Atom)
    (sortName leftOKName rightOKName termsName definitionsName contextName childrenName bindersName leftName rightName : String)
    (capturedSort : applySubst bindings (.var sortName) = boolean sortOK)
    (capturedLeftOK : applySubst bindings (.var leftOKName) = boolean leftOK)
    (capturedRightOK : applySubst bindings (.var rightOKName) = boolean rightOK)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDefinitions : applySubst bindings (.var definitionsName) = definitions)
    (capturedContext : applySubst bindings (.var contextName) = context)
    (capturedChildren : applySubst bindings (.var childrenName) = children)
    (capturedBinders : applySubst bindings (.var bindersName) = binders)
    (capturedLeft : applySubst bindings (.var leftName) = left)
    (capturedRight : applySubst bindings (.var rightName) = right)
    (failed : sortOK = false ∨ leftOK = false ∨ rightOK = false) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:conversion-argument-checked", .var sortName, .var leftOKName, .var rightOKName, .var termsName,
        .var definitionsName, .var contextName, .var childrenName, .var bindersName, .var leftName, .var rightName]) state (.symbol "None") := by
  apply authored_variable_call_returns program bindings (checkedEnvironment sortOK leftOK rightOK terms definitions context children binders left right) state state
    "mm0:conversion-argument-checked" [sortName, leftOKName, rightOKName, termsName, definitionsName, contextName, childrenName, bindersName, leftName, rightName]
    checkedEquation.body _ (by decide) (by decide) (by decide) _ (failed_guard_body_returns state sortOK leftOK rightOK terms definitions context children binders left right failed) (by decide)
  simpa [capturedSort, capturedLeftOK, capturedRightOK, capturedTerms, capturedDefinitions, capturedContext, capturedChildren, capturedBinders, capturedLeft, capturedRight] using
    checked_clause sortOK leftOK rightOK terms definitions context children binders left right

/-- Composition of the actual successful guard branch with a checked tail.
The recursive conversion-arguments call is the premise discharged by the
structural witness/list proof; the source still constructs both extended lists. -/
theorem checked_true_body_returns (before after : State) (terms definitions context children binders : Atom)
    (left right : Kernel.Preterm) (tail : Option (List Kernel.Preterm × List Kernel.Preterm))
    (checkedTail : PureReturns program
      (checkedEnvironment true true true terms definitions context children binders (Data.preterm left) (Data.preterm right))
      before (.expression [.symbol "mm0:conversion-arguments", .var "table", .var "definitions", .var "context", .var "children", .var "binders"])
      after (ConversionResults.argumentsResultValue tail)) :
    PureReturns program
      (checkedEnvironment true true true terms definitions context children binders (Data.preterm left) (Data.preterm right))
      before checkedEquation.body after
      (ConversionResults.argumentsResultValue (tail.map fun values => (left :: values.1, right :: values.2))) := by
  rw [checked_body_shape]
  let bindings := checkedEnvironment true true true terms definitions context children binders (Data.preterm left) (Data.preterm right)
  apply case_returns program bindings bindings before before after
    (.expression [.var "sort-okInput", .var "left-okInput", .var "right-okInput"])
    (.expression [boolean true, boolean true, boolean true]) continuationBody _ _ checkedCases (read_cases_encoded checkedCases)
  · simpa [bindings, checkedEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["sort-okInput", "left-okInput", "right-okInput"]
  · simp [checked_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, boolean]
  · rw [continuation_body_shape]
    let withTail := ("conversionArgumentsResult", ConversionResults.argumentsResultValue tail) :: bindings
    apply let_returns program bindings withTail before after after (.var "conversionArgumentsResult") _ _ (ConversionResults.argumentsResultValue tail) _
    · exact checkedTail
    · simp [SourceProgram.matchValue, matchAtom, withTail, bindings, checkedEnvironment, Subst.lookup]
    · exact ConversionResults.tail_captured_returns withTail after tail left right "conversionArgumentsResult" "left" "right" rfl rfl rfl

/-- The actual remaining-argument call, allowing its caller's captured names. -/
def Call (terms definitions : Atom) (context : Kernel.Context) (children : Atom) (binders : Kernel.Context)
    (before after : State) (result : Option (List Kernel.Preterm × List Kernel.Preterm)) : Prop :=
  ∀ bindings termsName definitionsName contextName childrenName bindersName,
    applySubst bindings (.var termsName) = terms →
    applySubst bindings (.var definitionsName) = definitions →
    applySubst bindings (.var contextName) = Data.context context →
    applySubst bindings (.var childrenName) = children →
    applySubst bindings (.var bindersName) = Data.context binders →
    PureReturns program bindings before
      (.expression [.symbol "mm0:conversion-arguments", .var termsName, .var definitionsName,
        .var contextName, .var childrenName, .var bindersName]) after (ConversionResults.argumentsResultValue result)

theorem checked_true_captured_returns (bindings : Subst) (before after : State)
    (terms definitions : Atom) (context : Kernel.Context) (children : Atom) (binders : Kernel.Context)
    (left right : Kernel.Preterm) (tail : Option (List Kernel.Preterm × List Kernel.Preterm))
    (checkedTail : Call terms definitions context children binders before after tail)
    (sortName leftOKName rightOKName termsName definitionsName contextName childrenName bindersName leftName rightName : String)
    (capturedSort : applySubst bindings (.var sortName) = boolean true)
    (capturedLeftOK : applySubst bindings (.var leftOKName) = boolean true)
    (capturedRightOK : applySubst bindings (.var rightOKName) = boolean true)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDefinitions : applySubst bindings (.var definitionsName) = definitions)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedChildren : applySubst bindings (.var childrenName) = children)
    (capturedBinders : applySubst bindings (.var bindersName) = Data.context binders)
    (capturedLeft : applySubst bindings (.var leftName) = Data.preterm left)
    (capturedRight : applySubst bindings (.var rightName) = Data.preterm right) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:conversion-argument-checked", .var sortName, .var leftOKName, .var rightOKName, .var termsName,
        .var definitionsName, .var contextName, .var childrenName, .var bindersName, .var leftName, .var rightName]) after
      (ConversionResults.argumentsResultValue (tail.map fun values => (left :: values.1, right :: values.2))) := by
  apply authored_variable_call_returns program bindings
    (checkedEnvironment true true true terms definitions (Data.context context) children (Data.context binders) (Data.preterm left) (Data.preterm right)) before after
    "mm0:conversion-argument-checked" [sortName, leftOKName, rightOKName, termsName, definitionsName, contextName, childrenName, bindersName, leftName, rightName]
    checkedEquation.body _ (by decide) (by decide) (by decide) _
    (checked_true_body_returns before after terms definitions (Data.context context) children (Data.context binders) left right tail
      (checkedTail _ "table" "definitions" "context" "children" "binders" rfl rfl rfl rfl rfl)) (by decide)
  simpa [capturedSort, capturedLeftOK, capturedRightOK, capturedTerms, capturedDefinitions, capturedContext, capturedChildren, capturedBinders, capturedLeft, capturedRight] using
    checked_clause true true true terms definitions (Data.context context) children (Data.context binders) (Data.preterm left) (Data.preterm right)

/-- Compose both endpoint checks before selecting the tail. The tail execution
is supplied by the structural witness/list induction, not by proof search. -/
theorem argument_body_returns (handle cache : NamedSpaces.Handle) (entries : List ServiceInferenceCache.Row)
    (uniqueRows : ServiceInferenceCache.Unique entries) (separate : handle ≠ cache)
    (definitions : Atom) (context : Kernel.Context) (children : Atom) (binder : Binder) (binders : Kernel.Context)
    (result : Option Kernel.ConversionResult) (tail : Option (List Kernel.Preterm × List Kernel.Preterm)) (before : State)
    (tailReturns : ∀ state, (∃ bound, InferenceCache.Frame cache (tableValue handle) bound before state) →
      state.read handle = some (declarationRows entries) →
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache state →
      ∃ after bound, Call (tableValue handle) definitions context children binders state after tail ∧
        InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
        InferenceCache.Frame cache (tableValue handle) bound state after)
    (allocated : before.read handle = some (declarationRows entries))
    (ready : InferenceCache.Ready (signatureOf entries) (tableValue handle) cache before) :
    ∃ after bound, PureReturns program
      (argumentEnvironment result (tableValue handle) definitions context children binder binders) before argumentEquation.body after
      (ConversionResults.argumentsResultValue (result.bind fun value =>
        if value.sort = binder.sort ∧ Kernel.Preterm.checkBinder (signatureOf entries) context value.left binder = true ∧
          Kernel.Preterm.checkBinder (signatureOf entries) context value.right binder = true then
          tail.map fun values => (value.left :: values.1, value.right :: values.2) else none)) ∧
      InferenceCache.Ready (signatureOf entries) (tableValue handle) cache after ∧
      InferenceCache.Frame cache (tableValue handle) bound before after := by
  rw [argument_body_shape]
  cases result with
  | none =>
      refine ⟨before, 0, ?_, ready, InferenceCache.Frame.refl _ _ _ _⟩
      let bindings := argumentEnvironment none (tableValue handle) definitions context children binder binders
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None") (.symbol "None") _ _ argumentCases (read_cases_encoded argumentCases)
      · simpa [bindings, argumentEnvironment, ConversionResults.resultValue, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
      · simp [argument_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some result =>
      obtain ⟨middle, leftChecked, readyMiddle, leftFrame⟩ := BinderChecking.returns handle cache entries uniqueRows separate context result.left binder before allocated ready
      obtain ⟨tested, rightChecked, readyTested, rightFrame⟩ := BinderChecking.returns handle cache entries uniqueRows separate context result.right binder middle
        (by rw [leftFrame.other handle separate]; exact allocated) readyMiddle
      let sameSort := decide (result.sort = binder.sort)
      let leftOK := Kernel.Preterm.checkBinder (signatureOf entries) context result.left binder
      let rightOK := Kernel.Preterm.checkBinder (signatureOf entries) context result.right binder
      let bindings := argumentEnvironment (some result) (tableValue handle) definitions context children binder binders
      let boundBindings := ("sort", natural result.sort) :: ("right", Data.preterm result.right) :: ("left", Data.preterm result.left) :: bindings
      let withEqual := ("equal", boolean sameSort) :: boundBindings
      let withLeft := ("binderFits", boolean leftOK) :: withEqual
      let withRight := ("binderFits2", boolean rightOK) :: withLeft
      have baseFrame := (leftFrame.weaken (Nat.le_max_left _ _)).trans (rightFrame.weaken (Nat.le_max_right _ _))
      have finish (after : State) (answer : Atom)
          (continued : PureReturns program withRight tested
            (.expression [.symbol "mm0:conversion-argument-checked", .var "equal", .var "binderFits", .var "binderFits2", .var "table",
              .var "definitions", .var "context", .var "children", .var "binders", .var "left", .var "right"]) after answer) :
          PureReturns program bindings before
            (.expression [.symbol "case", .var "valueInput", .expression (argumentCases.map fun e => .expression [e.1,e.2])]) after answer := by
        apply case_returns program bindings boundBindings before before after (.var "valueInput") (ConversionResults.resultValue (some result)) convertedBody _ _ argumentCases (read_cases_encoded argumentCases)
        · simpa [bindings, argumentEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
        · simp [argument_cases_shape, ConversionResults.resultValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
            matchAtom, boundBindings, bindings, argumentEnvironment, Subst.lookup]
        · rw [converted_body_shape]
          apply let_returns program boundBindings withEqual before before after (.var "equal") _ _ (boolean sameSort) _
          · let withSort := ("conversionBinderSortResult", natural binder.sort) :: boundBindings
            apply let_returns program boundBindings withSort before before before (.var "conversionBinderSortResult") _ _ (natural binder.sort) _
            · exact sort_captured_returns boundBindings before binder "binder" rfl
            · simp [SourceProgram.matchValue, matchAtom, withSort, boundBindings, bindings, argumentEnvironment, Subst.lookup]
            · simpa [sameSort, natural] using Scalar.data_equality_captured_returns withSort before (natural result.sort) (natural binder.sort) "sort" "conversionBinderSortResult" rfl rfl
          · simp [SourceProgram.matchValue, matchAtom, withEqual, boundBindings, bindings, argumentEnvironment, Subst.lookup]
          · apply let_returns program withEqual withLeft before middle after (.var "binderFits") _ _ (boolean leftOK) _
            · exact leftChecked withEqual "table" "context" "left" "binder" rfl rfl rfl rfl
            · simp [SourceProgram.matchValue, matchAtom, withLeft, withEqual, boundBindings, bindings, argumentEnvironment, Subst.lookup]
            · apply let_returns program withLeft withRight middle tested after (.var "binderFits2") _ _ (boolean rightOK) _
              · exact rightChecked withLeft "table" "context" "right" "binder" rfl rfl rfl rfl
              · simp [SourceProgram.matchValue, matchAtom, withRight, withLeft, withEqual, boundBindings, bindings, argumentEnvironment, Subst.lookup]
              · exact continued
      by_cases safe : result.sort = binder.sort ∧ Kernel.Preterm.checkBinder (signatureOf entries) context result.left binder = true ∧
          Kernel.Preterm.checkBinder (signatureOf entries) context result.right binder = true
      · obtain ⟨after, tailBound, checkedTail, readyAfter, tailFrame⟩ := tailReturns tested ⟨_, baseFrame⟩
          (by rw [baseFrame.other handle separate]; exact allocated) readyTested
        refine ⟨after, max (max (sizeOf result.left) (sizeOf result.right)) tailBound, ?_, readyAfter,
          (baseFrame.weaken (Nat.le_max_left _ _)).trans (tailFrame.weaken (Nat.le_max_right _ _))⟩
        simp only [Option.bind_some, if_pos safe]
        apply finish
        exact checked_true_captured_returns withRight tested after (tableValue handle) definitions context children binders result.left result.right tail checkedTail
          "equal" "binderFits" "binderFits2" "table" "definitions" "context" "children" "binders" "left" "right"
          (by simp [withRight, withLeft, withEqual, sameSort, safe.1, applySubst, Subst.lookup])
          (by simp [withRight, withLeft, leftOK, safe.2.1, applySubst, Subst.lookup])
          (by simp [withRight, rightOK, safe.2.2, applySubst, Subst.lookup]) rfl rfl rfl rfl rfl rfl rfl
      · refine ⟨tested, max (sizeOf result.left) (sizeOf result.right), ?_, readyTested, baseFrame⟩
        simp only [Option.bind_some, if_neg safe]
        apply finish
        apply failed_guard_captured_returns withRight tested sameSort leftOK rightOK (tableValue handle) definitions (Data.context context) children (Data.context binders)
          (Data.preterm result.left) (Data.preterm result.right) "equal" "binderFits" "binderFits2" "table" "definitions" "context" "children" "binders" "left" "right"
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        by_cases sorts : result.sort = binder.sort
        · by_cases left : leftOK = true
          · exact Or.inr (Or.inr (Bool.eq_false_iff.mpr (fun right => safe ⟨sorts, left, right⟩)))
          · exact Or.inr (Or.inl (Bool.eq_false_iff.mpr left))
        · exact Or.inl (by simp [sameSort, sorts])

theorem argument_captured_returns (bindings : Subst) (before after : State)
    (result : Option Kernel.ConversionResult) (terms definitions : Atom) (context : Kernel.Context)
    (children : Atom) (binder : Binder) (binders : Kernel.Context) (answer : Atom)
    (computed : PureReturns program (argumentEnvironment result terms definitions context children binder binders)
      before argumentEquation.body after answer)
    (resultName termsName definitionsName contextName childrenName binderName bindersName : String)
    (capturedResult : applySubst bindings (.var resultName) = ConversionResults.resultValue result)
    (capturedTerms : applySubst bindings (.var termsName) = terms)
    (capturedDefinitions : applySubst bindings (.var definitionsName) = definitions)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedChildren : applySubst bindings (.var childrenName) = children)
    (capturedBinder : applySubst bindings (.var binderName) = Data.binder binder)
    (capturedBinders : applySubst bindings (.var bindersName) = Data.context binders) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:conversion-argument", .var resultName, .var termsName, .var definitionsName, .var contextName,
        .var childrenName, .var binderName, .var bindersName]) after answer := by
  apply authored_variable_call_returns program bindings (argumentEnvironment result terms definitions context children binder binders) before after
    "mm0:conversion-argument" [resultName, termsName, definitionsName, contextName, childrenName, binderName, bindersName]
    argumentEquation.body answer (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedResult, capturedTerms, capturedDefinitions, capturedContext, capturedChildren, capturedBinder, capturedBinders] using
    argument_clause result terms definitions context children binder binders

theorem call_from_view (terms definitions : Atom) (context : Kernel.Context) (children : List Atom) (binders : Kernel.Context)
    (before after : State) (result : Option (List Kernel.Preterm × List Kernel.Preterm))
    (viewed : PureReturns program (viewEnvironment terms definitions context children binders) before viewEquation.body after
      (ConversionResults.argumentsResultValue result)) :
    Call terms definitions context (listValue children) binders before after result := by
  have body : PureReturns program (listEnvironment terms definitions context children binders) before listEquation.body after
      (ConversionResults.argumentsResultValue result) := by
    rw [list_body_shape]
    let bindings := listEnvironment terms definitions context children binders
    let withView := ("view", ListAccess.viewValue children) :: bindings
    let withBoth := ("view2", ListAccess.viewValue (binders.map Data.binder)) :: withView
    apply let_returns program bindings withView before before after (.var "view") _ _ (ListAccess.viewValue children) _
    · exact ListAccess.view_captured_returns bindings before "children" children rfl
    · simp [SourceProgram.matchValue, matchAtom, withView, bindings, listEnvironment, Subst.lookup]
    · apply let_returns program withView withBoth before before after (.var "view2") _ _ (ListAccess.viewValue (binders.map Data.binder)) _
      · exact ListAccess.view_captured_returns withView before "formal" (binders.map Data.binder) rfl
      · simp [SourceProgram.matchValue, matchAtom, withBoth, withView, bindings, listEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program withBoth (viewEnvironment terms definitions context children binders) before after
          "mm0:conversion-arguments-view" ["view", "view2", "table", "definitions", "context"] viewEquation.body _
          (by decide) (by decide) (by decide) _ viewed (by decide)
        simpa [withBoth, withView, bindings, listEnvironment, applySubst, Subst.lookup] using view_clause terms definitions context children binders
  intro bindings termsName definitionsName contextName childrenName bindersName capturedTerms capturedDefinitions capturedContext capturedChildren capturedBinders
  apply authored_variable_call_returns program bindings (listEnvironment terms definitions context children binders) before after
    "mm0:conversion-arguments" [termsName, definitionsName, contextName, childrenName, bindersName] listEquation.body _
    (by decide) (by decide) (by decide) _ body (by decide)
  simpa [capturedTerms, capturedDefinitions, capturedContext, capturedChildren, capturedBinders] using list_clause terms definitions context children binders

theorem view_empty_returns (terms definitions : Atom) (context : Kernel.Context) (binders : Kernel.Context) (state : State) :
    PureReturns program (viewEnvironment terms definitions context [] binders) state viewEquation.body state
      (ConversionResults.argumentsResultValue (if binders = [] then some ([], []) else none)) := by
  rw [view_body_shape]
  cases binders with
  | nil =>
      let bindings := viewEnvironment terms definitions context [] []
      apply case_returns program bindings bindings state state state (.expression [.var "valueInput", .var "valueInputValue"])
        (.expression [.symbol "List:Nil", .symbol "List:Nil"]) emptyBody _ _ viewCases (read_cases_encoded viewCases)
      · simpa [bindings, viewEnvironment, ListAccess.viewValue, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "valueInputValue"]
      · simp [view_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom]
      · rw [empty_body_shape]
        let withItems := ("items", listValue []) :: bindings
        let withBoth := ("items2", listValue []) :: withItems
        apply let_returns program bindings withItems state state state (.var "items") _ _ (listValue []) _
        · exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
        · simp [SourceProgram.matchValue, matchAtom, withItems, bindings, viewEnvironment, Subst.lookup]
        · apply let_returns program withItems withBoth state state state (.var "items2") _ _ (listValue []) _
          · exact empty_constructor_returns program withItems state "MM0:L" (by decide +kernel) (by decide)
          · simp [SourceProgram.matchValue, matchAtom, withBoth, withItems, bindings, viewEnvironment, Subst.lookup]
          · simpa [ConversionResults.argumentsResultValue, ListSubstitution.expressionsValue, withBoth, withItems, bindings, viewEnvironment, applySubst, Subst.lookup] using
              constructor_variables_return program withBoth state "MM0:ConvertedArgs" ["items", "items2"] (by decide +kernel) (by decide)
  | cons binder binders =>
      let bindings := viewEnvironment terms definitions context [] (binder :: binders)
      let bound := ("binders", Data.context binders) :: ("binder", Data.binder binder) :: bindings
      apply case_returns program bindings bound state state state (.expression [.var "valueInput", .var "valueInputValue"])
        (.expression [ListAccess.viewValue [], ListAccess.viewValue ((binder :: binders).map Data.binder)]) (.symbol "None") _ _ viewCases (read_cases_encoded viewCases)
      · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "valueInputValue"]
      · simp [view_cases_shape, ListAccess.viewValue, listValue, Data.context, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, bound, bindings, viewEnvironment, Subst.lookup]
      · exact symbol_returns program bound state "None"

theorem view_missing_binder_returns (terms definitions : Atom) (context : Kernel.Context) (child : Atom) (children : List Atom) (state : State) :
    PureReturns program (viewEnvironment terms definitions context (child :: children) []) state viewEquation.body state (.symbol "None") := by
  rw [view_body_shape]
  let bindings := viewEnvironment terms definitions context (child :: children) []
  let bound := ("children", listValue children) :: ("child", child) :: bindings
  apply case_returns program bindings bound state state state (.expression [.var "valueInput", .var "valueInputValue"])
    (.expression [ListAccess.viewValue (child :: children), ListAccess.viewValue []]) (.symbol "None") _ _ viewCases (read_cases_encoded viewCases)
  · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput", "valueInputValue"]
  · simp [view_cases_shape, ListAccess.viewValue, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, viewEnvironment, Subst.lookup]
  · exact symbol_returns program bound state "None"

theorem view_cons_returns (terms definitions : Atom) (context : Kernel.Context)
    (child : Atom) (children : List Atom) (binder : Binder) (binders : Kernel.Context)
    (before middle after : State) (result : Option Kernel.ConversionResult) (answer : Atom)
    (childReturned : ∀ bindings termsName definitionsName contextName childName,
      applySubst bindings (.var termsName) = terms → applySubst bindings (.var definitionsName) = definitions →
      applySubst bindings (.var contextName) = Data.context context → applySubst bindings (.var childName) = child →
      PureReturns program bindings before
        (.expression [.symbol "mm0:conversion", .var termsName, .var definitionsName, .var contextName, .var childName]) middle (ConversionResults.resultValue result))
    (argumentReturned : PureReturns program (argumentEnvironment result terms definitions context (listValue children) binder binders)
      middle argumentEquation.body after answer) :
    PureReturns program (viewEnvironment terms definitions context (child :: children) (binder :: binders)) before viewEquation.body after answer := by
  rw [view_body_shape]
  let bindings := viewEnvironment terms definitions context (child :: children) (binder :: binders)
  let bound := ("binders", Data.context binders) :: ("binder", Data.binder binder) :: ("children", listValue children) :: ("child", child) :: bindings
  apply case_returns program bindings bound before before after (.expression [.var "valueInput", .var "valueInputValue"])
    (.expression [ListAccess.viewValue (child :: children), ListAccess.viewValue ((binder :: binders).map Data.binder)]) consBody _ _ viewCases (read_cases_encoded viewCases)
  · simpa [bindings, viewEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
  · simp [view_cases_shape, ListAccess.viewValue, listValue, Data.context, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, bound, bindings, viewEnvironment, Subst.lookup]
  · rw [cons_body_shape]
    let withResult := ("converted", ConversionResults.resultValue result) :: bound
    apply let_returns program bound withResult before middle after (.var "converted") _ _ (ConversionResults.resultValue result) _
    · exact childReturned bound "table" "definitions" "context" "child" rfl rfl rfl rfl
    · simp [SourceProgram.matchValue, matchAtom, withResult, bound, bindings, viewEnvironment, Subst.lookup]
    · exact argument_captured_returns withResult middle after result terms definitions context (listValue children) binder binders answer argumentReturned
        "converted" "table" "definitions" "context" "children" "binder" "binders" rfl rfl rfl rfl rfl rfl rfl

end Mettapedia.Languages.MM0.MeTTa.ConversionArguments
