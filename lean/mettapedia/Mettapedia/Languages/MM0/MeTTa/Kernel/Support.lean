import Mettapedia.Languages.MM0.MeTTa.Data.Data
import Mettapedia.Languages.MM0.Presentation.SupportData

/-!
# Occurrence support computed by the retained MeTTa program

The source keeps repeated occurrences in lists. Their finite-set interpretation
is MM0's independent bound-variable support judgment. Missing variables cause
refusal; successful empty support is a distinct result. All paths below read
the pinned source bodies and preserve the store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Support

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (listValue optionValue)
open Presentation.ComputationalSupport (indices?)

def indicesValue (values : List Nat) : Atom := listValue (values.map natural)

def resultValue (result : Option (List Nat)) : Atom := optionValue (result.map indicesValue)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 146)[145]'(by decide +kernel)

private def binderEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 147)[146]'(by decide +kernel)

private def functionEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 148)[147]'(by decide +kernel)

private def argumentEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 149)[148]'(by decide +kernel)

private def environment (context : Context) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("context", Data.context context)]

private def binderEnvironment (entry : Option Kernel.Binder) (index : Nat) : Subst :=
  [("index", natural index), ("valueInput", optionValue (entry.map Data.binder))]

private def functionEnvironment (result : Option (List Nat)) (context : Context)
    (argument : Preterm) : Subst :=
  [("argument", Data.preterm argument), ("context", Data.context context), ("valueInput", resultValue result)]

private def argumentEnvironment (left : List Nat) (result : Option (List Nat)) : Subst :=
  [("valueInput", resultValue result), ("left", indicesValue left)]

private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def cases := sourceCases equation.body
private def binderCases := sourceCases binderEquation.body
private def functionCases := sourceCases functionEquation.body
private def argumentCases := sourceCases argumentEquation.body
private def variableBody : Atom := (cases[0]'(by decide)).2
private def termBody : Atom := (cases[1]'(by decide)).2
private def appBody : Atom := (cases[2]'(by decide)).2
private def boundBody : Atom := (binderCases[1]'(by decide)).2
private def functionBody : Atom := (functionCases[1]'(by decide)).2
private def argumentBody : Atom := (argumentCases[1]'(by decide)).2

private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:support") = [equation] := by decide

private theorem binder_unique :
    program.equations.filter (fun entry => entry.head == "mm0:support-binder") = [binderEquation] := by decide

private theorem function_unique :
    program.equations.filter (fun entry => entry.head == "mm0:support-function") = [functionEquation] := by decide

private theorem argument_unique :
    program.equations.filter (fun entry => entry.head == "mm0:support-argument") = [argumentEquation] := by decide

private theorem formals : equation.arguments = [.var "context", .var "expression"] := by decide

private theorem binder_formals : binderEquation.arguments = [.var "valueInput", .var "index"] := by decide

private theorem function_formals :
    functionEquation.arguments = [.var "valueInput", .var "context", .var "argument"] := by decide

private theorem argument_formals : argumentEquation.arguments = [.var "left", .var "valueInput"] := by decide

private theorem body_shape :
    equation.body = .expression [.symbol "case", .var "expression",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:Var", .var "index"], variableBody),
      (.expression [.symbol "MM0:Term", .var "index"], termBody),
      (.expression [.symbol "MM0:App", .var "function", .var "argument"], appBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem variable_body_shape :
    variableBody = .expression [.symbol "let", .var "entry",
      .expression [.symbol "mm0:data-at", .var "context", .var "index"],
      .expression [.symbol "mm0:support-binder", .var "entry", .var "index"]] := by decide

private theorem term_body_shape :
    termBody = .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []],
      .expression [.symbol "Some", .var "items"]] := by decide

private theorem app_body_shape :
    appBody = .expression [.symbol "let", .var "supportResult",
      .expression [.symbol "mm0:support", .var "context", .var "function"],
      .expression [.symbol "mm0:support-function", .var "supportResult", .var "context", .var "argument"]] := by decide

private theorem binder_body_shape :
    binderEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (binderCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem binder_cases_shape :
    binderCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Bound", .var "sort"]]], boundBody),
      (.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]]],
          .expression [.symbol "Some", .var "dependencies"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem bound_body_shape :
    boundBody = .expression [.symbol "let", .var "items",
      .expression [.symbol "MM0:L", .expression [.var "index"]],
      .expression [.symbol "Some", .var "items"]] := by decide

private theorem clause (context : Context) (expression : Preterm) :
    clauses program "mm0:support" [Data.context context, Data.preterm expression] =
      [.evaluate (environment context expression) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem binder_clause (entry : Option Kernel.Binder) (index : Nat) :
    clauses program "mm0:support-binder" [optionValue (entry.map Data.binder), natural index] =
      [.evaluate (binderEnvironment entry index) binderEquation.body] := by
  rw [clauses_use_only_the_named_equations, binder_unique]
  simp [binder_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, binderEnvironment]

private def binderResult (entry : Option Kernel.Binder) (index : Nat) : Option (List Nat) :=
  match entry with
  | none => none
  | some (.bound _) => some [index]
  | some (.regular _ values) => some (values.sort (· ≤ ·))

private theorem binder_body_returns (state : State) (entry : Option Kernel.Binder) (index : Nat) :
    PureReturns program (binderEnvironment entry index) state binderEquation.body state
      (resultValue (binderResult entry index)) := by
  rw [binder_body_shape]
  let bindings := binderEnvironment entry index
  have input : PureReturns program bindings state (.var "valueInput") state
      (optionValue (entry.map Data.binder)) := by
    simpa [bindings, binderEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "valueInput"
  cases entry with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ binderCases (read_cases_encoded binderCases) input
      · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some entry =>
      cases entry with
      | bound sort =>
          let bound := ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.bound sort)))) boundBody _ _ binderCases
            (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, binderEnvironment, Subst.lookup]
          · rw [bound_body_shape]
            let wrapped := ("items", indicesValue [index]) :: bound
            apply let_returns program bound wrapped state state state (.var "items") _ _ (indicesValue [index]) _
            · simpa [indicesValue, bound, bindings, binderEnvironment, applySubst, Subst.lookup] using
                ListAccess.list_variables_return bound state ["index"]
            · simp [SpaceSemantics.matchValue, matchAtom, wrapped, bound, bindings, binderEnvironment, Subst.lookup]
            · simpa [wrapped, resultValue, binderResult, optionValue, applySubst, Subst.lookup] using
                unary_constructor_returns program wrapped state "Some" "items" some_is_data_constructor (by decide)
      | regular sort values =>
          let bound := ("dependencies", Data.dependencies values) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (optionValue (some (Data.binder (.regular sort values))))
            (.expression [.symbol "Some", .var "dependencies"]) _ _ binderCases
            (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, Data.binder, listValue,
              bound, bindings, binderEnvironment, Subst.lookup]
          · simpa [bound, indicesValue, resultValue, binderResult, Data.dependencies, optionValue,
                applySubst, Subst.lookup] using
              unary_constructor_returns program bound state "Some" "dependencies" some_is_data_constructor (by decide)

private theorem function_body_shape :
    functionEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (functionCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem function_cases_shape :
    functionCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "left"], functionBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem function_some_body_shape :
    functionBody = .expression [.symbol "let", .var "supportResult",
      .expression [.symbol "mm0:support", .var "context", .var "argument"],
      .expression [.symbol "mm0:support-argument", .var "left", .var "supportResult"]] := by decide

private theorem argument_body_shape :
    argumentEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (argumentCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem argument_cases_shape :
    argumentCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "right"], argumentBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem argument_some_body_shape :
    argumentBody = .expression [.symbol "let", .var "combined",
      .expression [.symbol "mm0:list-append", .var "left", .var "right"],
      .expression [.symbol "Some", .var "combined"]] := by decide

private theorem function_clause (result : Option (List Nat)) (context : Context) (argument : Preterm) :
    clauses program "mm0:support-function" [resultValue result, Data.context context, Data.preterm argument] =
      [.evaluate (functionEnvironment result context argument) functionEquation.body] := by
  rw [clauses_use_only_the_named_equations, function_unique]
  simp [function_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, functionEnvironment]

private theorem argument_clause (left : List Nat) (result : Option (List Nat)) :
    clauses program "mm0:support-argument" [indicesValue left, resultValue result] =
      [.evaluate (argumentEnvironment left result) argumentEquation.body] := by
  rw [clauses_use_only_the_named_equations, argument_unique]
  simp [argument_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, argumentEnvironment]

private theorem argument_body_returns (state : State) (left : List Nat) (result : Option (List Nat)) :
    PureReturns program (argumentEnvironment left result) state argumentEquation.body state
      (resultValue (result.map fun right => left ++ right)) := by
  rw [argument_body_shape]
  let bindings := argumentEnvironment left result
  have input : PureReturns program bindings state (.var "valueInput") state (resultValue result) := by
    simpa [bindings, argumentEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ argumentCases (read_cases_encoded argumentCases) input
      · simp [argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some right =>
      let bound := ("right", indicesValue right) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (resultValue (some right)) argumentBody _ _ argumentCases (read_cases_encoded argumentCases) input
      · simp [argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue, bound,
          bindings, argumentEnvironment, Subst.lookup]
      · rw [argument_some_body_shape]
        let combined := ("combined", indicesValue (left ++ right)) :: bound
        apply let_returns program bound combined state state state (.var "combined") _ _
          (indicesValue (left ++ right)) _
        · simpa [indicesValue, List.map_append] using
            (ListAccess.append_captured_returns bound state (left.map natural) (right.map natural)
              "left" "right"
              (by simp [bound, bindings, argumentEnvironment, indicesValue, applySubst, Subst.lookup]) (by rfl))
        · simp [SpaceSemantics.matchValue, matchAtom, combined, bound, bindings, argumentEnvironment, Subst.lookup]
        · simpa [combined, resultValue, optionValue, applySubst, Subst.lookup] using
            unary_constructor_returns program combined state "Some" "combined" some_is_data_constructor (by decide)

private theorem function_body_returns (state : State) (result : Option (List Nat))
    (context : Context) (argument : Preterm)
    (recursive : PureReturns program (environment context argument) state equation.body state
      (resultValue (indices? context argument))) :
    PureReturns program (functionEnvironment result context argument) state functionEquation.body state
      (resultValue (result.bind fun left => (indices? context argument).map fun right => left ++ right)) := by
  rw [function_body_shape]
  let bindings := functionEnvironment result context argument
  have input : PureReturns program bindings state (.var "valueInput") state (resultValue result) := by
    simpa [bindings, functionEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ functionCases (read_cases_encoded functionCases) input
      · simp [function_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some left =>
      let bound := ("left", indicesValue left) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (resultValue (some left)) functionBody _ _ functionCases (read_cases_encoded functionCases) input
      · simp [function_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue, bound,
          bindings, functionEnvironment, Subst.lookup]
      · rw [function_some_body_shape]
        let supported := ("supportResult", resultValue (indices? context argument)) :: bound
        apply let_returns program bound supported state state state (.var "supportResult") _ _
          (resultValue (indices? context argument)) _
        · apply authored_variable_call_returns program bound (environment context argument) state state
            "mm0:support" ["context", "argument"] equation.body _
            (by decide) (by decide) (by decide) _ recursive (by decide)
          simpa [bound, bindings, functionEnvironment, applySubst, Subst.lookup] using clause context argument
        · simp [SpaceSemantics.matchValue, matchAtom, supported, bound, bindings, functionEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program supported (argumentEnvironment left (indices? context argument))
            state state "mm0:support-argument" ["left", "supportResult"] argumentEquation.body _
            (by decide) (by decide) (by decide) _
            (argument_body_returns state left (indices? context argument)) (by decide)
          simpa [supported, bound, bindings, functionEnvironment, applySubst, Subst.lookup] using
            argument_clause left (indices? context argument)

theorem body_returns (state : State) (context : Context) (expression : Preterm) :
    PureReturns program (environment context expression) state equation.body state
      (resultValue (indices? context expression)) := by
  induction expression with
  | var index =>
      let bindings := environment context (.var index)
      let bound := ("index", natural index) :: bindings
      rw [body_shape]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.var index)) variableBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm,
          bindings, bound, environment, Subst.lookup]
      · rw [variable_body_shape]
        let entry := ("entry", optionValue (context[index]?.map Data.binder)) :: bound
        apply let_returns program bound entry state state state (.var "entry") _ _
          (optionValue (context[index]?.map Data.binder)) _
        · simpa [Data.context, List.getElem?_map] using
            (ListAccess.data_at_list_returns bound state (context.map Data.binder) index "context" "index"
              (by simp [bound, bindings, environment, Data.context, applySubst, Subst.lookup]) (by rfl))
        · simp [SpaceSemantics.matchValue, matchAtom, entry, bound, bindings, environment, Subst.lookup]
        · have computed : indices? context (.var index) = binderResult context[index]? index := by
            cases lookup : context[index]? with
            | none => simp [indices?, binderResult, lookup]
            | some binder => cases binder <;> simp [indices?, binderResult, lookup]
          rw [computed]
          apply authored_variable_call_returns program entry (binderEnvironment context[index]? index)
            state state "mm0:support-binder" ["entry", "index"] binderEquation.body _
            (by decide) (by decide) (by decide) _ (binder_body_returns state context[index]? index) (by decide)
          simpa [entry, bound, bindings, environment, applySubst, Subst.lookup] using
            binder_clause context[index]? index
  | term index =>
      let bindings := environment context (.term index)
      let bound := ("index", natural index) :: bindings
      rw [body_shape]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.term index)) termBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm,
          bindings, bound, environment, Subst.lookup]
      · rw [term_body_shape]
        let wrapped := ("items", indicesValue []) :: bound
        apply let_returns program bound wrapped state state state (.var "items") _ _ (indicesValue []) _
        · exact empty_constructor_returns program bound state "MM0:L" list_is_data_constructor (by decide)
        · simp [SpaceSemantics.matchValue, matchAtom, wrapped, bound, bindings, environment, Subst.lookup]
        · simpa [indices?, wrapped, resultValue, optionValue, applySubst, Subst.lookup] using
            unary_constructor_returns program wrapped state "Some" "items" some_is_data_constructor (by decide)
  | app function argument ihFunction ihArgument =>
      let bindings := environment context (.app function argument)
      let bound := ("argument", Data.preterm argument) :: ("function", Data.preterm function) :: bindings
      rw [body_shape]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.app function argument)) appBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm,
          bindings, bound, environment, Subst.lookup]
      · rw [app_body_shape]
        let supported := ("supportResult", resultValue (indices? context function)) :: bound
        apply let_returns program bound supported state state state (.var "supportResult") _ _
          (resultValue (indices? context function)) _
        · apply authored_variable_call_returns program bound (environment context function) state state
            "mm0:support" ["context", "function"] equation.body _
            (by decide) (by decide) (by decide) _ ihFunction (by decide)
          simpa [bound, bindings, environment, applySubst, Subst.lookup] using clause context function
        · simp [SpaceSemantics.matchValue, matchAtom, supported, bound, bindings, environment, Subst.lookup]
        · have handled := function_body_returns state (indices? context function) context argument ihArgument
          apply authored_variable_call_returns program supported
            (functionEnvironment (indices? context function) context argument) state state
            "mm0:support-function" ["supportResult", "context", "argument"] functionEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [supported, bound, bindings, environment, applySubst, Subst.lookup] using
              function_clause (indices? context function) context argument
          · cases left : indices? context function <;> cases right : indices? context argument <;>
              simpa [indices?, left, right] using handled

theorem captured_returns (bindings : Subst) (state : State) (context : Context) (expression : Preterm)
    (contextName expressionName : String)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:support", .var contextName, .var expressionName]) state
      (resultValue (indices? context expression)) := by
  apply authored_variable_call_returns program bindings (environment context expression) state state
    "mm0:support" [contextName, expressionName] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns state context expression) (by decide)
  simpa [capturedContext, capturedExpression] using clause context expression

def requestConfiguration (state : State) (context : Context) (expression : Preterm) : Configuration :=
  { state, control := .evaluate (environment context expression)
      (.expression [.symbol "mm0:support", .var "context", .var "expression"]) }

theorem sufficient_fuel (state : State) (context : Context) (expression : Preterm) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state context expression) =
      .complete state [resultValue (indices? context expression)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment context expression)
    state state _ _ (captured_returns (environment context expression) state context expression
      "context" "expression" rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem resultValue_injective : Function.Injective resultValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [resultValue, optionValue]
  | some first =>
      cases second with
      | none => simp [resultValue, optionValue] at same
      | some second =>
          have items : first.map natural = second.map natural := by
            simpa [resultValue, optionValue, indicesValue, listValue] using same
          exact congrArg some ((List.map_injective_iff.mpr Data.natural_injective) items)

/-- Preservation and reflection of the full occurrence list. -/
theorem result_iff_source_returns (state : State) (context : Context) (expression : Preterm)
    (result : Option (List Nat)) :
    indices? context expression = result ↔
      ∃ fuel, run program fuel (requestConfiguration state context expression) =
        .complete state [resultValue result] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state context expression
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same
    exact ⟨referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨fuel, accepted⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference accepted
    exact resultValue_injective (List.singleton_inj.mp same.2.1)

theorem supports_iff_source_returns (state : State) (context : Context) (expression : Preterm)
    (support : Finset Nat) :
    Preterm.Supports context expression support ↔
      ∃ indices fuel, run program fuel (requestConfiguration state context expression) =
        .complete state [resultValue (some indices)] [] [] ∧ indices.toFinset = support := by
  constructor
  · intro supported
    obtain ⟨indices, computed, same⟩ := Presentation.ComputationalSupport.indices_complete supported
    obtain ⟨fuel, returned⟩ := (result_iff_source_returns state context expression (some indices)).mp computed
    exact ⟨indices, fuel, returned, same⟩
  · rintro ⟨indices, fuel, returned, rfl⟩
    exact Presentation.ComputationalSupport.indices_sound
      ((result_iff_source_returns state context expression (some indices)).mpr ⟨fuel, returned⟩)

theorem refusal_iff_source_returns_none (state : State) (context : Context) (expression : Preterm) :
    (¬ ∃ support, Preterm.Supports context expression support) ↔
      ∃ fuel, run program fuel (requestConfiguration state context expression) =
        .complete state [.symbol "None"] [] [] :=
  (Presentation.ComputationalSupport.indices_refusal_iff context expression).symm.trans
    (result_iff_source_returns state context expression none)

theorem repeated_occurrences_returned (state : State) :
    ∃ fuel, run program fuel (requestConfiguration state [.bound 0] (.app (.var 0) (.var 0))) =
      .complete state [resultValue (some [0, 0])] [] [] :=
  (result_iff_source_returns state [.bound 0] (.app (.var 0) (.var 0)) (some [0, 0])).mp rfl

theorem undefined_child_refused (state : State) :
    ∃ fuel, run program fuel (requestConfiguration state [.bound 0] (.app (.var 0) (.var 1))) =
      .complete state [.symbol "None"] [] [] :=
  (result_iff_source_returns state [.bound 0] (.app (.var 0) (.var 1)) none).mp rfl

end Mettapedia.Languages.MM0.MeTTa.Support
