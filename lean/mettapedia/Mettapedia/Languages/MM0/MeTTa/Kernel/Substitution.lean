import Mettapedia.Languages.MM0.MeTTa.Data.Lookup
import Mettapedia.Languages.MM0.MeTTa.Data.Data
import Mettapedia.Languages.MM0.Upstream.Lean3Dependencies

/-!
# Simultaneous substitution in the retained MM0 source

The three source bodies are projections of the pinned file. Their execution
agrees with the independent structural substitution judgment for every MM0
preterm and supplied substitution list, including missing variable images.
Variables are replaced simultaneously; their images are not substituted again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Substitution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Store (natural)
open ListAccess (linkedValue optionValue)
open Kernel (Preterm)
open Upstream.Lean3Typing.Reference (SExpr)

private def valuesCode (values : List Preterm) : Atom := linkedValue (values.map Data.preterm)

private def resultCode (result : Option Preterm) : Atom := optionValue (result.map Data.preterm)

private def environment (source : Preterm) (values : List Preterm) : Subst :=
  [("values", valuesCode values), ("expression", Data.preterm source)]

private def functionEnvironment (result : Option Preterm) (argument : Preterm)
    (values : List Preterm) : Subst :=
  [("values", valuesCode values), ("x", Data.preterm argument), ("valueInput", resultCode result)]

private def argumentEnvironment (function : Preterm) (result : Option Preterm) : Subst :=
  [("valueInput", resultCode result), ("f", Data.preterm function)]

theorem subst_clause (source : Preterm) (values : List Preterm) :
    clauses program "mm0:subst" [Data.preterm source, valuesCode values] =
      [.evaluate (environment source values) substEquation.body] := by
  rw [clauses_use_only_the_named_equations, subst_equation_is_unique]
  simp [subst_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem function_clause (result : Option Preterm) (argument : Preterm)
    (values : List Preterm) :
    clauses program "mm0:subst-function" [resultCode result, Data.preterm argument, valuesCode values] =
      [.evaluate (functionEnvironment result argument values) substFunctionEquation.body] := by
  rw [clauses_use_only_the_named_equations, subst_function_equation_is_unique]
  simp [subst_function_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, functionEnvironment]

private theorem argument_clause (function : Preterm) (result : Option Preterm) :
    clauses program "mm0:subst-argument" [Data.preterm function, resultCode result] =
      [.evaluate (argumentEnvironment function result) substArgumentEquation.body] := by
  rw [clauses_use_only_the_named_equations, subst_argument_equation_is_unique]
  simp [subst_argument_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, argumentEnvironment]

private def cases : SpaceSemantics.Cases :=
  match substEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def varBody : Atom := (cases[0]'(by decide)).2
private def termBody : Atom := (cases[1]'(by decide)).2
private def appBody : Atom := (cases[2]'(by decide)).2

private def functionCases : SpaceSemantics.Cases :=
  match substFunctionEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def functionBody : Atom := (functionCases[1]'(by decide)).2

private def argumentCases : SpaceSemantics.Cases :=
  match substArgumentEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def argumentBody : Atom := (argumentCases[1]'(by decide)).2

private theorem body_is_case :
    substEquation.body = .expression [.symbol "case", .var "expression",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:Var", .var "i"], varBody),
      (.expression [.symbol "MM0:Term", .var "i"], termBody),
      (.expression [.symbol "MM0:App", .var "f", .var "x"], appBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem var_body_shape :
    varBody = .expression [.symbol "mm0:lookup", .var "values", .var "i"] := by decide

private theorem term_body_shape :
    termBody = .expression [.symbol "let", .var "term",
      .expression [.symbol "MM0:Term", .var "i"], .expression [.symbol "Some", .var "term"]] := by decide

private theorem app_body_shape :
    appBody = .expression [.symbol "let", .var "substituted",
      .expression [.symbol "mm0:subst", .var "f", .var "values"],
      .expression [.symbol "mm0:subst-function", .var "substituted", .var "x", .var "values"]] := by decide

private theorem function_body_is_case :
    substFunctionEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (functionCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem function_cases_shape :
    functionCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "f"], functionBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem function_body_shape :
    functionBody = .expression [.symbol "let", .var "substituted",
      .expression [.symbol "mm0:subst", .var "x", .var "values"],
      .expression [.symbol "mm0:subst-argument", .var "f", .var "substituted"]] := by decide

private theorem argument_body_is_case :
    substArgumentEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (argumentCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem argument_cases_shape :
    argumentCases = [(.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "x"], argumentBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem argument_body_shape :
    argumentBody = .expression [.symbol "let", .var "app",
      .expression [.symbol "MM0:App", .var "f", .var "x"],
      .expression [.symbol "Some", .var "app"]] := by decide

private theorem argument_body_returns (state : State) (function : Preterm) (result : Option Preterm) :
    PureReturns program (argumentEnvironment function result) state substArgumentEquation.body state
      (resultCode (result.map (Preterm.app function))) := by
  rw [argument_body_is_case]
  cases result with
  | none =>
      let bindings := argumentEnvironment function none
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ argumentCases (read_cases_encoded argumentCases)
      · simpa [bindings, argumentEnvironment, resultCode, optionValue, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some argument =>
      let bindings := argumentEnvironment function (some argument)
      let bound := ("x", Data.preterm argument) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (resultCode (some argument)) argumentBody _ _ argumentCases (read_cases_encoded argumentCases)
      · simpa [bindings, argumentEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [argument_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, resultCode, optionValue, bindings, bound,
          argumentEnvironment, matchAtom, Subst.lookup]
      · rw [argument_body_shape]
        let wrapped := ("app", Data.preterm (.app function argument)) :: bound
        apply let_returns program bound wrapped state state state (.var "app") _ _
          (Data.preterm (.app function argument)) _
        · simpa [bound, bindings, argumentEnvironment, applySubst, Subst.lookup, Data.preterm] using
            constructor_variables_return program bound state "MM0:App" ["f", "x"]
              app_is_data_constructor (by decide)
        · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, argumentEnvironment,
            Subst.lookup, wrapped]
        · simpa [wrapped, applySubst, Subst.lookup, resultCode, optionValue] using
            unary_constructor_returns program wrapped state "Some" "app" some_is_data_constructor (by decide)

private theorem function_body_returns (state : State) (functionResult : Option Preterm)
    (argument : Preterm) (values : List Preterm)
    (recursive : PureReturns program (environment argument values) state substEquation.body state
      (resultCode (argument.substitute (Kernel.Substitution.ofList values)))) :
    PureReturns program (functionEnvironment functionResult argument values) state
      substFunctionEquation.body state (resultCode (functionResult.bind fun function =>
        (argument.substitute (Kernel.Substitution.ofList values)).map (Preterm.app function))) := by
  rw [function_body_is_case]
  cases functionResult with
  | none =>
      let bindings := functionEnvironment none argument values
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (.symbol "None") _ _ functionCases (read_cases_encoded functionCases)
      · simpa [bindings, functionEnvironment, resultCode, optionValue, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [function_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some function =>
      let result := argument.substitute (Kernel.Substitution.ofList values)
      let bindings := functionEnvironment (some function) argument values
      let bound := ("f", Data.preterm function) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (resultCode (some function)) functionBody _ _ functionCases (read_cases_encoded functionCases)
      · simpa [bindings, functionEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [function_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, resultCode, optionValue, bindings, bound,
          functionEnvironment, matchAtom, Subst.lookup]
      · rw [function_body_shape]
        let substituted := ("substituted", resultCode result) :: bound
        apply let_returns program bound substituted state state state (.var "substituted") _ _
          (resultCode result) _
        · apply authored_variable_call_returns program bound (environment argument values) state state
            "mm0:subst" ["x", "values"] substEquation.body _
            (by decide) (by decide) (by decide) _ recursive (by decide)
          simpa [bound, bindings, functionEnvironment, applySubst, Subst.lookup] using subst_clause argument values
        · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, functionEnvironment,
            Subst.lookup, substituted]
        · apply authored_variable_call_returns program substituted (argumentEnvironment function result)
            state state "mm0:subst-argument" ["f", "substituted"] substArgumentEquation.body _
            (by decide) (by decide) (by decide) _ (argument_body_returns state function result) (by decide)
          simpa [substituted, bound, bindings, functionEnvironment, applySubst, Subst.lookup] using
            argument_clause function result

theorem subst_body_returns (state : State) (source : Preterm) (values : List Preterm) :
    PureReturns program (environment source values) state substEquation.body state
      (resultCode (source.substitute (Kernel.Substitution.ofList values))) := by
  induction source with
  | var index =>
      let bindings := environment (.var index) values
      let bound := ("i", natural index) :: bindings
      rw [body_is_case]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.var index)) varBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, Data.preterm, bindings, bound,
          environment, matchAtom, Subst.lookup]
      · rw [var_body_shape]
        simpa [resultCode, Preterm.substitute, Kernel.Substitution.ofList, List.getElem?_map] using
          Lookup.lookup_returns bound state (values.map Data.preterm) index "values" "i"
            (by simp [bound, bindings, environment, valuesCode, applySubst, Subst.lookup])
            (by simp [bound, applySubst, Subst.lookup])
  | term index =>
      let bindings := environment (.term index) values
      let bound := ("i", natural index) :: bindings
      rw [body_is_case]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.term index)) termBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, Data.preterm, bindings, bound,
          environment, matchAtom, Subst.lookup]
      · rw [term_body_shape]
        let wrapped := ("term", Data.preterm (.term index)) :: bound
        apply let_returns program bound wrapped state state state (.var "term") _ _
          (Data.preterm (.term index)) _
        · simpa [bound, applySubst, Subst.lookup, Data.preterm] using
            unary_constructor_returns program bound state "MM0:Term" "i" term_is_data_constructor (by decide)
        · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, environment, Subst.lookup, wrapped]
        · simpa [wrapped, applySubst, Subst.lookup, resultCode, optionValue, Preterm.substitute] using
            unary_constructor_returns program wrapped state "Some" "term" some_is_data_constructor (by decide)
  | app function argument ihFunction ihArgument =>
      let result := function.substitute (Kernel.Substitution.ofList values)
      let bindings := environment (.app function argument) values
      let bound := ("x", Data.preterm argument) :: ("f", Data.preterm function) :: bindings
      rw [body_is_case]
      apply case_returns program bindings bound state state state (.var "expression")
        (Data.preterm (.app function argument)) appBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "expression"
      · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, Data.preterm, bindings, bound,
          environment, matchAtom, Subst.lookup]
      · rw [app_body_shape]
        let substituted := ("substituted", resultCode result) :: bound
        apply let_returns program bound substituted state state state (.var "substituted") _ _
          (resultCode result) _
        · apply authored_variable_call_returns program bound (environment function values) state state
            "mm0:subst" ["f", "values"] substEquation.body _
            (by decide) (by decide) (by decide) _ ihFunction (by decide)
          simpa [bound, bindings, environment, applySubst, Subst.lookup] using subst_clause function values
        · simp [SpaceSemantics.matchValue, matchAtom, bound, bindings, environment, Subst.lookup, substituted]
        · have finished := function_body_returns state result argument values ihArgument
          apply authored_variable_call_returns program substituted
            (functionEnvironment result argument values) state state "mm0:subst-function"
            ["substituted", "x", "values"] substFunctionEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [substituted, bound, bindings, environment, applySubst, Subst.lookup] using
              function_clause result argument values
          · simpa [result, Preterm.substitute, Option.map_eq_bind, Function.comp_def] using finished

theorem subst_captured_returns (bindings : Subst) (state : State) (source : Preterm) (values : List Preterm)
    (sourceName valuesName : String)
    (capturedSource : applySubst bindings (.var sourceName) = Data.preterm source)
    (capturedValues : applySubst bindings (.var valuesName) = valuesCode values) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:subst", .var sourceName, .var valuesName]) state
      (resultCode (source.substitute (Kernel.Substitution.ofList values))) := by
  apply authored_variable_call_returns program bindings (environment source values) state state
    "mm0:subst" [sourceName, valuesName] substEquation.body _ (by decide) (by decide) (by decide)
    _ (subst_body_returns state source values) (by decide)
  simpa [capturedSource, capturedValues] using subst_clause source values

theorem subst_returns (state : State) (source : Preterm) (values : List Preterm) :
    PureReturns program [] state
      (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) state
      (resultCode (source.substitute (Kernel.Substitution.ofList values))) := by
  apply raw_call_returns program [] state state "mm0:subst" _ _ (by decide) _ _ (by decide)
  · intro index bounded
    have positions : index = 0 ∨ index = 1 := by have : index < 2 := bounded; omega
    rcases positions with rfl | rfl <;> decide
  · simp only [List.map, applySubst_nil]
    exact authored_function_arguments_return program [] (environment source values) state state
      "mm0:subst" [Data.preterm source, valuesCode values] 2 substEquation.body _
      (by decide) (by decide) (subst_clause source values) (subst_body_returns state source values)

theorem subst_has_sufficient_fuel (state : State) (source : Preterm) (values : List Preterm) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
      .complete state [resultCode (source.substitute (Kernel.Substitution.ofList values))] [] [] :=
  pure_returns_has_sufficient_fuel program [] state state _ _ (subst_returns state source values)

theorem result_eq_iff_source_returns (state : State) (source : Preterm) (values : List Preterm)
    (result : Option Preterm) :
    source.substitute (Kernel.Substitution.ofList values) = result ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
        .complete state [resultCode result] [] [] := by
  constructor
  · intro accepted
    simpa [accepted] using subst_has_sufficient_fuel state source values
  · rintro ⟨fuel, accepted⟩
    obtain ⟨referenceFuel, completed⟩ := subst_has_sufficient_fuel state source values
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] []
      completed accepted
    exact Data.optional_preterm_injective (List.singleton_inj.mp same.2.1)

theorem substitutes_iff_source_returns (state : State) (source result : Preterm) (values : List Preterm) :
    Preterm.Substitutes (Kernel.Substitution.ofList values) source result ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
        .complete state [resultCode (some result)] [] [] := by
  rw [← Preterm.substitute_eq_some_iff]
  exact result_eq_iff_source_returns state source values (some result)

theorem refusal_iff_source_returns_none (state : State) (source : Preterm) (values : List Preterm) :
    source.substitute (Kernel.Substitution.ofList values) = none ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
        .complete state [.symbol "None"] [] [] :=
  result_eq_iff_source_returns state source values none

/-- The image domain is essential: the historical upstream helper defaults
outside it, whereas MM0 certificate checking must refuse a missing image. -/
theorem upstream_substitution_iff_source_returns (state : State) (source result : Preterm)
    (values : List Preterm) :
    (Upstream.Lean3Dependencies.Reference.withinImages values.length (SExpr.ofKernel source) ∧
      Upstream.Lean3Dependencies.Reference.substitute (values.map SExpr.ofKernel)
        (SExpr.ofKernel source) = SExpr.ofKernel result) ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
        .complete state [resultCode (some result)] [] [] :=
  (Upstream.Lean3Dependencies.substitution_iff values source result).symm.trans
    (result_eq_iff_source_returns state source values (some result))

theorem upstream_missing_domain_iff_source_refuses (state : State) (source : Preterm)
    (values : List Preterm) :
    (¬ Upstream.Lean3Dependencies.Reference.withinImages values.length (SExpr.ofKernel source)) ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:subst", Data.preterm source, valuesCode values]) =
        .complete state [.symbol "None"] [] [] :=
  (Upstream.Lean3Dependencies.substitution_refuses_iff values source).symm.trans
    (refusal_iff_source_returns_none state source values)

theorem missing_image_returns_none (state : State) (values : List Preterm) (index : Nat)
    (absent : values.length ≤ index) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:subst", Data.preterm (.var index), valuesCode values]) =
      .complete state [.symbol "None"] [] [] := by
  simpa [Preterm.substitute, Kernel.Substitution.ofList, List.getElem?_eq_none absent,
    resultCode, optionValue] using subst_has_sufficient_fuel state (.var index) values

theorem simultaneous_images_are_not_rewritten (state : State) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:subst", Data.preterm (.var 0), valuesCode [.var 1, .term 2]]) =
      .complete state [resultCode (some (.var 1))] [] [] := by
  simpa [Preterm.substitute, Kernel.Substitution.ofList] using
    subst_has_sufficient_fuel state (.var 0) [.var 1, .term 2]

theorem missing_child_refuses_the_application (state : State) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:subst", Data.preterm (.app (.term 2) (.var 0)), valuesCode []]) =
      .complete state [.symbol "None"] [] [] := by
  simpa [Preterm.substitute, Kernel.Substitution.ofList, resultCode, optionValue] using
    subst_has_sufficient_fuel state (.app (.term 2) (.var 0)) []

end Mettapedia.Languages.MM0.MeTTa.Substitution
