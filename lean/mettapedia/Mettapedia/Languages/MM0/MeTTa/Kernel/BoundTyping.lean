import Mettapedia.Languages.MM0.MeTTa.Data.Data

/-!
# Bound arguments in the retained MM0 source

The source accepts a bound argument exactly when it is a context variable
whose binder is bound. An application or a declared term is not a bound
argument, even when it has the same sort. Every path below executes a body
projected from the pinned source and leaves the source store unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.BoundTyping

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Store (natural)
open Kernel (Preterm Binder Context)
open ListAccess (optionValue)

private def sortCode (value : Option Nat) : Atom := optionValue (value.map natural)

private def binderCode (value : Option Binder) : Atom := optionValue (value.map Data.binder)

private def binderEnvironment (value : Option Binder) : Subst := [("valueInput", binderCode value)]

private def environment (context : Context) (expression : Preterm) : Subst :=
  [("valueInput", Data.preterm expression), ("context", Data.context context)]

private def boundSortEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 138)[137]'(by decide +kernel)

private def boundBinderEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 139)[138]'(by decide +kernel)

private theorem bound_sort_equation_unique :
    program.equations.filter (fun equation => equation.head == "mm0:bound-sort") =
      [boundSortEquation] := by decide

private theorem bound_binder_equation_unique :
    program.equations.filter (fun equation => equation.head == "mm0:bound-binder") =
      [boundBinderEquation] := by decide

private theorem bound_sort_formals :
    boundSortEquation.arguments = [.var "context", .var "valueInput"] := by decide

private theorem bound_binder_formals :
    boundBinderEquation.arguments = [.var "valueInput"] := by decide

private def binderCases : SpaceSemantics.Cases :=
  match boundBinderEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def sortCases : SpaceSemantics.Cases :=
  match boundSortEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def variableBody : Atom := (sortCases[0]'(by decide)).2

private theorem binder_body_shape :
    boundBinderEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
      .expression (binderCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem binder_cases_shape :
    binderCases = [(.expression [.symbol "None"], .symbol "None"),
      (.expression [.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Bound", .var "sort"]]]],
        .expression [.symbol "Some", .var "sort"]),
      (.expression [.expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]]]], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem sort_body_shape :
    boundSortEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (sortCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem sort_cases_shape :
    sortCases = [(.expression [.symbol "MM0:Var", .var "index"], variableBody),
      (.expression [.symbol "MM0:Term", .var "index"], .symbol "None"),
      (.expression [.symbol "MM0:App", .var "function", .var "argument"], .symbol "None"),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem variable_body_shape :
    variableBody = .expression [.symbol "let", .var "entry",
      .expression [.symbol "mm0:data-at", .var "context", .var "index"],
      .expression [.symbol "mm0:bound-binder", .var "entry"]] := by decide

private theorem binder_clause (value : Option Binder) :
    clauses program "mm0:bound-binder" [binderCode value] =
      [.evaluate (binderEnvironment value) boundBinderEquation.body] := by
  rw [clauses_use_only_the_named_equations, bound_binder_equation_unique]
  simp [bound_binder_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, binderEnvironment]

private theorem bound_sort_clause (context : Context) (expression : Preterm) :
    clauses program "mm0:bound-sort" [Data.context context, Data.preterm expression] =
      [.evaluate (environment context expression) boundSortEquation.body] := by
  rw [clauses_use_only_the_named_equations, bound_sort_equation_unique]
  simp [bound_sort_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private def binderSort : Option Binder → Option Nat
  | some (.bound sort) => some sort
  | _ => none

private theorem binder_body_returns (state : State) (value : Option Binder) :
    PureReturns program (binderEnvironment value) state boundBinderEquation.body state
      (sortCode (binderSort value)) := by
  rw [binder_body_shape]
  have tuple := tuple_variables_return program (binderEnvironment value) state ["valueInput"]
  have input : PureReturns program (binderEnvironment value) state
      (.expression [.var "valueInput"]) state (.expression [binderCode value]) := by
    simpa [binderEnvironment, applySubst, Subst.lookup] using tuple
  cases value with
  | none =>
      apply case_returns program (binderEnvironment none) (binderEnvironment none)
        state state state _ (.expression [.symbol "None"]) (.symbol "None") _ _ binderCases
        (read_cases_encoded binderCases) input
      · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
      · exact symbol_returns program (binderEnvironment none) state "None"
  | some value =>
      cases value with
      | bound sort =>
          let bound := ("sort", natural sort) :: binderEnvironment (some (.bound sort))
          apply case_returns program (binderEnvironment (some (.bound sort))) bound
            state state state _ (.expression [binderCode (some (.bound sort))])
            (.expression [.symbol "Some", .var "sort"]) _ _ binderCases
            (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, binderCode, optionValue,
              Data.binder, ListAccess.listValue, bound, binderEnvironment, Subst.lookup]
          · simpa [sortCode, binderSort, optionValue, bound, applySubst, Subst.lookup] using
              unary_constructor_returns program bound state "Some" "sort"
                some_is_data_constructor (by decide)
      | regular sort dependencies =>
          let bound := ("dependencies", Data.dependencies dependencies) :: ("sort", natural sort) ::
            binderEnvironment (some (.regular sort dependencies))
          apply case_returns program (binderEnvironment (some (.regular sort dependencies))) bound
            state state state _ (.expression [binderCode (some (.regular sort dependencies))])
            (.symbol "None") _ _ binderCases (read_cases_encoded binderCases) input
          · simp [binder_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, binderCode, optionValue,
              Data.binder, ListAccess.listValue, bound, binderEnvironment, Subst.lookup]
          · exact symbol_returns program bound state "None"

private theorem binder_captured_returns (bindings : Subst) (state : State)
    (name : String) (value : Option Binder)
    (captured : applySubst bindings (.var name) = binderCode value) :
    PureReturns program bindings state (.expression [.symbol "mm0:bound-binder", .var name])
      state (sortCode (binderSort value)) := by
  apply authored_variable_call_returns program bindings (binderEnvironment value) state state
    "mm0:bound-binder" [name] boundBinderEquation.body _ (by decide) (by decide) (by decide)
    _ (binder_body_returns state value) (by decide)
  simpa [captured] using binder_clause value

theorem bound_sort_body_returns (state : State) (context : Context) (expression : Preterm) :
    PureReturns program (environment context expression) state boundSortEquation.body state
      (sortCode (Preterm.boundSort? context expression)) := by
  rw [sort_body_shape]
  cases expression with
  | var index =>
      let bindings := environment context (.var index)
      let bound := ("index", natural index) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.preterm (.var index)) variableBody _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [sort_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings,
          environment, Subst.lookup]
      · rw [variable_body_shape]
        let entry := ("entry", binderCode context[index]?) :: bound
        apply let_returns program bound entry state state state (.var "entry") _ _
          (binderCode context[index]?) _
        · simpa [binderCode, Data.context, List.getElem?_map] using
            ListAccess.data_at_list_returns bound state (context.map Data.binder) index "context" "index"
              (by simp [bound, bindings, environment, applySubst, Subst.lookup, Data.context])
              (by simp [bound, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, entry, bound, bindings, environment, Subst.lookup]
        · have result := binder_captured_returns entry state "entry" context[index]?
            (by simp [entry, applySubst, Subst.lookup])
          have same : binderSort context[index]? = Preterm.boundSort? context (.var index) := by
            cases found : context[index]? with
            | none => simp [binderSort, Preterm.boundSort?, found]
            | some binder => cases binder <;> simp [binderSort, Preterm.boundSort?, found]
          simpa only [same] using result
  | term index =>
      let bindings := environment context (.term index)
      let bound := ("index", natural index) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.preterm (.term index)) (.symbol "None") _ _ sortCases (read_cases_encoded sortCases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [sort_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings,
          environment, Subst.lookup]
      · exact symbol_returns program bound state "None"
  | app function argument =>
      let bindings := environment context (.app function argument)
      let bound := ("argument", Data.preterm argument) :: ("function", Data.preterm function) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.preterm (.app function argument)) (.symbol "None") _ _ sortCases
        (read_cases_encoded sortCases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [sort_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.preterm, bound, bindings,
          environment, Subst.lookup]
      · exact symbol_returns program bound state "None"

theorem bound_sort_captured_returns (bindings : Subst) (state : State) (context : Context)
    (expression : Preterm) (contextName expressionName : String)
    (capturedContext : applySubst bindings (.var contextName) = Data.context context)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:bound-sort", .var contextName, .var expressionName]) state
      (sortCode (Preterm.boundSort? context expression)) := by
  apply authored_variable_call_returns program bindings (environment context expression) state state
    "mm0:bound-sort" [contextName, expressionName] boundSortEquation.body _
    (by decide) (by decide) (by decide) _ (bound_sort_body_returns state context expression) (by decide)
  simpa [capturedContext, capturedExpression] using bound_sort_clause context expression

theorem bound_sort_returns (state : State) (context : Context) (expression : Preterm) :
    PureReturns program [] state
      (.expression [.symbol "mm0:bound-sort", Data.context context, Data.preterm expression]) state
      (sortCode (Preterm.boundSort? context expression)) := by
  apply raw_call_returns program [] state state "mm0:bound-sort" _ _ (by decide) _ _ (by decide)
  · intro index bounded
    have positions : index = 0 ∨ index = 1 := by have : index < 2 := bounded; omega
    rcases positions with rfl | rfl <;> decide
  · simp only [List.map, applySubst_nil]
    exact authored_function_arguments_return program [] (environment context expression) state state
      "mm0:bound-sort" [Data.context context, Data.preterm expression] 2 boundSortEquation.body _
      (by decide) (by decide) (bound_sort_clause context expression)
      (bound_sort_body_returns state context expression)

private theorem sort_code_injective : Function.Injective sortCode := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [sortCode, optionValue]
  | some first =>
      cases second with
      | none => simp [sortCode, optionValue] at same
      | some second =>
          exact congrArg some (Data.natural_injective (by simpa [sortCode, optionValue] using same))

theorem bound_sort_result_iff_source_returns (state : State) (context : Context)
    (expression : Preterm) (result : Option Nat) :
    Preterm.boundSort? context expression = result ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:bound-sort", Data.context context, Data.preterm expression]) =
        .complete state [sortCode result] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := pure_returns_has_sufficient_fuel program [] state state _ _
    (bound_sort_returns state context expression)
  constructor
  · intro same
    exact ⟨referenceFuel, same ▸ completed⟩
  · rintro ⟨fuel, accepted⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] []
      completed accepted
    exact sort_code_injective (List.singleton_inj.mp same.2.1)

theorem bound_argument_iff_source_returns (state : State) (context : Context)
    (expression : Preterm) (sort : Nat) :
    (∃ index, expression = .var index ∧ context[index]? = some (.bound sort)) ↔
      ∃ fuel, evaluate program fuel state
        (.expression [.symbol "mm0:bound-sort", Data.context context, Data.preterm expression]) =
        .complete state [.expression [.symbol "Some", natural sort]] [] [] :=
  (Preterm.boundSort_eq_some_iff context expression sort).symm.trans
    (bound_sort_result_iff_source_returns state context expression (some sort))

theorem regular_variable_is_not_a_bound_argument (state : State) (sort : Nat)
    (dependencies : Finset Nat) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:bound-sort", Data.context [.regular sort dependencies],
        Data.preterm (.var 0)]) = .complete state [.symbol "None"] [] [] := by
  exact (bound_sort_result_iff_source_returns state [.regular sort dependencies] (.var 0) none).mp rfl

theorem bound_variable_returns_declared_sort (state : State) (sort : Nat) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:bound-sort", Data.context [.bound sort], Data.preterm (.var 0)]) =
      .complete state [.expression [.symbol "Some", natural sort]] [] [] :=
  (bound_sort_result_iff_source_returns state [.bound sort] (.var 0) (some sort)).mp rfl

end Mettapedia.Languages.MM0.MeTTa.BoundTyping
