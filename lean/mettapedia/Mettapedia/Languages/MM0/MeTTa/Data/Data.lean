import Mettapedia.Languages.MM0.Kernel.Term
import Mettapedia.Languages.MM0.Kernel.Typing
import Mettapedia.Languages.MM0.MeTTa.Data.ListAccess
import Mathlib.Data.Finset.Sort

/-!
# MM0 typed data in the native source carrier

The retained service uses native numeric atoms and constructor expressions.
This representation is distinct from the string-literal carrier of the
equation programs. The map below encodes data, not checking computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Data

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Kernel (Preterm)
open Store (natural)

def dependencies (values : Finset Nat) : Atom :=
  ListAccess.listValue ((values.sort (· ≤ ·)).map natural)

def binder : Kernel.Binder → Atom
  | .bound sort => ListAccess.listValue [.symbol "MM0:Bound", natural sort]
  | .regular sort values =>
      ListAccess.listValue [.symbol "MM0:Regular", natural sort, dependencies values]

def context (values : Kernel.Context) : Atom := ListAccess.listValue (values.map binder)

def inferred : Option Kernel.ExpressionType → Atom
  | none => .symbol "None"
  | some (remaining, sort) => .expression [.symbol "MM0:Inferred", context remaining, natural sort]

def declaration (value : Kernel.TermDecl) : Atom :=
  ListAccess.listValue [.symbol "MM0:TermDecl", context value.arguments,
    natural value.resultSort, dependencies value.dependencies]

theorem natural_injective : Function.Injective natural := by
  intro first second same
  have numbers : (first : Int) = (second : Int) := by simpa [natural] using same
  exact Int.ofNat.inj numbers

theorem dependencies_injective : Function.Injective dependencies := by
  intro first second same
  have items : first.sort (· ≤ ·) = second.sort (· ≤ ·) :=
    (List.map_injective_iff.mpr natural_injective) (by
      simpa [dependencies, ListAccess.listValue] using same)
  simpa using congrArg List.toFinset items

theorem binder_injective : Function.Injective binder := by
  intro first second same
  cases first with
  | bound first =>
      cases second with
      | bound second =>
          have numbers : natural first = natural second := by
            simpa [binder, ListAccess.listValue] using same
          exact congrArg Kernel.Binder.bound (natural_injective numbers)
      | regular => simp [binder, ListAccess.listValue] at same
  | regular first deps =>
      cases second with
      | bound => simp [binder, ListAccess.listValue] at same
      | regular second other =>
          have parts : natural first = natural second ∧ dependencies deps = dependencies other := by
            simpa [binder, ListAccess.listValue] using same
          exact congrArg₂ Kernel.Binder.regular
            (natural_injective parts.1) (dependencies_injective parts.2)

theorem context_injective : Function.Injective context := by
  intro first second same
  apply List.map_injective_iff.mpr binder_injective
  simpa [context, ListAccess.listValue] using same

theorem inferred_injective : Function.Injective inferred := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [inferred]
  | some first =>
      cases second with
      | none => simp [inferred] at same
      | some second =>
          rcases first with ⟨remaining, sort⟩
          rcases second with ⟨other, result⟩
          have parts : context remaining = context other ∧ natural sort = natural result := by
            simpa [inferred] using same
          exact congrArg some (Prod.ext (context_injective parts.1) (natural_injective parts.2))

def preterm : Preterm → Atom
  | .var index => .expression [.symbol "MM0:Var", natural index]
  | .term index => .expression [.symbol "MM0:Term", natural index]
  | .app function argument => .expression [.symbol "MM0:App", preterm function, preterm argument]

theorem preterm_injective : Function.Injective preterm := by
  intro first
  induction first with
  | var index =>
      intro second same
      cases second <;> simp [preterm, natural] at same
      cases same
      rfl
  | term index =>
      intro second same
      cases second <;> simp [preterm, natural] at same
      cases same
      rfl
  | app function argument ihFunction ihArgument =>
      intro second same
      cases second with
      | var | term => simp [preterm] at same
      | app otherFunction otherArgument =>
          simp only [preterm, Atom.expression.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg₂ Preterm.app (ihFunction same.1) (ihArgument same.2)

open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Literal)

theorem natural_literal (index : Nat) : Literal (natural index) := .grounded _

private theorem list_wrapper_literal (items : List Atom) (literal : Literal (.expression items)) :
    Literal (ListAccess.listValue items) := by
  apply Literal.constructor "MM0:L" [.expression items] (by decide)
  simpa using literal

theorem dependencies_literal (values : Finset Nat) : Literal (dependencies values) := by
  apply list_wrapper_literal
  apply Literal.expression
  · intro first rest same
    cases sorted : values.sort (· ≤ ·) with
    | nil => simp [sorted] at same
    | cons index indices => simp [sorted, natural] at same
  · intro item member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact natural_literal index

theorem binder_literal (value : Kernel.Binder) : Literal (binder value) := by
  cases value with
  | bound sort =>
      apply list_wrapper_literal
      apply Literal.constructor "MM0:Bound" [natural sort] (by decide)
      simpa using natural_literal sort
  | regular sort values =>
      apply list_wrapper_literal
      apply Literal.constructor "MM0:Regular" [natural sort, dependencies values] (by decide)
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact natural_literal sort
      · obtain rfl := List.mem_singleton.mp member
        exact dependencies_literal values

theorem context_literal (values : Kernel.Context) : Literal (context values) := by
  apply list_wrapper_literal
  apply Literal.expression
  · intro first rest same
    cases values with
    | nil => simp at same
    | cons value values =>
        cases value <;> simp [binder, ListAccess.listValue] at same
  · intro item member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    exact binder_literal value

theorem preterm_literal (value : Preterm) : Literal (preterm value) := by
  induction value with
  | var index =>
      apply Literal.constructor "MM0:Var" [natural index] (by decide)
      simpa using natural_literal index
  | term index =>
      apply Literal.constructor "MM0:Term" [natural index] (by decide)
      simpa using natural_literal index
  | app function argument ihFunction ihArgument =>
      apply Literal.constructor "MM0:App" [preterm function, preterm argument] (by decide)
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihFunction
      · obtain rfl := List.mem_singleton.mp member
        exact ihArgument

theorem optional_preterm_injective :
    Function.Injective (fun value : Option Preterm => ListAccess.optionValue (value.map preterm)) := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [ListAccess.optionValue]
  | some first =>
      cases second with
      | none => simp [ListAccess.optionValue] at same
      | some second =>
          simp only [Option.map_some, ListAccess.optionValue, Atom.expression.injEq,
            List.cons.injEq, true_and, and_true] at same
          exact congrArg some (preterm_injective same)

/-! ## Authored input constructors

These calls construct the existing preterm data. Formation and proof checking
remain the operations that authorize its use. The scalar calls demand numeric
arguments; the application call captures its two Atom arguments without running
them. Every constructor preserves the complete store.
-/

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)

private def makeVarEquation : SpaceSemantics.Equation :=
  dataSource.program.equations[0]'(by decide)
private def makeTermEquation : SpaceSemantics.Equation :=
  dataSource.program.equations[1]'(by decide)
private def makeAppEquation : SpaceSemantics.Equation :=
  dataSource.program.equations[2]'(by decide)

private def indexEnvironment (index : Nat) : Subst := [("index", natural index)]
private def appEnvironment (function argument : Preterm) : Subst :=
  [("argument", preterm argument), ("function", preterm function)]

private theorem make_var_unique :
    program.equations.filter (fun equation => equation.head == "mm0:make-var") =
      [makeVarEquation] := by decide
private theorem make_term_unique :
    program.equations.filter (fun equation => equation.head == "mm0:make-term") =
      [makeTermEquation] := by decide
private theorem make_app_unique :
    program.equations.filter (fun equation => equation.head == "mm0:make-app") =
      [makeAppEquation] := by decide

private theorem make_var_formals : makeVarEquation.arguments = [.var "index"] := by decide
private theorem make_term_formals : makeTermEquation.arguments = [.var "index"] := by decide
private theorem make_app_formals :
    makeAppEquation.arguments = [.var "function", .var "argument"] := by decide
private theorem make_var_shape :
    makeVarEquation.body = .expression [.symbol "MM0:Var", .var "index"] := by decide
private theorem make_term_shape :
    makeTermEquation.body = .expression [.symbol "MM0:Term", .var "index"] := by decide
private theorem make_app_shape :
    makeAppEquation.body = .expression [.symbol "MM0:App", .var "function", .var "argument"] := by decide

private theorem make_var_clause (index : Nat) :
    clauses program "mm0:make-var" [natural index] =
      [.evaluate (indexEnvironment index) makeVarEquation.body] := by
  rw [clauses_use_only_the_named_equations, make_var_unique]
  simp [make_var_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, indexEnvironment]
private theorem make_term_clause (index : Nat) :
    clauses program "mm0:make-term" [natural index] =
      [.evaluate (indexEnvironment index) makeTermEquation.body] := by
  rw [clauses_use_only_the_named_equations, make_term_unique]
  simp [make_term_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, indexEnvironment]
private theorem make_app_clause (function argument : Preterm) :
    clauses program "mm0:make-app" [preterm function, preterm argument] =
      [.evaluate (appEnvironment function argument) makeAppEquation.body] := by
  rw [clauses_use_only_the_named_equations, make_app_unique]
  simp [make_app_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, appEnvironment]

private theorem make_var_body_returns (state : State) (index : Nat) :
    PureReturns program (indexEnvironment index) state makeVarEquation.body state
      (preterm (.var index)) := by
  rw [make_var_shape]
  simpa [preterm, indexEnvironment, applySubst, Subst.lookup] using
    unary_constructor_returns program (indexEnvironment index) state "MM0:Var" "index"
      (by decide) (by decide)
private theorem make_term_body_returns (state : State) (index : Nat) :
    PureReturns program (indexEnvironment index) state makeTermEquation.body state
      (preterm (.term index)) := by
  rw [make_term_shape]
  simpa [preterm, indexEnvironment, applySubst, Subst.lookup] using
    unary_constructor_returns program (indexEnvironment index) state "MM0:Term" "index"
      term_is_data_constructor (by decide)
private theorem make_app_body_returns (state : State) (function argument : Preterm) :
    PureReturns program (appEnvironment function argument) state makeAppEquation.body state
      (preterm (.app function argument)) := by
  rw [make_app_shape]
  simpa [preterm, appEnvironment, applySubst, Subst.lookup] using
    constructor_variables_return program (appEnvironment function argument) state
      "MM0:App" ["function", "argument"] app_is_data_constructor (by decide)

/-- A literal natural index is evaluated by the source's Number argument policy. -/
theorem make_var_returns (bindings : Subst) (state : State) (index : Nat) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:make-var", natural index]) state (preterm (.var index)) := by
  apply call_returns program bindings state state "mm0:make-var" [natural index] _
    (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:make-var")
    (natural index) (natural index) _ [] [] 0 (by decide)
    (grounded_returns program bindings state (.int index))
  exact authored_function_arguments_return program bindings (indexEnvironment index) state state
    "mm0:make-var" [natural index] 1 makeVarEquation.body _ (by decide) (by decide)
    (make_var_clause index) (make_var_body_returns state index)

/-- The source constructor preserves a term identifier without looking it up. -/
theorem make_term_returns (bindings : Subst) (state : State) (index : Nat) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:make-term", natural index]) state (preterm (.term index)) := by
  apply call_returns program bindings state state "mm0:make-term" [natural index] _
    (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:make-term")
    (natural index) (natural index) _ [] [] 0 (by decide)
    (grounded_returns program bindings state (.int index))
  exact authored_function_arguments_return program bindings (indexEnvironment index) state state
    "mm0:make-term" [natural index] 1 makeTermEquation.body _ (by decide) (by decide)
    (make_term_clause index) (make_term_body_returns state index)

/-- Raw source arguments reuse captured preterm values without evaluating their contents. -/
theorem make_app_captured_returns (bindings : Subst) (state : State)
    (function argument : Preterm) (functionExpression argumentExpression : Atom)
    (capturedFunction : applySubst bindings functionExpression = preterm function)
    (capturedArgument : applySubst bindings argumentExpression = preterm argument) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:make-app", functionExpression, argumentExpression]) state
      (preterm (.app function argument)) := by
  apply raw_call_returns program bindings state state "mm0:make-app"
    [functionExpression, argumentExpression] _ (by decide) _ _ (by decide)
  · intro index bounded
    have bound : index < 2 := by simpa using bounded
    cases index with
    | zero => decide
    | succ index =>
        cases index with
        | zero => decide
        | succ index =>
            exact False.elim ((Nat.not_lt_zero index)
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))
  · simpa [capturedFunction, capturedArgument] using
      authored_function_arguments_return program bindings (appEnvironment function argument) state state
        "mm0:make-app" [preterm function, preterm argument] 2 makeAppEquation.body _
        (by decide) (by decide) (make_app_clause function argument)
        (make_app_body_returns state function argument)

theorem make_var_sufficient_fuel (bindings : Subst) (state : State) (index : Nat) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:make-var", natural index]) } =
      .complete state [preterm (.var index)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (make_var_returns bindings state index)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [preterm (.var index)] [] [] completed⟩

theorem make_term_sufficient_fuel (bindings : Subst) (state : State) (index : Nat) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:make-term", natural index]) } =
      .complete state [preterm (.term index)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (make_term_returns bindings state index)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [preterm (.term index)] [] [] completed⟩

theorem make_app_sufficient_fuel (bindings : Subst) (state : State)
    (function argument : Preterm) (functionExpression argumentExpression : Atom)
    (capturedFunction : applySubst bindings functionExpression = preterm function)
    (capturedArgument : applySubst bindings argumentExpression = preterm argument) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings
          (.expression [.symbol "mm0:make-app", functionExpression, argumentExpression]) } =
      .complete state [preterm (.app function argument)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (make_app_captured_returns bindings state function argument functionExpression argumentExpression
      capturedFunction capturedArgument)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [preterm (.app function argument)] [] [] completed⟩

namespace ConstructorControls

/-- Repeated captures build an application using the same supplied value twice. -/
theorem repeated_capture_returns (state : State) (value : Preterm) :
    PureReturns program [("shared", preterm value)] state
      (.expression [.symbol "mm0:make-app", .var "shared", .var "shared"]) state
      (preterm (.app value value)) :=
  make_app_captured_returns _ state value value _ _ rfl rfl

/-- Constructing an unbound variable succeeds as data; independent typing refuses it. -/
theorem unbound_variable_is_data (bindings : Subst) (state : State) (index : Nat) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:make-var", natural index]) state (preterm (.var index)) ∧
      Kernel.Preterm.infer (fun _ => none) [] (.var index) = none := by
  exact ⟨make_var_returns bindings state index, by simp [Kernel.Preterm.infer]⟩

/-- An unknown term identifier is retained by construction, then refused by typing. -/
theorem unknown_term_is_data (bindings : Subst) (state : State) (index : Nat) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:make-term", natural index]) state (preterm (.term index)) ∧
      Kernel.Preterm.infer (fun _ => none) [] (.term index) = none := by
  exact ⟨make_term_returns bindings state index, rfl⟩

end ConstructorControls

end Mettapedia.Languages.MM0.MeTTa.Data
