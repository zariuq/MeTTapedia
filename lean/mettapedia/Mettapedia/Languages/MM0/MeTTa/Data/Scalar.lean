import Mettapedia.Languages.MM0.MeTTa.Program
import Mettapedia.Languages.MM0.MeTTa.Data.Store
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Scalar computations in the retained MM0 source

The zero test, predecessor, addition and equality use bodies read from the pinned MeTTa file.
Their computations are proved for every natural input and source store. These
component theorems do not assert correctness of admission or
of the whole MM0 checker. Native equality conformance remains a runtime boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Scalar

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)

private def environment (value : Nat) : MORK.Subst := [("n", natural value)]

theorem zero_clause (value : Nat) :
    clauses program "mm0:nat-zero" [natural value] =
      [.evaluate (environment value) natZeroEquation.body] := by
  rw [clauses_use_only_the_named_equations, nat_zero_equation_is_unique]
  simp [nat_zero_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, MORK.Subst.lookup, environment]

theorem zero_body_returns (state : State) (value : Nat) :
    PureReturns program (environment value) state natZeroEquation.body state
      (boolean (value == 0)) := by
  rw [nat_zero_body]
  apply native_binary_call_returns program (environment value) state state state state "=="
    (.var "n") (.grounded (.int 0)) (natural value) (natural 0) (boolean (value == 0))
    (by decide) (by decide) (by decide) (by decide)
    _ (grounded_returns program (environment value) state (.int 0)) _ (by decide)
  · simpa [environment, applySubst, MORK.Subst.lookup] using
      variable_returns program (environment value) state "n"
  · simp [StdLib.apply, natural, boolean]

theorem zero_captured_returns (bindings : MORK.Subst) (state : State) (name : String) (value : Nat)
    (captured : applySubst bindings (.var name) = natural value) :
    PureReturns program bindings state (.expression [.symbol "mm0:nat-zero", .var name]) state
      (boolean (value == 0)) := by
  apply authored_variable_call_returns program bindings (environment value) state state
    "mm0:nat-zero" [name] natZeroEquation.body _ (by decide) (by decide) (by decide)
    _ (zero_body_returns state value) (by decide)
  simpa [captured] using zero_clause value

theorem pred_clause (value : Nat) :
    clauses program "mm0:nat-pred" [natural value] =
      [.evaluate (environment value) natPredEquation.body] := by
  rw [clauses_use_only_the_named_equations, nat_pred_equation_is_unique]
  simp [nat_pred_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, MORK.Subst.lookup, environment]

theorem pred_body_returns (state : State) (value : Nat) :
    PureReturns program (environment value) state natPredEquation.body state (natural value.pred) := by
  rw [nat_pred_body]
  apply if_returns program (environment value) state state state _ _ _ _ _ (zero_body_returns state value)
  cases value with
  | zero =>
      simpa [boolean, natural] using grounded_returns program (environment 0) state (.int 0)
  | succ value =>
      simp only [boolean, Nat.pred_succ]
      apply native_binary_call_returns program (environment (value + 1)) state state state state "-"
        (.var "n") (.grounded (.int 1)) (natural (value + 1)) (natural 1) (natural value)
        (by decide) (by decide) (by decide) (by decide)
        _ (grounded_returns program (environment (value + 1)) state (.int 1)) _ (by decide)
      · simpa [environment, applySubst, MORK.Subst.lookup] using
          variable_returns program (environment (value + 1)) state "n"
      · simp [StdLib.apply, natural]

theorem pred_captured_returns (bindings : MORK.Subst) (state : State) (name : String) (value : Nat)
    (captured : applySubst bindings (.var name) = natural value) :
    PureReturns program bindings state (.expression [.symbol "mm0:nat-pred", .var name]) state
      (natural value.pred) := by
  apply authored_variable_call_returns program bindings (environment value) state state
    "mm0:nat-pred" [name] natPredEquation.body _ (by decide) (by decide) (by decide)
    _ (pred_body_returns state value) (by decide)
  simpa [captured] using pred_clause value

theorem zero_returns (state : State) (value : Nat) :
    PureReturns program [] state (.expression [.symbol "mm0:nat-zero", natural value]) state
      (boolean (value == 0)) := by
  apply call_returns program [] state state "mm0:nat-zero" [natural value]
    (boolean (value == 0)) (by decide) _ (by decide)
  have entered : (theory program).MultiStep
      { state, control := .arguments [] (.function "mm0:nat-zero") [] [natural value] 1 }
      (finished state [boolean (value == 0)] [] []) :=
    authored_function_arguments_return program [] (environment value) state state
      "mm0:nat-zero" [natural value] 1 natZeroEquation.body (boolean (value == 0))
      (by decide) (by decide) (zero_clause value) (zero_body_returns state value)
  exact evaluated_argument_returns program [] state state state (.function "mm0:nat-zero")
    (natural value) (natural value) (boolean (value == 0)) [] [] 0
    nat_zero_is_computational (grounded_returns program [] state (.int value)) entered

theorem zero_has_sufficient_fuel (state : State) (value : Nat) :
    ∃ fuel, evaluate program fuel state
      (.expression [.symbol "mm0:nat-zero", natural value]) =
      .complete state [boolean (value == 0)] [] [] :=
  pure_returns_has_sufficient_fuel program [] state state _ _ (zero_returns state value)

private def equalityEnvironment (first second : Nat) : MORK.Subst :=
  [("b", natural second), ("a", natural first)]

theorem equality_clause (first second : Nat) :
    clauses program "mm0:nat-eq" [natural first, natural second] =
      [.evaluate (equalityEnvironment first second) natEqualEquation.body] := by
  rw [clauses_use_only_the_named_equations, nat_equal_equation_is_unique]
  simp [nat_equal_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, MORK.Subst.lookup, equalityEnvironment]

theorem equality_body_returns (state : State) (first second : Nat) :
    PureReturns program (equalityEnvironment first second) state natEqualEquation.body state
      (boolean (decide (first = second))) := by
  rw [nat_equal_body]
  apply native_variable_call_returns program (equalityEnvironment first second) state state
    "==" ["a", "b"] _ (by decide) (by decide) _ (by decide)
  simp [StdLib.apply, equalityEnvironment, applySubst, MORK.Subst.lookup,
    natural, boolean, beq_eq_decide]
  exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩

theorem equality_captured_returns (bindings : MORK.Subst) (state : State)
    (firstName secondName : String) (first second : Nat)
    (capturedFirst : applySubst bindings (.var firstName) = natural first)
    (capturedSecond : applySubst bindings (.var secondName) = natural second) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-eq", .var firstName, .var secondName]) state
      (boolean (decide (first = second))) := by
  apply authored_variable_call_returns program bindings (equalityEnvironment first second)
    state state "mm0:nat-eq" [firstName, secondName] natEqualEquation.body _
    (by decide) (by decide) (by decide) _ (equality_body_returns state first second) (by decide)
  simpa [capturedFirst, capturedSecond] using equality_clause first second

private def additionEquation : SpaceSemantics.Equation := dataSource.program.equations[18]'(by decide)
private theorem addition_unique :
    program.equations.filter (fun entry => entry.head == "mm0:nat-add") = [additionEquation] := by decide
private theorem addition_formals : additionEquation.arguments = [.var "a", .var "b"] := by decide
private theorem addition_body :
    additionEquation.body = .expression [.symbol "+", .var "a", .var "b"] := by decide

theorem addition_clause (first second : Nat) :
    clauses program "mm0:nat-add" [natural first, natural second] =
      [.evaluate (equalityEnvironment first second) additionEquation.body] := by
  rw [clauses_use_only_the_named_equations, addition_unique]
  simp [addition_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, MORK.Subst.lookup, equalityEnvironment]

theorem addition_body_returns (state : State) (first second : Nat) :
    PureReturns program (equalityEnvironment first second) state additionEquation.body state (natural (first + second)) := by
  rw [addition_body]
  apply native_variable_call_returns program (equalityEnvironment first second) state state
    "+" ["a", "b"] _ (by decide) (by decide) _ (by decide)
  simp [StdLib.apply, equalityEnvironment, applySubst, MORK.Subst.lookup, natural]

theorem addition_returns (bindings : MORK.Subst) (state : State) (first second : Nat)
    (left right : Atom)
    (leftReturns : PureReturns program bindings state left state (natural first))
    (rightReturns : PureReturns program bindings state right state (natural second)) :
    PureReturns program bindings state (.expression [.symbol "mm0:nat-add", left, right]) state (natural (first + second)) :=
  authored_binary_call_returns program bindings (equalityEnvironment first second) state state state state
    "mm0:nat-add" left right (natural first) (natural second) additionEquation.body (natural (first + second))
    (by decide) (by decide) (by decide) (by decide) (by decide) leftReturns rightReturns
    (addition_clause first second) (addition_body_returns state first second) (by decide)

/-! ## Structural equality of captured data -/

private def dataEqualityEquation : SpaceSemantics.Equation := dataSource.program.equations[14]'(by decide)
private def dataEqualityEnvironment (first second : Atom) : MORK.Subst := [("second", second), ("first", first)]
private theorem data_equality_unique :
    program.equations.filter (fun e => e.head == "mm0:data-eq") = [dataEqualityEquation] := by decide
private theorem data_equality_formals : dataEqualityEquation.arguments = [.var "first", .var "second"] := by decide
private theorem data_equality_body_shape : dataEqualityEquation.body =
    .expression [.symbol "==", .var "first", .var "second"] := by decide
private theorem data_equality_clause (first second : Atom) :
    clauses program "mm0:data-eq" [first, second] =
      [.evaluate (dataEqualityEnvironment first second) dataEqualityEquation.body] := by
  rw [clauses_use_only_the_named_equations, data_equality_unique]
  simp [data_equality_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, MORK.Subst.lookup, dataEqualityEnvironment]

theorem data_equality_body_returns (state : State) (first second : Atom) :
    PureReturns program (dataEqualityEnvironment first second) state dataEqualityEquation.body state
      (boolean (decide (first = second))) := by
  rw [data_equality_body_shape]
  apply native_variable_call_returns program (dataEqualityEnvironment first second) state state
    "==" ["first", "second"] _ (by decide) (by decide) _ (by decide)
  simp [StdLib.apply, dataEqualityEnvironment, applySubst, MORK.Subst.lookup, beq_eq_decide]

theorem data_equality_captured_returns (bindings : MORK.Subst) (state : State)
    (first second : Atom) (firstName secondName : String)
    (capturedFirst : applySubst bindings (.var firstName) = first)
    (capturedSecond : applySubst bindings (.var secondName) = second) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:data-eq", .var firstName, .var secondName]) state
      (boolean (decide (first = second))) := by
  apply authored_variable_call_returns program bindings (dataEqualityEnvironment first second) state state
    "mm0:data-eq" [firstName, secondName] dataEqualityEquation.body _
    (by decide) (by decide) (by decide) _ (data_equality_body_returns state first second) (by decide)
  simpa [capturedFirst, capturedSecond] using data_equality_clause first second

end Mettapedia.Languages.MM0.MeTTa.Scalar
