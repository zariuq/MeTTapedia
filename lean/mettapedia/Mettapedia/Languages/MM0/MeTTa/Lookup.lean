import Mettapedia.Languages.MM0.MeTTa.ListAccess
import Mettapedia.Languages.MM0.MeTTa.Scalar

/-!
# Substitution-list lookup in the retained MM0 source

This executes the pinned lookup and lookup-zero equations, with the existing
scalar contracts for their zero test and predecessor. The induction is over
the supplied list, not a list of proof-certificate nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Lookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open Store (natural)
open ListAccess (linkedValue optionValue)

private def environment (values : List Atom) (index : Nat) : Subst :=
  [("i", natural index), ("valueInput", linkedValue values)]

private def zeroEnvironment (condition : Bool) (head : Atom) (tail : List Atom) (index : Nat) : Subst :=
  [("i", natural index), ("t", linkedValue tail), ("h", head), ("conditionInput", boolean condition)]

theorem lookup_clause (values : List Atom) (index : Nat) :
    clauses program "mm0:lookup" [linkedValue values, natural index] =
      [.evaluate (environment values index) lookupEquation.body] := by
  rw [clauses_use_only_the_named_equations, lookup_equation_is_unique]
  simp [lookup_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem zero_clause (condition : Bool) (head : Atom) (tail : List Atom) (index : Nat) :
    clauses program "mm0:lookup-zero" [boolean condition, head, linkedValue tail, natural index] =
      [.evaluate (zeroEnvironment condition head tail index) lookupZeroEquation.body] := by
  rw [clauses_use_only_the_named_equations, lookup_zero_equation_is_unique]
  simp [lookup_zero_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, zeroEnvironment]

private def cases : SourceProgram.Cases :=
  match lookupEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def consBody : Atom := (cases[1]'(by decide)).2

private def zeroCases : SourceProgram.Cases :=
  match lookupZeroEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def trueBody : Atom := (zeroCases[0]'(by decide)).2

private def falseBody : Atom := (zeroCases[1]'(by decide)).2

private theorem body_is_case :
    lookupEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape :
    cases = [(.symbol "LNil", .symbol "None"),
      (.expression [.symbol "LCons", .var "h", .var "t"], consBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem cons_body_shape :
    consBody = .expression [.symbol "let", .var "isZero",
      .expression [.symbol "mm0:nat-zero", .var "i"],
      .expression [.symbol "mm0:lookup-zero", .var "isZero", .var "h", .var "t", .var "i"]] := by
  decide

private theorem zero_body_is_case :
    lookupZeroEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (zeroCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem zero_cases_shape :
    zeroCases = [(boolean true, trueBody), (boolean false, falseBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem true_body_shape : trueBody = .expression [.symbol "Some", .var "h"] := by decide

private theorem false_body_shape :
    falseBody = .expression [.symbol "let", .var "previous",
      .expression [.symbol "mm0:nat-pred", .var "i"],
      .expression [.symbol "mm0:lookup", .var "t", .var "previous"]] := by decide

private theorem zero_body_returns (state : State) (head : Atom) (tail : List Atom) (index : Nat)
    (recursive : PureReturns program (environment tail index.pred) state lookupEquation.body state
      (optionValue (tail[index.pred]?))) :
    PureReturns program (zeroEnvironment (index == 0) head tail index) state
      lookupZeroEquation.body state (optionValue ((head :: tail)[index]?)) := by
  rw [zero_body_is_case]
  cases index with
  | zero =>
      let bindings := zeroEnvironment true head tail 0
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean true) trueBody _ _ zeroCases (read_cases_encoded zeroCases)
      · simpa [bindings, zeroEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "conditionInput"
      · simp [zero_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · rw [true_body_shape]
        simpa [bindings, zeroEnvironment, optionValue, applySubst, Subst.lookup] using
          unary_constructor_returns program bindings state "Some" "h" some_is_data_constructor (by decide)
  | succ index =>
      let bindings := zeroEnvironment false head tail (index + 1)
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean false) falseBody _ _ zeroCases (read_cases_encoded zeroCases)
      · simpa [bindings, zeroEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "conditionInput"
      · simp [zero_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          matchAtom, boolean]
      · rw [false_body_shape]
        let bound := ("previous", natural index) :: bindings
        apply let_returns program bindings bound state state state (.var "previous") _ _ (natural index) _
        · apply Scalar.pred_captured_returns bindings state "i" (index + 1)
          simp [bindings, zeroEnvironment, applySubst, Subst.lookup]
        · simp [SourceProgram.matchValue, matchAtom, bindings, zeroEnvironment, Subst.lookup, bound]
        · apply authored_variable_call_returns program bound (environment tail index) state state
            "mm0:lookup" ["t", "previous"] lookupEquation.body _
            (by decide) (by decide) (by decide)
            _ (by simpa using recursive) (by decide)
          simpa [bound, bindings, zeroEnvironment, applySubst, Subst.lookup] using lookup_clause tail index

theorem lookup_body_returns (state : State) (values : List Atom) (index : Nat) :
    PureReturns program (environment values index) state lookupEquation.body state
      (optionValue (values[index]?)) := by
  induction values generalizing index with
  | nil =>
      rw [body_is_case]
      apply case_returns program (environment [] index) (environment [] index) state state state
        (.var "valueInput") (.symbol "LNil") (.symbol "None") _ _ cases (read_cases_encoded cases)
      · simpa [environment, linkedValue, applySubst, Subst.lookup] using
          variable_returns program (environment [] index) state "valueInput"
      · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom]
      · simpa [optionValue] using symbol_returns program (environment [] index) state "None"
  | cons head tail ih =>
      let bindings := environment (head :: tail) index
      let bound := ("t", linkedValue tail) :: ("h", head) :: bindings
      rw [body_is_case]
      apply case_returns program bindings bound state state state (.var "valueInput")
        (linkedValue (head :: tail)) consBody _ _ cases (read_cases_encoded cases)
      · simpa [bindings, environment, applySubst, Subst.lookup] using
          variable_returns program bindings state "valueInput"
      · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues, linkedValue, bindings, bound, environment,
          matchAtom, Subst.lookup]
      · rw [cons_body_shape]
        let tested := ("isZero", boolean (index == 0)) :: bound
        apply let_returns program bound tested state state state (.var "isZero") _ _
          (boolean (index == 0)) _
        · apply Scalar.zero_captured_returns bound state "i" index
          simp [bound, bindings, environment, applySubst, Subst.lookup]
        · simp [SourceProgram.matchValue, matchAtom, bound, bindings, environment, Subst.lookup, tested]
        · apply authored_variable_call_returns program tested
            (zeroEnvironment (index == 0) head tail index) state state "mm0:lookup-zero"
            ["isZero", "h", "t", "i"] lookupZeroEquation.body _
            (by decide) (by decide) (by decide)
            _ (zero_body_returns state head tail index (ih index.pred)) (by decide)
          simpa [tested, bound, bindings, environment, applySubst, Subst.lookup] using
            zero_clause (index == 0) head tail index

theorem lookup_returns (bindings : Subst) (state : State) (values : List Atom) (index : Nat)
    (valuesName indexName : String)
    (valuesCaptured : applySubst bindings (.var valuesName) = linkedValue values)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:lookup", .var valuesName, .var indexName]) state
      (optionValue (values[index]?)) := by
  apply authored_variable_call_returns program bindings (environment values index) state state
    "mm0:lookup" [valuesName, indexName] lookupEquation.body _
    (by decide) (by decide) (by decide) _ (lookup_body_returns state values index) (by decide)
  simpa [valuesCaptured, indexCaptured] using lookup_clause values index

end Mettapedia.Languages.MM0.MeTTa.Lookup
