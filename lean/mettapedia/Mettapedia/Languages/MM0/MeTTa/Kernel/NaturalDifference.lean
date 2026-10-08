import Mettapedia.Languages.MM0.MeTTa.Kernel.Dependencies
import Mettapedia.Languages.MM0.Presentation.FreeVariablesData

/-!
# Ordered natural-number difference in the retained MM0 source

The source removes every occurrence of a selected natural number and keeps
the order and multiplicity of all other entries. The finite-set observation
is set difference; execution changes no store or cache.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.MeTTa.NaturalDifference

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue viewValue)
open Support (indicesValue)
open Presentation.ComputationalFreeVariables (subtract)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 159)[158]'(by decide)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 160)[159]'(by decide)
private def keepEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 161)[160]'(by decide)
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def cases := casesOf viewEquation.body
private def keepCases := casesOf keepEquation.body
private def consBody := (cases[1]'(by decide)).2
private def environment (source removed : List Nat) : Subst :=
  [("removed", indicesValue removed), ("source", indicesValue source)]
private def viewEnvironment (source removed : List Nat) : Subst :=
  [("removed", indicesValue removed), ("valueInput", viewValue (source.map natural))]
private def keepEnvironment (condition : Bool) (first : Nat) (rest : List Nat) : Subst :=
  [("rest", indicesValue rest), ("first", natural first), ("conditionInput", boolean condition)]

private theorem unique :
    program.equations.filter (fun e => e.head == "mm0:nat-difference") = [equation] := by decide
private theorem view_unique :
    program.equations.filter (fun e => e.head == "mm0:difference-view") = [viewEquation] := by decide
private theorem keep_unique :
    program.equations.filter (fun e => e.head == "mm0:difference-keep") = [keepEquation] := by decide
private theorem formals : equation.arguments = [.var "source", .var "removed"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "removed"] := by decide
private theorem keep_formals : keepEquation.arguments = [.var "conditionInput", .var "first", .var "rest"] := by decide
private theorem shape : equation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "source"],
      .expression [.symbol "mm0:difference-view", .var "view", .var "removed"]] := by decide
private theorem view_shape : viewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (.symbol "List:Nil", .expression [.symbol "MM0:L", .expression []]),
    (.expression [.symbol "List:Cons", .var "first", .var "rest"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_shape : consBody =
    .expression [.symbol "let", .var "natMemberResult", .expression [.symbol "mm0:nat-member", .var "first", .var "removed"],
      .expression [.symbol "let", .var "natDifferenceResult", .expression [.symbol "mm0:nat-difference", .var "rest", .var "removed"],
        .expression [.symbol "mm0:difference-keep", .var "natMemberResult", .var "first", .var "natDifferenceResult"]]] := by decide
private theorem keep_shape : keepEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (keepCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem keep_cases : keepCases = [
    (boolean true, .var "rest"),
    (boolean false, .expression [.symbol "mm0:list-cons", .var "first", .var "rest"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem clause (source removed : List Nat) :
    clauses program "mm0:nat-difference" [indicesValue source, indicesValue removed] =
      [.evaluate (environment source removed) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]
private theorem view_clause (source removed : List Nat) :
    clauses program "mm0:difference-view" [viewValue (source.map natural), indicesValue removed] =
      [.evaluate (viewEnvironment source removed) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, viewEnvironment]
private theorem keep_clause (condition : Bool) (first : Nat) (rest : List Nat) :
    clauses program "mm0:difference-keep" [boolean condition, natural first, indicesValue rest] =
      [.evaluate (keepEnvironment condition first rest) keepEquation.body] := by
  rw [clauses_use_only_the_named_equations, keep_unique]
  simp [keep_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, keepEnvironment]

private theorem keep_body_returns (state : State) (condition : Bool) (first : Nat) (rest : List Nat) :
    PureReturns program (keepEnvironment condition first rest) state keepEquation.body state
      (indicesValue (if condition then rest else first :: rest)) := by
  rw [keep_shape]
  cases condition with
  | true =>
      apply case_returns program (keepEnvironment true first rest) (keepEnvironment true first rest) state state state
        (.var "conditionInput") (boolean true) (.var "rest") _ _ keepCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [keep_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact variable_returns program _ state "rest"
  | false =>
      apply case_returns program (keepEnvironment false first rest) (keepEnvironment false first rest) state state state
        (.var "conditionInput") (boolean false) (.expression [.symbol "mm0:list-cons", .var "first", .var "rest"])
        _ _ keepCases (read_cases_encoded _)
      · exact variable_returns program _ state "conditionInput"
      · simp [keep_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact ListAccess.cons_captured_returns _ state (natural first) (rest.map natural) "first" "rest" rfl rfl

theorem body_returns (state : State) (source removed : List Nat) :
    PureReturns program (environment source removed) state equation.body state
      (indicesValue (subtract source removed)) := by
  induction source with
  | nil =>
      rw [shape]
      let bindings := environment [] removed
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "source" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment [] removed) state state
          "mm0:difference-view" ["view", "removed"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause [] removed
        · rw [view_shape]
          apply case_returns program (viewEnvironment [] removed) (viewEnvironment [] removed) state state state
            (.var "valueInput") (viewValue []) (.expression [.symbol "MM0:L", .expression []])
            _ _ cases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · exact empty_constructor_returns program _ state "MM0:L" list_is_data_constructor (by decide)
  | cons first rest recursive =>
      rw [shape]
      let bindings := environment (first :: rest) removed
      let viewed := ("view", viewValue ((first :: rest).map natural)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((first :: rest).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "source" _ rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, environment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment (first :: rest) removed) state state
          "mm0:difference-view" ["view", "removed"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, environment, applySubst, Subst.lookup] using view_clause (first :: rest) removed
        · rw [view_shape]
          let callee := viewEnvironment (first :: rest) removed
          let bound := ("rest", indicesValue rest) :: ("first", natural first) :: callee
          apply case_returns program callee bound state state state (.var "valueInput")
            (viewValue ((first :: rest).map natural)) consBody _ _ cases (read_cases_encoded _)
          · exact variable_returns program _ state "valueInput"
          · simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, bound, callee,
              viewEnvironment, indicesValue, Subst.lookup]
          · rw [cons_shape]
            let tested := ("natMemberResult", boolean (decide (first ∈ removed))) :: bound
            apply let_returns program bound tested state state state (.var "natMemberResult") _ _
              (boolean (decide (first ∈ removed))) _
            · exact Dependencies.member_captured_returns bound state first removed "first" "removed" rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, tested, bound, callee, viewEnvironment, Subst.lookup]
            · let completed := ("natDifferenceResult", indicesValue (subtract rest removed)) :: tested
              apply let_returns program tested completed state state state (.var "natDifferenceResult") _ _
                (indicesValue (subtract rest removed)) _
              · apply authored_variable_call_returns program tested (environment rest removed) state state
                  "mm0:nat-difference" ["rest", "removed"] equation.body _
                  (by decide) (by decide) (by decide) _ recursive (by decide)
                simpa [tested, bound, callee, viewEnvironment, applySubst, Subst.lookup] using clause rest removed
              · simp [SpaceSemantics.matchValue, matchAtom, completed, tested, bound, callee, viewEnvironment, Subst.lookup]
              · have same : subtract (first :: rest) removed =
                    if decide (first ∈ removed) then subtract rest removed else first :: subtract rest removed := by
                  by_cases member : first ∈ removed <;> simp [subtract, member]
                rw [same]
                apply authored_variable_call_returns program completed
                  (keepEnvironment (decide (first ∈ removed)) first (subtract rest removed)) state state
                  "mm0:difference-keep" ["natMemberResult", "first", "natDifferenceResult"] keepEquation.body _
                  (by decide) (by decide) (by decide) _ (keep_body_returns state _ first _) (by decide)
                simpa [completed, tested, bound, callee, viewEnvironment, applySubst, Subst.lookup] using
                  keep_clause (decide (first ∈ removed)) first (subtract rest removed)

theorem captured_returns (bindings : Subst) (state : State) (source removed : List Nat)
    (sourceName removedName : String)
    (capturedSource : applySubst bindings (.var sourceName) = indicesValue source)
    (capturedRemoved : applySubst bindings (.var removedName) = indicesValue removed) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-difference", .var sourceName, .var removedName]) state
      (indicesValue (subtract source removed)) := by
  apply authored_variable_call_returns program bindings (environment source removed) state state
    "mm0:nat-difference" [sourceName, removedName] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns state source removed) (by decide)
  simpa [capturedSource, capturedRemoved] using clause source removed

theorem membership_meaning (source removed : List Nat) (index : Nat) :
    index ∈ subtract source removed ↔ index ∈ source ∧ index ∉ removed := by
  simp [subtract]

theorem removes_all_occurrences : subtract [0, 1, 0, 2, 1] [0] = [1, 2, 1] := by decide

theorem keeps_unselected_occurrences : subtract [0, 1, 0, 2, 1] [3] = [0, 1, 0, 2, 1] := by decide

end Mettapedia.Languages.MM0.MeTTa.NaturalDifference
