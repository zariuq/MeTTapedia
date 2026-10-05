import Mettapedia.Languages.MM0.MeTTa.Dependencies
import Mettapedia.Languages.MM0.MeTTa.ListSubstitution
import Mettapedia.Languages.MM0.Kernel.FreshDummies

/-!
# Freshness of dummy images in the retained MM0 source

Freshness requires defined occurrence support as well as the absence of the
candidate variable. Every parameter image is checked in order. An undefined
parameter refuses; it is not silently classified as independent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Freshness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (listValue viewValue)
open ListSubstitution (expressionsValue)

private def freshEquation : SourceProgram.Equation := (kernelSource.program.equations.take 65)[64]'(by decide)
private def allEquation : SourceProgram.Equation := (kernelSource.program.equations.take 66)[65]'(by decide)
private def viewEquation : SourceProgram.Equation := (kernelSource.program.equations.take 67)[66]'(by decide)
private def nextEquation : SourceProgram.Equation := (kernelSource.program.equations.take 68)[67]'(by decide)
private def freshEnvironment (target : Context) (image : Nat) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("image", natural image), ("target", Data.context target)]
private def allEnvironment (target : Context) (image : Nat) (arguments : List Preterm) : Subst :=
  [("arguments", expressionsValue arguments), ("image", natural image), ("target", Data.context target)]
private def viewEnvironment (target : Context) (image : Nat) (arguments : List Preterm) : Subst :=
  [("image", natural image), ("target", Data.context target), ("valueInput", viewValue (arguments.map Data.preterm))]
private def nextEnvironment (answer : Bool) (target : Context) (image : Nat) (arguments : List Preterm) : Subst :=
  [("arguments", expressionsValue arguments), ("image", natural image), ("target", Data.context target), ("conditionInput", boolean answer)]
private def sourceCases (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def viewCases := sourceCases viewEquation.body
private def nextCases := sourceCases nextEquation.body
private def consBody : Atom := (viewCases[1]'(by decide)).2
private theorem fresh_unique : program.equations.filter (fun e => e.head == "mm0:fresh-for") = [freshEquation] := by decide
private theorem all_unique : program.equations.filter (fun e => e.head == "mm0:fresh-all") = [allEquation] := by decide
private theorem view_unique : program.equations.filter (fun e => e.head == "mm0:fresh-all-view") = [viewEquation] := by decide
private theorem next_unique : program.equations.filter (fun e => e.head == "mm0:fresh-all-next") = [nextEquation] := by decide
private theorem fresh_formals : freshEquation.arguments = [.var "target", .var "image", .var "expression"] := by decide
private theorem all_formals : allEquation.arguments = [.var "target", .var "image", .var "arguments"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "valueInput", .var "target", .var "image"] := by decide
private theorem next_formals : nextEquation.arguments = [.var "conditionInput", .var "target", .var "image", .var "arguments"] := by decide
private theorem fresh_body_shape : freshEquation.body =
    .expression [.symbol "let", .var "items", .expression [.symbol "let", .var "items2", listValue [],
      .expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", natural 0, .var "items2"]]],
      .expression [.symbol "mm0:check-pair", .var "target", natural 0, .var "image", .var "items", natural 0, .var "expression"]] := by decide
private theorem all_body_shape : allEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "arguments"],
      .expression [.symbol "mm0:fresh-all-view", .var "view", .var "target", .var "image"]] := by decide
private theorem view_body_shape : viewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (viewCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem view_cases_shape : viewCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "expression", .var "arguments"], consBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "freshForResult", .expression [.symbol "mm0:fresh-for", .var "target", .var "image", .var "expression"],
      .expression [.symbol "mm0:fresh-all-next", .var "freshForResult", .var "target", .var "image", .var "arguments"]] := by decide
private theorem next_body_shape : nextEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (nextCases.map fun e => .expression [e.1, e.2])] := by decide
private theorem next_cases_shape : nextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:fresh-all", .var "target", .var "image", .var "arguments"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem fresh_clause (target : Context) (image : Nat) (expression : Preterm) :
    clauses program "mm0:fresh-for" [Data.context target, natural image, Data.preterm expression] =
      [.evaluate (freshEnvironment target image expression) freshEquation.body] := by
  rw [clauses_use_only_the_named_equations, fresh_unique]
  simp [fresh_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, freshEnvironment]
private theorem all_clause (target : Context) (image : Nat) (arguments : List Preterm) :
    clauses program "mm0:fresh-all" [Data.context target, natural image, expressionsValue arguments] =
      [.evaluate (allEnvironment target image arguments) allEquation.body] := by
  rw [clauses_use_only_the_named_equations, all_unique]
  simp [all_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, allEnvironment]
private theorem view_clause (target : Context) (image : Nat) (arguments : List Preterm) :
    clauses program "mm0:fresh-all-view" [viewValue (arguments.map Data.preterm), Data.context target, natural image] =
      [.evaluate (viewEnvironment target image arguments) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, viewEnvironment]
private theorem next_clause (answer : Bool) (target : Context) (image : Nat) (arguments : List Preterm) :
    clauses program "mm0:fresh-all-next" [boolean answer, Data.context target, natural image, expressionsValue arguments] =
      [.evaluate (nextEnvironment answer target image arguments) nextEquation.body] := by
  rw [clauses_use_only_the_named_equations, next_unique]
  simp [next_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, nextEnvironment]

theorem fresh_body_returns (state : State) (target : Context) (image : Nat) (expression : Preterm) :
    PureReturns program (freshEnvironment target image expression) state freshEquation.body state
      (boolean (Preterm.checkFreshFor target image expression)) := by
  rw [fresh_body_shape]
  let bindings := freshEnvironment target image expression
  let inner := ("items2", listValue []) :: bindings
  let bound := ("items", Data.binder (.regular 0 ∅)) :: bindings
  apply let_returns program bindings bound state state state (.var "items") _ _ (Data.binder (.regular 0 ∅)) _
  · apply let_returns program bindings inner state state state (.var "items2") _ _ (listValue []) _
    · exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
    · simp [SourceProgram.matchValue, matchAtom, inner, bindings, freshEnvironment, Subst.lookup]
    · apply unary_constructor_of_returns program inner state state "MM0:L" _ _ (by decide +kernel) (by decide)
      apply binary_constructor_returns program inner state state state "MM0:Regular" _ _ _ _ (by decide +kernel) (by decide)
      · exact grounded_returns program inner state (.int 0)
      · simpa [inner, Data.dependencies, applySubst, Subst.lookup] using variable_returns program inner state "items2"
  · simp [SourceProgram.matchValue, matchAtom, bound, bindings, freshEnvironment, Subst.lookup]
  · apply raw_call_returns program bound state state "mm0:check-pair"
      [.var "target", natural 0, .var "image", .var "items", natural 0, .var "expression"] _ (by decide) _ _ (by decide)
    · intro index h
      have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by simp at h; omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have numeric : applySubst bound (natural 0) = natural 0 := by simp [natural, applySubst]
      have targetCaptured : applySubst bound (.var "target") = Data.context target := rfl
      have imageCaptured : applySubst bound (.var "image") = natural image := rfl
      have binderCaptured : applySubst bound (.var "items") = Data.binder (.regular 0 ∅) := rfl
      have expressionCaptured : applySubst bound (.var "expression") = Data.preterm expression := rfl
      apply authored_function_arguments_return program bound _ state state "mm0:check-pair" _ _ _ _ (by decide) (by decide)
      · simpa only [List.map_cons, List.map_nil, numeric, targetCaptured, imageCaptured, binderCaptured, expressionCaptured] using
          Dependencies.pair_clause target 0 image (.regular 0 ∅) 0 expression
      · have pair := Dependencies.pair_body_returns state target 0 image (.regular 0 ∅) 0 expression
        cases support : Preterm.support? target expression <;>
          simpa [Kernel.Substitution.checkPair, Kernel.Binder.DependsOn, Preterm.checkFreshFor, support] using pair

-- The call is scoped to captured data, including constructor-shaped expressions.
theorem fresh_captured_returns (bindings : Subst) (state : State) (target : Context) (image : Nat) (expression : Preterm)
    (targetName imageName expressionName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedImage : applySubst bindings (.var imageName) = natural image)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression) :
    PureReturns program bindings state (.expression [.symbol "mm0:fresh-for", .var targetName, .var imageName, .var expressionName]) state
      (boolean (Preterm.checkFreshFor target image expression)) := by
  apply authored_variable_call_returns program bindings (freshEnvironment target image expression) state state
    "mm0:fresh-for" [targetName, imageName, expressionName] freshEquation.body _
    (by decide) (by decide) (by decide) _ (fresh_body_returns state target image expression) (by decide)
  simpa [capturedTarget, capturedImage, capturedExpression] using fresh_clause target image expression

private theorem all_call_from_body (bindings : Subst) (state : State) (target : Context) (image : Nat) (arguments : List Preterm)
    (targetName imageName argumentsName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedImage : applySubst bindings (.var imageName) = natural image)
    (capturedArguments : applySubst bindings (.var argumentsName) = expressionsValue arguments)
    (computed : PureReturns program (allEnvironment target image arguments) state allEquation.body state
      (boolean (arguments.all (Preterm.checkFreshFor target image)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:fresh-all", .var targetName, .var imageName, .var argumentsName]) state
      (boolean (arguments.all (Preterm.checkFreshFor target image))) := by
  apply authored_variable_call_returns program bindings (allEnvironment target image arguments) state state
    "mm0:fresh-all" [targetName, imageName, argumentsName] allEquation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTarget, capturedImage, capturedArguments] using all_clause target image arguments

private theorem next_body_returns (state : State) (answer : Bool) (target : Context) (image : Nat) (arguments : List Preterm)
    (recursive : PureReturns program (allEnvironment target image arguments) state allEquation.body state
      (boolean (arguments.all (Preterm.checkFreshFor target image)))) :
    PureReturns program (nextEnvironment answer target image arguments) state nextEquation.body state
      (boolean (answer && arguments.all (Preterm.checkFreshFor target image))) := by
  rw [next_body_shape]
  cases answer with
  | false =>
      let bindings := nextEnvironment false target image arguments
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ nextCases (read_cases_encoded nextCases)
      · simpa [bindings, nextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [next_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := nextEnvironment true target image arguments
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        (.expression [.symbol "mm0:fresh-all", .var "target", .var "image", .var "arguments"]) _ _ nextCases (read_cases_encoded nextCases)
      · simpa [bindings, nextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [next_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
      · exact all_call_from_body bindings state target image arguments "target" "image" "arguments" rfl rfl rfl recursive

theorem all_body_returns (state : State) (target : Context) (image : Nat) (arguments : List Preterm) :
    PureReturns program (allEnvironment target image arguments) state allEquation.body state
      (boolean (arguments.all (Preterm.checkFreshFor target image))) := by
  induction arguments with
  | nil =>
      rw [all_body_shape]
      let bindings := allEnvironment target image []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "arguments" [] rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, allEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment target image []) state state
          "mm0:fresh-all-view" ["view", "target", "image"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, allEnvironment, applySubst, Subst.lookup] using view_clause target image []
        · rw [view_body_shape]
          let callee := viewEnvironment target image []
          apply case_returns program callee callee state state state (.var "valueInput") (viewValue []) (boolean true)
            _ _ viewCases (read_cases_encoded viewCases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [view_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, viewValue]
          · exact grounded_returns program callee state (.bool true)
  | cons expression arguments ih =>
      rw [all_body_shape]
      let bindings := allEnvironment target image (expression :: arguments)
      let viewed := ("view", viewValue ((expression :: arguments).map Data.preterm)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((expression :: arguments).map Data.preterm)) _
      · exact ListAccess.view_captured_returns bindings state "arguments" ((expression :: arguments).map Data.preterm) rfl
      · simp [SourceProgram.matchValue, matchAtom, viewed, bindings, allEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment target image (expression :: arguments)) state state
          "mm0:fresh-all-view" ["view", "target", "image"] viewEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, allEnvironment, applySubst, Subst.lookup] using view_clause target image (expression :: arguments)
        · rw [view_body_shape]
          let callee := viewEnvironment target image (expression :: arguments)
          let bound := ("arguments", expressionsValue arguments) :: ("expression", Data.preterm expression) :: callee
          apply case_returns program callee bound state state state (.var "valueInput") (viewValue ((expression :: arguments).map Data.preterm))
            consBody _ _ viewCases (read_cases_encoded viewCases)
          · simpa [callee, viewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [view_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
              matchAtom, viewValue, expressionsValue, listValue, bound, callee, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let answer := Preterm.checkFreshFor target image expression
            let tested := ("freshForResult", boolean answer) :: bound
            apply let_returns program bound tested state state state (.var "freshForResult") _ _ (boolean answer) _
            · exact fresh_captured_returns bound state target image expression "target" "image" "expression" rfl rfl rfl
            · simp [SourceProgram.matchValue, matchAtom, tested, bound, callee, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program tested (nextEnvironment answer target image arguments) state state
                "mm0:fresh-all-next" ["freshForResult", "target", "image", "arguments"] nextEquation.body _
                (by decide) (by decide) (by decide) _ (next_body_returns state answer target image arguments ih) (by decide)
              simpa [tested, bound, callee, viewEnvironment, applySubst, Subst.lookup] using next_clause answer target image arguments

theorem all_captured_returns (bindings : Subst) (state : State) (target : Context) (image : Nat) (arguments : List Preterm)
    (targetName imageName argumentsName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedImage : applySubst bindings (.var imageName) = natural image)
    (capturedArguments : applySubst bindings (.var argumentsName) = expressionsValue arguments) :
    PureReturns program bindings state (.expression [.symbol "mm0:fresh-all", .var targetName, .var imageName, .var argumentsName]) state
      (boolean (arguments.all (Preterm.checkFreshFor target image))) :=
  all_call_from_body bindings state target image arguments targetName imageName argumentsName capturedTarget capturedImage capturedArguments
    (all_body_returns state target image arguments)

def requestConfiguration (state : State) (target : Context) (image : Nat) (expression : Preterm) : Configuration :=
  { state, control := .evaluate (freshEnvironment target image expression)
      (.expression [.symbol "mm0:fresh-for", .var "target", .var "image", .var "expression"]) }

theorem sufficient_fuel (state : State) (target : Context) (image : Nat) (expression : Preterm) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (requestConfiguration state target image expression) =
      .complete state [boolean (Preterm.checkFreshFor target image expression)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (freshEnvironment target image expression) state state _ _
    (fresh_captured_returns _ state target image expression "target" "image" "expression" rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (state : State) (target : Context) (image : Nat) (expression : Preterm) (answer : Bool) :
    Preterm.checkFreshFor target image expression = answer ↔
      ∃ fuel, run program fuel (requestConfiguration state target image expression) = .complete state [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state target image expression
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same; exact ⟨referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

theorem fresh_iff_source_accepts (state : State) (target : Context) (image : Nat) (expression : Preterm) :
    Preterm.FreshFor target image expression ↔
      ∃ fuel, run program fuel (requestConfiguration state target image expression) = .complete state [boolean true] [] [] :=
  (Preterm.checkFreshFor_iff target image expression).symm.trans (result_iff_source_returns state target image expression true)

end Mettapedia.Languages.MM0.MeTTa.Freshness
