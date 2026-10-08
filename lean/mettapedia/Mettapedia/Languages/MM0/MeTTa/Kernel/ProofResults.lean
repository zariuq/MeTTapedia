import Mettapedia.Languages.MM0.MeTTa.Kernel.ConversionResults
import Mettapedia.Languages.MM0.MeTTa.Kernel.Hypothesis

/-!
# Premise and conversion matching in the retained MM0 source

The proof checker compares the supplied children's actual conclusions with
the instantiated premises, in order and with multiplicity. A conversion
checks the child's conclusion against the conversion's left endpoint. These
helpers neither infer an alternative proof nor admit a declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ProofResults

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Preterm)
open ListAccess (optionValue)
open ListSubstitution (expressionsValue)

def resultValue (result : Option Preterm) : Atom := optionValue (result.map Data.preterm)

theorem resultValue_injective : Function.Injective resultValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [resultValue, optionValue]
  | some first =>
      cases second with
      | none => simp [resultValue, optionValue] at same
      | some second =>
          have encoded : Data.preterm first = Data.preterm second := by simpa [resultValue, optionValue] using same
          exact congrArg some (Data.preterm_injective encoded)

private def premisesEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 5)[4]'(by decide)
private def matchedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 6)[5]'(by decide)
private def leftEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 8)[7]'(by decide)
private def conversionMatchedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 9)[8]'(by decide)
private def tailEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 13)[12]'(by decide)
private def premisesEnvironment (actual : Option (List Preterm)) (premises : List Preterm) (conclusion : Preterm) : Subst :=
  [("conclusion", Data.preterm conclusion), ("premises", expressionsValue premises), ("valueInput", ListSubstitution.resultValue actual)]
private def leftEnvironment (actual : Option Preterm) (left right : Preterm) : Subst :=
  [("right", Data.preterm right), ("left", Data.preterm left), ("valueInput", resultValue actual)]
private def matchedEnvironment (answer : Bool) (conclusion : Preterm) : Subst :=
  [("conclusion", Data.preterm conclusion), ("conditionInput", boolean answer)]
private def conversionMatchedEnvironment (answer : Bool) (right : Preterm) : Subst :=
  [("right", Data.preterm right), ("conditionInput", boolean answer)]
private def tailEnvironment (rest : Option (List Preterm)) (first : Preterm) : Subst :=
  [("first", Data.preterm first), ("valueInput", ListSubstitution.resultValue rest)]
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def premisesCases := casesOf premisesEquation.body
private def leftCases := casesOf leftEquation.body
private def premisesBody : Atom := (premisesCases[1]'(by decide)).2
private def leftBody : Atom := (leftCases[1]'(by decide)).2
private theorem premises_unique : program.equations.filter (fun e => e.head == "mm0:proof-premises") = [premisesEquation] := by decide
private theorem matched_unique : program.equations.filter (fun e => e.head == "mm0:proof-matched") = [matchedEquation] := by decide
private theorem left_unique : program.equations.filter (fun e => e.head == "mm0:proof-left") = [leftEquation] := by decide
private theorem conversion_matched_unique : program.equations.filter (fun e => e.head == "mm0:proof-conversion-matched") = [conversionMatchedEquation] := by decide
private theorem tail_unique : program.equations.filter (fun e => e.head == "mm0:proof-tail") = [tailEquation] := by decide
private theorem premises_formals : premisesEquation.arguments = [.var "valueInput", .var "premises", .var "conclusion"] := by decide
private theorem matched_formals : matchedEquation.arguments = [.var "conditionInput", .var "conclusion"] := by decide
private theorem left_formals : leftEquation.arguments = [.var "valueInput", .var "left", .var "right"] := by decide
private theorem conversion_matched_formals : conversionMatchedEquation.arguments = [.var "conditionInput", .var "right"] := by decide
private theorem tail_formals : tailEquation.arguments = [.var "valueInput", .var "first"] := by decide
private theorem premises_body_shape : premisesEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (premisesCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem premises_cases_shape : premisesCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Expressions", .var "actual"], premisesBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem premises_some_shape : premisesBody =
    .expression [.symbol "let", .var "equal", .expression [.symbol "mm0:data-eq", .var "actual", .var "premises"],
      .expression [.symbol "mm0:proof-matched", .var "equal", .var "conclusion"]] := by decide
private theorem left_body_shape : leftEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (leftCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem left_cases_shape : leftCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "conclusion"], leftBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem left_some_shape : leftBody =
    .expression [.symbol "let", .var "equal", .expression [.symbol "mm0:data-eq", .var "conclusion", .var "left"],
      .expression [.symbol "mm0:proof-conversion-matched", .var "equal", .var "right"]] := by decide
private theorem premises_clause (actual : Option (List Preterm)) (premises : List Preterm) (conclusion : Preterm) :
    clauses program "mm0:proof-premises" [ListSubstitution.resultValue actual, expressionsValue premises, Data.preterm conclusion] =
      [.evaluate (premisesEnvironment actual premises conclusion) premisesEquation.body] := by
  rw [clauses_use_only_the_named_equations, premises_unique]
  simp [premises_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, premisesEnvironment]
private theorem matched_clause (answer : Bool) (conclusion : Preterm) :
    clauses program "mm0:proof-matched" [boolean answer, Data.preterm conclusion] =
      [.evaluate (matchedEnvironment answer conclusion) matchedEquation.body] := by
  rw [clauses_use_only_the_named_equations, matched_unique]
  simp [matched_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, matchedEnvironment]
private theorem left_clause (actual : Option Preterm) (left right : Preterm) :
    clauses program "mm0:proof-left" [resultValue actual, Data.preterm left, Data.preterm right] =
      [.evaluate (leftEnvironment actual left right) leftEquation.body] := by
  rw [clauses_use_only_the_named_equations, left_unique]
  simp [left_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, leftEnvironment]
private theorem conversion_matched_clause (answer : Bool) (right : Preterm) :
    clauses program "mm0:proof-conversion-matched" [boolean answer, Data.preterm right] =
      [.evaluate (conversionMatchedEnvironment answer right) conversionMatchedEquation.body] := by
  rw [clauses_use_only_the_named_equations, conversion_matched_unique]
  simp [conversion_matched_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, conversionMatchedEnvironment]
private theorem tail_clause (rest : Option (List Preterm)) (first : Preterm) :
    clauses program "mm0:proof-tail" [ListSubstitution.resultValue rest, Data.preterm first] =
      [.evaluate (tailEnvironment rest first) tailEquation.body] := by
  rw [clauses_use_only_the_named_equations, tail_unique]
  simp [tail_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailEnvironment]

private def optionCases (name : String) : SpaceSemantics.Cases :=
  [(boolean false, .symbol "None"), (boolean true, .expression [.symbol "Some", .var name]), (.var "mm0Malformed", .symbol "MM0:Malformed")]

private theorem option_case_returns (bindings : Subst) (state : State) (answer : Bool) (value : Preterm) (name : String)
    (capturedAnswer : applySubst bindings (.var "conditionInput") = boolean answer)
    (capturedValue : applySubst bindings (.var name) = Data.preterm value) :
    PureReturns program bindings state
      (.expression [.symbol "case", .var "conditionInput", .expression ((optionCases name).map fun e => .expression [e.1,e.2])]) state
      (resultValue (if answer then some value else none)) := by
  cases answer with
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None") _ _ (optionCases name) (read_cases_encoded _)
      · simpa only [capturedAnswer] using variable_returns program bindings state "conditionInput"
      · simp [optionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) (.expression [.symbol "Some", .var name]) _ _ (optionCases name) (read_cases_encoded _)
      · simpa only [capturedAnswer] using variable_returns program bindings state "conditionInput"
      · simp [optionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · simpa [resultValue, optionValue, capturedValue] using unary_constructor_returns program bindings state "Some" name (by decide +kernel) (by decide)

private theorem matched_body_returns (state : State) (answer : Bool) (conclusion : Preterm) :
    PureReturns program (matchedEnvironment answer conclusion) state matchedEquation.body state (resultValue (if answer then some conclusion else none)) := by
  have shape : matchedEquation.body = .expression [.symbol "case", .var "conditionInput", .expression ((optionCases "conclusion").map fun e => .expression [e.1,e.2])] := by decide
  rw [shape]
  exact option_case_returns _ state answer conclusion "conclusion" rfl rfl

private theorem matched_captured_returns (bindings : Subst) (state : State) (answer : Bool) (conclusion : Preterm) (answerName conclusionName : String)
    (capturedAnswer : applySubst bindings (.var answerName) = boolean answer) (capturedConclusion : applySubst bindings (.var conclusionName) = Data.preterm conclusion) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof-matched", .var answerName, .var conclusionName]) state
      (resultValue (if answer then some conclusion else none)) := by
  apply authored_variable_call_returns program bindings (matchedEnvironment answer conclusion) state state "mm0:proof-matched" [answerName, conclusionName]
    matchedEquation.body _ (by decide) (by decide) (by decide) _ (matched_body_returns state answer conclusion) (by decide)
  simpa [capturedAnswer, capturedConclusion] using matched_clause answer conclusion

private theorem conversion_matched_body_returns (state : State) (answer : Bool) (right : Preterm) :
    PureReturns program (conversionMatchedEnvironment answer right) state conversionMatchedEquation.body state (resultValue (if answer then some right else none)) := by
  have shape : conversionMatchedEquation.body = .expression [.symbol "case", .var "conditionInput", .expression ((optionCases "right").map fun e => .expression [e.1,e.2])] := by decide
  rw [shape]
  exact option_case_returns _ state answer right "right" rfl rfl

private theorem conversion_matched_captured_returns (bindings : Subst) (state : State) (answer : Bool) (right : Preterm) (answerName rightName : String)
    (capturedAnswer : applySubst bindings (.var answerName) = boolean answer) (capturedRight : applySubst bindings (.var rightName) = Data.preterm right) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof-conversion-matched", .var answerName, .var rightName]) state
      (resultValue (if answer then some right else none)) := by
  apply authored_variable_call_returns program bindings (conversionMatchedEnvironment answer right) state state "mm0:proof-conversion-matched" [answerName, rightName]
    conversionMatchedEquation.body _ (by decide) (by decide) (by decide) _ (conversion_matched_body_returns state answer right) (by decide)
  simpa [capturedAnswer, capturedRight] using conversion_matched_clause answer right

theorem premises_body_returns (state : State) (actual : Option (List Preterm)) (premises : List Preterm) (conclusion : Preterm) :
    PureReturns program (premisesEnvironment actual premises conclusion) state premisesEquation.body state
      (resultValue (actual.bind fun actual => if actual = premises then some conclusion else none)) := by
  rw [premises_body_shape]
  cases actual with
  | none =>
      let bindings := premisesEnvironment none premises conclusion
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ premisesCases (read_cases_encoded _)
      · simpa [bindings, premisesEnvironment, ListSubstitution.resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [premises_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some actual =>
      let bindings := premisesEnvironment (some actual) premises conclusion
      let bound := ("actual", expressionsValue actual) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (ListSubstitution.resultValue (some actual)) premisesBody _ _ premisesCases (read_cases_encoded _)
      · simpa [bindings, premisesEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [premises_cases_shape, ListSubstitution.resultValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, bound, bindings, premisesEnvironment, Subst.lookup]
      · rw [premises_some_shape]
        let withEqual := ("equal", boolean (decide (actual = premises))) :: bound
        apply let_returns program bound withEqual state state state (.var "equal") _ _ (boolean (decide (actual = premises))) _
        · simpa [expressionsValue, ListAccess.listValue, List.map_injective_iff.mpr Data.preterm_injective |>.eq_iff] using
            Scalar.data_equality_captured_returns bound state (expressionsValue actual) (expressionsValue premises) "actual" "premises" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, withEqual, bound, bindings, premisesEnvironment, Subst.lookup]
        · simpa only [Option.bind_some, Bool.decide_coe, decide_eq_true_eq] using matched_captured_returns withEqual state (decide (actual = premises)) conclusion "equal" "conclusion" rfl rfl

theorem left_body_returns (state : State) (actual : Option Preterm) (left right : Preterm) :
    PureReturns program (leftEnvironment actual left right) state leftEquation.body state
      (resultValue (actual.bind fun conclusion => if conclusion = left then some right else none)) := by
  rw [left_body_shape]
  cases actual with
  | none =>
      let bindings := leftEnvironment none left right
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ leftCases (read_cases_encoded _)
      · simpa [bindings, leftEnvironment, resultValue, optionValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [left_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some actual =>
      let bindings := leftEnvironment (some actual) left right
      let bound := ("conclusion", Data.preterm actual) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some actual)) leftBody _ _ leftCases (read_cases_encoded _)
      · simpa [bindings, leftEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [left_cases_shape, resultValue, optionValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, bound, bindings, leftEnvironment, Subst.lookup]
      · rw [left_some_shape]
        let withEqual := ("equal", boolean (decide (actual = left))) :: bound
        apply let_returns program bound withEqual state state state (.var "equal") _ _ (boolean (decide (actual = left))) _
        · simpa only [Data.preterm_injective.eq_iff] using Scalar.data_equality_captured_returns bound state (Data.preterm actual) (Data.preterm left) "conclusion" "left" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, withEqual, bound, bindings, leftEnvironment, Subst.lookup]
        · simpa only [Option.bind_some, Bool.decide_coe, decide_eq_true_eq] using conversion_matched_captured_returns withEqual state (decide (actual = left)) right "equal" "right" rfl rfl

theorem premises_captured_returns (bindings : Subst) (state : State) (actual : Option (List Preterm)) (premises : List Preterm) (conclusion : Preterm)
    (actualName premisesName conclusionName : String)
    (capturedActual : applySubst bindings (.var actualName) = ListSubstitution.resultValue actual)
    (capturedPremises : applySubst bindings (.var premisesName) = expressionsValue premises)
    (capturedConclusion : applySubst bindings (.var conclusionName) = Data.preterm conclusion) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof-premises", .var actualName, .var premisesName, .var conclusionName]) state
      (resultValue (actual.bind fun actual => if actual = premises then some conclusion else none)) := by
  apply authored_variable_call_returns program bindings (premisesEnvironment actual premises conclusion) state state "mm0:proof-premises" [actualName, premisesName, conclusionName]
    premisesEquation.body _ (by decide) (by decide) (by decide) _ (premises_body_returns state actual premises conclusion) (by decide)
  simpa [capturedActual, capturedPremises, capturedConclusion] using premises_clause actual premises conclusion

theorem left_captured_returns (bindings : Subst) (state : State) (actual : Option Preterm) (left right : Preterm)
    (actualName leftName rightName : String)
    (capturedActual : applySubst bindings (.var actualName) = resultValue actual)
    (capturedLeft : applySubst bindings (.var leftName) = Data.preterm left)
    (capturedRight : applySubst bindings (.var rightName) = Data.preterm right) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof-left", .var actualName, .var leftName, .var rightName]) state
      (resultValue (actual.bind fun conclusion => if conclusion = left then some right else none)) := by
  apply authored_variable_call_returns program bindings (leftEnvironment actual left right) state state "mm0:proof-left" [actualName, leftName, rightName]
    leftEquation.body _ (by decide) (by decide) (by decide) _ (left_body_returns state actual left right) (by decide)
  simpa [capturedActual, capturedLeft, capturedRight] using left_clause actual left right

/-- The retained proof-tail body is the already verified list-substitution tail
body. Reuse that source execution proof, rather than authoring another traversal. -/
theorem tail_captured_returns (bindings : Subst) (state : State) (rest : Option (List Preterm)) (first : Preterm) (restName firstName : String)
    (capturedRest : applySubst bindings (.var restName) = ListSubstitution.resultValue rest)
    (capturedFirst : applySubst bindings (.var firstName) = Data.preterm first) :
    PureReturns program bindings state (.expression [.symbol "mm0:proof-tail", .var restName, .var firstName]) state
      (ListSubstitution.resultValue (rest.map (first :: ·))) := by
  apply authored_variable_call_returns program bindings (tailEnvironment rest first) state state "mm0:proof-tail" [restName, firstName]
    tailEquation.body _ (by decide) (by decide) (by decide) _
    (ListSubstitution.tail_body_returns state rest first) (by decide)
  simpa [capturedRest, capturedFirst] using tail_clause rest first

end Mettapedia.Languages.MM0.MeTTa.ProofResults
