import Mettapedia.Languages.MM0.MeTTa.Kernel.Inference
import Mettapedia.Languages.MM0.MeTTa.Data.Scalar
import Mettapedia.Languages.MM0.MeTTa.Kernel.Application
import Mettapedia.Languages.MM0.MeTTa.Kernel.ListSubstitution
import Mettapedia.Languages.MM0.Kernel.Conversion

/-!
# Endpoint and sort checks in retained MM0 conversion code

Conversion witnesses compute typed endpoints. The retained helper functions
refuse unsaturated reflexivity and a transitivity join whose actual middle
expression or sort differs. These proofs concern the quoted source functions;
the recursive witness and definition-unfolding paths are separate components.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.ConversionResults

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm ConversionResult ExpressionType)
open Store (natural)
open ListAccess (listValue viewValue)

def resultValue : Option ConversionResult → Atom
  | none => .symbol "None"
  | some value => .expression [.symbol "MM0:Converted", Data.preterm value.left, Data.preterm value.right, natural value.sort]

def argumentsResultValue : Option (List Preterm × List Preterm) → Atom
  | none => .symbol "None"
  | some values => .expression [.symbol "MM0:ConvertedArgs", ListSubstitution.expressionsValue values.1, ListSubstitution.expressionsValue values.2]

theorem resultValue_injective : Function.Injective resultValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [resultValue]
  | some first =>
      cases second with
      | none => simp [resultValue] at same
      | some second =>
          have parts : Data.preterm first.left = Data.preterm second.left ∧
              Data.preterm first.right = Data.preterm second.right ∧ natural first.sort = natural second.sort := by
            simpa [resultValue] using same
          have left := Data.preterm_injective parts.1
          have right := Data.preterm_injective parts.2.1
          have sort := Data.natural_injective parts.2.2
          exact congrArg some (by cases first; cases second; simp_all)

theorem argumentsResultValue_injective : Function.Injective argumentsResultValue := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [argumentsResultValue]
  | some first =>
      cases second with
      | none => simp [argumentsResultValue] at same
      | some second =>
          have parts : ListSubstitution.expressionsValue first.1 = ListSubstitution.expressionsValue second.1 ∧
              ListSubstitution.expressionsValue first.2 = ListSubstitution.expressionsValue second.2 := by
            simpa [argumentsResultValue] using same
          have left : first.1 = second.1 := (List.map_injective_iff.mpr Data.preterm_injective)
            (by simpa [ListSubstitution.expressionsValue, listValue] using parts.1)
          have right : first.2 = second.2 := (List.map_injective_iff.mpr Data.preterm_injective)
            (by simpa [ListSubstitution.expressionsValue, listValue] using parts.2)
          exact congrArg some (Prod.ext left right)

private def congruentEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 27)[26]'(by decide)
private def typedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 30)[29]'(by decide)
private def tailEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 36)[35]'(by decide)
private def congruentEnvironment (result : Option (List Preterm × List Preterm)) (symbol sort : Nat) : Subst :=
  [("sort", natural sort), ("symbol", natural symbol), ("valueInput", argumentsResultValue result)]
private def typedEnvironment (answer : Bool) (symbol : Nat) (arguments : List Preterm) (result : Preterm) (sort : Nat) : Subst :=
  [("sort", natural sort), ("result", Data.preterm result), ("arguments", ListSubstitution.expressionsValue arguments),
    ("symbol", natural symbol), ("conditionInput", boolean answer)]
private def tailEnvironment (result : Option (List Preterm × List Preterm)) (left right : Preterm) : Subst :=
  [("right", Data.preterm right), ("left", Data.preterm left), ("valueInput", argumentsResultValue result)]

private def reflEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 20)[19]'(by decide)
private def saturatedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 21)[20]'(by decide)
private def swapEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 22)[21]'(by decide)
private def joinEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 24)[23]'(by decide)
private def joinedEquation : SpaceSemantics.Equation := (kernelSource.program.equations.take 25)[24]'(by decide)
private def reflEnvironment (type : Option ExpressionType) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("valueInput", Data.inferred type)]
private def saturatedEnvironment (remaining : Context) (expression : Preterm) (sort : Nat) : Subst :=
  [("sort", natural sort), ("expression", Data.preterm expression), ("valueInput", viewValue (remaining.map Data.binder))]
private def swapEnvironment (result : Option ConversionResult) : Subst := [("valueInput", resultValue result)]
private def joinEnvironment (first : ConversionResult) (second : Option ConversionResult) : Subst :=
  [("valueInput", resultValue second), ("sort", natural first.sort), ("middle", Data.preterm first.right), ("left", Data.preterm first.left)]
private def joinedEnvironment (answer : Bool) (left right : Preterm) (sort : Nat) : Subst :=
  [("sort", natural sort), ("right", Data.preterm right), ("left", Data.preterm left), ("conditionInput", boolean answer)]
private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def reflCases := sourceCases reflEquation.body
private def saturatedCases := sourceCases saturatedEquation.body
private def swapCases := sourceCases swapEquation.body
private def joinCases := sourceCases joinEquation.body
private def joinedCases := sourceCases joinedEquation.body
private def congruentCases := sourceCases congruentEquation.body
private def typedCases := sourceCases typedEquation.body
private def tailCases := sourceCases tailEquation.body
private def congruentBody : Atom := (congruentCases[1]'(by decide)).2
private def typedBody : Atom := (typedCases[0]'(by decide)).2
private def tailBody : Atom := (tailCases[1]'(by decide)).2
private def inferredBody : Atom := (reflCases[1]'(by decide)).2
private def secondBody : Atom := (joinCases[1]'(by decide)).2
private theorem refl_unique : program.equations.filter (fun e => e.head == "mm0:conversion-refl-type") = [reflEquation] := by decide
private theorem saturated_unique : program.equations.filter (fun e => e.head == "mm0:conversion-refl-saturated") = [saturatedEquation] := by decide
private theorem swap_unique : program.equations.filter (fun e => e.head == "mm0:conversion-swap") = [swapEquation] := by decide
private theorem join_unique : program.equations.filter (fun e => e.head == "mm0:conversion-join") = [joinEquation] := by decide
private theorem joined_unique : program.equations.filter (fun e => e.head == "mm0:conversion-joined") = [joinedEquation] := by decide
private theorem refl_formals : reflEquation.arguments = [.var "valueInput", .var "expression"] := by decide
private theorem saturated_formals : saturatedEquation.arguments = [.var "valueInput", .var "expression", .var "sort"] := by decide
private theorem swap_formals : swapEquation.arguments = [.var "valueInput"] := by decide
private theorem join_formals : joinEquation.arguments = [.var "left", .var "middle", .var "sort", .var "valueInput"] := by decide
private theorem joined_formals : joinedEquation.arguments = [.var "conditionInput", .var "left", .var "right", .var "sort"] := by decide
private theorem refl_body_shape : reflEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (reflCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem refl_cases_shape : reflCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Inferred", .var "remaining", .var "sort"], inferredBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem inferred_body_shape : inferredBody =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "remaining"],
      .expression [.symbol "mm0:conversion-refl-saturated", .var "view", .var "expression", .var "sort"]] := by decide
private theorem saturated_body_shape : saturatedEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (saturatedCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem saturated_cases_shape : saturatedCases = [(.symbol "List:Nil", .expression [.symbol "MM0:Converted", .var "expression", .var "expression", .var "sort"]),
    (.expression [.symbol "List:Cons", .var "first", .var "rest"], .symbol "None"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem swap_body_shape : swapEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput"], .expression (swapCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem swap_cases_shape : swapCases = [(.expression [.symbol "None"], .symbol "None"),
    (.expression [.expression [.symbol "MM0:Converted", .var "left", .var "right", .var "sort"]],
      .expression [.symbol "MM0:Converted", .var "right", .var "left", .var "sort"]), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem joined_body_shape : joinedEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (joinedCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem joined_cases_shape : joinedCases = [(boolean true, .expression [.symbol "MM0:Converted", .var "left", .var "right", .var "sort"]),
    (boolean false, .symbol "None"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem join_body_shape : joinEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (joinCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem join_cases_shape : joinCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:Converted", .var "start", .var "right", .var "other-sort"], secondBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem second_body_shape : secondBody =
    .expression [.symbol "let", .var "equal", .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression [.var "middle", .var "sort"]],
      .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression [.var "start", .var "other-sort"]],
        .expression [.symbol "mm0:data-eq", .var "items", .var "items2"]]],
      .expression [.symbol "mm0:conversion-joined", .var "equal", .var "left", .var "right", .var "sort"]] := by decide
private theorem refl_clause (type : Option ExpressionType) (expression : Preterm) :
    clauses program "mm0:conversion-refl-type" [Data.inferred type, Data.preterm expression] =
      [.evaluate (reflEnvironment type expression) reflEquation.body] := by
  rw [clauses_use_only_the_named_equations, refl_unique]
  simp [refl_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, reflEnvironment]
private theorem saturated_clause (remaining : Context) (expression : Preterm) (sort : Nat) :
    clauses program "mm0:conversion-refl-saturated" [viewValue (remaining.map Data.binder), Data.preterm expression, natural sort] =
      [.evaluate (saturatedEnvironment remaining expression sort) saturatedEquation.body] := by
  rw [clauses_use_only_the_named_equations, saturated_unique]
  simp [saturated_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, saturatedEnvironment]
private theorem swap_clause (result : Option ConversionResult) :
    clauses program "mm0:conversion-swap" [resultValue result] = [.evaluate (swapEnvironment result) swapEquation.body] := by
  rw [clauses_use_only_the_named_equations, swap_unique]
  simp [swap_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, swapEnvironment]
private theorem joined_clause (answer : Bool) (left right : Preterm) (sort : Nat) :
    clauses program "mm0:conversion-joined" [boolean answer, Data.preterm left, Data.preterm right, natural sort] =
      [.evaluate (joinedEnvironment answer left right sort) joinedEquation.body] := by
  rw [clauses_use_only_the_named_equations, joined_unique]
  simp [joined_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, joinedEnvironment]
private theorem join_clause (first : ConversionResult) (second : Option ConversionResult) :
    clauses program "mm0:conversion-join" [Data.preterm first.left, Data.preterm first.right, natural first.sort, resultValue second] =
      [.evaluate (joinEnvironment first second) joinEquation.body] := by
  rw [clauses_use_only_the_named_equations, join_unique]
  simp [join_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, joinEnvironment]

private theorem saturated_body_returns (state : State) (remaining : Context) (expression : Preterm) (sort : Nat) :
    PureReturns program (saturatedEnvironment remaining expression sort) state saturatedEquation.body state
      (resultValue (if remaining = [] then some ⟨expression, expression, sort⟩ else none)) := by
  rw [saturated_body_shape]
  cases remaining with
  | nil =>
      let bindings := saturatedEnvironment [] expression sort
      apply case_returns program bindings bindings state state state (.var "valueInput") (viewValue [])
        (.expression [.symbol "MM0:Converted", .var "expression", .var "expression", .var "sort"]) _ _ saturatedCases (read_cases_encoded saturatedCases)
      · simpa [bindings, saturatedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [saturated_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
      · simpa [resultValue, bindings, saturatedEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program bindings state "MM0:Converted" ["expression", "expression", "sort"] (by decide +kernel) (by decide)
  | cons first rest =>
      let bindings := saturatedEnvironment (first :: rest) expression sort
      let bound := ("rest", Data.context rest) :: ("first", Data.binder first) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (viewValue ((first :: rest).map Data.binder))
        (.symbol "None") _ _ saturatedCases (read_cases_encoded saturatedCases)
      · simpa [bindings, saturatedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [saturated_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, viewValue, Data.context, bound, bindings, saturatedEnvironment, Subst.lookup]
      · exact symbol_returns program bound state "None"

theorem reflexivity_body_returns (state : State) (type : Option ExpressionType) (expression : Preterm) :
    PureReturns program (reflEnvironment type expression) state reflEquation.body state
      (resultValue (type.bind fun type => if type.1 = [] then some ⟨expression, expression, type.2⟩ else none)) := by
  rw [refl_body_shape]
  cases type with
  | none =>
      let bindings := reflEnvironment none expression
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ reflCases (read_cases_encoded reflCases)
      · simpa [bindings, reflEnvironment, Data.inferred, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [refl_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some type =>
      rcases type with ⟨remaining, sort⟩
      let bindings := reflEnvironment (some (remaining, sort)) expression
      let bound := ("sort", natural sort) :: ("remaining", Data.context remaining) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (Data.inferred (some (remaining, sort))) inferredBody
        _ _ reflCases (read_cases_encoded reflCases)
      · simpa [bindings, reflEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [refl_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Data.inferred, bound, bindings, reflEnvironment, Subst.lookup]
      · rw [inferred_body_shape]
        let viewed := ("view", viewValue (remaining.map Data.binder)) :: bound
        apply let_returns program bound viewed state state state (.var "view") _ _ (viewValue (remaining.map Data.binder)) _
        · exact ListAccess.view_captured_returns bound state "remaining" (remaining.map Data.binder) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bound, bindings, reflEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program viewed (saturatedEnvironment remaining expression sort) state state
            "mm0:conversion-refl-saturated" ["view", "expression", "sort"] saturatedEquation.body _
            (by decide) (by decide) (by decide) _ (saturated_body_returns state remaining expression sort) (by decide)
          simpa [viewed, bound, bindings, reflEnvironment, applySubst, Subst.lookup] using saturated_clause remaining expression sort

theorem reflexivity_captured_returns (bindings : Subst) (state : State) (type : Option ExpressionType) (expression : Preterm)
    (typeName expressionName : String)
    (capturedType : applySubst bindings (.var typeName) = Data.inferred type)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-refl-type", .var typeName, .var expressionName]) state
      (resultValue (type.bind fun type => if type.1 = [] then some ⟨expression, expression, type.2⟩ else none)) := by
  apply authored_variable_call_returns program bindings (reflEnvironment type expression) state state
    "mm0:conversion-refl-type" [typeName, expressionName] reflEquation.body _
    (by decide) (by decide) (by decide) _ (reflexivity_body_returns state type expression) (by decide)
  simpa [capturedType, capturedExpression] using refl_clause type expression

theorem swap_body_returns (state : State) (result : Option ConversionResult) :
    PureReturns program (swapEnvironment result) state swapEquation.body state
      (resultValue (result.map fun value => ⟨value.right, value.left, value.sort⟩)) := by
  rw [swap_body_shape]
  cases result with
  | none =>
      let bindings := swapEnvironment none
      apply case_returns program bindings bindings state state state (.expression [.var "valueInput"]) (.expression [.symbol "None"]) (.symbol "None")
        _ _ swapCases (read_cases_encoded swapCases)
      · simpa [bindings, swapEnvironment, resultValue, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [swap_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some result =>
      let bindings := swapEnvironment (some result)
      let bound := ("sort", natural result.sort) :: ("right", Data.preterm result.right) :: ("left", Data.preterm result.left) :: bindings
      apply case_returns program bindings bound state state state (.expression [.var "valueInput"]) (.expression [resultValue (some result)])
        (.expression [.symbol "MM0:Converted", .var "right", .var "left", .var "sort"]) _ _ swapCases (read_cases_encoded swapCases)
      · simpa [bindings, swapEnvironment, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [swap_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, resultValue, bound, bindings, swapEnvironment, Subst.lookup]
      · simpa [resultValue, bound, bindings, swapEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program bound state "MM0:Converted" ["right", "left", "sort"] (by decide +kernel) (by decide)

theorem swap_captured_returns (bindings : Subst) (state : State) (result : Option ConversionResult) (name : String)
    (captured : applySubst bindings (.var name) = resultValue result) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-swap", .var name]) state
      (resultValue (result.map fun value => ⟨value.right, value.left, value.sort⟩)) := by
  apply authored_variable_call_returns program bindings (swapEnvironment result) state state
    "mm0:conversion-swap" [name] swapEquation.body _ (by decide) (by decide) (by decide) _ (swap_body_returns state result) (by decide)
  simpa [captured] using swap_clause result

private theorem joined_body_returns (state : State) (answer : Bool) (left right : Preterm) (sort : Nat) :
    PureReturns program (joinedEnvironment answer left right sort) state joinedEquation.body state
      (resultValue (if answer then some ⟨left, right, sort⟩ else none)) := by
  rw [joined_body_shape]
  cases answer with
  | false =>
      let bindings := joinedEnvironment false left right sort
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None")
        _ _ joinedCases (read_cases_encoded joinedCases)
      · simpa [bindings, joinedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [joined_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      let bindings := joinedEnvironment true left right sort
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        (.expression [.symbol "MM0:Converted", .var "left", .var "right", .var "sort"]) _ _ joinedCases (read_cases_encoded joinedCases)
      · simpa [bindings, joinedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [joined_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · simpa [resultValue, bindings, joinedEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program bindings state "MM0:Converted" ["left", "right", "sort"] (by decide +kernel) (by decide)

theorem join_body_returns (state : State) (first : ConversionResult) (second : Option ConversionResult) :
    PureReturns program (joinEnvironment first second) state joinEquation.body state
      (resultValue (second.bind fun second => if first.right = second.left ∧ first.sort = second.sort then
        some ⟨first.left, second.right, first.sort⟩ else none)) := by
  rw [join_body_shape]
  cases second with
  | none =>
      let bindings := joinEnvironment first none
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None")
        _ _ joinCases (read_cases_encoded joinCases)
      · simpa [bindings, joinEnvironment, resultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [join_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some second =>
      let bindings := joinEnvironment first (some second)
      let bound := ("other-sort", natural second.sort) :: ("right", Data.preterm second.right) :: ("start", Data.preterm second.left) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some second)) secondBody
        _ _ joinCases (read_cases_encoded joinCases)
      · simpa [bindings, joinEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [join_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, resultValue, bound, bindings, joinEnvironment, Subst.lookup]
      · rw [second_body_shape]
        let answer := decide (first.right = second.left ∧ first.sort = second.sort)
        let tested := ("equal", boolean answer) :: bound
        apply let_returns program bound tested state state state (.var "equal") _ _ (boolean answer) _
        · let firstValue := listValue [Data.preterm first.right, natural first.sort]
          let secondValue := listValue [Data.preterm second.left, natural second.sort]
          let withFirst := ("items", firstValue) :: bound
          let withBoth := ("items2", secondValue) :: withFirst
          apply let_returns program bound withFirst state state state (.var "items") _ _ firstValue _
          · apply unary_constructor_of_returns program bound state state "MM0:L" _ _ (by decide +kernel) (by decide)
            simpa [firstValue, listValue, bound, bindings, joinEnvironment, applySubst, Subst.lookup] using
              tuple_variables_return program bound state ["middle", "sort"]
          · simp [SpaceSemantics.matchValue, matchAtom, withFirst, bound, bindings, joinEnvironment, Subst.lookup]
          · apply let_returns program withFirst withBoth state state state (.var "items2") _ _ secondValue _
            · apply unary_constructor_of_returns program withFirst state state "MM0:L" _ _ (by decide +kernel) (by decide)
              simpa [secondValue, listValue, withFirst, bound, bindings, joinEnvironment, applySubst, Subst.lookup] using
                tuple_variables_return program withFirst state ["start", "other-sort"]
            · simp [SpaceSemantics.matchValue, matchAtom, withBoth, withFirst, bound, bindings, joinEnvironment, Subst.lookup]
            · simpa [firstValue, secondValue, listValue, answer, Data.preterm_injective.eq_iff, Data.natural_injective.eq_iff] using
                Scalar.data_equality_captured_returns withBoth state firstValue secondValue "items" "items2" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, tested, bound, bindings, joinEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program tested (joinedEnvironment answer first.left second.right first.sort) state state
            "mm0:conversion-joined" ["equal", "left", "right", "sort"] joinedEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [tested, bound, bindings, joinEnvironment, applySubst, Subst.lookup] using joined_clause answer first.left second.right first.sort
          · simpa [answer] using joined_body_returns state answer first.left second.right first.sort

theorem join_captured_returns (bindings : Subst) (state : State) (first : ConversionResult) (second : Option ConversionResult)
    (leftName middleName sortName secondName : String)
    (capturedLeft : applySubst bindings (.var leftName) = Data.preterm first.left)
    (capturedMiddle : applySubst bindings (.var middleName) = Data.preterm first.right)
    (capturedSort : applySubst bindings (.var sortName) = natural first.sort)
    (capturedSecond : applySubst bindings (.var secondName) = resultValue second) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-join", .var leftName, .var middleName, .var sortName, .var secondName]) state
      (resultValue (second.bind fun second => if first.right = second.left ∧ first.sort = second.sort then
        some ⟨first.left, second.right, first.sort⟩ else none)) := by
  apply authored_variable_call_returns program bindings (joinEnvironment first second) state state
    "mm0:conversion-join" [leftName, middleName, sortName, secondName] joinEquation.body _
    (by decide) (by decide) (by decide) _ (join_body_returns state first second) (by decide)
  simpa [capturedLeft, capturedMiddle, capturedSort, capturedSecond] using join_clause first second

private theorem congruent_unique : program.equations.filter (fun e => e.head == "mm0:conversion-congruent") = [congruentEquation] := by decide
private theorem typed_unique : program.equations.filter (fun e => e.head == "mm0:conversion-unfold-typed") = [typedEquation] := by decide
private theorem tail_unique : program.equations.filter (fun e => e.head == "mm0:conversion-argument-tail") = [tailEquation] := by decide
private theorem congruent_formals : congruentEquation.arguments = [.var "valueInput", .var "symbol", .var "sort"] := by decide
private theorem typed_formals : typedEquation.arguments = [.var "conditionInput", .var "symbol", .var "arguments", .var "result", .var "sort"] := by decide
private theorem tail_formals : tailEquation.arguments = [.var "valueInput", .var "left", .var "right"] := by decide
private theorem congruent_body_shape : congruentEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (congruentCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem congruent_cases_shape : congruentCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:ConvertedArgs", .var "left", .var "right"], congruentBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem congruent_some_shape : congruentBody =
    .expression [.symbol "let", .var "applyArgsResult", .expression [.symbol "let", .var "term", .expression [.symbol "MM0:Term", .var "symbol"],
      .expression [.symbol "mm0:apply-args", .var "term", .var "left"]],
      .expression [.symbol "let", .var "applyArgsResult2", .expression [.symbol "let", .var "term2", .expression [.symbol "MM0:Term", .var "symbol"],
        .expression [.symbol "mm0:apply-args", .var "term2", .var "right"]],
        .expression [.symbol "MM0:Converted", .var "applyArgsResult", .var "applyArgsResult2", .var "sort"]]] := by decide
private theorem typed_body_shape : typedEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (typedCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem typed_cases_shape : typedCases = [(boolean true, typedBody), (boolean false, .symbol "None"), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem typed_true_shape : typedBody =
    .expression [.symbol "let", .var "applyArgsResult", .expression [.symbol "let", .var "term", .expression [.symbol "MM0:Term", .var "symbol"],
      .expression [.symbol "mm0:apply-args", .var "term", .var "arguments"]],
      .expression [.symbol "MM0:Converted", .var "applyArgsResult", .var "result", .var "sort"]] := by decide
private theorem tail_body_shape : tailEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (tailCases.map fun e => .expression [e.1,e.2])] := by decide
private theorem tail_cases_shape : tailCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "MM0:ConvertedArgs", .var "lefts", .var "rights"], tailBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem tail_some_shape : tailBody =
    .expression [.symbol "let", .var "extended", .expression [.symbol "mm0:list-cons", .var "left", .var "lefts"],
      .expression [.symbol "let", .var "extended2", .expression [.symbol "mm0:list-cons", .var "right", .var "rights"],
        .expression [.symbol "MM0:ConvertedArgs", .var "extended", .var "extended2"]]] := by decide
private theorem congruent_clause (result : Option (List Preterm × List Preterm)) (symbol sort : Nat) :
    clauses program "mm0:conversion-congruent" [argumentsResultValue result, natural symbol, natural sort] =
      [.evaluate (congruentEnvironment result symbol sort) congruentEquation.body] := by
  rw [clauses_use_only_the_named_equations, congruent_unique]
  simp [congruent_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, congruentEnvironment]
private theorem typed_clause (answer : Bool) (symbol : Nat) (arguments : List Preterm) (result : Preterm) (sort : Nat) :
    clauses program "mm0:conversion-unfold-typed" [boolean answer, natural symbol, ListSubstitution.expressionsValue arguments, Data.preterm result, natural sort] =
      [.evaluate (typedEnvironment answer symbol arguments result sort) typedEquation.body] := by
  rw [clauses_use_only_the_named_equations, typed_unique]
  simp [typed_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, typedEnvironment]
private theorem tail_clause (result : Option (List Preterm × List Preterm)) (left right : Preterm) :
    clauses program "mm0:conversion-argument-tail" [argumentsResultValue result, Data.preterm left, Data.preterm right] =
      [.evaluate (tailEnvironment result left right) tailEquation.body] := by
  rw [clauses_use_only_the_named_equations, tail_unique]
  simp [tail_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailEnvironment]

private theorem applied_term_returns (bindings : Subst) (state : State) (symbol : Nat) (arguments : List Preterm)
    (termName argumentsName : String)
    (capturedSymbol : applySubst bindings (.var "symbol") = natural symbol)
    (fresh : Subst.lookup bindings termName = none)
    (capturedArguments : applySubst bindings (.var argumentsName) = ListSubstitution.expressionsValue arguments) :
    PureReturns program bindings state
      (.expression [.symbol "let", .var termName, .expression [.symbol "MM0:Term", .var "symbol"],
        .expression [.symbol "mm0:apply-args", .var termName, .var argumentsName]]) state
      (Data.preterm (Preterm.applyArgs (.term symbol) arguments)) := by
  let withTerm := (termName, Data.preterm (.term symbol)) :: bindings
  apply let_returns program bindings withTerm state state state (.var termName) _ _ (Data.preterm (.term symbol)) _
  · simpa [Data.preterm, capturedSymbol] using
      unary_constructor_returns program bindings state "MM0:Term" "symbol" (by decide +kernel) (by decide)
  · simp [SpaceSemantics.matchValue, matchAtom, withTerm, fresh]
  · apply Application.captured_returns withTerm state (.term symbol) arguments termName argumentsName
    · simp [withTerm, applySubst, Subst.lookup]
    · by_cases same : termName = argumentsName
      · subst argumentsName
        simp only [applySubst, fresh, Option.getD_none] at capturedArguments
        cases capturedArguments
      · simpa [withTerm, applySubst, Subst.lookup, same, ListSubstitution.expressionsValue] using capturedArguments

theorem congruent_body_returns (state : State) (result : Option (List Preterm × List Preterm)) (symbol sort : Nat) :
    PureReturns program (congruentEnvironment result symbol sort) state congruentEquation.body state
      (resultValue (result.map fun values => ⟨Preterm.applyArgs (.term symbol) values.1, Preterm.applyArgs (.term symbol) values.2, sort⟩)) := by
  rw [congruent_body_shape]
  cases result with
  | none =>
      let bindings := congruentEnvironment none symbol sort
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ congruentCases (read_cases_encoded congruentCases)
      · simpa [bindings, congruentEnvironment, argumentsResultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [congruent_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some values =>
      let bindings := congruentEnvironment (some values) symbol sort
      let bound := ("right", ListSubstitution.expressionsValue values.2) :: ("left", ListSubstitution.expressionsValue values.1) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (argumentsResultValue (some values)) congruentBody _ _ congruentCases (read_cases_encoded congruentCases)
      · simpa [bindings, congruentEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [congruent_cases_shape, argumentsResultValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, bound, bindings, congruentEnvironment, Subst.lookup]
      · rw [congruent_some_shape]
        let left := Preterm.applyArgs (.term symbol) values.1
        let right := Preterm.applyArgs (.term symbol) values.2
        let withLeft := ("applyArgsResult", Data.preterm left) :: bound
        let withRight := ("applyArgsResult2", Data.preterm right) :: withLeft
        apply let_returns program bound withLeft state state state (.var "applyArgsResult") _ _ (Data.preterm left) _
        · exact applied_term_returns bound state symbol values.1 "term" "left" rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, withLeft, bound, bindings, congruentEnvironment, Subst.lookup]
        · apply let_returns program withLeft withRight state state state (.var "applyArgsResult2") _ _ (Data.preterm right) _
          · exact applied_term_returns withLeft state symbol values.2 "term2" "right" rfl rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, withRight, withLeft, bound, bindings, congruentEnvironment, Subst.lookup]
          · simpa [resultValue, withRight, withLeft, bound, bindings, congruentEnvironment, applySubst, Subst.lookup] using
              constructor_variables_return program withRight state "MM0:Converted" ["applyArgsResult", "applyArgsResult2", "sort"] (by decide +kernel) (by decide)

theorem typed_body_returns (state : State) (answer : Bool) (symbol : Nat) (arguments : List Preterm) (result : Preterm) (sort : Nat) :
    PureReturns program (typedEnvironment answer symbol arguments result sort) state typedEquation.body state
      (resultValue (if answer then some ⟨Preterm.applyArgs (.term symbol) arguments, result, sort⟩ else none)) := by
  rw [typed_body_shape]
  cases answer with
  | false =>
      let bindings := typedEnvironment false symbol arguments result sort
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (.symbol "None") _ _ typedCases (read_cases_encoded typedCases)
      · simpa [bindings, typedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact symbol_returns program bindings state "None"
  | true =>
      let bindings := typedEnvironment true symbol arguments result sort
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true) typedBody _ _ typedCases (read_cases_encoded typedCases)
      · simpa [bindings, typedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [typed_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [typed_true_shape]
        let applied := ("applyArgsResult", Data.preterm (Preterm.applyArgs (.term symbol) arguments)) :: bindings
        apply let_returns program bindings applied state state state (.var "applyArgsResult") _ _ (Data.preterm (Preterm.applyArgs (.term symbol) arguments)) _
        · exact applied_term_returns bindings state symbol arguments "term" "arguments" rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, applied, bindings, typedEnvironment, Subst.lookup]
        · simpa [resultValue, applied, bindings, typedEnvironment, applySubst, Subst.lookup] using
            constructor_variables_return program applied state "MM0:Converted" ["applyArgsResult", "result", "sort"] (by decide +kernel) (by decide)

theorem tail_body_returns (state : State) (result : Option (List Preterm × List Preterm)) (left right : Preterm) :
    PureReturns program (tailEnvironment result left right) state tailEquation.body state
      (argumentsResultValue (result.map fun values => (left :: values.1, right :: values.2))) := by
  rw [tail_body_shape]
  cases result with
  | none =>
      let bindings := tailEnvironment none left right
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None") (.symbol "None") _ _ tailCases (read_cases_encoded tailCases)
      · simpa [bindings, tailEnvironment, argumentsResultValue, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [tail_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some values =>
      let bindings := tailEnvironment (some values) left right
      let bound := ("rights", ListSubstitution.expressionsValue values.2) :: ("lefts", ListSubstitution.expressionsValue values.1) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (argumentsResultValue (some values)) tailBody _ _ tailCases (read_cases_encoded tailCases)
      · simpa [bindings, tailEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [tail_cases_shape, argumentsResultValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, bound, bindings, tailEnvironment, Subst.lookup]
      · rw [tail_some_shape]
        let extended := ("extended", ListSubstitution.expressionsValue (left :: values.1)) :: bound
        let both := ("extended2", ListSubstitution.expressionsValue (right :: values.2)) :: extended
        apply let_returns program bound extended state state state (.var "extended") _ _ (ListSubstitution.expressionsValue (left :: values.1)) _
        · exact ListAccess.cons_captured_returns bound state (Data.preterm left) (values.1.map Data.preterm) "left" "lefts" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, extended, bound, bindings, tailEnvironment, Subst.lookup]
        · apply let_returns program extended both state state state (.var "extended2") _ _ (ListSubstitution.expressionsValue (right :: values.2)) _
          · exact ListAccess.cons_captured_returns extended state (Data.preterm right) (values.2.map Data.preterm) "right" "rights" rfl rfl
          · simp [SpaceSemantics.matchValue, matchAtom, both, extended, bound, bindings, tailEnvironment, Subst.lookup]
          · simpa [argumentsResultValue, both, extended, bound, bindings, tailEnvironment, applySubst, Subst.lookup] using
              constructor_variables_return program both state "MM0:ConvertedArgs" ["extended", "extended2"] (by decide +kernel) (by decide)

theorem congruent_captured_returns (bindings : Subst) (state : State) (result : Option (List Preterm × List Preterm)) (symbol sort : Nat)
    (resultName symbolName sortName : String)
    (capturedResult : applySubst bindings (.var resultName) = argumentsResultValue result)
    (capturedSymbol : applySubst bindings (.var symbolName) = natural symbol)
    (capturedSort : applySubst bindings (.var sortName) = natural sort) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-congruent", .var resultName, .var symbolName, .var sortName]) state
      (resultValue (result.map fun values => ⟨Preterm.applyArgs (.term symbol) values.1, Preterm.applyArgs (.term symbol) values.2, sort⟩)) := by
  apply authored_variable_call_returns program bindings (congruentEnvironment result symbol sort) state state
    "mm0:conversion-congruent" [resultName, symbolName, sortName] congruentEquation.body _
    (by decide) (by decide) (by decide) _ (congruent_body_returns state result symbol sort) (by decide)
  simpa [capturedResult, capturedSymbol, capturedSort] using congruent_clause result symbol sort

theorem typed_captured_returns (bindings : Subst) (state : State) (answer : Bool) (symbol : Nat) (arguments : List Preterm) (result : Preterm) (sort : Nat)
    (answerName symbolName argumentsName resultName sortName : String)
    (capturedAnswer : applySubst bindings (.var answerName) = boolean answer)
    (capturedSymbol : applySubst bindings (.var symbolName) = natural symbol)
    (capturedArguments : applySubst bindings (.var argumentsName) = ListSubstitution.expressionsValue arguments)
    (capturedResult : applySubst bindings (.var resultName) = Data.preterm result)
    (capturedSort : applySubst bindings (.var sortName) = natural sort) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-unfold-typed", .var answerName, .var symbolName, .var argumentsName, .var resultName, .var sortName]) state
      (resultValue (if answer then some ⟨Preterm.applyArgs (.term symbol) arguments, result, sort⟩ else none)) := by
  apply authored_variable_call_returns program bindings (typedEnvironment answer symbol arguments result sort) state state
    "mm0:conversion-unfold-typed" [answerName, symbolName, argumentsName, resultName, sortName] typedEquation.body _
    (by decide) (by decide) (by decide) _ (typed_body_returns state answer symbol arguments result sort) (by decide)
  simpa [capturedAnswer, capturedSymbol, capturedArguments, capturedResult, capturedSort] using typed_clause answer symbol arguments result sort

theorem tail_captured_returns (bindings : Subst) (state : State) (result : Option (List Preterm × List Preterm)) (left right : Preterm)
    (resultName leftName rightName : String)
    (capturedResult : applySubst bindings (.var resultName) = argumentsResultValue result)
    (capturedLeft : applySubst bindings (.var leftName) = Data.preterm left)
    (capturedRight : applySubst bindings (.var rightName) = Data.preterm right) :
    PureReturns program bindings state (.expression [.symbol "mm0:conversion-argument-tail", .var resultName, .var leftName, .var rightName]) state
      (argumentsResultValue (result.map fun values => (left :: values.1, right :: values.2))) := by
  apply authored_variable_call_returns program bindings (tailEnvironment result left right) state state
    "mm0:conversion-argument-tail" [resultName, leftName, rightName] tailEquation.body _
    (by decide) (by decide) (by decide) _ (tail_body_returns state result left right) (by decide)
  simpa [capturedResult, capturedLeft, capturedRight] using tail_clause result left right

end Mettapedia.Languages.MM0.MeTTa.ConversionResults
