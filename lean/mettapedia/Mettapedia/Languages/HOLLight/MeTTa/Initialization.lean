import Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable
import Mettapedia.Languages.HOLLight.MeTTa.TermJudgment
import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# The authored HOL Light initial state and its registered signature

Executing the retained initialization equation constructs the primitive
operator and constant tables, including their exact presentation order and
schemas. The caller supplies the explicit commitment table. Proof caches and
receipts start empty; initialization does not manufacture theorem evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Initialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State)
open TypeSubstitution (typeAtom)
open Representation (registeredOperatorAtom)

/-- A data head is not a primitive, so it is not `match` either: it avoids every
special form. -/
private theorem notForm (head : String)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
  have notMatch : head ≠ "match" := ne_match_of_not_known (by
    simp only [Bool.or_eq_false_iff] at inert
    exact inert.1.2)
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ordinary
  tauto

private theorem two_literal (head : String) (first second : Atom)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (left : PureData.Literal program first) (right : PureData.Literal program second) :
    PureData.Literal program (.expression [.symbol head, first, second]) := by
  apply PureData.Literal.constructor head [first, second] inert (notForm head inert ordinary)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

private theorem one_literal (head : String) (value : Atom)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (child : PureData.Literal program value) :
    PureData.Literal program (.expression [.symbol head, value]) := by
  apply PureData.Literal.constructor head [value] inert (notForm head inert ordinary)
  intro argument member
  have equal := List.mem_singleton.mp member
  exact equal ▸ child

private def booleanEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:bool"))[0]'(by decide)

theorem authored_boolean_type_certificate (bindings : Subst) (state : State) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:bool"]) state
      (typeAtom registeredOperatorAtom Ty.bool) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings [] state state "hol-light:bool" [] booleanEquation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · rw [clauses_use_only_the_named_equations]
    have unique : program.equations.filter (fun row => row.head == "hol-light:bool") = [booleanEquation] := by rfl
    rw [unique]
    have formals : booleanEquation.arguments = [] := by decide
    simp [formals, SpaceSemantics.matchValue.matchValues]
  · have body : booleanEquation.body = .expression [.symbol "Tyapp", .grounded (.string "bool"), .symbol "HOL:Nil"] := by decide
    rw [body]
    have literal : PureData.Literal program booleanEquation.body := by
      rw [body]
      exact two_literal "Tyapp" _ _ (by decide) (by decide) (.grounded _) (.symbol _)
    simpa [body, Ty.bool, typeAtom, Premises.keys] using
      BoundCalls.CorePath.literal_return program [] state booleanEquation.body literal

theorem authored_boolean_type_return (bindings : Subst) (state : State) :
    PureReturns program bindings state (.expression [.symbol "hol-light:bool"]) state
      (typeAtom registeredOperatorAtom Ty.bool) :=
  (authored_boolean_type_certificate bindings state).original

private def equalityEquation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:eq-type"))[0]'(by decide)
private def equalityEnvironment (type : Ty) : Subst := [("type", typeAtom registeredOperatorAtom type)]

private theorem equality_clause (type : Ty) :
    clauses program "hol-light:eq-type" [typeAtom registeredOperatorAtom type] =
      [.evaluate (equalityEnvironment type) equalityEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:eq-type") = [equalityEquation] := by rfl
  rw [unique]
  have formals : equalityEquation.arguments = [.var "type"] := by decide
  simp [formals, equalityEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem equality_body_return (type : Ty) (state : State) :
    BoundCalls.CorePath.PureReturns program (equalityEnvironment type) state equalityEquation.body state
      (typeAtom registeredOperatorAtom (Ty.equality type)) := by
  have body : equalityEquation.body = .expression [.symbol "hol-light:fun", .var "type",
    .expression [.symbol "hol-light:fun", .var "type", .expression [.symbol "hol-light:bool"]]] := by decide
  rw [body]
  apply TermJudgment.authored_function_certificate (equalityEnvironment type) state _ _ type (.function type Ty.bool)
  · simpa [equalityEnvironment, applySubst, Subst.lookup] using
      BoundCalls.CorePath.variable_returns program (equalityEnvironment type) state "type"
  · exact TermJudgment.authored_function_certificate (equalityEnvironment type) state _ _ type Ty.bool
      (by simpa [equalityEnvironment, applySubst, Subst.lookup] using
        BoundCalls.CorePath.variable_returns program (equalityEnvironment type) state "type")
      (authored_boolean_type_certificate (equalityEnvironment type) state)

theorem authored_equality_type_certificate (bindings : Subst) (state : State) (expression : Atom) (type : Ty)
    (computed : BoundCalls.CorePath.PureReturns program bindings state expression state (typeAtom registeredOperatorAtom type)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:eq-type", expression]) state
      (typeAtom registeredOperatorAtom (Ty.equality type)) := by
  apply BoundCalls.CorePath.call_returns program bindings state state "hol-light:eq-type" [expression] _ (by decide) _ (by decide)
  apply BoundCalls.CorePath.evaluated_argument_returns program bindings state state state (.function "hol-light:eq-type") expression
    (typeAtom registeredOperatorAtom type) _ [] [] 0 (by decide) computed
  exact BoundCalls.CorePath.authored_function_arguments_return program bindings (equalityEnvironment type) state state
    "hol-light:eq-type" [typeAtom registeredOperatorAtom type] 1 equalityEquation.body _
    (by decide) (by decide) (equality_clause type) (equality_body_return type state)

theorem authored_equality_type_return (bindings : Subst) (state : State) (expression : Atom) (type : Ty)
    (computed : PureReturns program bindings state expression state (typeAtom registeredOperatorAtom type)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:eq-type", expression]) state
      (typeAtom registeredOperatorAtom (Ty.equality type)) := by
  apply call_returns program bindings state state "hol-light:eq-type" [expression] _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:eq-type") expression
    (typeAtom registeredOperatorAtom type) _ [] [] 0 (by decide) computed
  exact authored_function_arguments_return program bindings (equalityEnvironment type) state state
    "hol-light:eq-type" [typeAtom registeredOperatorAtom type] 1 equalityEquation.body _
    (by decide) (by decide) (equality_clause type) (equality_body_return type state).original

private def parameter : Atom := .expression [.symbol "Tyvar", .grounded (.string "A")]

private theorem parameter_return (bindings : Subst) (state : State) :
    PureReturns program bindings state parameter state
      (typeAtom registeredOperatorAtom (.var DefinitionAdapters.ContextControls.equalityParameter)) := by
  have literal : PureData.Literal program parameter :=
    one_literal "Tyvar" _ (by decide) (by decide) (.grounded _)
  simpa [parameter, typeAtom, DefinitionAdapters.ContextControls.equalityParameter] using
    PureData.literal_return program bindings state parameter literal

private def operatorBody : Atom :=
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "bool"),
    .expression [.symbol "HOL:TypeOperator", .grounded (.int 0), .symbol "HOL:Primitive"]],
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "fun"),
    .expression [.symbol "HOL:TypeOperator", .grounded (.int 2), .symbol "HOL:Primitive"]],
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "ind"),
    .expression [.symbol "HOL:TypeOperator", .grounded (.int 0), .symbol "HOL:Primitive"]],
    .symbol "HOL:Nil"]]]

private def constantBody : Atom :=
  .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "="),
    .expression [.symbol "HOL:Constant", .expression [.symbol "hol-light:eq-type", parameter],
      .expression [.symbol "HOL:Primitive", .grounded (.string "=")]]],
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "@"),
      .expression [.symbol "HOL:Constant", .expression [.symbol "hol-light:fun",
        .expression [.symbol "hol-light:fun", parameter, .expression [.symbol "hol-light:bool"]], parameter],
        .expression [.symbol "HOL:Primitive", .grounded (.string "@")]]], .symbol "HOL:Nil"]]

private theorem operator_body_return (bindings : Subst) (state : State) :
    PureReturns program bindings state operatorBody state
      (OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators (fun _ => .symbol "HOL:Primitive")) := by
  rw [DeclarationTable.source_primitive_operator_table, OperatorTable.source_primitive_table]
  have literal : PureData.Literal program operatorBody := by
    unfold operatorBody
    repeat' first
      | exact PureData.Literal.grounded _
      | exact PureData.Literal.symbol _
      | apply two_literal _ _ _ (by decide) (by decide)
  exact PureData.literal_return program bindings state operatorBody literal

private theorem primitive_identity_return (bindings : Subst) (state : State) (name : String) :
    PureReturns program bindings state
      (.expression [.symbol "HOL:Primitive", .grounded (.string name)]) state
      (.expression [.symbol "HOL:Primitive", .grounded (.string name)]) :=
  PureData.literal_return program bindings state _
    (one_literal "HOL:Primitive" _ (by decide) (by decide) (.grounded _))

private theorem constant_body_return (bindings : Subst) (state : State) :
    PureReturns program bindings state constantBody state
      (DeclarationTable.tableAtom DeclarationTable.sourcePrimitive DeclarationTable.primitiveIdentity) := by
  rw [DeclarationTable.source_primitive_constant_table]
  unfold constantBody
  apply binary_constructor_returns program bindings state state state "HOL:Cons" _ _ _ _ (by decide) (by decide)
  · apply binary_constructor_returns program bindings state state state "HOL:Entry" _ _ _ _ (by decide) (by decide)
    · exact grounded_returns program bindings state (.string "=")
    · apply binary_constructor_returns program bindings state state state "HOL:Constant" _ _ _ _ (by decide) (by decide)
      · exact authored_equality_type_return bindings state parameter _ (parameter_return bindings state)
      · exact primitive_identity_return bindings state "="
  · apply binary_constructor_returns program bindings state state state "HOL:Cons" _ _ _ _ (by decide) (by decide)
    · apply binary_constructor_returns program bindings state state state "HOL:Entry" _ _ _ _ (by decide) (by decide)
      · exact grounded_returns program bindings state (.string "@")
      · apply binary_constructor_returns program bindings state state state "HOL:Constant" _ _ _ _ (by decide) (by decide)
        · exact TermJudgment.authored_function_return bindings state _ _
            (.function (.var DefinitionAdapters.ContextControls.equalityParameter) Ty.bool)
            (.var DefinitionAdapters.ContextControls.equalityParameter)
            (TermJudgment.authored_function_return bindings state _ _
              (.var DefinitionAdapters.ContextControls.equalityParameter) Ty.bool
              (parameter_return bindings state) (authored_boolean_type_return bindings state))
            (parameter_return bindings state)
        · exact primitive_identity_return bindings state "@"
    · exact symbol_returns program bindings state "HOL:Nil"

def initialState (commitments : Atom) : Atom := .expression [.symbol "HOL:State",
  OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators (fun _ => .symbol "HOL:Primitive"),
  DeclarationTable.tableAtom DeclarationTable.sourcePrimitive DeclarationTable.primitiveIdentity,
  commitments, .symbol "HOL:Nil", .symbol "HOL:Nil"]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:initial"))[0]'(by decide)
private def environment (commitments : Atom) : Subst := [("commitments", commitments)]
private theorem clause (commitments : Atom) :
    clauses program "hol-light:initial" [commitments] = [.evaluate (environment commitments) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:initial") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "commitments"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_return (commitments : Atom) (state : State) :
    PureReturns program (environment commitments) state equation.body state (initialState commitments) := by
  have body : equation.body = .expression [.symbol "HOL:State", operatorBody, constantBody,
    .var "commitments", .symbol "HOL:Nil", .symbol "HOL:Nil"] := by decide
  rw [body]
  apply PureData.constructor_return program (environment commitments) state "HOL:State" _ _ (by decide) (by decide)
  exact .cons (operator_body_return (environment commitments) state)
    (.cons (constant_body_return (environment commitments) state)
      (.cons (by simpa [environment, applySubst, Subst.lookup] using variable_returns program (environment commitments) state "commitments")
        (.cons (symbol_returns program (environment commitments) state "HOL:Nil")
          (.cons (symbol_returns program (environment commitments) state "HOL:Nil") .nil))))

/-- The retained authored initialization constructs the registered primitive
signature. Captured commitments stay data, and both proof stores start empty. -/
theorem authored_initial_state_return (bindings : Subst) (state : State) (commitments : Atom)
    (commitmentsKey : String) (captured : applySubst bindings (.var commitmentsKey) = commitments) :
    PureReturns program bindings state (.expression [.symbol "hol-light:initial", .var commitmentsKey]) state
      (initialState commitments) := by
  apply authored_variable_call_returns program bindings (environment commitments) state state "hol-light:initial"
    [commitmentsKey] equation.body _ (by decide) (by decide) (by decide) _ (body_return commitments state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using clause commitments

end Mettapedia.Languages.HOLLight.MeTTa.Initialization
