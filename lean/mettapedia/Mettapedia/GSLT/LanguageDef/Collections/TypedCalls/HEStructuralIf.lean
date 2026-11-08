import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralBoundary

/-!
# HE conditionals at closed structural expected types

The conditional's private range variable is bound to the caller's expected
type, including compound structural types. The chosen branch retains that
record. This is an actual HE interpreter equation, not an untyped replacement
for the conditional.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralIf

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HEReturns

mutual
private theorem variables_eq : ∀ atom : Atom,
    atomVariables atom = Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars atom
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression fields => variablesList_eq fields

private theorem variablesList_eq : ∀ fields : List Atom,
    atomListVariables fields = Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars.varsList fields
  | [] => rfl
  | first :: rest => by
      simp only [atomListVariables, Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars.varsList,
        variables_eq first, variablesList_eq rest]
end

theorem matchAtoms_ground_var {expected : Atom} (ground : atomVariables expected = [])
    (name : String) (fuel : Nat) :
    matchAtoms expected (.var name) (fuel + 1) = [Bindings.empty.assign name expected] := by
  have noLoop : (Bindings.empty.assign name expected).hasLoop = false :=
    Bindings.hasLoop_false_of_assignment_vars_nil _ fun entry member => by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] at member
      rw [member]
      change Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars expected = []
      rw [← variables_eq]
      exact ground
  cases expected with
  | var x => simp [atomVariables] at ground
  | symbol label => exact matchAtoms_symbol_var label name fuel
  | grounded value =>
      simp [matchAtoms, getMetaType, Atom.groundedType, Atom.variableType, noLoop]
  | expression fields =>
      simp [matchAtoms, getMetaType, Atom.expressionType, Atom.variableType, noLoop]

/-- Binding a fresh type variable to a closed structural type preserves one
applicability path, just as for a scalar class. -/
theorem matchTypes_ground_var {expected : Atom} (ground : atomVariables expected = [])
    (notUndefined : expected ≠ Atom.undefinedType) (notAtom : expected ≠ Atom.atomType)
    (name : String) {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = []) (fuel : Nat) :
    matchTypes expected (.var name) bindings (fuel + 2) = [bindings.assign name expected] := by
  have notU : expected ≠ .symbol "%Undefined%" := notUndefined
  have notA : expected ≠ .symbol "Atom" := notAtom
  unfold matchTypes
  rw [if_neg (by simp [Atom.undefinedType, Atom.atomType, notU, notA]),
    matchAtoms_ground_var ground, List.flatMap_singleton]
  exact mergeBindings_single_assign_fresh unbound noEqualities fuel

/-- The actual conditional protocol applies at any closed structural expected
type, not only Number/String/Bool. Its branch is evaluated under `ifRecord`,
with the expected type retained as the private range variable's binding. -/
theorem if_call_closed {space : Space} {dispatch : GroundedDispatch} {name : String}
    {condition truth chosen other expected : Atom}
    (declared : getAtomTypes space (.symbol "if") = [ifArrow name])
    (notExecutable : dispatch.isExecutable (.symbol "if") = false)
    (notInstruction : minimalInstruction (.expression [.symbol "if", truth, chosen, other]) = false)
    (expectedGround : atomVariables expected = [])
    (notUndefined : expected ≠ Atom.undefinedType)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (conditionChecked : ArgumentChecked space (.symbol "Bool") condition)
    (chosenChecked : ArgumentChecked space Atom.atomType chosen)
    (otherChecked : ArgumentChecked space Atom.atomType other)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    {fuel : Nat} (enough : 9 ≤ fuel)
    (decided : ∀ live, evalAtom space dispatch condition (.symbol "Bool")
      (ifRecord bindings name expected) fuel live =
        [(truth, ifRecord bindings name expected)])
    (running : isEmptyOrError truth = false)
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression [.symbol "if", truth, chosen, other])
      (.var name) (ifRecord bindings name expected) (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression [.symbol "if", condition, chosen, other]) expected
        bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression [.symbol "if", truth, chosen, other]) reply.1 reply.2
          fun value record => evalAtom space dispatch value (.var name) record (fuel + 1) live) := by
  obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have boolClass : ValueClass (.symbol "Bool") := Or.inr (Or.inr (Or.inl rfl))
  have atomGround : atomVariables Atom.atomType = [] := rfl
  have bound : (bindings.assign name expected).lookup name = some expected :=
    lookup_assign_of_lookup_none bindings name expected unbound
  have boundSelf : SelfEqualities name (bindings.assign name expected) := by
    intro e member
    simp [Bindings.assign, noEqualities] at member
  have steps : CheckSteps space (g + 2) [.symbol "Bool", Atom.atomType, Atom.atomType]
      [condition, chosen, other] bindings bindings :=
    .cons (checkArgumentType_checked boolClass.ground conditionChecked bindings
        (by rw [boolClass.matchFuel_eq]; omega))
      (.cons (checkArgumentType_checked atomGround chosenChecked bindings
          (by simp [matchFuel, Atom.atomType]))
        (.cons (checkArgumentType_checked atomGround otherChecked bindings
            (by simp [matchFuel, Atom.atomType]))
          (.nil bindings)))
  have loop := checkArgLoop_steps (expr := .expression [.symbol "if", condition, chosen, other])
    steps [] 1
  have applicable : checkIfFunctionTypeIsApplicable
      (.expression [.symbol "if", condition, chosen, other]) (ifArrow name) expected space bindings
      (g + 1 + 2) = .inr [bindings.assign name expected] := by
    rw [checkIfFunctionTypeIsApplicable]
    simp only [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType]
    simp [loop, matchTypes_ground_var expectedGround notUndefined notAtom name
      unbound noEqualities g]
  have shapes : ∀ atom ∈ (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++
      [.var name]) : List Atom), (∃ label, atom = .symbol label) ∨ atom = .var name := by
    intro atom member
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl
  have headEval : ∀ live, evalAtom space dispatch (.symbol "if") (ifArrow name)
      (bindings.assign name expected) (g + 1 + 1) live =
        [(.symbol "if", ifRecord bindings name expected)] := by
    intro live
    rw [evalAtom_head_selfMatch declared shapes (by decide) boundSelf bound (by simp; omega) live]
    have count : (.symbol "->" :: ([.symbol "Bool", Atom.atomType, Atom.atomType] ++ [.var name]) :
        List Atom).count (.var name) = 1 := by simp [Atom.atomType]
    rw [count]
    rfl
  have branches : ∀ live, interpretArgs space dispatch [chosen, other] [Atom.atomType, Atom.atomType]
      (ifRecord bindings name expected) (g + 1) live =
        [(argumentPacket [chosen, other], ifRecord bindings name expected)] := by
    intro live
    obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
    exact interpretArgs_cons_self
      (fun live => HECorrespondence.he_atom_demand space dispatch chosen _ (k + 1) live)
      (interpretArgs_cons_self
        (fun live => HECorrespondence.he_atom_demand space dispatch other _ k live)
        (fun live => interpretArgs_nil_self _ k live)) live
  have arguments : ∀ live, interpretArgs space dispatch [condition, chosen, other]
      [.symbol "Bool", Atom.atomType, Atom.atomType] (ifRecord bindings name expected)
      (g + 1 + 1) live =
        [(argumentPacket [truth, chosen, other], ifRecord bindings name expected)] := by
    intro live
    exact interpretArgs_cons_value decided running branches live
  have interpreted : ∀ live, interpretFunction space dispatch
      (.expression [.symbol "if", condition, chosen, other]) (ifArrow name)
      (bindings.assign name expected) (g + 1 + 2) live =
        [(.expression [.symbol "if", truth, chosen, other], ifRecord bindings name expected)] := by
    intro live
    have general := interpretFunction_general headEval (isEmptyOrError_symbol (by decide))
      (getFunctionArgTypes_arrowType _ _) arguments live
    simp only [argumentsSucceeded_packet, argumentValues_packet, Bool.true_eq_false, if_false] at general
    exact general
  have returnType : callReturnType (.var name) = .var name := by
    simp [callReturnType, Atom.expressionType]
  have invoked : invoke space dispatch (.ordinary (callReturnType (.var name)))
      (.expression [.symbol "if", truth, chosen, other]) (ifRecord bindings name expected)
      (g + 1 + 2) live =
        replies.flatMap fun reply => ordinaryCallReturn (.expression [.symbol "if", truth, chosen, other])
          reply.1 reply.2 fun value record => evalAtom space dispatch value (.var name) record
            (g + 1 + 1) live := by
    rw [returnType]
    exact invoke_queried notExecutable notInstruction (isErrorAtom_call (by decide) _)
      queried nonempty plain none
  rw [evalAtom_expression (isEmptyOrError_call (by decide) _) notAtom notExpression,
    interpretExpression_single declared applicable interpreted invoked]

/-- A Boolean condition supplied as a value discharges the evaluation
premise of the conditional protocol without assuming an evaluator equation. -/
theorem if_bool_closed {space : Space} {dispatch : GroundedDispatch} {name : String}
    (truth : Bool) {chosen other expected : Atom}
    (declared : getAtomTypes space (.symbol "if") = [ifArrow name])
    (notExecutable : dispatch.isExecutable (.symbol "if") = false)
    (notInstruction : minimalInstruction
      (.expression [.symbol "if", .grounded (.bool truth), chosen, other]) = false)
    (expectedGround : atomVariables expected = [])
    (notUndefined : expected ≠ Atom.undefinedType)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (chosenChecked : HEConstructorAdmission.checkOnce space Atom.atomType chosen = true)
    (otherChecked : HEConstructorAdmission.checkOnce space Atom.atomType other = true)
    {bindings : Bindings} (unbound : bindings.lookup name = none)
    (noEqualities : bindings.equalities = [])
    {fuel : Nat} (enough : 9 ≤ fuel) {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space
      (.expression [.symbol "if", .grounded (.bool truth), chosen, other])
      (.var name) (ifRecord bindings name expected) (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    evalAtom space dispatch (.expression [.symbol "if", .grounded (.bool truth), chosen, other])
        expected bindings (fuel + 4) live =
      keep (replies.flatMap fun reply =>
        ordinaryCallReturn (.expression [.symbol "if", .grounded (.bool truth), chosen, other])
          reply.1 reply.2 fun value record =>
            evalAtom space dispatch value (.var name) record (fuel + 1) live) := by
  apply if_call_closed declared notExecutable notInstruction expectedGround notUndefined
    notAtom notExpression (argumentChecked_grounded space (.bool truth) (by rfl))
    (HEConstructorAdmission.checkOnce_sound chosenChecked)
    (HEConstructorAdmission.checkOnce_sound otherChecked) unbound noEqualities enough
    ?_ (by rfl) queried nonempty plain
  intro retained
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  rw [evalAtom_grounded (.bool truth) (type_ := .symbol "Bool") rfl
    (by decide) (by decide) _ (by simp [matchFuel]; omega)]
  rfl

namespace Controls

def listNumbers : Atom := .expression [.symbol "List", .symbol "Number"]
def listStrings : Atom := .expression [.symbol "List", .symbol "String"]
def numbers : Atom := .symbol "Numbers"
def strings : Atom := .symbol "Strings"
def declaration (atom type : Atom) : Atom := .expression [.symbol ":", atom, type]
def equation (left right : Atom) : Atom := .expression [.symbol "=", left, right]
def conditional (truth : Bool) : Atom :=
  .expression [.symbol "if", .grounded (.bool truth), numbers, strings]

def space : Space := Space.ofList
  [declaration numbers listNumbers, declaration strings listStrings,
   declaration (.symbol "if") (ifArrow "t"),
   equation (.expression [.symbol "if", .grounded (.bool true), .var "x", .var "y"]) (.var "x"),
   equation (.expression [.symbol "if", .grounded (.bool false), .var "x", .var "y"]) (.var "y")]

theorem structural_expected_bound :
    matchTypes listNumbers (.var "t") Bindings.empty 32 =
      [Bindings.empty.assign "t" listNumbers] := by decide

theorem same_frame_branch_keeps_type :
    (evalAtom space GroundedDispatch.none (conditional true) listNumbers Bindings.empty 48 []).map
      Prod.fst = [numbers] := by decide

theorem incompatible_branch_is_error :
    ((evalAtom space GroundedDispatch.none (conditional false) listNumbers
      Bindings.empty 48 []).map Prod.fst).all isErrorAtom = true := by decide

theorem expected_type_is_not_erased :
    (evalAtom space GroundedDispatch.none (conditional false) listNumbers Bindings.empty 48 []).map
      Prod.fst ≠
    (evalAtom space GroundedDispatch.none (conditional false) Atom.undefinedType Bindings.empty 48 []).map
      Prod.fst := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStructuralIf
