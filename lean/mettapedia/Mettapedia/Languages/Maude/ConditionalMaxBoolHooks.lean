import Mettapedia.Languages.Maude.ConditionalMaxBoolModel
import Mettapedia.Languages.Maude.ConditionalMaxBoolAlgebra

/-! Ground equality hooks compare explicit canonical constructor terms.
Their specification does not appeal to the equational relation whose
soundness and conservativity are being proved. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

inductive EqualityHook : EquationHook where
  | naturalEqual (context : VariableContext) (first second : Nat) : EqualityHook context "Bool"
      (binary "BOOL.eq.Nat" (numeral first) (numeral second))
      (represent (.boolean (decide (first = second))))
  | naturalDifferent (context : VariableContext) (first second : Nat) : EqualityHook context "Bool"
      (binary "BOOL.ne.Nat" (numeral first) (numeral second))
      (represent (.boolean (decide (first ≠ second))))
  | booleanEqual (context : VariableContext) (first second : Bool) : EqualityHook context "Bool"
      (binary "BOOL.eq.Bool" (represent (.boolean first)) (represent (.boolean second)))
      (represent (.boolean (decide (first = second))))
  | booleanDifferent (context : VariableContext) (first second : Bool) : EqualityHook context "Bool"
      (binary "BOOL.ne.Bool" (represent (.boolean first)) (represent (.boolean second)))
      (represent (.boolean (decide (first ≠ second))))

theorem evaluate_numeral (assignment : String → Option Value) (value : Nat) :
    evaluate assignment (numeral value) = some (.natural value) :=
  (evaluate_local (numeral_sorted [] value) assignment).trans (interpret_numeral assignment value)

theorem evaluate_boolean (assignment : String → Option Value) (value : Bool) :
    evaluate assignment (represent (.boolean value)) = some (.boolean value) := by
  cases value with
  | false =>
    rw [represent, if_neg (by decide), falsehood, evaluate_app]
    rfl
  | true =>
    rw [represent, if_pos rfl, truth, evaluate_app]
    rfl

theorem equality_hook_sound {context : VariableContext} {sort : String} {source target : Term}
    (step : EqualityHook context sort source target) (assignment : String → Option Value) :
    evaluate assignment source = evaluate assignment target := by
  cases step with
  | naturalEqual context first second =>
    dsimp only [binary]
    simp only [evaluate_app, List.map_cons, List.map_nil, evaluate_numeral, evaluate_boolean]; rfl
  | naturalDifferent context first second =>
    dsimp only [binary]
    simp only [evaluate_app, List.map_cons, List.map_nil, evaluate_numeral, evaluate_boolean]; rfl
  | booleanEqual context first second =>
    dsimp only [binary]
    simp only [evaluate_app, List.map_cons, List.map_nil, evaluate_boolean]; rfl
  | booleanDifferent context first second =>
    dsimp only [binary]
    simp only [evaluate_app, List.map_cons, List.map_nil, evaluate_boolean]; rfl

def model : EquationModel theory EqualityHook where
  toEquationalInterpretation := interpretation
  algebra_sound step assignment _ := algebra_sound step assignment
  equation_sound row member assignment assigned conditions := by
    simp only [theory, List.mem_append] at member
    rcases member with ((original | boolean) | naturalBranch) | booleanBranch
    · exact original_rows_sound row original assignment assigned conditions
    · exact boolean_rows_sound row boolean assignment assigned
    · exact branch_rows_sound "Nat" (.inl rfl) row naturalBranch assignment assigned
    · exact branch_rows_sound "Bool" (.inr rfl) row booleanBranch assignment assigned
  hook_sound step assignment _ := equality_hook_sound step assignment

theorem equivalent_sound {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : HookedEquivalent theory EqualityHook context sort source target)
    (assignment : String → Option Value) (assigned : Assigned context assignment) :
    evaluate assignment source = evaluate assignment target :=
  model.sound equivalent assignment assigned

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
