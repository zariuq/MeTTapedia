import Mettapedia.Languages.Maude.ConditionalMaxBoolPrelude

/-! The associativity and commutativity declared by BOOL-OPS preserve its
interpretation. These laws hold for the partial interpretation as well;
ill-sorted arguments do not manufacture a Boolean value. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

private theorem value_cases (value : Option Value) :
    value = none ∨ (∃ number, value = some (.natural number)) ∨
      (∃ boolean, value = some (SemanticValue.boolean boolean)) := by
  cases value with
  | none => exact .inl rfl
  | some value => cases value with
    | natural number => exact .inr (.inl ⟨number, rfl⟩)
    | boolean value => exact .inr (.inr ⟨value, rfl⟩)

private theorem finish_associative (label : String)
    (known : label = "BOOL.and" ∨ label = "BOOL.or" ∨ label = "BOOL.xor")
    (first second third : Option Value) :
    finish label [finish label [first, second], third] =
      finish label [first, finish label [second, third]] := by
  rcases known with rfl | rfl | rfl
  all_goals rcases value_cases first with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals rcases value_cases second with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals rcases value_cases third with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals first
  | rfl
  | rename_i first second third
    first
    | change some (SemanticValue.boolean ((first && second) && third)) = some (SemanticValue.boolean (first && (second && third)))
      rw [Bool.and_assoc]
    | change some (SemanticValue.boolean ((first || second) || third)) = some (SemanticValue.boolean (first || (second || third)))
      rw [Bool.or_assoc]
    | change some (SemanticValue.boolean ((Bool.xor first second) ^^ third)) = some (SemanticValue.boolean (first ^^ (second ^^ third)))
      rw [Bool.xor_assoc]

private theorem finish_commutative (label : String)
    (known : label = "BOOL.and" ∨ label = "BOOL.or" ∨ label = "BOOL.xor")
    (first second : Option Value) : finish label [first, second] = finish label [second, first] := by
  rcases known with rfl | rfl | rfl
  all_goals rcases value_cases first with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals rcases value_cases second with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  all_goals first
  | rfl
  | rename_i first second
    first
    | change some (SemanticValue.boolean (first && second)) = some (SemanticValue.boolean (second && first))
      rw [Bool.and_comm]
    | change some (SemanticValue.boolean (first || second)) = some (SemanticValue.boolean (second || first))
      rw [Bool.or_comm]
    | change some (SemanticValue.boolean (first ^^ second)) = some (SemanticValue.boolean (second ^^ first))
      rw [Bool.xor_comm]

private theorem active_operator (declaration : Operator) (member : declaration ∈ signature.operators)
    (active : declaration.attributes.associative = true ∨ declaration.attributes.commutative = true) :
    declaration.id = "BOOL.and" ∨ declaration.id = "BOOL.or" ∨ declaration.id = "BOOL.xor" := by
  rcases List.mem_append.mp member with original | imported
  · rcases operators original with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [zeroOperator, successorOperator, trueOperator, falseOperator, leOperator, maxOperator] at active
  · simp only [extraOperators, List.mem_cons, List.not_mem_nil, or_false] at imported
    rcases imported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [booleanBinary]

private theorem no_identity (declaration : Operator) (member : declaration ∈ signature.operators) :
    declaration.attributes.identity = none := by
  rcases List.mem_append.mp member with original | imported
  · rcases operators original with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [extraOperators, List.mem_cons, List.not_mem_nil, or_false] at imported
    rcases imported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem algebra_sound {context : VariableContext} {sort : String} {source target : Term}
    (step : AlgebraStep signature context sort source target)
    (assignment : String → Option Value) : evaluate assignment source = evaluate assignment target := by
  cases step.schema with
  | @associative declaration first second third member active =>
    simpa only [evaluate_app, List.map_cons, List.map_nil] using
      finish_associative declaration.id (active_operator declaration member (.inl active))
        (evaluate assignment first) (evaluate assignment second) (evaluate assignment third)
  | @commutative declaration first second member active =>
    simpa only [evaluate_app, List.map_cons, List.map_nil] using
      finish_commutative declaration.id (active_operator declaration member (.inr active))
        (evaluate assignment first) (evaluate assignment second)
  | leftUnit member active => rw [no_identity _ member] at active; cases active
  | rightUnit member active => rw [no_identity _ member] at active; cases active

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
