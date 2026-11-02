import Mettapedia.Languages.OCaml.ComparisonPrimitive

/-! Successful source primitive evaluation determines the required argument
shape. These are inverse facts about the independent source evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem integer_binary_arguments {operator : Primitive} {arguments : List Value} {result : Result}
    (allowed : operator = .add ∨ operator = .subtract ∨ operator = .multiply ∨ operator = .divide ∨ operator = .modulo)
    (evaluated : operator.eval arguments = .ok result) :
    ∃ left right, arguments = [.literal (.integer left), .literal (.integer right)] := by
  unfold Primitive.eval at evaluated
  split at evaluated <;> first
    | exact ⟨_, _, rfl⟩
    | simp_all

theorem negate_arguments {arguments : List Value} {result : Result}
    (evaluated : Primitive.negate.eval arguments = .ok result) :
    ∃ number, arguments = [.literal (.integer number)] := by
  unfold Primitive.eval at evaluated
  split at evaluated <;> first
    | exact ⟨_, rfl⟩
    | simp_all

theorem not_arguments {arguments : List Value} {result : Result}
    (evaluated : Primitive.notBool.eval arguments = .ok result) :
    ∃ flag, arguments = [.literal (.boolean flag)] := by
  unfold Primitive.eval at evaluated
  split at evaluated <;> first
    | exact ⟨_, rfl⟩
    | simp_all

theorem comparison_arguments {operator : Primitive} {arguments : List Value} {result : Result}
    (allowed : operator.isComparison = true) (evaluated : operator.eval arguments = .ok result) :
    ∃ left right, arguments = [left, right] := by
  unfold Primitive.eval at evaluated
  split at evaluated <;> first
    | exact ⟨_, _, rfl⟩
    | simp_all [Primitive.isComparison]

#print axioms integer_binary_arguments
#print axioms negate_arguments
#print axioms not_arguments
#print axioms comparison_arguments

end Mettapedia.Languages.OCaml
