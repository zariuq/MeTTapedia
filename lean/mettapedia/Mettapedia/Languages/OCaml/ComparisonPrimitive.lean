import Mettapedia.Languages.OCaml.ComparisonOutcome

/-! The six source comparison primitives share the same value comparison,
mapping a successful order to a Boolean and retaining source refusal/fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def Primitive.isComparison : Primitive → Bool
  | .equal | .different | .less | .lessEqual | .greater | .greaterEqual => true
  | _ => false

def comparisonResult (operator : Primitive) (result : Compared) : Except InternalError Result := do
  pure ((← result).map fun order => .literal (.boolean (comparison operator order)))

theorem comparison_evaluates (operator : Primitive) (allowed : operator.isComparison = true) (left right : Value) :
    operator.eval [left, right] = comparisonResult operator (compareValue left right) := by
  cases operator <;> simp [Primitive.isComparison] at allowed
  all_goals rfl

#print axioms comparison_evaluates

end Mettapedia.Languages.OCaml
