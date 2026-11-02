import Mettapedia.Languages.OCaml.Primitives

/-! The independent structural comparison judgment composes lexicographic
steps through one continuation. Only an equal successful prefix continues;
faults, refusal and a strict order stop at their first occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def continueCompared (first later : Compared) : Compared := do
  match ← first with
  | .error fault => pure (.error fault)
  | .ok .eq => later
  | .ok order => pure (.ok order)

theorem compare_cons (head tail other rest : Value) :
    compareValue (.cons head tail) (.cons other rest) =
      continueCompared (compareValue head other) (compareValue tail rest) := by
  rw [compareValue]
  rfl

theorem compare_fields_cons (head other : Value) (tail rest : List Value) :
    compareFields (head :: tail) (other :: rest) =
      continueCompared (compareValue head other) (compareFields tail rest) := by
  rw [compareFields]
  rfl

theorem compare_tuple (left right : List Value) :
    compareValue (.tuple left) (.tuple right) =
      if left.length = right.length then compareFields left right
      else .error (.incomparableValues (.tuple left) (.tuple right)) := by
  rw [compareValue]

theorem compare_variant (leftType leftTag rightType rightTag : Nat) (left right : List Value) :
    compareValue (.variant leftType leftTag left) (.variant rightType rightTag right) =
      if leftType ≠ rightType then
        .error (.incomparableValues (.variant leftType leftTag left) (.variant rightType rightTag right))
      else if left.isEmpty && !right.isEmpty then .ok (.ok .lt)
      else if !left.isEmpty && right.isEmpty then .ok (.ok .gt)
      else match (if leftTag < rightTag then Ordering.lt else if leftTag = rightTag then .eq else .gt) with
        | .eq => compareFields left right
        | order => .ok (.ok order) := by
  rw [compareValue]
  rfl

theorem compare_closure_left (function : FunctionRef) (captured : List Value) (other : Value) :
    compareValue (.closure function captured) other = .ok (.error .functionalComparison) := by
  cases other <;> rw [compareValue]

theorem compare_closure_right (function : FunctionRef) (captured : List Value) (other : Value) :
    compareValue other (.closure function captured) = .ok (.error .functionalComparison) := by
  cases other <;> rw [compareValue] <;> simp

theorem continue_functional_fault (later : Compared) :
    continueCompared (.ok (.error .functionalComparison)) later = .ok (.error .functionalComparison) := rfl

theorem continue_strict_order (order : Ordering) (strict : order ≠ .eq) (later : Compared) :
    continueCompared (.ok (.ok order)) later = .ok (.ok order) := by
  cases order with
  | lt => rfl
  | eq => exact (strict rfl).elim
  | gt => rfl

example : continueCompared (.ok (.ok .lt)) (.ok (.error .functionalComparison)) = .ok (.ok .lt) := rfl
example : continueCompared (.ok (.ok .eq)) (.ok (.error .functionalComparison)) = .ok (.error .functionalComparison) := rfl
example : continueCompared (.ok (.error .functionalComparison)) (.ok (.ok .gt)) ≠ .ok (.ok .gt) := by intro same; cases same

#print axioms compare_cons
#print axioms compare_variant
#print axioms compare_closure_left
#print axioms continue_strict_order

end Mettapedia.Languages.OCaml
