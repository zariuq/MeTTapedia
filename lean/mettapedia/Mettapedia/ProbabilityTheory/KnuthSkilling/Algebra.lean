/-
# Knuth-Skilling Algebra: Basic Operations

Basic lemmas for KnuthSkillingAlgebra including:
- iterate_op function
- Commutativity for commutative operations
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

namespace KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-- Iterate the operation: x ⊕ x ⊕ ... ⊕ x (n times).
This builds the sequence: ident, x, x⊕x, x⊕(x⊕x), ... -/
def iterate_op (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (iterate_op x n)

/-- For commutative K&S algebras, iterate_op respects addition.
Note: The minimal KnuthSkillingAlgebra doesn't assume commutativity.
For the probability case (combine_fn is commutative), this holds. -/
theorem iterate_op_add_comm (x : α) (h_comm : ∀ a b : α, op a b = op b a)
    (m n : ℕ) :
    iterate_op x (m + n) = op (iterate_op x m) (iterate_op x n) := by
  induction n with
  | zero => simp [iterate_op, op_ident_right]
  | succ n ih =>
    -- Use commutativity to swap arguments and apply associativity
    calc iterate_op x (m + (n + 1))
        = iterate_op x ((m + n) + 1) := by ring_nf
      _ = op x (iterate_op x (m + n)) := rfl
      _ = op x (op (iterate_op x m) (iterate_op x n)) := by rw [ih]
      _ = op (op x (iterate_op x m)) (iterate_op x n) := by rw [← op_assoc]
      _ = op (op (iterate_op x m) x) (iterate_op x n) := by rw [h_comm x]
      _ = op (iterate_op x m) (op x (iterate_op x n)) := by rw [op_assoc]
      _ = op (iterate_op x m) (iterate_op x (n + 1)) := rfl

end KnuthSkillingAlgebra

end Mettapedia.ProbabilityTheory.KnuthSkilling
