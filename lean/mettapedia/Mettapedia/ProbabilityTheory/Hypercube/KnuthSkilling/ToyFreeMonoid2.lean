/-
Knuth–Skilling slice of the probability hypercube. See the aggregator
`Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling.lean` for the overview.
-/
import Mathlib.Data.List.Basic

/-!
# Toy Model: Free Monoid on Two Generators (List Bool)

This file provides a tiny, fully explicit non-commutative monoid used in the hypercube “shape”
lemmas (`Hypercube/KnuthSkilling/Proofs.lean`).

It is *not* part of the Knuth–Skilling Appendix A representation theorem; it is only used as a
sanity-check example that:

- associativity + identity do **not** imply commutativity, and
- “scaling” identities like `(a ⊕ b)^2 = a^2 ⊕ b^2` can fail without commutativity.
-/

namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling

namespace ToyFreeMonoid2

/-- The free monoid on two generators, represented as `List Bool`. -/
abbrev FreeMonoid2 := List Bool

/-- Concatenation operation on the free monoid. -/
def op (x y : FreeMonoid2) : FreeMonoid2 := x ++ y

/-- Identity element (empty list). -/
def ident : FreeMonoid2 := []

/-- Generator “a” (represented as `[false]`). -/
def genA : FreeMonoid2 := [false]

/-- Generator “b” (represented as `[true]`). -/
def genB : FreeMonoid2 := [true]

/-- Iterate operation: `x^n = x ⊕ x ⊕ ... ⊕ x` (n times). -/
def iterate (x : FreeMonoid2) : ℕ → FreeMonoid2
  | 0 => ident
  | n + 1 => op (iterate x n) x

/-- Computation: `(ab) ⊕ (ab) = abab`. -/
theorem ab_squared :
    op (op genA genB) (op genA genB) = [false, true, false, true] := rfl

/-- Computation: `a^2 ⊕ b^2 = aabb`. -/
theorem aa_bb :
    op (iterate genA 2) (iterate genB 2) = [false, false, true, true] := rfl

/-- **Counterexample**: `(a ⊕ b)^2 ≠ a^2 ⊕ b^2`.

This is the simplest “mass vs ordering” failure in a non-commutative monoid. -/
theorem ab_square_ne_aa_bb :
    op (op genA genB) (op genA genB) ≠ op (iterate genA 2) (iterate genB 2) := by
  rw [ab_squared, aa_bb]
  decide

theorem op_assoc (x y z : FreeMonoid2) : op (op x y) z = op x (op y z) :=
  List.append_assoc x y z

theorem op_ident_left (x : FreeMonoid2) : op ident x = x := rfl

theorem op_ident_right (x : FreeMonoid2) : op x ident = x := List.append_nil x

/-- The free monoid is not commutative: `a ⊕ b ≠ b ⊕ a`. -/
theorem op_not_comm : op genA genB ≠ op genB genA := by decide

end ToyFreeMonoid2

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling

