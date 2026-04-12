import Mathlib.Order.Closure

namespace Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1

/-!
# Seven Sketches, Chapter 1: Abstract Adjunctions

This file lifts the Chapter 1 Codex development from the concrete powerset
example to the abstract preorder-level notion of adjunction as a Galois
connection.  It records the induced closure and interior behavior that Fong and
Spivak emphasize in the chapter.
-/

section

variable {P Q : Type*}
variable [PartialOrder P] [PartialOrder Q]
variable {l : P → Q} {u : Q → P}

/-- Chapter 1 order-theoretic adjunctions are Galois connections. -/
abbrev IsAdjunction (l : P → Q) (u : Q → P) : Prop :=
  GaloisConnection l u

/-- Every adjunction induces a closure operator on the source preorder. -/
def inducedClosure (h : IsAdjunction l u) : ClosureOperator P :=
  h.closureOperator

/-- Every adjunction induces an interior-like operator on the target preorder. -/
def inducedInterior (_h : IsAdjunction l u) : Q → Q :=
  l ∘ u

theorem lowerAdjoint_monotone (h : IsAdjunction l u) : Monotone l :=
  h.monotone_l

theorem upperAdjoint_monotone (h : IsAdjunction l u) : Monotone u :=
  h.monotone_u

theorem le_inducedClosure (h : IsAdjunction l u) (x : P) :
    x ≤ inducedClosure h x :=
  (inducedClosure h).le_closure x

theorem inducedClosure_monotone (h : IsAdjunction l u) :
    Monotone (inducedClosure h) :=
  (inducedClosure h).monotone

theorem inducedClosure_idempotent (h : IsAdjunction l u) (x : P) :
    inducedClosure h (inducedClosure h x) = inducedClosure h x :=
  (inducedClosure h).idempotent x

theorem inducedInterior_le (h : IsAdjunction l u) (y : Q) :
    inducedInterior h y ≤ y :=
  h.l_u_le y

theorem inducedInterior_monotone (h : IsAdjunction l u) :
    Monotone (inducedInterior h) := by
  intro y₁ y₂ hy
  exact h.monotone_l (h.monotone_u hy)

theorem inducedInterior_idempotent (h : IsAdjunction l u) (y : Q) :
    inducedInterior h (inducedInterior h y) = inducedInterior h y := by
  show l (u (l (u y))) = l (u y)
  apply le_antisymm
  · exact h.l_u_le (l (u y))
  · exact h.monotone_l (h.le_u_l (u y))

/-- Positive canary: every source element lies below its induced closure. -/
theorem closure_extensive_example (h : IsAdjunction l u) (x : P) :
    x ≤ inducedClosure h x :=
  le_inducedClosure h x

/-- Negative canary: if an element strictly exceeds its induced closure, the order
relation contradicts extensivity. -/
theorem not_gt_inducedClosure (h : IsAdjunction l u) {x : P}
    (hgt : inducedClosure h x < x) :
    False :=
  not_lt_of_ge (le_inducedClosure h x) hgt

end

end Mettapedia.AutoBooks.Codex.SevenSketches.Chapter1
