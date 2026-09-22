import Mettapedia.OSLF.Syntax.ObservationClosure
import Mathlib.Algebra.Order.Group.Nat

/-!
# Both signs of the observation ladder

The ladder says stability is the same condition at every rung, and that the
relation nevertheless changes.  Here are the two witnesses for the second half,
kept apart from the ladder itself so that the general module needs nothing but
the relation library.

**The climb can collapse everything.**  Adjacency on the numbers is a tolerance,
is not transitive, and its equivalence closure is the total relation -- so a
predicate that cannot separate adjacent numbers cannot separate any two numbers.
That is the sorites, as a theorem, and it is the reason the rungs must stay
distinct: passing to the closure is sound for observations and catastrophic for
the relation.

**And it need not.**  Stepping by two has a closure that is not total, witnessed
by a stable predicate that is not constant, so the collapse above is a property
of adjacency rather than of the construction.
-/

namespace Mettapedia.OSLF.Syntax.ObservationClosure

open Relation

set_option autoImplicit false

/-! ## Negative control: the climb can collapse everything

Adjacency on the numbers.  It is a tolerance; it is not transitive; and its
equivalence closure is the total relation.  So the rungs are not
interchangeable as relations, however interchangeable they are as observations. -/

namespace Sorites

/-- One step apart. -/
def adjacent : ℕ → ℕ → Prop := fun m n => m + 1 = n

/-- The tolerance it generates is not transitive: `0` and `1` are
indistinguishable, and `1` and `2` are, but `0` and `2` are not. -/
theorem adjacent_tolerance_not_transitive :
    ¬ ∀ x y z : ℕ, Tolerance adjacent x y → Tolerance adjacent y z →
        Tolerance adjacent x z := by
  intro h
  have h01 : Tolerance adjacent 0 1 := Or.inr (Or.inl rfl)
  have h12 : Tolerance adjacent 1 2 := Or.inr (Or.inl rfl)
  rcases h 0 1 2 h01 h12 with h' | h' | h' <;> simp [adjacent] at h'

theorem eqvGen_adjacent_from_zero : ∀ n : ℕ, EqvGen adjacent 0 n
  | 0 => EqvGen.refl 0
  | n + 1 =>
      EqvGen.trans _ _ _ (eqvGen_adjacent_from_zero n) (EqvGen.rel n (n + 1) rfl)

/-- **The closure is total.**  Everything is equated. -/
theorem eqvGen_adjacent_total (m n : ℕ) : EqvGen adjacent m n :=
  EqvGen.trans _ _ _ (EqvGen.symm _ _ (eqvGen_adjacent_from_zero m))
    (eqvGen_adjacent_from_zero n)

/-- **The sorites, as a theorem.**  A predicate that cannot separate adjacent
numbers cannot separate any two numbers.  Nothing about the predicate is
assumed: the conclusion comes from stability being invariant up the ladder
together with the closure being total. -/
theorem stable_adjacent_is_constant {P : ℕ → Prop} (h : Stable adjacent P)
    (m n : ℕ) : P m ↔ P n :=
  (stable_eqvGen_iff.mp h) m n (eqvGen_adjacent_total m n)

end Sorites

/-! ## Positive control: a policy whose closure keeps information

The other sign.  Stepping by two has a closure with two classes, and parity is
a stable predicate that is not constant -- so `stable_adjacent_is_constant` is
a fact about adjacency rather than about stability. -/

namespace Parity

/-- Two steps apart. -/
def step2 : ℕ → ℕ → Prop := fun m n => m + 2 = n

def parity (n : ℕ) : Prop := n % 2 = 0

/-- Parity is an observation for this policy. -/
theorem parity_stable : Stable step2 parity := by
  intro x y h
  simp only [step2] at h
  subst h
  simp only [parity, Nat.add_mod_right]

/-- And it is not constant. -/
theorem parity_not_constant : ¬ (parity 0 ↔ parity 1) := by
  intro h
  have h1 : parity 1 := h.mp (by simp [parity])
  simp [parity] at h1

/-- **So this closure is not total**, and the collapse above was a property of
adjacency rather than of the construction. -/
theorem eqvGen_step2_not_total : ¬ EqvGen step2 0 1 := fun h =>
  parity_not_constant ((stable_eqvGen_iff.mp parity_stable) 0 1 h)

end Parity

end Mettapedia.OSLF.Syntax.ObservationClosure
