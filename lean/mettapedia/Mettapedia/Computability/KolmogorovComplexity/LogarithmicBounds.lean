import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Uniform logarithmic bounds

Asymptotic comparison is a statement about a family.  Its multiplicative and
additive constants must therefore be chosen once for the whole family, before
the family index is introduced.  Allowing fresh constants for every individual
index makes a logarithmic upper bound vacuous.

This module records that quantifier order explicitly and supplies a negative
control separating uniform bounds from pointwise existential bounds.
-/

namespace KolmogorovComplexity

/-- `left` is bounded by `right` with logarithmic overhead, using one pair of
constants for every member of the indexed family. -/
def UniformLogarithmicUpperBound {ι : Type*}
    (left right scale : ι → Nat) : Prop :=
  ∃ multiplier constant : Nat, ∀ i,
    left i ≤ right i + multiplier * Nat.log 2 (scale i + 1) + constant

/-- A uniform logarithmic bound specializes to every individual family
member, while retaining the same constants. -/
theorem UniformLogarithmicUpperBound.pointwise
    {ι : Type*} {left right scale : ι → Nat}
    (bound : UniformLogarithmicUpperBound left right scale) (i : ι) :
    ∃ multiplier constant : Nat,
      left i ≤ right i + multiplier * Nat.log 2 (scale i + 1) + constant := by
  obtain ⟨multiplier, constant, familyBound⟩ := bound
  exact ⟨multiplier, constant, familyBound i⟩

/-- Pointwise existential constants do not imply a uniform logarithmic bound.
Every natural number is bounded by its own additive constant, but no single
constant bounds the identity family at zero scale. -/
theorem pointwiseLogarithmicBounds_do_not_imply_uniform :
    (∀ i : Nat, ∃ multiplier constant : Nat,
      i ≤ 0 + multiplier * Nat.log 2 (0 + 1) + constant) ∧
    ¬ UniformLogarithmicUpperBound
      (fun i : Nat => i) (fun _ => 0) (fun _ => 0) := by
  constructor
  · intro i
    exact ⟨0, i, by simp⟩
  · rintro ⟨multiplier, constant, bound⟩
    have impossible := bound (constant + 1)
    simp at impossible

#print axioms UniformLogarithmicUpperBound.pointwise
#print axioms pointwiseLogarithmicBounds_do_not_imply_uniform

end KolmogorovComplexity
