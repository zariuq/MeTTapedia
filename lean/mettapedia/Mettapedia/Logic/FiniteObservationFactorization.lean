import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! A finite joint weight table factors exactly when every rectangular
observation has the corresponding product weight. Positivity, normalization,
and provenance labels are unnecessary for this algebraic characterization;
they are separate requirements of a probabilistic realization. -/

set_option autoImplicit false

namespace Mettapedia.Logic.FiniteObservationFactorization

open scoped BigOperators

variable {A B R : Type*} [CommSemiring R]

theorem factorization_iff_rectangles (joint : A → B → R) (left : A → R) (right : B → R) :
    (∀ a b, joint a b = left a * right b) ↔
      ∀ first : Finset A, ∀ second : Finset B,
        (∑ a ∈ first, ∑ b ∈ second, joint a b) = (∑ a ∈ first, left a) * (∑ b ∈ second, right b) := by
  constructor
  · intro factors first second
    simp only [factors]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro atom member
    rw [Finset.mul_sum]
  · intro rectangles a b
    simpa using rectangles {a} {b}

/-- One common latent bit, with perfect correlation. -/
def correlated (first second : Bool) : Rat := if first = second then 1 / 2 else 0
def fair (_ : Bool) : Rat := 1 / 2

theorem correlated_marginals :
    (∀ first : Bool, correlated first false + correlated first true = fair first) ∧
    (∀ second : Bool, correlated false second + correlated true second = fair second) := by
  constructor <;> intro bit <;> cases bit <;> norm_num [correlated, fair]

theorem marginal_agreement_does_not_license_multiplication :
    correlated true true = 1 / 2 ∧ fair true * fair true = 1 / 4 ∧
      correlated true true ≠ fair true * fair true := by
  norm_num [correlated, fair]

end Mettapedia.Logic.FiniteObservationFactorization
