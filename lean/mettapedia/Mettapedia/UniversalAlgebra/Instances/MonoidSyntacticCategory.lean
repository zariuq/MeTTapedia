import Mettapedia.UniversalAlgebra.Instances.Monoid
import Mettapedia.UniversalAlgebra.SyntacticCategory

/-!
# Monoid controls in the finite-context syntactic category

The existing positive and negative monoid consequences become respectively
an equality and an inequality of arrows.  These controls witness that the
syntactic-category quotient neither loses generated equations nor collapses
distinct terms.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra

/-- Multiplication preserves a finite variable bound. -/
theorem variablesBelow_mul {bound : Nat} {left right : Term signature}
    (leftBounded : left.VariablesBelow bound)
    (rightBounded : right.VariablesBelow bound) :
    (mul left right).VariablesBelow bound := by
  intro position
  by_cases first : position.val = 0
  · simpa only [mul, first, if_true] using leftBounded
  · simpa only [mul, first, if_false] using rightBounded

/-- The unit term contains no variables. -/
theorem variablesBelow_one (bound : Nat) : one.VariablesBelow bound := by
  intro position
  exact Fin.elim0 position

/-- The first variable as a one-variable bounded term. -/
def boundedX : Term.Bounded signature 1 :=
  ⟨x, by simp only [x, Term.VariablesBelow]; omega⟩

/-- The positive monoid term as a one-variable bounded term. -/
def boundedOneMulMulOne : Term.Bounded signature 1 :=
  ⟨mul (mul one x) one,
    variablesBelow_mul
      (variablesBelow_mul (variablesBelow_one 1) boundedX.2)
      (variablesBelow_one 1)⟩

/-- Positive categorical control: the derived monoid equation is equality of
one-output arrows. -/
theorem one_mul_mul_one_arrows_equal :
    SyntacticCategory.termArrow equationSystem boundedOneMulMulOne =
      SyntacticCategory.termArrow equationSystem boundedX :=
  (SyntacticCategory.termArrow_eq_iff equationSystem _ _).mpr
    one_mul_mul_one

/-- The first variable as a two-variable bounded term. -/
def boundedX₂ : Term.Bounded signature 2 :=
  ⟨x, by simp only [x, Term.VariablesBelow]; omega⟩

/-- The second variable as a two-variable bounded term. -/
def boundedY₂ : Term.Bounded signature 2 :=
  ⟨y, by simp only [y, Term.VariablesBelow]; omega⟩

/-- Negative categorical control: the two variable projections remain
distinct arrows in the ordinary monoid syntactic category. -/
theorem distinct_variable_arrows :
    SyntacticCategory.termArrow equationSystem boundedX₂ ≠
      SyntacticCategory.termArrow equationSystem boundedY₂ := by
  intro arrowsEqual
  exact distinct_variables_not_consequence
    ((SyntacticCategory.termArrow_eq_iff equationSystem _ _).mp arrowsEqual)

end Mettapedia.UniversalAlgebra.Monoid
