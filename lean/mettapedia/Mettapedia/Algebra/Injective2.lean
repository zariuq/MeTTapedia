import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic

/-!
# Joint injectivity and two-sided units

Elementary consequences of Mathlib's `Function.Injective2` for binary
operations with a two-sided unit.
-/

namespace Mettapedia.Algebra

/-- A jointly injective binary operation with a two-sided unit has a
subsingleton carrier, and every binary operation on a subsingleton carrier is
jointly injective. -/
theorem injective2_iff_subsingleton_of_twoSidedUnit
    {α : Type*} (operation : α → α → α) (unit : α)
    (leftUnit : ∀ value, operation unit value = value)
    (rightUnit : ∀ value, operation value unit = value) :
    Function.Injective2 operation ↔ Subsingleton α := by
  constructor
  · intro injective
    constructor
    intro left right
    have leftEq : unit = left ∧ left = unit := by
      apply injective
      rw [leftUnit, rightUnit]
    have rightEq : unit = right ∧ right = unit := by
      apply injective
      rw [leftUnit, rightUnit]
    exact leftEq.2.trans rightEq.1
  · intro subsingleton left₁ left₂ right₁ right₂ _
    exact ⟨subsingleton.elim _ _, subsingleton.elim _ _⟩

/-- Joint injectivity of monoid multiplication is equivalent to the carrier
being a subsingleton. -/
theorem mul_injective2_iff_subsingleton {M : Type*} [Monoid M] :
    Function.Injective2 (fun left right : M => left * right) ↔
      Subsingleton M :=
  injective2_iff_subsingleton_of_twoSidedUnit
    (fun left right : M => left * right) 1 (by simp) (by simp)

/-- Joint injectivity of additive-monoid addition is equivalent to the carrier
being a subsingleton. -/
theorem add_injective2_iff_subsingleton {A : Type*} [AddMonoid A] :
    Function.Injective2 (fun left right : A => left + right) ↔
      Subsingleton A :=
  injective2_iff_subsingleton_of_twoSidedUnit
    (fun left right : A => left + right) 0 (by simp) (by simp)

end Mettapedia.Algebra
