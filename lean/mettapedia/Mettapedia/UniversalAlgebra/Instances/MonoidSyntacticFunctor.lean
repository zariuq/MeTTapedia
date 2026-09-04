import Mettapedia.UniversalAlgebra.Instances.MonoidInterpretation
import Mettapedia.UniversalAlgebra.Instances.MonoidSyntacticCategory
import Mettapedia.UniversalAlgebra.SyntacticFunctor

/-!
# The monoid-to-commutative-monoid syntactic functor

The canonical interpretation preserves all ordinary monoid equations but is
not consequence-reflecting: its syntactic functor identifies the two orders
of a binary product.  This is a concrete positive/negative control for the
distinction between an interpretation and a conservative interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Mettapedia.UniversalAlgebra

/-- `x * y` in the two-variable context. -/
def boundedMulXY : Term.Bounded signature 2 :=
  ⟨mul x y, variablesBelow_mul boundedX₂.2 boundedY₂.2⟩

/-- `y * x` in the two-variable context. -/
def boundedMulYX : Term.Bounded signature 2 :=
  ⟨mul y x, variablesBelow_mul boundedY₂.2 boundedX₂.2⟩

/-- The two multiplication orders are distinct arrows before adjoining
commutativity. -/
theorem multiplication_order_arrows_distinct :
    SyntacticCategory.termArrow equationSystem boundedMulXY ≠
      SyntacticCategory.termArrow equationSystem boundedMulYX := by
  intro arrowsEqual
  exact commutativity_not_consequence
    ((SyntacticCategory.termArrow_eq_iff equationSystem _ _).mp arrowsEqual)

/-- The target commutative system generates the translated commutativity
equation. -/
theorem translated_commutativity_consequence :
    EquationalConsequence commutativeEquationSystem
      (Equation.translate interpretationInCommutative.symbols
        (mul x y, mul y x)) := by
  have base : EquationalConsequence commutativeEquationSystem
      (mul x y, mul y x) := by
    apply EquationalConsequence.of_mem
    change (mul x y, mul y x) ∈
      equationSystem.equations ++ [(mul x y, mul y x)]
    exact List.mem_append_right _ (by simp)
  simpa only [interpretationInCommutative, Equation.translate,
    Term.translate_id] using base

/-- The induced syntactic functor identifies the two multiplication-order
arrows. -/
theorem syntacticFunctor_identifies_multiplication_orders :
    interpretationInCommutative.syntacticFunctor.map
        (SyntacticCategory.termArrow equationSystem boundedMulXY) =
      interpretationInCommutative.syntacticFunctor.map
        (SyntacticCategory.termArrow equationSystem boundedMulYX) := by
  rw [EquationSystem.Interpretation.syntacticFunctor_map_termArrow,
    EquationSystem.Interpretation.syntacticFunctor_map_termArrow]
  exact (SyntacticCategory.termArrow_eq_iff
    commutativeEquationSystem _ _).mpr translated_commutativity_consequence

/-- Negative control: the canonical monoid interpretation in commutative
monoids is not consequence-reflecting. -/
theorem interpretationInCommutative_not_consequenceReflecting :
    ¬ interpretationInCommutative.ConsequenceReflecting := by
  intro reflecting
  exact commutativity_not_consequence
    (reflecting (mul x y, mul y x) translated_commutativity_consequence)

/-- Equivalently, the induced finite-product syntactic functor is not
faithful. -/
theorem interpretationInCommutative_syntacticFunctor_not_faithful :
    ¬ interpretationInCommutative.syntacticFunctor.Faithful := by
  intro faithful
  exact interpretationInCommutative_not_consequenceReflecting
    (EquationSystem.Interpretation.consequenceReflecting_of_syntacticFunctor_faithful
        interpretationInCommutative faithful)

/-- Positive control: the functor preserves the already-derived unit
equation. -/
theorem syntacticFunctor_preserves_one_mul_mul_one :
    interpretationInCommutative.syntacticFunctor.map
        (SyntacticCategory.termArrow equationSystem boundedOneMulMulOne) =
      interpretationInCommutative.syntacticFunctor.map
        (SyntacticCategory.termArrow equationSystem boundedX) :=
  congrArg interpretationInCommutative.syntacticFunctor.map
    one_mul_mul_one_arrows_equal

end Mettapedia.UniversalAlgebra.Monoid
