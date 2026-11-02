import Mettapedia.Languages.Maude.ConditionalMaxExpression
import Mettapedia.Languages.Maude.ConditionalMaxBounds

/-! Positive and negative observations for recursive comparison and
conditional max, including equal operands and nested expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax

#guard value? (maximum (numeral 2) (numeral 1)) == some 2
#guard value? (maximum (numeral 1) (numeral 3)) == some 3
#guard value? (maximum (numeral 2) (numeral 2)) == some 2
#guard value? (maximum (maximum (numeral 1) (numeral 2)) (numeral 3)) == some 3
#guard value? (.var "N") == none
#guard value? truth == none
#guard successorCount (maximum (numeral 2) (numeral 1)) == 3

theorem standard_source_result : Equivalent Examples.conditional [] "Nat"
    (maximum (numeral 2) (numeral 1)) (numeral 2) := maximum_left 2 1 (by decide)

theorem equal_operands_result : Equivalent Examples.conditional [] "Nat"
    (maximum (numeral 2) (numeral 2)) (numeral 2) := maximum_left 2 2 (by decide)

theorem false_comparison_result : Equivalent Examples.conditional [] "Bool"
    (le (numeral 3) (numeral 1)) falsehood := by
  simpa only [show ¬(3 : Nat) ≤ 1 by decide, if_false] using comparison_equivalent 3 1

#print axioms standard_source_result
#print axioms false_comparison_result

end Mettapedia.Languages.Maude.ConditionalMax
