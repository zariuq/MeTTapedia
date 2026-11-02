import Mettapedia.Data.Nat.DoublingDivisionStep

/-! Exact arithmetic controls distinguish the divisor, quotient and
remainder, including values beyond machine-word multiplication precision.
-/

set_option autoImplicit false

namespace Mettapedia.Data.Nat.DoublingDivision

example : run 27 4 = (6, 3) := by decide +kernel
example : run 27 4 ≠ (6, 2) := by decide +kernel
example : run 27 4 ≠ (7, 3) := by decide +kernel
example : run 16 16 = (1, 0) := by decide +kernel
example : run 0 16 = (0, 0) := by decide +kernel
example : run (2 ^ 63 + 7) 16 = ((2 ^ 63 + 7) / 16, (2 ^ 63 + 7) % 16) :=
  exact_result _ _ (by decide)
example (number divisor : Nat) (positive : 0 < divisor) : (run number divisor).2 < divisor :=
  (invariant number divisor positive).2

end Mettapedia.Data.Nat.DoublingDivision
