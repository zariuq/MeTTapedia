import Mettapedia.Languages.OCaml.IntegerWrapAlgorithm

/-! Signed boundary controls exercise the exact 63-bit OCaml profile.
Magnitude wrapping and signed modular wrapping agree at every integer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

example : magnitudeWrap (2 ^ 62 - 1) = 2 ^ 62 - 1 := by decide +kernel
example : magnitudeWrap (2 ^ 62) = -(2 ^ 62) := by decide +kernel
example : magnitudeWrap (2 ^ 63) = 0 := by decide +kernel
example : magnitudeWrap (-(2 ^ 62) - 1) = 2 ^ 62 - 1 := by decide +kernel
example : magnitudeWrap (-(2 ^ 63)) = 0 := by decide +kernel
example : magnitudeWrap (2 ^ 62) ≠ 2 ^ 62 := by decide +kernel
example : magnitudeWrap (-1) ≠ 1 := by decide +kernel

theorem magnitudeWrap_bounds (number : Int) :
    -integerHalf ≤ magnitudeWrap number ∧ magnitudeWrap number < integerHalf := by
  rw [magnitudeWrap_eq_wrapInteger]
  exact wrapInteger_bounds number

#print axioms magnitudeWrap_bounds

end Mettapedia.Languages.OCaml
