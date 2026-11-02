import Mettapedia.Languages.OCaml.Primitives

/-! Sign-and-magnitude recovery agrees with the source model's truncating
integer quotient and remainder. Wrapping remains the primitive's separate
postprocessing policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def magnitudeQuotient (left right : Int) : Int :=
  let quotient : Int := left.natAbs / right.natAbs
  if decide (left < 0) = decide (right < 0) then quotient else -quotient

def magnitudeRemainder (left right : Int) : Int :=
  let remainder : Int := left.natAbs % right.natAbs
  if left < 0 then -remainder else remainder

theorem magnitudeQuotient_eq_tdiv (left right : Int) : magnitudeQuotient left right = left.tdiv right := by
  cases left <;> cases right <;>
    dsimp [magnitudeQuotient, Int.tdiv, Int.natAbs] <;>
    simp only [not_lt_of_ge (Int.natCast_nonneg _), Int.negSucc_lt_zero,
      decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]

theorem magnitudeRemainder_eq_tmod (left right : Int) : magnitudeRemainder left right = left.tmod right := by
  cases left <;> cases right <;>
    dsimp [magnitudeRemainder, Int.tmod, Int.natAbs] <;>
    simp only [not_lt_of_ge (Int.natCast_nonneg _), Int.negSucc_lt_zero, if_true, if_false]

example : magnitudeQuotient (-7) 3 = -2 := by decide +kernel
example : magnitudeRemainder (-7) 3 = -1 := by decide +kernel
example : magnitudeQuotient 7 (-3) = -2 := by decide +kernel
example : magnitudeRemainder 7 (-3) = 1 := by decide +kernel
example : magnitudeRemainder (-7) 3 ≠ 2 := by decide +kernel

#print axioms magnitudeQuotient_eq_tdiv
#print axioms magnitudeRemainder_eq_tmod

end Mettapedia.Languages.OCaml
