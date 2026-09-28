import Mettapedia.Algebra.Order.Infinitesimal.NoFiniteInverse

/-!
# Multiplication and summation are different operations

`NoFiniteInverse.lean` proves that no finite level series denotes `(Ω - 1)⁻¹`.
That leaves an obvious question, and it is one worth answering rather than
leaving as an impression: the inverse *does* exist, since the carrier is a
field — so by what operation is it obtained?

Not by multiplication. It is obtained by **summation of an infinite family**,
which is a different operation with a different domain of definition, and the
distinction is visible in the upstream construction: the field instance on
Hahn series is built from `SummableFamily.powers` and
`one_sub_self_mul_hsum_powers`, not from any product of the data.

Here that is made explicit for the element at issue.

* `one_sub_omInv_mul_geometric` — `(1 - Ω⁻¹) · (Ω⁻¹ + Ω⁻² + ⋯) = 1`, the
  geometric sum, upstream's theorem applied at our infinitesimal.
* `toHahn_omegaSubOne_factors` — `Ω - 1 = Ω (1 - Ω⁻¹)`, so the element whose
  inverse escapes the representation is a unit times the geometric case.
* `inv_omegaSubOne_is_a_summation` — hence `(Ω - 1) · (Ω⁻¹ · ∑ₙ Ω⁻ⁿ) = 1`.

Put beside `toHahn_mul_omegaSubOne_ne_one`, the pair is the whole point:
the same element has an inverse reachable by summation and unreachable by
multiplying anything the representation can hold.

So a finitely represented fragment is closed under the ring operations and not
under inversion, and that is not an artefact of choosing lists — it is the
difference between a finite convolution and an infinite sum.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

/-- `Ω⁻¹`, as a plain Hahn series. -/
noncomputable def omInvSeries : HahnSeries ℤ ℚ := single (1 : ℤ) (1 : ℚ)

/-- It sits strictly above level `0`, which is what makes its powers
summable. -/
theorem omInvSeries_orderTop_pos : 0 < omInvSeries.orderTop := by
  rw [omInvSeries, orderTop_single one_ne_zero]
  exact_mod_cast Int.zero_lt_one

/-- The geometric sum `Ω⁻¹ + Ω⁻² + Ω⁻³ + ⋯`, as the value of upstream's
summable family of powers.  It is a single element of the field, but it is
**not** produced by any product: it is the sum of infinitely many terms. -/
noncomputable def geometric : HahnSeries ℤ ℚ :=
  (SummableFamily.powers omInvSeries).hsum

/-- **The geometric series inverts `1 - Ω⁻¹`** — upstream's theorem, at our
infinitesimal. -/
theorem one_sub_omInv_mul_geometric : (1 - omInvSeries) * geometric = 1 :=
  SummableFamily.one_sub_self_mul_hsum_powers omInvSeries_orderTop_pos

/-- **`Ω - 1` is `Ω` times the geometric case.**  So the element whose inverse
escapes the finite representation is not exotic: it is a unit multiple of
`1 - Ω⁻¹`. -/
theorem toHahn_omegaSubOne_factors :
    toHahn omegaSubOne = single (-1 : ℤ) (1 : ℚ) * (1 - omInvSeries) := by
  rw [toHahn_omegaSubOne, omInvSeries, mul_sub, mul_one, single_mul_single,
    show (-1 : ℤ) + 1 = 0 from by omega, mul_one, sub_eq_add_neg, ← single_neg]

/-- `Ω · Ω⁻¹ = 1`, at the level of plain series. -/
theorem single_neg_one_mul_omInvSeries :
    single (-1 : ℤ) (1 : ℚ) * omInvSeries = 1 := by
  rw [omInvSeries, single_mul_single, show (-1 : ℤ) + 1 = 0 from by omega, mul_one,
    single_zero_one]

/-- **The inverse is obtained by summation.**  `(Ω - 1) · (Ω⁻¹ · ∑ₙ Ω⁻ⁿ) = 1`. -/
theorem inv_omegaSubOne_is_a_summation :
    toHahn omegaSubOne * (omInvSeries * geometric) = 1 := by
  rw [toHahn_omegaSubOne_factors, mul_mul_mul_comm,
    single_neg_one_mul_omInvSeries, one_sub_omInv_mul_geometric, mul_one]

/-- **The audit, in one statement.**  The very same element has an inverse that
summation reaches and that no product of representable data reaches.  Field
multiplication and infinite summation are therefore not interchangeable, and a
finitely represented fragment is closed under the first only. -/
theorem multiplication_is_not_summation :
    (∀ q : LevelSeries, toHahn (mul q omegaSubOne) ≠ 1) ∧
      toHahn omegaSubOne * (omInvSeries * geometric) = 1 :=
  ⟨toHahn_mul_omegaSubOne_ne_one, inv_omegaSubOne_is_a_summation⟩

/-! ## Controls -/

namespace SummationControls

/-- The fragment *is* closed under multiplication, so the failure above is
about inversion specifically. -/
theorem representable_product (p q : LevelSeries) :
    toHahn (mul p q) = toHahn p * toHahn q := toHahn_mul p q

/-- And under addition and negation. -/
theorem representable_sum (p q : LevelSeries) :
    toHahn (add p q) = toHahn p + toHahn q := toHahn_add p q

/-- A single term *does* invert inside the fragment, so it is the *sum* in
`Ω - 1` that does the damage, not division as such. -/
theorem representable_reciprocal : toLevelField (mul omega omegaInv) = 1 :=
  omega_inverts

end SummationControls

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.one_sub_omInv_mul_geometric
#print axioms Mettapedia.Algebra.Order.Infinitesimal.inv_omegaSubOne_is_a_summation
#print axioms Mettapedia.Algebra.Order.Infinitesimal.multiplication_is_not_summation
