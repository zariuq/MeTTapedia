import Mettapedia.SetTheory.Surreal.AddGroup

/-!
# The birthday of a sum

```
birthday (x + y)  ≤  birthday x ⊕ birthday y
```

where `⊕` is the natural (Hessenberg) sum from `SetTheory/Ordinal/NaturalSum.lean`.

`BoundedBirthday.lean` records that this bound was *not* available at that
point in the development, and why: `IsCut.birthday_le_bound` applies only to a
number known to be the cut of the families in question, and knowing the sum is
that cut was exactly what needed the boundedness. Smallness broke that circle
without mentioning the sum at all. With separation now proved, the circle is
gone — `isCut_add'` holds unconditionally — and the bound follows.

The induction is the one already set up: each option of `x + y` is a sum with
one summand replaced by a younger number, so the hypothesis applies at a
smaller `pairMeasure`, and the bound at an option is strictly below the bound
at the sum because `⊕` is strictly monotone in *both* arguments.

That last point is why the natural sum is the right bound and ordinary ordinal
addition is not. `+` on ordinals is not strictly monotone on the left —
`0 + ω = 1 + ω` — and worse, it is not commutative, while surreal addition is;
so no bound stated with `+` could be correct in both argument orders. See
`AdditionBirthdayControls.ordinal_bound_not_symmetric`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Mettapedia.SetTheory.OrdinalArithmetic

/-- **The birthday of a sum is at most the natural sum of the birthdays.** -/
theorem birthday_add_le (x y : Surreal) :
    birthday (add x y) ≤ naturalAdd (birthday x) (birthday y) := by
  refine (InvImage.wf (fun t : Surreal × Surreal => pairMeasure t.1 t.2)
      measure_wellFounded).induction
    (C := fun t : Surreal × Surreal =>
      birthday (add t.1 t.2) ≤ naturalAdd (birthday t.1) (birthday t.2)) (x, y) ?_
  clear x y
  rintro ⟨x, y⟩ ih
  simp only at ih ⊢
  refine (isCut_add' x y).birthday_le_bound ?_
  rintro p (hp | hp)
  · rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact lt_of_le_of_lt (ih (u, y) (pairMeasure_lt_pairMeasure_left hu.2))
        (naturalAdd_lt_naturalAdd_left hu.2)
    · exact lt_of_le_of_lt (ih (x, u) (pairMeasure_lt_pairMeasure_right hu.2))
        (naturalAdd_lt_naturalAdd_right hu.2)
  · rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact lt_of_le_of_lt (ih (v, y) (pairMeasure_lt_pairMeasure_left hv.2))
        (naturalAdd_lt_naturalAdd_left hv.2)
    · exact lt_of_le_of_lt (ih (x, v) (pairMeasure_lt_pairMeasure_right hv.2))
        (naturalAdd_lt_naturalAdd_right hv.2)

theorem birthday_add_le' (x y : Surreal) :
    birthday (x + y) ≤ naturalAdd (birthday x) (birthday y) :=
  birthday_add_le x y

/-- **A difference is no older than the natural sum either**, since negation
preserves birthdays exactly. -/
theorem birthday_sub_le (x y : Surreal) :
    birthday (x - y) ≤ naturalAdd (birthday x) (birthday y) := by
  have h := birthday_add_le x (-y)
  rwa [birthday_neg] at h

/-! ## Controls -/

namespace AdditionBirthdayControls

open Mettapedia.SetTheory.OrdinalArithmetic

@[simp] theorem birthday_zero : birthday (0 : Surreal) = 0 := rfl

/-- **The bound is attained**, so it is not loose to the point of being
uninformative: adding `0` changes neither side. -/
theorem bound_attained (x : Surreal) :
    birthday (add x 0) = naturalAdd (birthday x) (birthday (0 : Surreal)) := by
  rw [add_zero', birthday_zero, naturalAdd_zero_right]

/-- And it is attained at a number with options on both sides, not only at the
degenerate `0 + 0`. -/
theorem bound_attained_at_half :
    birthday (add (mk (dyadicPre 1)) 0)
      = naturalAdd (birthday (mk (dyadicPre 1))) (birthday (0 : Surreal)) :=
  bound_attained _

/-- **Negative control**: ordinary ordinal addition cannot be the bound.
Surreal addition is commutative, so any correct bound on `birthday (x + y)` is
symmetric in the two birthdays; ordinal addition is not. -/
theorem ordinal_bound_not_symmetric :
    (1 : Ordinal) + Ordinal.omega0 ≠ Ordinal.omega0 + 1 := by
  have h1 : (1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 := by
    rw [← NaturalSumControls.ordinal_add_not_strict_left, zero_add]
  rw [h1]
  exact ne_of_lt (lt_add_one _)

/-- Whereas the bound that *was* proved survives the swap, which is the
property the previous control shows ordinal addition would lack. -/
theorem bound_holds_in_both_orders (x y : Surreal) :
    birthday (add x y) ≤ naturalAdd (birthday y) (birthday x) := by
  rw [add_comm']
  exact birthday_add_le y x

end AdditionBirthdayControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_add_le
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_sub_le
