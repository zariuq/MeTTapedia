import Mettapedia.SetTheory.Surreal.AdditionOrder

/-!
# Additive inverses

`x + (-x) = 0`, by induction on the birthday of `x`.

The argument is short now that monotonicity is available. `x + (-x)` is the
simplest number strictly between its options, so it is enough to show that `0`
is too — and then the uniqueness of cuts finishes it.

Each option of `x + (-x)` is compared with a *smaller* instance of the same
theorem. A left option is either `xᴸ + (-x)` or `x + (-xᴿ)`, and

```
xᴸ + (-x)  <  xᴸ + (-xᴸ)  =  0          since  -x < -xᴸ
x + (-xᴿ)  <  xᴿ + (-xᴿ)  =  0          since   x <  xᴿ
```

where each equality is the induction hypothesis at an option, which is younger.
Right options are the mirror image. That `0` is the *simplest* separator needs
nothing at all: no number is born earlier than `0`.

Note what is **not** used: no cancellation, no associativity, and no appeal to
`x + (-x)` being anything in particular. The inverse law comes before the
monoid laws here, not after.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-- **Every number has an additive inverse, and it is its negation.** -/
theorem add_neg_self (x : Surreal) : add x (-x) = 0 := by
  refine (InvImage.wf birthday wellFounded_lt).induction
    (C := fun z : Surreal => add z (-z) = 0) x ?_
  clear x
  intro x ih
  refine (isCut_add' x (-x)).unique ⟨?_, ?_, fun y _ => CutControls.zero_is_simplest y⟩
  · -- Every left option of `x + (-x)` is negative.
    intro p hp
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hstep : add u (-x) < add u (-u) :=
        add_lt_add_left (neg_lt_neg_iff.mpr hu.1) u
      rwa [ih u hu.2] at hstep
    · rw [leftOptions_neg] at hu
      obtain ⟨r, hr, rfl⟩ := hu
      have hstep : add x (-r) < add r (-r) := add_lt_add_right hr.1 (-r)
      rwa [ih r hr.2] at hstep
  · -- And every right option is positive.
    intro p hp
    rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hstep : add v (-v) < add v (-x) :=
        add_lt_add_left (neg_lt_neg_iff.mpr hv.1) v
      rwa [ih v hv.2] at hstep
    · rw [rightOptions_neg] at hv
      obtain ⟨l, hl, rfl⟩ := hv
      have hstep : add l (-l) < add x (-l) := add_lt_add_right hl.1 (-l)
      rwa [ih l hl.2] at hstep

theorem neg_add_self (x : Surreal) : add (-x) x = 0 := by
  rw [add_comm']; exact add_neg_self x

/-- **Negation is determined by the sum**, so the inverse is unique — a
consequence of cancellation rather than a second construction. -/
theorem neg_eq_of_add_eq_zero {x y : Surreal} (h : add x y = 0) : y = -x := by
  refine add_left_cancel (c := x) ?_
  rw [h, add_neg_self]

theorem add_eq_zero_iff {x y : Surreal} : add x y = 0 ↔ y = -x := by
  refine ⟨neg_eq_of_add_eq_zero, ?_⟩
  rintro rfl
  exact add_neg_self x

/-! ## Subtraction -/

/-- Difference, written out rather than derived, so the order laws below do not
depend on the group instance that has not been assembled yet. -/
noncomputable def sub (x y : Surreal) : Surreal := add x (-y)

theorem sub_self (x : Surreal) : sub x x = 0 := add_neg_self x

theorem sub_eq_zero_iff {x y : Surreal} : sub x y = 0 ↔ x = y := by
  rw [sub, add_eq_zero_iff]
  refine ⟨fun h => ?_, ?_⟩
  · simpa using (congrArg (fun z : Surreal => -z) h).symm
  · rintro rfl
    rfl

/-- **Sign of a difference reads off the order.**  This is the form the dyadic
comparison will want. -/
theorem sub_pos_iff {x y : Surreal} : 0 < sub x y ↔ y < x := by
  rw [sub, ← add_neg_self y, add_comm' y (-y), add_comm' x (-y)]
  exact add_lt_add_left_iff

theorem sub_neg_iff {x y : Surreal} : sub x y < 0 ↔ x < y := by
  rw [sub, ← add_neg_self y, add_comm' y (-y), add_comm' x (-y)]
  exact add_lt_add_left_iff

/-! ## Controls -/

namespace AdditiveInverseControls

/-- The inverse law at a number with options on both sides, rather than only at
`0` where it would be vacuous. -/
theorem half_add_neg_half : add (mk (dyadicPre 1)) (-(mk (dyadicPre 1))) = 0 :=
  add_neg_self _

/-- **Negative control**: `x + (-y)` is not zero when the two differ, so the
law is about the actual inverse and not about addition collapsing. -/
theorem half_add_neg_zero_ne_zero :
    add (mk (dyadicPre 1)) (-(0 : Surreal)) ≠ 0 := by
  rw [neg_zero', add_zero']
  exact ne_of_gt (dyadic_pos 1)

/-- **Negative control**: the difference of distinct numbers is nonzero, and it
carries the right sign. -/
theorem half_sub_zero_pos : 0 < sub (mk (dyadicPre 1)) 0 :=
  sub_pos_iff.mpr (dyadic_pos 1)

theorem zero_sub_half_neg : sub 0 (mk (dyadicPre 1)) < 0 :=
  sub_neg_iff.mpr (dyadic_pos 1)

end AdditiveInverseControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_neg_self
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.neg_eq_of_add_eq_zero
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.sub_pos_iff
