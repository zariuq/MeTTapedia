import Mettapedia.SetTheory.Surreal.CutConstruction

/-!
# Strict inequality is always witnessed by an option

A number is the simplest thing strictly between its own options, so a strict
inequality between two numbers cannot be an accident of the order: one side's
options must already show it.

```
a < b  ↔  (∃ l ∈ leftOptions b,  a ≤ l) ∨ (∃ r ∈ rightOptions a, r ≤ b)
```

Either `b` has an earlier left option that `a` fails to exceed, or `a` has an
earlier right option that does not exceed `b`. This is the form Conway's
arguments actually consume: it converts a comparison between two arbitrary
numbers into a comparison involving something born strictly earlier, which is
what lets an induction proceed.

It is a direct consequence of the cut characterisation — a number is the cut of
its canonical options, and the cut comparison criterion says when one cut lies
below another. Nothing about addition is involved.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-- **Strictness is witnessed by an option.**  The right-to-left direction is
immediate; the left-to-right direction is the cut comparison criterion applied
to the two numbers' own canonical options. -/
theorem lt_iff_exists_option {a b : Surreal} :
    a < b ↔ (∃ l ∈ leftOptions b, a ≤ l) ∨ (∃ r ∈ rightOptions a, r ≤ b) := by
  constructor
  · intro hab
    by_contra hcon
    push Not at hcon
    obtain ⟨hL, hR⟩ := hcon
    have hba : b ≤ a := (IsCut.le_iff (isCut_self b) (isCut_self a)).mpr ⟨hL, hR⟩
    exact absurd hab (not_lt.mpr hba)
  · rintro (⟨l, hl, hal⟩ | ⟨r, hr, hrb⟩)
    · exact lt_of_le_of_lt hal hl.1
    · exact lt_of_lt_of_le hr.1 hrb

/-- The contrapositive form, which is how the induction usually needs it: to
place `a` below `b` it is enough to produce one witnessing option. -/
theorem lt_of_le_leftOption {a b l : Surreal} (hl : l ∈ leftOptions b) (hal : a ≤ l) :
    a < b :=
  lt_iff_exists_option.mpr (Or.inl ⟨l, hl, hal⟩)

theorem lt_of_rightOption_le {a b r : Surreal} (hr : r ∈ rightOptions a) (hrb : r ≤ b) :
    a < b :=
  lt_iff_exists_option.mpr (Or.inr ⟨r, hr, hrb⟩)

/-! ## Controls -/

namespace OptionWitnessControls

/-- At `0 < 1` the witness is on the left: `0` is a left option of `1`. -/
theorem zero_lt_one_witness :
    ∃ l ∈ leftOptions (mk (dyadicPre 0)), (0 : Surreal) ≤ l := by
  refine ⟨0, ⟨dyadic_pos 0, ?_⟩, le_refl _⟩
  show birthday (0 : Surreal) < birthday (mk (dyadicPre 0))
  rw [birthday_mk, dyadicPre_length, Nat.cast_zero, zero_add]
  show (0 : Ordinal) < 1
  exact zero_lt_one

/-- `0` has no options, so when `0` is the *upper* number the witness must be
on the other side — and there is none, which is why `x < 0` needs `x` to have a
right option at or below `0`. -/
theorem nothing_below_zero_without_right_option {x : Surreal} (h : x < 0) :
    ∃ r ∈ rightOptions x, r ≤ (0 : Surreal) := by
  rcases lt_iff_exists_option.mp h with ⟨l, hl, -⟩ | hr
  · rw [CutControls.zero_leftOptions_empty] at hl
    exact absurd hl (by simp)
  · exact hr

end OptionWitnessControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.lt_iff_exists_option
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.lt_of_le_leftOption
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.lt_of_rightOption_le
