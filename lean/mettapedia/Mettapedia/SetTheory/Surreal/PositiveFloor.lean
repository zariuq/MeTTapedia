import Mettapedia.SetTheory.Surreal.Negation
import Mettapedia.SetTheory.Surreal.CutConstruction
import Mathlib.Algebra.Order.SuccPred

/-!
# The smallest positive number of each birthday

One fact controls the whole dyadic interpretation: **`mk (dyadicPre k)` is the
least positive number born by day `k + 1`.** Its expansion is a single plus
followed by `k` minuses, and that is the lexicographically least positive
expansion of that length — anything smaller and still positive has to keep
going, which costs another day.

```
dyadicPre 0 = +          = 1
dyadicPre 1 = + -        = 1/2
dyadicPre 2 = + - -      = 1/4
```

`dyadicPre_le_of_pos` is that statement, and the proof is a sign comparison
with no arithmetic in it. Everything else here is a corollary, and together
they pin down the option families of the halving ladder:

* `leftOptions_dyadicPre_nonpos` — every left option of `1/2^k` is `≤ 0`,
  because a positive number younger than it would have to be at least
  `1/2^{k-1}`, which is larger;
* `rightOptions_dyadicPre_ge` — every right option of `1/2^{k+1}` is at least
  `1/2^k`, the same bound read the other way.

Those two bounds are what the sum `1/2^{k+1} + 1/2^{k+1}` needs. They matter
because the canonical option families are *every* younger number on the
correct side — infinite as sets, and not enumerable term by term — so the sum
has to be computed from bounds on them rather than from a listing.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open PreSurreal

/-! ## Opening signs -/

/-- Every sign of the zero expansion is `zero`, at every position. -/
theorem zeroPre_signAt (β : Ordinal) : zeroPre.signAt β = Sign.zero :=
  signAt_of_ge (by exact zero_le)

/-- **A positive number opens with a plus.**  Position `0` is where it must
differ from zero: agreeing with zero there would end the expansion. -/
theorem signAt_zero_of_pos {p : PreSurreal} (h : (0 : Surreal) < mk p) :
    p.signAt 0 = Sign.pos := by
  have h' : PreSurreal.Lt zeroPre p := h
  obtain ⟨β, hagree, hlt⟩ := h'
  rw [zeroPre_signAt] at hlt
  have hpos : p.signAt β = Sign.pos := by
    cases hs : p.signAt β with
    | neg => rw [hs] at hlt; exact absurd hlt (by decide)
    | zero => rw [hs] at hlt; exact absurd hlt (by decide)
    | pos => rfl
  rcases eq_or_ne β 0 with rfl | hβ
  · exact hpos
  · have h0 := hagree 0 (lt_of_le_of_ne (by exact zero_le) (Ne.symm hβ))
    rw [zeroPre_signAt] at h0
    have hlen : p.length ≤ 0 := signAt_eq_zero_iff.mp h0.symm
    rw [signAt_of_ge (hlen.trans (by exact zero_le))] at hpos
    exact absurd hpos (by decide)

/-- **Only `0` is born on day zero.** -/
theorem birthday_eq_zero_iff {z : Surreal} : birthday z = 0 ↔ z = 0 := by
  induction z using Quotient.inductionOn with
  | h p =>
    refine ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
    have hlen : p.length = 0 := h
    refine mk_eq_mk.mpr ?_
    funext β
    rw [signAt_of_ge (by rw [hlen]; exact zero_le), zeroPre_signAt]

/-! ## The floor -/

/-- **`mk (dyadicPre k)` is the least positive number born by day `k + 1`.**

Suppose some positive `z` of birthday at most `k + 1` were smaller, and look
at the first position where the two expansions differ.

* At position `0` both are a plus, since `z` is positive.
* Between `1` and `k` the ladder point has a minus, and nothing is below a
  minus.
* At `k + 1` or beyond the ladder point has run out, so `z` would need a minus
  there — which means `z` is still going at position `k + 1`, contradicting
  its birthday.
-/
theorem dyadicPre_le_of_pos {z : Surreal} {k : ℕ} (hz : 0 < z)
    (hb : birthday z ≤ (k : Ordinal) + 1) : mk (dyadicPre k) ≤ z := by
  induction z using Quotient.inductionOn with
  | h p =>
    refine le_of_not_gt ?_
    rintro ⟨β, hagree, hlt⟩
    have hp0 : p.signAt 0 = Sign.pos := signAt_zero_of_pos hz
    rcases eq_or_ne β 0 with rfl | hβ
    · rw [hp0, dyadicPre_signAt_zero] at hlt
      exact absurd hlt (by decide)
    · rcases lt_or_ge β ((k : Ordinal) + 1) with hsmall | hbig
      · rw [dyadicPre_signAt_pos_lt hβ hsmall] at hlt
        cases hs : p.signAt β <;> rw [hs] at hlt <;> exact absurd hlt (by decide)
      · rw [dyadicPre_signAt_ge hbig] at hlt
        have hne : p.signAt β ≠ Sign.zero := by
          intro hz'; rw [hz'] at hlt; exact absurd hlt (by decide)
        have hβlen : β < p.length := by
          by_contra hcon
          exact hne (signAt_of_ge (not_lt.mp hcon))
        exact absurd (lt_of_lt_of_le hβlen hb) (not_lt.mpr hbig)

/-- Dually, `-mk (dyadicPre k)` is the greatest negative number born that
early. -/
theorem le_neg_dyadicPre_of_neg {z : Surreal} {k : ℕ} (hz : z < 0)
    (hb : birthday z ≤ (k : Ordinal) + 1) : z ≤ -mk (dyadicPre k) := by
  have hpos : 0 < -z := by rw [← neg_zero']; exact neg_lt_neg_iff.mpr hz
  have h := dyadicPre_le_of_pos (z := -z) hpos (by rwa [birthday_neg])
  refine le_of_not_gt (fun hgt => ?_)
  rw [← neg_neg' z] at hgt
  exact absurd (neg_lt_neg_iff.mp hgt) (not_lt.mpr h)

/-- Dually to `le_ofNat_of_birthday_le`: `-ofNat n` is the smallest number born
by day `n`. -/
theorem neg_ofNat_le_of_birthday_le {z : Surreal} {n : ℕ}
    (hb : birthday z ≤ (n : Ordinal)) : -(ofNat n) ≤ z := by
  have h : -z ≤ ofNat n := le_ofNat_of_birthday_le (by rwa [birthday_neg])
  refine le_of_not_gt (fun hgt => ?_)
  rw [← neg_neg' z] at hgt
  exact absurd (neg_lt_neg_iff.mp hgt) (not_lt.mpr h)

/-! ## The option families of the ladder -/

/-- **Every left option of `1/2^k` is at most `0`.**  A positive one would be a
positive number born by day `k`, hence at least `1/2^{k-1}` — which is bigger
than `1/2^k`, not smaller. -/
theorem leftOptions_dyadicPre_nonpos {k : ℕ} {u : Surreal}
    (hu : u ∈ leftOptions (mk (dyadicPre k))) : u ≤ 0 := by
  have hb : birthday u ≤ (k : Ordinal) := by
    have h := hu.2
    rw [birthday_mk, dyadicPre_length] at h
    exact Order.le_of_lt_add_one h
  cases k with
  | zero =>
      rw [Nat.cast_zero] at hb
      rw [birthday_eq_zero_iff.mp (le_antisymm hb (by exact zero_le))]
  | succ j =>
      refine le_of_not_gt (fun hpos => ?_)
      have hj : birthday u ≤ (j : Ordinal) + 1 := by
        rw [Nat.cast_succ] at hb; exact hb
      exact absurd (lt_of_le_of_lt (dyadicPre_le_of_pos hpos hj) hu.1)
        (not_lt.mpr (le_of_lt (dyadic_anti j)))

/-- **Every right option of `1/2^{k+1}` is at least `1/2^k`.** -/
theorem rightOptions_dyadicPre_ge {k : ℕ} {v : Surreal}
    (hv : v ∈ rightOptions (mk (dyadicPre (k + 1)))) : mk (dyadicPre k) ≤ v := by
  have hb : birthday v ≤ (k : Ordinal) + 1 := by
    have h := hv.2
    rw [birthday_mk, dyadicPre_length] at h
    have h2 := Order.le_of_lt_add_one h
    rwa [Nat.cast_succ] at h2
  exact dyadicPre_le_of_pos (lt_trans (dyadic_pos (k + 1)) hv.1) hb

/-- At the bottom of the ladder there is nothing above: no number born by day
`0` exceeds `1`. -/
theorem rightOptions_dyadicPre_zero_empty :
    rightOptions (mk (dyadicPre 0)) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hlt, hb⟩
  rw [birthday_mk, dyadicPre_length, Nat.cast_zero, zero_add] at hb
  rw [birthday_eq_zero_iff.mp (Order.lt_one_iff.mp hb)] at hlt
  exact absurd hlt (not_lt.mpr (le_of_lt (dyadic_pos 0)))

/-! ## Controls -/

namespace PositiveFloorControls

/-- The floor is attained, not merely a bound: `1/2` *is* the least positive
number born by day two, and it is itself born then. -/
theorem half_is_least_positive_of_day_two {z : Surreal} (hz : 0 < z)
    (hb : birthday z ≤ (1 : Ordinal) + 1) : mk (dyadicPre 1) ≤ z :=
  dyadicPre_le_of_pos hz (by rwa [Nat.cast_one])

theorem half_birthday : birthday (mk (dyadicPre 1)) = (1 : Ordinal) + 1 := by
  rw [birthday_mk, dyadicPre_length, Nat.cast_one]

/-- **Negative control**: the birthday hypothesis is doing work. `1/4` is
positive and strictly below `1/2`, so without a bound the conclusion fails. -/
theorem quarter_below_half : (0 : Surreal) < mk (dyadicPre 2) ∧
    mk (dyadicPre 2) < mk (dyadicPre 1) :=
  ⟨dyadic_pos 2, dyadic_anti 1⟩

/-- **Negative control**: positivity is doing work too — `0` is born on day
zero and lies below every ladder point. -/
theorem zero_not_above_ladder : ¬ (mk (dyadicPre 0) ≤ (0 : Surreal)) :=
  not_le.mpr (dyadic_pos 0)

/-- The option bound is not vacuous: `0` really is a left option of `1/2`. -/
theorem zero_mem_leftOptions_half :
    (0 : Surreal) ∈ leftOptions (mk (dyadicPre 1)) := by
  refine ⟨dyadic_pos 1, ?_⟩
  rw [birthday_mk, dyadicPre_length]
  exact lt_of_le_of_lt (by exact zero_le) (lt_add_one _)

end PositiveFloorControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.dyadicPre_le_of_pos
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_eq_zero_iff
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.rightOptions_dyadicPre_ge
