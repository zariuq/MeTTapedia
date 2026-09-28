import Mettapedia.SetTheory.Surreal.FiniteDay

/-!
# Bracket facts

A number `c` of finite birthday is pinned between its greatest left option `a`
and its least right option `b` — when those exist. This file records what such
a bracket forces about the brackets of `a` and `b` themselves, which is what
the doubling induction consumes.

Two facts do all the work, and both are proved by asking where a candidate
sits relative to `c`:

* `leftBound_le_of_bracket` — the greatest left option of `b` is at most `a`.
  It is younger than `c`, so if it were in `(a, c)` it would beat `a`, and if
  it were in `(c, b)` it would beat `b`.
* `le_rightBound_of_bracket` — dually, the least right option of `a` is at
  least `b`.

The integer edge cases need their own bounds, because `ofNat k` has no right
options at all: `ofNat_succ_le_of_lt` says `ofNat (k+1)` is the least number
above `ofNat k` born by day `k+1`, which is what replaces the missing option.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-! ## Integer bounds -/

/-- Every left option of `ofNat (k+1)` is at most `ofNat k`. -/
theorem leftOptions_ofNat_succ_le {k : ℕ} {u : Surreal}
    (hu : u ∈ leftOptions (ofNat (k + 1))) : u ≤ ofNat k := by
  refine le_ofNat_of_birthday_le ?_
  have h := hu.2
  rw [birthday_ofNat, Nat.cast_succ] at h
  exact Order.le_of_lt_add_one h

/-- **`ofNat (k+1)` is the least number above `ofNat k` born by day `k+1`.**
Anything strictly between would have a younger number above `ofNat k`. -/
theorem ofNat_succ_le_of_lt {k : ℕ} {z : Surreal} (hlt : ofNat k < z)
    (hb : birthday z ≤ ((k + 1 : ℕ) : Ordinal)) : ofNat (k + 1) ≤ z := by
  by_contra hcon
  have hzlt : z < ofNat (k + 1) := not_le.mp hcon
  have hge : ((k + 1 : ℕ) : Ordinal) ≤ birthday z := by
    have h := (isCut_ofNat_succ k).simplest z
      ⟨fun l hl => by rw [Set.mem_singleton_iff] at hl; rw [hl]; exact hlt,
       fun r hr => hr.elim⟩
    rwa [birthday_ofNat] at h
  have hbz : birthday z = birthday (ofNat (k + 1)) := by
    rw [birthday_ofNat]; exact le_antisymm hb hge
  obtain ⟨w, hw, hzw, _⟩ := exists_earlier_between hzlt hbz
  have hwb : birthday w ≤ (k : Ordinal) := by
    rw [birthday_ofNat, Nat.cast_succ] at hw
    exact Order.le_of_lt_add_one hw
  exact absurd (le_ofNat_of_birthday_le hwb) (not_le.mpr (lt_trans hlt hzw))

/-- Dually: every right option of `-ofNat (k+1)` is at least `-ofNat k`. -/
theorem rightOptions_neg_ofNat_succ_ge {k : ℕ} {v : Surreal}
    (hv : v ∈ rightOptions (-(ofNat (k + 1)))) : -(ofNat k) ≤ v := by
  have hb : birthday (-v) ≤ (k : Ordinal) := by
    have h := hv.2
    rw [birthday_neg, birthday_ofNat, Nat.cast_succ] at h
    rw [birthday_neg]
    exact Order.le_of_lt_add_one h
  have h := le_ofNat_of_birthday_le (x := -v) (n := k) hb
  refine le_of_not_gt (fun hgt => ?_)
  rw [← neg_neg' v] at hgt
  exact absurd (neg_lt_neg_iff.mp hgt) (not_lt.mpr h)

/-- Dually to `ofNat_succ_le_of_lt`. -/
theorem le_neg_ofNat_succ_of_lt {k : ℕ} {z : Surreal} (hlt : z < -(ofNat k))
    (hb : birthday z ≤ ((k + 1 : ℕ) : Ordinal)) : z ≤ -(ofNat (k + 1)) := by
  have hpos : ofNat k < -z := by
    rw [← neg_neg' (ofNat k)]
    exact neg_lt_neg_iff.mpr hlt
  have h := ofNat_succ_le_of_lt hpos (by rwa [birthday_neg])
  refine le_of_not_gt (fun hgt => ?_)
  rw [← neg_neg' z] at hgt
  exact absurd (neg_lt_neg_iff.mp hgt) (not_lt.mpr h)

/-! ## The bracket -/

/-- `a` is the greatest left option of `c` and `b` the least right option. -/
structure HasBracket (c a b : Surreal) : Prop where
  memLeft : a ∈ leftOptions c
  memRight : b ∈ rightOptions c
  maxLeft : ∀ u ∈ leftOptions c, u ≤ a
  minRight : ∀ v ∈ rightOptions c, b ≤ v

theorem HasBracket.lt_left {c a b : Surreal} (h : HasBracket c a b) : a < c :=
  h.memLeft.1

theorem HasBracket.lt_right {c a b : Surreal} (h : HasBracket c a b) : c < b :=
  h.memRight.1

theorem HasBracket.birthday_left {c a b : Surreal} (h : HasBracket c a b) :
    birthday a < birthday c := h.memLeft.2

theorem HasBracket.birthday_right {c a b : Surreal} (h : HasBracket c a b) :
    birthday b < birthday c := h.memRight.2

/-- **The greatest left option of `b` is at most `a`.**

It is younger than `b`, hence younger than `c`. So it cannot lie in `(a, c)` —
that would beat `a` as the greatest left option — and it cannot lie in
`(c, b)`, which would beat `b`. -/
theorem leftBound_le_of_bracket {c a b w : Surreal} (h : HasBracket c a b)
    (hw : w ∈ leftOptions b) : w ≤ a := by
  have hwb : birthday w < birthday c := lt_trans hw.2 h.birthday_right
  rcases lt_trichotomy w c with hlt | heq | hgt
  · exact h.maxLeft w ⟨hlt, hwb⟩
  · exact absurd (heq ▸ hwb) (lt_irrefl _)
  · exact absurd (h.minRight w ⟨hgt, hwb⟩) (not_le.mpr hw.1)

/-- **And the least right option of `a` is at least `b`.** -/
theorem le_rightBound_of_bracket {c a b w : Surreal} (h : HasBracket c a b)
    (hw : w ∈ rightOptions a) : b ≤ w := by
  have hwb : birthday w < birthday c := lt_trans hw.2 h.birthday_left
  rcases lt_trichotomy w c with hlt | heq | hgt
  · exact absurd (h.maxLeft w ⟨hlt, hwb⟩) (not_le.mpr hw.1)
  · exact absurd (heq ▸ hwb) (lt_irrefl _)
  · exact h.minRight w ⟨hgt, hwb⟩

/-! ## Existence -/

/-- A finite-birthday number with options on both sides has a bracket. -/
theorem exists_hasBracket {c : Surreal} (hfin : birthday c < Ordinal.omega0)
    (hl : (leftOptions c).Nonempty) (hr : (rightOptions c).Nonempty) :
    ∃ a b, HasBracket c a b := by
  obtain ⟨a, ha, hamax⟩ := exists_max_leftOptions hfin hl
  obtain ⟨b, hb, hbmin⟩ := exists_min_rightOptions hfin hr
  exact ⟨a, b, ⟨ha, hb, hamax, hbmin⟩⟩

/-! ## Controls -/

namespace OptionBoundsControls

/-- The bracket of `1/2` is `(0, 1)`, so the structure is inhabited at a
number with genuine options on both sides. -/
theorem bracket_half : HasBracket (ladder 1) 0 (mk (dyadicPre 0)) := by
  refine ⟨PositiveFloorControls.zero_mem_leftOptions_half,
    CutControls.one_mem_rightOptions_half, ?_, ?_⟩
  · exact fun u hu => leftOptions_dyadicPre_nonpos hu
  · exact fun v hv => rightOptions_dyadicPre_ge (k := 0) hv

/-- **Negative control**: `ofNat 1` has no right options, so the bracket does
not exist for every number and the integer bounds are genuinely needed. -/
theorem one_has_no_right : rightOptions (ofNat 1) = ∅ :=
  rightOptions_ofNat_empty 1

/-- **Negative control**: the integer bound is strict where it matters —
nothing born by day `k+1` sits strictly between `ofNat k` and `ofNat (k+1)`. -/
theorem nothing_between_one_two {z : Surreal} (hlt : ofNat 1 < z)
    (hb : birthday z ≤ ((2 : ℕ) : Ordinal)) : ofNat 2 ≤ z :=
  ofNat_succ_le_of_lt hlt hb

end OptionBoundsControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofNat_succ_le_of_lt
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.leftBound_le_of_bracket
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.exists_hasBracket
