import Mettapedia.SetTheory.Surreal.DyadicEmbedding
import Mettapedia.SetTheory.Surreal.IntegerEmbedding

/-!
# The integers add correctly, and the two integer embeddings agree

`IntegerEmbedding.lean` reads an integer into the surreals by its sign
expansion — `n` pluses for `n` — and proves its order properties without ever
mentioning addition. `DyadicEmbedding.lean` reads `m / 2^k` as `m • ladder k`,
so at `k = 0` it reads an integer as `m • 1`.

Those are **two integer embeddings in one development**, and nothing so far
made them equal. This file proves they are, which is the coherence the lane
would otherwise be missing.

## The step that does the work

Everything reduces to

```
ofNat n + 1 = ofNat (n+1)
```

and that is proved from the cut, not from the expansion. `ofNat (n+1)` is the
simplest number above `ofNat n` with nothing above it — because `ofNat n` is
the largest number born by day `n`, so anything above it is born strictly
later. The sum `ofNat n + 1` sits in the same cut:

* its right option families are **empty**, since nothing born by day `n`
  exceeds `ofNat n` and nothing born by day `1` exceeds `1`;
* each left option `u + 1` has birthday at most `birthday u ⊕ 1 = birthday u + 1 ≤ n`,
  so it is at most `ofNat n`, hence below `ofNat (n+1)`.

The birthday step is where `naturalAdd_one_right` is used: the bound on a sum's
birthday is a natural sum, and at `1` the natural sum is the successor.

From there `ofInt m = m • 1` follows by induction over `ℤ`, and with it both
additivity of `ofInt` and the agreement of the two embeddings.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Mettapedia.SetTheory.OrdinalArithmetic

/-! ## Option families of the naturals -/

/-- **Nothing born by day `n` exceeds `ofNat n`**, so a natural has no right
options at all. -/
theorem rightOptions_ofNat_empty (n : ℕ) : rightOptions (ofNat n) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hlt, hb⟩
  rw [birthday_ofNat] at hb
  exact absurd hlt (not_lt.mpr (le_ofNat_of_birthday_le (le_of_lt hb)))

/-- And the only left option of `1` is `0`. -/
theorem leftOptions_ofNat_one_eq_zero {u : Surreal}
    (hu : u ∈ leftOptions (ofNat 1)) : u = 0 := by
  have hb : birthday u < (1 : Ordinal) := by
    have h := hu.2
    rwa [birthday_ofNat, Nat.cast_one] at h
  exact birthday_eq_zero_iff.mp (Order.lt_one_iff.mp hb)

/-- **`ofNat (n+1)` is the simplest number above `ofNat n`.** -/
theorem isCut_ofNat_succ (n : ℕ) : IsCut {ofNat n} ∅ (ofNat (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro l rfl
    exact ofNat_lt_ofNat (Nat.lt_succ_self n)
  · intro r hr
    exact hr.elim
  · intro y hy
    have hgt : ofNat n < y := hy.1 _ rfl
    rw [birthday_ofNat]
    by_contra hcon
    have hb : birthday y ≤ (n : Ordinal) := by
      have h : birthday y < ((n : ℕ) : Ordinal) + 1 := by
        have := not_le.mp hcon
        rwa [Nat.cast_succ] at this
      exact Order.le_of_lt_add_one h
    exact absurd hgt (not_lt.mpr (le_ofNat_of_birthday_le hb))

/-! ## The successor law -/

/-- **`ofNat n + 1 = ofNat (n+1)`.** -/
theorem add_ofNat_one (n : ℕ) : add (ofNat n) (ofNat 1) = ofNat (n + 1) := by
  refine (isCut_add' _ _).eq_of_between (isCut_ofNat_succ n) ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · intro p hp
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have hbu : birthday u < (n : Ordinal) := by
        have h := hu.2
        rwa [birthday_ofNat] at h
      have hb : birthday (add u (ofNat 1)) ≤ (n : Ordinal) := by
        refine le_trans (birthday_add_le _ _) ?_
        rw [birthday_ofNat, Nat.cast_one, naturalAdd_one_right]
        exact Order.add_one_le_of_lt hbu
      exact lt_of_le_of_lt (le_ofNat_of_birthday_le hb)
        (ofNat_lt_ofNat (Nat.lt_succ_self n))
    · rw [leftOptions_ofNat_one_eq_zero hu, add_zero']
      exact ofNat_lt_ofNat (Nat.lt_succ_self n)
  · intro p hp
    rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [rightOptions_ofNat_empty] at hv; exact hv.elim
    · rw [rightOptions_ofNat_empty] at hv; exact hv.elim
  · rintro l rfl
    have h : add (ofNat n) 0 < add (ofNat n) (ofNat 1) :=
      add_lt_add_left (ofNat_pos Nat.one_pos) _
    rwa [add_zero'] at h
  · intro r hr
    exact hr.elim

/-- **The naturals add.** -/
theorem ofNat_add (m n : ℕ) : add (ofNat m) (ofNat n) = ofNat (m + n) := by
  induction n with
  | zero => rw [ofNat_zero, add_zero', Nat.add_zero]
  | succ k ih =>
      rw [← add_ofNat_one k, ← add_assoc', ih, add_ofNat_one, Nat.add_assoc]

/-! ## The integers -/

/-- **The sign-expansion embedding is the integer-multiple map.**  This is the
statement that makes the two embeddings one. -/
theorem ofInt_eq_zsmul (m : ℤ) : ofInt m = m • ofNat 1 := by
  refine Int.induction_on m ?_ ?_ ?_
  · rw [ofInt_zero, zero_zsmul]
  · intro i ih
    have hstep : ofInt ((i : ℤ) + 1) = add (ofInt (i : ℤ)) (ofNat 1) := by
      rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
        ofInt_ofNat, ofInt_ofNat, add_ofNat_one]
    rw [hstep, ih, add_eq, add_zsmul, one_zsmul]
  · intro i ih
    have hstep : ofInt (-(i : ℤ) - 1) = add (ofInt (-(i : ℤ))) (-(ofNat 1)) := by
      rw [show (-(i : ℤ) - 1) = -(((i + 1 : ℕ)) : ℤ) by push_cast; ring,
        show (-(i : ℤ)) = -((i : ℕ) : ℤ) from rfl,
        ofInt_neg, ofInt_neg, ofInt_ofNat, ofInt_ofNat, ← add_ofNat_one i, neg_add]
    rw [hstep, ih, add_eq, sub_zsmul, one_zsmul]

/-- **The integers add.** -/
theorem ofInt_add (m n : ℤ) : add (ofInt m) (ofInt n) = ofInt (m + n) := by
  rw [ofInt_eq_zsmul, ofInt_eq_zsmul, ofInt_eq_zsmul, add_eq, add_zsmul]

theorem ofInt_sub (m n : ℤ) : ofInt (m - n) = ofInt m - ofInt n := by
  rw [ofInt_eq_zsmul, ofInt_eq_zsmul, ofInt_eq_zsmul, sub_zsmul]
  abel

/-! ## The two embeddings agree -/

/-- **The dyadic interpretation restricted to the integers is the
sign-expansion embedding.**  Without this the lane would carry two unrelated
integer embeddings. -/
theorem toSurreal_ofPair_zero (m : ℤ) :
    toSurreal (Algebra.Order.Dyadic.ofPair m 0) = ofInt m := by
  rw [toSurreal_ofPair, ofPairSurreal, ladder_zero, ← ofInt_eq_zsmul]

theorem ofPairSurreal_zero_exp (m : ℤ) : ofPairSurreal m 0 = ofInt m := by
  rw [ofPairSurreal, ladder_zero, ← ofInt_eq_zsmul]

/-! ## Controls -/

namespace IntegerArithmeticControls

/-- The successor law at a number that is neither `0` nor `1`. -/
theorem two_eq_one_add_one : add (ofNat 1) (ofNat 1) = ofNat 2 := add_ofNat_one 1

/-- Addition of naturals at genuinely different arguments. -/
theorem two_add_three : add (ofNat 2) (ofNat 3) = ofNat 5 := ofNat_add 2 3

/-- Negative integers too. -/
theorem neg_two_add_three : add (ofInt (-2)) (ofInt 3) = ofInt 1 := by
  rw [ofInt_add]; norm_num

/-- **Negative control**: the embedding is not constant — distinct integers
land on distinct surreals, so additivity is not holding by collapse. -/
theorem two_ne_three : ofInt 2 ≠ ofInt 3 :=
  ne_of_lt (ofInt_lt_ofInt.mpr (by decide))

/-- **Negative control**: `2 + 3` is not `4`, so the addition law is computing
rather than absorbing. -/
theorem two_add_three_ne_four : add (ofNat 2) (ofNat 3) ≠ ofNat 4 := by
  rw [ofNat_add]
  exact ne_of_gt (ofNat_lt_ofNat (by decide))

/-- The agreement of the two embeddings, at a value with both a sign-expansion
description and a multiple description. -/
theorem embeddings_agree_at_three :
    toSurreal (Algebra.Order.Dyadic.ofPair 3 0) = ofInt 3 :=
  toSurreal_ofPair_zero 3

end IntegerArithmeticControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_ofNat_one
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofInt_eq_zsmul
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.toSurreal_ofPair_zero
