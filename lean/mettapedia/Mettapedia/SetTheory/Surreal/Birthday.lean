import Mettapedia.SetTheory.Surreal.SignExpansion
import Mathlib.Data.Nat.Size

/-!
# Birthday is position in the construction, not size and not description length

The level of a sign expansion is its *birthday*: the stage at which the number
first appears.  It is tempting — I made this mistake — to read it as a measure
of how complicated the number is, and so to identify it with description
length.  It is neither.

This file exhibits the dyadic family `1/2ᵏ`, whose expansion is a `+` followed
by `k` copies of `−`, and proves:

* `dyadicPre_length` — its birthday is exactly `k + 1`, so it grows without
  bound;
* `dyadic_anti` — the family is strictly decreasing, so its members are
  pairwise distinct;
* `dyadic_pos` and `dyadic_le_one` — they all lie in `(0, 1]`.

Together: **unboundedly large birthdays inside a bounded interval**.  Birthday
is not a size.

And against description length directly: the index `k` is written in
`Nat.size k` bits, so the family `1/2^(2ᵐ)` has descriptions of length about
`m` and birthdays about `2ᵐ`.  `birthday_exceeds_description_unboundedly`
states the gap and proves it unbounded, which is the counterexample to the
identification.

(What birthday *does* measure is where a number sits in the order of
construction, and `signAt` is exactly the record of the left/right choices made
to get there.)
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

open PreSurreal

namespace Surreal

/-! ## The dyadic family -/

/-- `1/2ᵏ`: a `+` at position `0`, then `k` copies of `−`. -/
noncomputable def dyadicPre (k : ℕ) : PreSurreal :=
  ⟨(k : Ordinal) + 1, fun β => decide (β = 0)⟩

@[simp] theorem dyadicPre_length (k : ℕ) :
    (dyadicPre k).length = (k : Ordinal) + 1 := rfl

theorem dyadicPre_signAt_zero (k : ℕ) : (dyadicPre k).signAt 0 = Sign.pos := by
  have h : (0 : Ordinal) < (dyadicPre k).length := by
    rw [dyadicPre_length]
    exact lt_of_le_of_lt zero_le (lt_add_one _)
  rw [PreSurreal.signAt_of_lt h]
  simp [dyadicPre]

theorem dyadicPre_signAt_pos_lt {k : ℕ} {β : Ordinal} (h0 : β ≠ 0)
    (h : β < (k : Ordinal) + 1) : (dyadicPre k).signAt β = Sign.neg := by
  have hlt : β < (dyadicPre k).length := by rwa [dyadicPre_length]
  rw [PreSurreal.signAt_of_lt hlt]
  simp [dyadicPre, h0]

theorem dyadicPre_signAt_ge {k : ℕ} {β : Ordinal} (h : (k : Ordinal) + 1 ≤ β) :
    (dyadicPre k).signAt β = Sign.zero :=
  PreSurreal.signAt_of_ge (by rwa [dyadicPre_length])

/-! ## The family is strictly decreasing

`1/2^(k+1)` and `1/2^k` agree for the first `k+1` positions.  At position
`k+1` the shorter one has run out — the middle sign — while the longer one
continues with `−`, and `neg < zero`. -/

theorem dyadicPre_lt_succ (k : ℕ) :
    PreSurreal.Lt (dyadicPre (k + 1)) (dyadicPre k) := by
  refine ⟨(k : Ordinal) + 1, ?_, ?_⟩
  · intro γ hγ
    rcases eq_or_ne γ 0 with rfl | h0
    · rw [dyadicPre_signAt_zero, dyadicPre_signAt_zero]
    · have hk1 : γ < ((k + 1 : ℕ) : Ordinal) + 1 := by
        refine hγ.trans ?_
        push_cast
        exact lt_add_one _
      rw [dyadicPre_signAt_pos_lt h0 hk1, dyadicPre_signAt_pos_lt h0 hγ]
  · have hne : ((k : Ordinal) + 1) ≠ 0 :=
      ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))
    have hlt : ((k : Ordinal) + 1) < ((k + 1 : ℕ) : Ordinal) + 1 := by
      push_cast
      exact lt_add_one _
    rw [dyadicPre_signAt_pos_lt hne hlt, dyadicPre_signAt_ge (le_refl _)]
    exact Sign.neg_lt_zero

/-- **Strictly decreasing**, hence pairwise distinct. -/
theorem dyadic_anti (k : ℕ) : mk (dyadicPre (k + 1)) < mk (dyadicPre k) :=
  dyadicPre_lt_succ k

theorem dyadic_strictAnti : StrictAnti (fun k : ℕ => mk (dyadicPre k)) :=
  strictAnti_nat_of_succ_lt dyadic_anti

theorem dyadic_injective : Function.Injective (fun k : ℕ => mk (dyadicPre k)) :=
  dyadic_strictAnti.injective

/-! ## And all of it lives in `(0, 1]` -/

theorem dyadic_pos (k : ℕ) : (0 : Surreal) < mk (dyadicPre k) := by
  refine ⟨0, ?_, ?_⟩
  · intro γ hγ
    exact absurd hγ (by simp)
  · rw [dyadicPre_signAt_zero]
    show zeroPre.signAt 0 < Sign.pos
    rw [PreSurreal.signAt_of_ge (by simp [zeroPre])]
    exact Sign.zero_lt_pos

/-- **`dyadicPre 0` denotes `1`**: one `+`, and nothing after.  They are not
the same *expansion* — `natPre 1` records `+` everywhere and `dyadicPre 0`
records `+` only at `0` — but past the level the recorded signs are invisible,
so they denote the same surreal. -/
theorem dyadicPre_zero_equiv_one : PreSurreal.Equiv (dyadicPre 0) (natPre 1) := by
  funext β
  rcases eq_or_ne β 0 with rfl | h0
  · rw [dyadicPre_signAt_zero, natPre_signAt_of_lt (by simp)]
  · have hβ : (1 : Ordinal) ≤ β := Order.one_le_iff_ne_zero.mpr h0
    rw [dyadicPre_signAt_ge (by simpa using hβ), natPre_signAt_of_ge (by simpa using hβ)]

theorem dyadic_zero_eq_one : mk (dyadicPre 0) = ofNat 1 :=
  Quotient.sound dyadicPre_zero_equiv_one

theorem dyadic_le_one (k : ℕ) : mk (dyadicPre k) ≤ mk (dyadicPre 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_refl _
  · exact le_of_lt (dyadic_strictAnti hk)

/-! ## Unbounded birthday inside a bounded interval -/

/-- **Birthday is not a size.**  For every bound there is a surreal past that
bound in birthday which still lies in `(0, 1]`. -/
theorem birthday_unbounded_in_unit_interval (N : ℕ) :
    ∃ x : PreSurreal, (N : Ordinal) < x.length ∧
      (0 : Surreal) < mk x ∧ mk x ≤ mk (dyadicPre 0) :=
  ⟨dyadicPre N, by rw [dyadicPre_length]; exact lt_add_one _,
    dyadic_pos N, dyadic_le_one N⟩

/-! ## Birthday is not description length

The index `k` is written in `Nat.size k` bits, and the birthday of the `k`-th
dyadic is `k + 1`.  The two are unboundedly far apart, so no reading of
"description length" that is bounded by the index's own length can equal
birthday. -/

theorem add_lt_two_pow (N : ℕ) : N + N + 2 < 2 ^ (N + 2) := by
  have h : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (N + 2) = 4 * 2 ^ N := by
    rw [pow_add]
    exact Nat.mul_comm _ _
  have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  omega

/-- **The gap between birthday and description length is unbounded.**  Taking
`k = 2^(N+2)`, the index needs at most `N + 3` bits while the birthday is
`k + 1`, and the difference exceeds `N`. -/
theorem birthday_exceeds_description_unboundedly (N : ℕ) :
    ∃ k : ℕ, Nat.size k + N < k + 1 ∧ (dyadicPre k).length = (k : Ordinal) + 1 := by
  refine ⟨2 ^ (N + 2), ?_, dyadicPre_length _⟩
  have hsize : Nat.size (2 ^ (N + 2)) = N + 3 := by
    rw [Nat.size_pow]
  have hbig : N + N + 2 < 2 ^ (N + 2) := add_lt_two_pow N
  omega

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.dyadic_anti
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.dyadic_injective
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.dyadic_pos
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_unbounded_in_unit_interval
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_exceeds_description_unboundedly
