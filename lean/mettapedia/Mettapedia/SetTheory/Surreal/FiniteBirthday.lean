import Mettapedia.SetTheory.Surreal.Doubling

/-!
# Finite-birthday surreals are precisely the represented dyadics

```
birthday x < ω   ↔   ∃ d : Dyadic, toSurreal d = x
```

`DyadicEmbedding.lean` proved the easy inclusion: a represented dyadic is an
integer multiple of a rung, and the birthday bound keeps that finite. This
file proves the converse, which is the substance.

## The argument

By induction on `n`, every `x` with `birthday x ≤ n` is an integer multiple of
`ladder n`. The step splits on the option families of `x`:

* **no right options** — then `x = ofNat k`, and an integer is a multiple of
  every rung, since `ofNat k = k / 1 = (k · 2^n) / 2^n`;
* **no left options** — then `x = -ofNat k`, the mirror image;
* **both present** — then `x` has a bracket `(a, b)`, both members are younger
  than `x` hence multiples of `ladder n` by the induction hypothesis, and
  `double_eq_bracket_sum` gives

  ```
  x + x = a + b = (p + q) • ladder n = ((p+q) + (p+q)) • ladder (n+1)
  ```

  so `x + x = w + w` for `w = (p+q) • ladder (n+1)`. Doubling is injective in a
  linearly ordered group, so `x = w`.

No birthday of a dyadic is ever computed. The whole weight sits on the bracket
identity, which is why that theorem was worth isolating.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-! ## Two small facts -/

/-- Multiples of a fixed rung add by adding numerators. -/
theorem ofPairSurreal_add (m n : ℤ) (k : ℕ) :
    add (ofPairSurreal m k) (ofPairSurreal n k) = ofPairSurreal (m + n) k := by
  simp only [ofPairSurreal, add_eq, add_zsmul]

/-- **Doubling is injective**, because addition is strictly monotone. -/
theorem double_injective {y z : Surreal} (h : add y y = add z z) : y = z := by
  rcases lt_trichotomy y z with hlt | heq | hgt
  · exact absurd h (ne_of_lt
      (lt_trans (add_lt_add_right hlt y) (add_lt_add_left hlt z)))
  · exact heq
  · exact absurd h.symm (ne_of_lt
      (lt_trans (add_lt_add_right hgt z) (add_lt_add_left hgt y)))

/-- An integer is a multiple of every rung. -/
theorem ofNat_eq_ofPairSurreal (k n : ℕ) :
    ofNat k = ofPairSurreal ((k : ℤ) * 2 ^ n) n := by
  have h := ofPairSurreal_shift (k : ℤ) 0 n
  rw [Nat.zero_add] at h
  rw [h, ofPairSurreal_zero_exp, ofInt_ofNat]

theorem neg_ofNat_eq_ofPairSurreal (k n : ℕ) :
    -(ofNat k) = ofPairSurreal (-((k : ℤ) * 2 ^ n)) n := by
  have h := ofPairSurreal_shift (-(k : ℤ)) 0 n
  rw [Nat.zero_add] at h
  rw [show (-((k : ℤ) * 2 ^ n)) = -(k : ℤ) * 2 ^ n by ring, h,
    ofPairSurreal_zero_exp, show (-(k : ℤ)) = -((k : ℕ) : ℤ) from rfl,
    ofInt_neg, ofInt_ofNat]

/-! ## Every number born by day `n` is a multiple of the `n`-th rung -/

theorem exists_numerator : ∀ (n : ℕ) (x : Surreal), birthday x ≤ (n : Ordinal) →
    ∃ m : ℤ, x = ofPairSurreal m n
  | 0, x, hb => by
      have hx : x = 0 := birthday_eq_zero_iff.mp
        (le_antisymm (by rwa [Nat.cast_zero] at hb) (by exact zero_le))
      exact ⟨0, by rw [hx, ofPairSurreal_zero_num]⟩
  | (n + 1), x, hb => by
      have hfinx : birthday x < Ordinal.omega0 :=
        lt_of_le_of_lt hb (Ordinal.natCast_lt_omega0 _)
      obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp hfinx
      by_cases hl : (leftOptions x).Nonempty
      · by_cases hr : (rightOptions x).Nonempty
        · -- Both option families present: use the bracket identity.
          obtain ⟨a, b, hbr⟩ := exists_hasBracket hfinx hl hr
          have hban : birthday a ≤ (n : Ordinal) := by
            refine Order.le_of_lt_add_one ?_
            refine lt_of_lt_of_le hbr.birthday_left ?_
            rwa [Nat.cast_succ] at hb
          have hbbn : birthday b ≤ (n : Ordinal) := by
            refine Order.le_of_lt_add_one ?_
            refine lt_of_lt_of_le hbr.birthday_right ?_
            rwa [Nat.cast_succ] at hb
          obtain ⟨p, hp⟩ := exists_numerator n a hban
          obtain ⟨q, hq⟩ := exists_numerator n b hbbn
          refine ⟨p + q, double_injective ?_⟩
          calc add x x = add a b := double_eq_bracket_sum x hfinx a b hbr
            _ = ofPairSurreal (p + q) n := by rw [hp, hq, ofPairSurreal_add]
            _ = ofPairSurreal ((p + q) * 2) (n + 1) := (ofPairSurreal_succ _ _).symm
            _ = ofPairSurreal ((p + q) + (p + q)) (n + 1) := by
                congr 1; ring
            _ = add (ofPairSurreal (p + q) (n + 1)) (ofPairSurreal (p + q) (n + 1)) :=
                (ofPairSurreal_add _ _ _).symm
        · -- No right options: `x` is a natural.
          refine ⟨(k : ℤ) * 2 ^ (n + 1), ?_⟩
          rw [eq_ofNat_of_rightOptions_empty hk (Set.not_nonempty_iff_eq_empty.mp hr),
            ofNat_eq_ofPairSurreal]
      · -- No left options: `x` is the negative of a natural.
        refine ⟨-((k : ℤ) * 2 ^ (n + 1)), ?_⟩
        rw [eq_neg_ofNat_of_leftOptions_empty hk (Set.not_nonempty_iff_eq_empty.mp hl),
          neg_ofNat_eq_ofPairSurreal]

/-! ## The characterisation -/

/-- **Every finite-birthday surreal is a represented dyadic.** -/
theorem exists_dyadic_of_birthday_lt_omega0 {x : Surreal}
    (h : birthday x < Ordinal.omega0) :
    ∃ d : Algebra.Order.Dyadic, toSurreal d = x := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h
  obtain ⟨m, hm⟩ := exists_numerator n x (le_of_eq hn)
  exact ⟨Algebra.Order.Dyadic.ofPair m n, by rw [toSurreal_ofPair, hm]⟩

/-- **Finite-birthday surreals are precisely the represented dyadics.** -/
theorem birthday_lt_omega0_iff_exists_dyadic {x : Surreal} :
    birthday x < Ordinal.omega0 ↔ ∃ d : Algebra.Order.Dyadic, toSurreal d = x := by
  refine ⟨exists_dyadic_of_birthday_lt_omega0, ?_⟩
  rintro ⟨d, rfl⟩
  exact birthday_toSurreal_lt_omega0 d

/-- The same statement as an equality of sets, with the universe of the
birthday ordinal pinned. -/
theorem range_toSurreal_eq_finite_birthday :
    Set.range toSurreal = {x : Surreal | birthday x < Ordinal.omega0.{0}} := by
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  exact (birthday_lt_omega0_iff_exists_dyadic).symm

/-- And the interpretation is an order isomorphism onto that set. -/
theorem toSurreal_strictMono_surjOn :
    StrictMono toSurreal ∧
      Set.SurjOn toSurreal Set.univ {x : Surreal | birthday x < Ordinal.omega0.{0}} := by
  refine ⟨fun _ _ h => toSurreal_lt_iff.mpr h, ?_⟩
  intro x hx
  obtain ⟨d, hd⟩ := exists_dyadic_of_birthday_lt_omega0 hx
  exact ⟨d, Set.mem_univ d, hd⟩

/-! ## Controls -/

namespace FiniteBirthdayControls

/-- The forward direction is not vacuous: `1/2` is a finite-birthday surreal,
and the theorem produces a dyadic for it. -/
theorem half_is_represented : ∃ d : Algebra.Order.Dyadic, toSurreal d = ladder 1 :=
  exists_dyadic_of_birthday_lt_omega0 (birthday_ladder_lt_omega0 1)

/-- **Negative control**: `ω` is *not* represented, so the characterisation is
a genuine boundary rather than a statement about all surreals. -/
theorem omega_not_represented : ¬ ∃ d : Algebra.Order.Dyadic, toSurreal d = omega := by
  rw [← birthday_lt_omega0_iff_exists_dyadic]
  refine not_lt.mpr (le_of_eq ?_)
  rfl

/-- **Negative control**: and neither is `ω`'s negation. -/
theorem neg_omega_not_represented :
    ¬ ∃ d : Algebra.Order.Dyadic, toSurreal d = -omega := by
  rw [← birthday_lt_omega0_iff_exists_dyadic, birthday_neg]
  refine not_lt.mpr (le_of_eq ?_)
  rfl

/-- The grid statement at a concrete day: everything born by day two is a
multiple of `1/4`. -/
theorem day_two_is_quarters (x : Surreal) (h : birthday x ≤ ((2 : ℕ) : Ordinal)) :
    ∃ m : ℤ, x = ofPairSurreal m 2 :=
  exists_numerator 2 x h

end FiniteBirthdayControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.exists_numerator
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_lt_omega0_iff_exists_dyadic
