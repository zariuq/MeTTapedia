import Mettapedia.SetTheory.Surreal.Negation

/-!
# The integers inside the surreals

The first step of the dyadic interpretation, and the one that needs no
arithmetic: a dyadic `m / 2 ^ k` at `k = 0` is an integer, and an integer's
sign expansion is a run of like signs — `n` pluses for `n`, `n` minuses for
`-n`. So the embedding is explicit, and both directions of the order comparison
follow from the lexicographic order on expansions.

* `ofNat_lt_ofNat` — strict monotonicity on `ℕ`. This was missing and
  everything else needs it.
* `ofInt` — the embedding, defined by cases on the sign and reusing `negPre`.
* `ofInt_lt_ofInt` — **order preservation and reflection**, as an `iff`.
* `ofInt_zero`, `ofInt_one`, `ofInt_neg` — the structure maps that do not
  require addition.
* `birthday_ofInt` — an integer is born on day `|n|`, exactly.

Addition is *not* connected here. `ofInt (m + n) = ofInt m + ofInt n` needs
surreal addition to be known to be Conway's sum, which is still outstanding
(see `Addition.lean`: `add_eq_cut` reduces that to separation of the sum's
option families). What is proved here is everything about the integer
embedding that is independent of it.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open PreSurreal

/-! ## Naturals -/

/-- **Strict monotonicity on the naturals.**  At position `m` the smaller
expansion has run out — the middle sign — while the larger continues with a
plus, and they agree below. -/
theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) : ofNat m < ofNat n := by
  refine ⟨(m : Ordinal), fun γ hγ => ?_, ?_⟩
  · have hm : γ < (m : Ordinal) := hγ
    have hn : γ < (n : Ordinal) := hm.trans (by exact_mod_cast h)
    rw [natPre_signAt_of_lt hm, natPre_signAt_of_lt hn]
  · rw [natPre_signAt_of_ge (le_refl _),
      natPre_signAt_of_lt (show (m : Ordinal) < (n : Ordinal) from by exact_mod_cast h)]
    exact Sign.zero_lt_pos

theorem ofNat_injective : Function.Injective (ofNat : ℕ → Surreal) := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (ne_of_lt (ofNat_lt_ofNat hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (ofNat_lt_ofNat hgt))

@[simp] theorem birthday_ofNat (n : ℕ) : birthday (ofNat n) = (n : Ordinal) := rfl

theorem ofNat_pos {n : ℕ} (h : 0 < n) : (0 : Surreal) < ofNat n := by
  rw [← ofNat_zero]
  exact ofNat_lt_ofNat h

/-! ## Integers -/

/-- The integers, embedded by sign: `n` pluses for a natural, and the negation
of that for a negative. -/
noncomputable def ofInt : ℤ → Surreal
  | .ofNat n => ofNat n
  | .negSucc n => -(ofNat (n + 1))

@[simp] theorem ofInt_ofNat (n : ℕ) : ofInt (n : ℤ) = ofNat n := rfl

@[simp] theorem ofInt_zero : ofInt 0 = 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ofInt_ofNat, ofNat_zero]

@[simp] theorem ofInt_one : ofInt 1 = ofNat 1 := rfl

/-- **Negation is preserved.**  This is the one structure map available without
addition, because negation has a closed form on expansions. -/
@[simp] theorem ofInt_neg (n : ℤ) : ofInt (-n) = -(ofInt n) := by
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          show ofInt (Int.ofNat 0) = -(ofInt (Int.ofNat 0))
          rw [show ofInt (Int.ofNat 0) = 0 from ofInt_zero, neg_zero']
      | succ j =>
          show ofInt (Int.negSucc j) = -(ofInt (Int.ofNat (j + 1)))
          rfl
  | negSucc k =>
      show ofInt (Int.ofNat (k + 1)) = -(ofInt (Int.negSucc k))
      show ofNat (k + 1) = - -(ofNat (k + 1))
      rw [neg_neg']

/-- **An integer is born on day `|n|`.**  An equality, not a bound. -/
@[simp] theorem birthday_ofInt (n : ℤ) : birthday (ofInt n) = (n.natAbs : Ordinal) := by
  cases n with
  | ofNat k => rfl
  | negSucc k =>
      show birthday (-(ofNat (k + 1))) = ((Int.negSucc k).natAbs : Ordinal)
      rw [birthday_neg, birthday_ofNat]
      rfl

/-! ## The order, both ways -/

theorem ofInt_neg_lt_zero {n : ℕ} : -(ofNat (n + 1)) < (0 : Surreal) := by
  rw [← neg_zero']
  exact neg_lt_neg_iff.mpr (ofNat_pos (Nat.succ_pos n))

/-- The forward direction, by cases on the two signs. -/
theorem ofInt_lt_of_lt : ∀ {a b : ℤ}, a < b → ofInt a < ofInt b := by
  intro a b hab
  cases a with
  | ofNat i =>
      cases b with
      | ofNat j =>
          exact ofNat_lt_ofNat (Int.ofNat_lt.mp hab)
      | negSucc j =>
          have h1 : (0 : ℤ) ≤ Int.ofNat i := Int.natCast_nonneg i
          have h2 : Int.negSucc j < 0 := Int.negSucc_lt_zero j
          exact absurd (hab.trans h2) (not_lt.mpr h1)
  | negSucc i =>
      have hneg : ofInt (Int.negSucc i) < 0 := ofInt_neg_lt_zero
      cases b with
      | ofNat j =>
          refine lt_of_lt_of_le hneg ?_
          cases j with
          | zero => rw [show ofInt (Int.ofNat 0) = 0 from ofInt_zero]
          | succ k => exact le_of_lt (ofNat_pos (Nat.succ_pos k))
      | negSucc j =>
          show -(ofNat (i + 1)) < -(ofNat (j + 1))
          refine neg_lt_neg_iff.mpr (ofNat_lt_ofNat ?_)
          have : (Int.negSucc i) < (Int.negSucc j) := hab
          simp only [Int.negSucc_eq] at this
          omega

/-- **Order preservation and reflection.**  The embedding is an order
embedding, so nothing about the integers' comparison is lost or invented. -/
theorem ofInt_lt_ofInt {m n : ℤ} : ofInt m < ofInt n ↔ m < n := by
  refine ⟨fun h => ?_, ofInt_lt_of_lt⟩
  by_contra hcon
  rcases lt_or_eq_of_le (not_lt.mp hcon) with hlt | rfl
  · exact absurd (h.trans (ofInt_lt_of_lt hlt)) (lt_irrefl _)
  · exact absurd h (lt_irrefl _)

theorem ofInt_injective : Function.Injective ofInt := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (ne_of_lt (ofInt_lt_ofInt.mpr hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (ofInt_lt_ofInt.mpr hgt))

/-! ## Controls -/

namespace IntegerEmbeddingControls

/-- Negative integers really are negative. -/
theorem neg_one_lt_zero : ofInt (-1) < ofInt 0 := ofInt_lt_ofInt.mpr (by decide)

/-- And the embedding separates them from the dyadics between: `-1 < -1/2`
would need halves, but `-1 < 0 < 1` is already strict both ways. -/
theorem neg_one_lt_one : ofInt (-1) < ofInt 1 := ofInt_lt_ofInt.mpr (by decide)

/-- **Reflection is not vacuous**: the embedding refuses a false comparison. -/
theorem not_one_lt_neg_one : ¬ (ofInt 1 < ofInt (-1)) := by
  rw [ofInt_lt_ofInt]
  decide

/-- The half from `Birthday.lean` sits strictly between `0` and `1`, so the
integers are not cofinal in the finite-birthday numbers — the dyadic
interpretation has something left to do. -/
theorem half_between : ofInt 0 < mk (dyadicPre 1) ∧ mk (dyadicPre 1) < ofInt 1 := by
  refine ⟨?_, ?_⟩
  · rw [ofInt_zero]
    exact dyadic_pos 1
  · rw [ofInt_one, ← dyadic_zero_eq_one]
    exact dyadic_anti 0

end IntegerEmbeddingControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofNat_lt_ofNat
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofInt_lt_ofInt
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofInt_neg
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_ofInt
