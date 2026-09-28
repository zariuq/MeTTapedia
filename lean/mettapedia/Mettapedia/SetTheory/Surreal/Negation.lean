import Mettapedia.SetTheory.Surreal.Cut

/-!
# Negation

Of the additive operations, negation is the one with a closed form on sign
expansions: **flip every sign**, and leave the level alone. No recursion and
no cut is needed, and the level is untouched, so a number and its negative are
born on the same day.

That closed form is a claim about the order, not a definition to be taken on
faith, so it is checked against `Lt` here: `lt_negPre_iff` proves that flipping
signs reverses the order exactly, and `neg_lt_neg_iff` carries it to the
quotient. Everything else follows.

* `Sign.opp` — the involution on signs, with `opp` reversing `<`.
* `negPre` — sign flip on expansions; `signAt_negPre` says it commutes with
  the padded sign function, which is what makes it well defined on the
  quotient.
* `neg_neg'`, `neg_lt_neg_iff`, `birthday_neg`, `neg_zero'` — the basic laws.
* `leftOptions_neg`, `rightOptions_neg` — **negation swaps the option
  families.** This is the law Conway's addition recursion needs, and it is
  available here without any of that recursion's machinery.

The level being preserved is worth noticing: `birthday_neg` is an equality, not
a bound. Negation is the only additive operation of which that is true.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

/-! ## Flipping a sign -/

namespace Sign

/-- Swap `+` and `−`, fix the middle sign. -/
def opp : Sign → Sign
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

@[simp] theorem opp_opp (a : Sign) : opp (opp a) = a := by cases a <;> rfl

theorem opp_injective : Function.Injective opp := by
  intro a b h
  rw [← opp_opp a, h, opp_opp]

@[simp] theorem opp_inj {a b : Sign} : opp a = opp b ↔ a = b :=
  ⟨fun h => opp_injective h, fun h => h ▸ rfl⟩

/-- **Flipping reverses the order.** -/
@[simp] theorem opp_lt_opp {a b : Sign} : opp a < opp b ↔ b < a := by
  cases a <;> cases b <;> decide

end Sign

/-! ## Flipping an expansion -/

namespace PreSurreal

/-- Negation: flip every recorded sign, keep the level. -/
def negPre (x : PreSurreal) : PreSurreal := ⟨x.length, fun β => !x.sign β⟩

@[simp] theorem negPre_length (x : PreSurreal) : (negPre x).length = x.length := rfl

/-- **Flipping commutes with the padded sign function.**  Past the level both
read the middle sign, which `opp` fixes. -/
@[simp] theorem signAt_negPre (x : PreSurreal) (β : Ordinal) :
    (negPre x).signAt β = Sign.opp (x.signAt β) := by
  by_cases h : β < x.length
  · rw [signAt_of_lt (show β < (negPre x).length from h), signAt_of_lt h]
    cases hs : x.sign β <;> simp [negPre, hs, Sign.opp]
  · rw [signAt_of_ge (show (negPre x).length ≤ β from not_lt.mp h),
      signAt_of_ge (not_lt.mp h)]
    rfl

@[simp] theorem negPre_negPre (x : PreSurreal) : negPre (negPre x) = x := by
  cases x with
  | mk length sign =>
      simp only [negPre, PreSurreal.mk.injEq, true_and]
      funext β
      simp

/-- **Flipping reverses the comparison.** -/
theorem lt_negPre_iff {x y : PreSurreal} : Lt (negPre x) (negPre y) ↔ Lt y x := by
  constructor
  · rintro ⟨β, hagree, hlt⟩
    refine ⟨β, fun γ hγ => ?_, ?_⟩
    · have := hagree γ hγ
      rw [signAt_negPre, signAt_negPre, Sign.opp_inj] at this
      exact this.symm
    · rw [signAt_negPre, signAt_negPre, Sign.opp_lt_opp] at hlt
      exact hlt
  · rintro ⟨β, hagree, hlt⟩
    refine ⟨β, fun γ hγ => ?_, ?_⟩
    · rw [signAt_negPre, signAt_negPre, Sign.opp_inj]
      exact (hagree γ hγ).symm
    · rw [signAt_negPre, signAt_negPre, Sign.opp_lt_opp]
      exact hlt

/-- And it is well defined on the quotient. -/
theorem equiv_negPre {x y : PreSurreal} (h : Equiv x y) : Equiv (negPre x) (negPre y) := by
  funext β
  rw [signAt_negPre, signAt_negPre, Sign.opp_inj]
  exact congrFun h β

end PreSurreal

/-! ## Negation on the numbers -/

namespace Surreal

open PreSurreal

noncomputable instance : Neg Surreal :=
  ⟨Quotient.map negPre fun _ _ h => equiv_negPre h⟩

@[simp] theorem neg_mk (x : PreSurreal) : -(mk x) = mk (negPre x) := rfl

@[simp] theorem neg_neg' (a : Surreal) : - -a = a := by
  induction a using Quotient.inductionOn with
  | h x =>
      show mk (negPre (negPre x)) = mk x
      rw [negPre_negPre]

theorem neg_injective : Function.Injective (fun a : Surreal => -a) := by
  intro a b h
  simpa using congrArg (fun z : Surreal => -z) h

/-- **Negation reverses the order.** -/
@[simp] theorem neg_lt_neg_iff {a b : Surreal} : -a < -b ↔ b < a := by
  induction a using Quotient.inductionOn with
  | h x =>
      induction b using Quotient.inductionOn with
      | h y => exact lt_negPre_iff

theorem lt_neg_iff {a b : Surreal} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff, neg_neg']

theorem neg_lt_iff {a b : Surreal} : -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg']

/-- **A number and its negative are born on the same day.** -/
@[simp] theorem birthday_neg (a : Surreal) : birthday (-a) = birthday a := by
  induction a using Quotient.inductionOn with
  | h x => rfl

@[simp] theorem neg_zero' : -(0 : Surreal) = 0 := by
  show mk (negPre zeroPre) = mk zeroPre
  apply Quotient.sound
  funext β
  rw [signAt_negPre, signAt_of_ge (show zeroPre.length ≤ β by simp [zeroPre])]
  rfl

/-! ## Negation swaps the options

This is the law Conway's addition recursion consumes, and it holds here
without any recursion: the options of `-x` are exactly the negated options of
`x`, on the other side. -/

theorem mem_leftOptions_neg {a z : Surreal} :
    z ∈ leftOptions (-a) ↔ -z ∈ rightOptions a := by
  constructor
  · rintro ⟨hlt, hb⟩
    exact ⟨lt_neg_iff.mp hlt, by rwa [birthday_neg, ← birthday_neg a]⟩
  · rintro ⟨hlt, hb⟩
    refine ⟨lt_neg_iff.mpr hlt, ?_⟩
    rw [birthday_neg]
    rwa [birthday_neg] at hb

theorem mem_rightOptions_neg {a z : Surreal} :
    z ∈ rightOptions (-a) ↔ -z ∈ leftOptions a := by
  constructor
  · rintro ⟨hlt, hb⟩
    exact ⟨neg_lt_iff.mp hlt, by rwa [birthday_neg, ← birthday_neg a]⟩
  · rintro ⟨hlt, hb⟩
    refine ⟨neg_lt_iff.mpr hlt, ?_⟩
    rw [birthday_neg]
    rwa [birthday_neg] at hb

/-- **The left options of `-x` are the negated right options of `x`.** -/
theorem leftOptions_neg (a : Surreal) :
    leftOptions (-a) = (fun z => -z) '' rightOptions a := by
  ext z
  rw [mem_leftOptions_neg]
  constructor
  · intro h
    exact ⟨-z, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

/-- And dually. -/
theorem rightOptions_neg (a : Surreal) :
    rightOptions (-a) = (fun z => -z) '' leftOptions a := by
  ext z
  rw [mem_rightOptions_neg]
  constructor
  · intro h
    exact ⟨-z, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

/-! ## Controls -/

namespace NegationControls

/-- Negation is not the identity: it moves `1`. -/
theorem neg_one_ne_one : -(ofNat 1) ≠ ofNat 1 := by
  intro h
  have h0 : (0 : Surreal) < ofNat 1 := dyadic_zero_eq_one ▸ dyadic_pos 0
  have hneg : -(ofNat 1) < 0 := by
    rw [← neg_zero']
    exact neg_lt_neg_iff.mpr h0
  rw [h] at hneg
  exact absurd (hneg.trans h0) (lt_irrefl _)

/-- It does fix zero, and that is the only fixed point among the numbers we
have named. -/
theorem neg_fixes_zero : -(0 : Surreal) = 0 := neg_zero'

/-- The negative of a positive is negative. -/
theorem neg_pos_is_neg {a : Surreal} (h : 0 < a) : -a < 0 := by
  rw [← neg_zero']
  exact neg_lt_neg_iff.mpr h

/-- Negation exchanges the dyadic family's direction: `-(1/2) < -(1/4)`
because `1/4 < 1/2`. -/
theorem neg_dyadic_anti (k : ℕ) :
    -(mk (dyadicPre k)) < -(mk (dyadicPre (k + 1))) :=
  neg_lt_neg_iff.mpr (dyadic_anti k)

end NegationControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.neg_lt_neg_iff
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.birthday_neg
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.leftOptions_neg
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.rightOptions_neg
