import Mettapedia.Machines.AdmissionRewriting.SortBySelection
import Mettapedia.Logic.Prolog.SourceTermOrder

/-!
# Binary64 patterns: their numbers, IEEE 754's `totalOrder`, and SWI's order of floats

SourceTermOrder compares the Prolog heap's numbers as SWI-Prolog does: binary64 patterns by
`compareFloatBits`, integers and patterns in one order (the number case of its comparison of
constants). This file reads each pattern as the number it stands for and compares
SourceTermOrder with SWI's order of numbers (`SortBySelection.swiLE`) and with IEEE 754's
`totalOrder`.

**The value of a pattern.** A pattern read as finite has the value of its sign times its
magnitude's units of `2^-1074`, the least subnormal (`finiteFloatRat_eq`, `units`), and the
units grow strictly with the magnitude (`units_strictMono`): the encoding is monotone. So a
smaller `totalOrder` key reads as a smaller value, except `-0.0` against `0.0`
(`finiteFloatRat_lt_of_key`, `patVal_lt_of_key`). The number a pattern stands for (`bitsNum`)
is NaN, `-0.0`, an infinity, or the point of its exact value.

**IEEE 754's `totalOrder`** (`totalKey`, `totalOrder`: the magnitude when the sign bit is clear,
minus the magnitude less one when it is set) meets the clauses of the standard's definition: it
follows numeric order (`totalKey_lt_of_patVal_lt`), puts `-0` before `+0` (`totalKey_zeros`),
negative NaNs first and positive NaNs last (`totalKey_nan`), and orders NaNs by sign, then by
payload, the negative ones reversed (`totalKey_nans`).

**SWI's order of floats is `totalOrder` but on positive NaNs.** SourceTermOrder compares two
patterns that are not NaN by their `totalOrder` keys, the zeros included
(`compareFloatBits_eq_totalKey`), and two NaNs by their payloads in `totalOrder`'s order
(`compareFloatBits_nans`, through `nanPayloadRat_eq`); it puts every NaN before every number
(`compareFloatBits_nan`), where `totalOrder` puts the positive ones after every number. The two
orders agree on a pair of patterns exactly when it is not a positive NaN against a pattern that
is not NaN (`compareFloatBits_eq_totalKey_iff`, `Controls.positive_nan_differs`,
`Controls.negative_nan_agrees`).

**SourceTermOrder's number case is SWI's order of numbers** (`compareConstants_eq_swiCompare`):
on every two number constants of the Prolog heap, integers and binary64 patterns, the heap's
comparison answers SWI's comparison of the numbers they stand for (`swiCompare`), except on two
different NaN patterns, which SourceTermOrder orders by payload and which stand for one NaN
(`Controls.nan_payloads`). Every integer and every pattern is covered; the numbers also hold
doubles that binary64 does not, which the heap never stores.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.Binary64Order

open MinMaxSWI (XR ofQ Dbl Num isNaN)
open MinMaxSelection (valOf)
open SortBySelection (swiRank rankKey swiLE swiLT rankKey_lt)
open Mettapedia.Logic.Prolog.SourceTermOrder (compareFloatBits)
open private signBit exponentBits fractionBits isNaNBits isInfinityBits finiteFloatRat
  compareRat compareInt compareFloatInt compareConstants reverseOrdering
  from Mettapedia.Logic.Prolog.SourceTermOrder

/-! ## The fields of a pattern -/

/-- A pattern's magnitude: its bits below the sign. -/
def mag (b : UInt64) : ℕ := b.toNat % 2 ^ 63

theorem and_two_pow_ne_zero (x n : ℕ) : x &&& 2 ^ n ≠ 0 ↔ x.testBit n = true := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : n = i
    · subst hi
      simpa using hb
    · simp [hi]
  · intro h h0
    have := congrArg (fun y => y.testBit n) h0
    simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.and_true,
      Nat.zero_testBit] at this
    rw [h] at this
    exact Bool.noConfusion this

theorem signBit_iff (b : UInt64) : signBit b = true ↔ 2 ^ 63 ≤ b.toNat := by
  have hlt := UInt64.toNat_lt b
  unfold signBit
  rw [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_and]
  have h1 : (0x8000000000000000 : UInt64).toNat = 2 ^ 63 := by decide
  rw [h1, UInt64.toNat_zero, ← ne_eq, and_two_pow_ne_zero, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq]
  omega

theorem fractionBits_eq (b : UInt64) : fractionBits b = mag b % 2 ^ 52 := by
  unfold fractionBits mag
  rw [UInt64.toNat_and]
  have : (0x000fffffffffffff : UInt64).toNat = 2 ^ 52 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem exponentBits_eq (b : UInt64) : exponentBits b = mag b / 2 ^ 52 := by
  have hlt := UInt64.toNat_lt b
  unfold exponentBits mag
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h1 : (0x7ff : UInt64).toNat = 2 ^ 11 - 1 := by decide
  have h2 : (52 : UInt64).toNat % 64 = 52 := by decide
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  omega

/-- The magnitude of an infinity: all-ones exponent, zero fraction. -/
abbrev infMag : ℕ := 2047 * 2 ^ 52

theorem isNaNBits_iff (b : UInt64) : isNaNBits b = true ↔ infMag < mag b := by
  have hm : mag b < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
  unfold isNaNBits
  rw [exponentBits_eq, fractionBits_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, infMag]
  omega

theorem isInfinityBits_iff (b : UInt64) : isInfinityBits b = true ↔ mag b = infMag := by
  have hm : mag b < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
  unfold isInfinityBits
  rw [exponentBits_eq, fractionBits_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, infMag]
  omega

/-- A pattern is its sign and its magnitude. -/
theorem eq_of_sign_mag {b c : UInt64} (hs : signBit b = signBit c) (hm : mag b = mag c) :
    b = c := by
  have hb := UInt64.toNat_lt b
  have hc := UInt64.toNat_lt c
  have hsb := signBit_iff b
  have hsc := signBit_iff c
  rw [← UInt64.toNat_inj]
  unfold mag at hm
  cases h : signBit b <;> rw [h] at hs <;> rw [h] at hsb <;> rw [← hs] at hsc
  · simp only [Bool.false_eq_true, false_iff, not_le] at hsb hsc
    omega
  · simp only [true_iff] at hsb hsc
    omega

/-! ## The value of a pattern -/

/-- A magnitude's value in units of `2^-1074`, the least subnormal: the fraction below the
least normal exponent, and otherwise the significand, with its hidden bit, times two to the
exponent less one. -/
def units (m : ℕ) : ℕ :=
  if m / 2 ^ 52 = 0 then m % 2 ^ 52 else (2 ^ 52 + m % 2 ^ 52) * 2 ^ (m / 2 ^ 52 - 1)

theorem units_lt_bound (m : ℕ) : units m < 2 ^ 52 * 2 ^ (m / 2 ^ 52) := by
  unfold units
  split_ifs with h
  · rw [h, pow_zero, mul_one]
    exact Nat.mod_lt _ (by norm_num)
  · have hf : m % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
    have he : 2 ^ (m / 2 ^ 52) = 2 * 2 ^ (m / 2 ^ 52 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [he, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

theorem units_ge_bound {m : ℕ} (h : m / 2 ^ 52 ≠ 0) :
    2 ^ 52 * 2 ^ (m / 2 ^ 52 - 1) ≤ units m := by
  unfold units
  rw [if_neg h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- **The encoding is monotone**: a larger magnitude has a larger value. -/
theorem units_strictMono : StrictMono units := by
  intro m m' hmm'
  by_cases he : m / 2 ^ 52 = m' / 2 ^ 52
  · have hf : m % 2 ^ 52 < m' % 2 ^ 52 := by omega
    unfold units
    rw [he]
    split_ifs
    · exact hf
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  · have hlt : m / 2 ^ 52 < m' / 2 ^ 52 := by
      rcases lt_or_gt_of_ne he with h | h
      · exact h
      · exact absurd (Nat.div_le_div_right (c := 2 ^ 52) hmm'.le) (not_le.mpr h)
    calc units m < 2 ^ 52 * 2 ^ (m / 2 ^ 52) := units_lt_bound m
      _ ≤ 2 ^ 52 * 2 ^ (m' / 2 ^ 52 - 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ units m' := units_ge_bound (by omega)

theorem units_zero : units 0 = 0 := by decide

theorem units_eq_zero {m : ℕ} : units m = 0 ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    have := units_strictMono (Nat.pos_of_ne_zero hm)
    rw [units_zero, h] at this
    exact lt_irrefl _ this
  · rintro rfl
    exact units_zero

theorem finiteFloatRat_formula (s : Bool) (e f : ℕ) :
    (let effective := if e = 0 then 1 else e
      let significand := if e = 0 then f else 2 ^ 52 + f
      let signed : ℤ := if s then -(Int.ofNat significand) else Int.ofNat significand
      if 1075 ≤ effective then Rat.ofInt (signed * Int.ofNat (2 ^ (effective - 1075)))
      else Rat.ofInt signed / Rat.ofInt (Int.ofNat (2 ^ (1075 - effective)))) =
      (if s then -1 else 1) * ((if e = 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1) : ℕ) : ℚ) /
        2 ^ 1074 := by
  dsimp only
  have hsig : ∀ k : ℕ, Rat.ofInt (if s then -(Int.ofNat k) else Int.ofNat k) =
      (if s then -1 else 1) * (k : ℚ) := by
    intro k
    cases s
    · rw [if_neg Bool.false_ne_true, Rat.ofInt_eq_cast, Int.ofNat_eq_natCast, Int.cast_natCast,
        if_neg Bool.false_ne_true, one_mul]
    · rw [if_pos rfl, Rat.ofInt_eq_cast, Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast,
        if_pos rfl, neg_one_mul]
  have hpow : ∀ k : ℕ, Rat.ofInt (Int.ofNat (2 ^ k)) = (2 : ℚ) ^ k := by
    intro k
    rw [Rat.ofInt_eq_cast, Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat]
  by_cases he : e = 0
  · rw [if_pos he, if_pos he, if_pos he, if_neg (by norm_num : ¬ 1075 ≤ 1), hsig, hpow]
  · rw [if_neg he, if_neg he, if_neg he]
    by_cases hle : 1075 ≤ e
    · rw [if_pos hle]
      have hp : (2 : ℚ) ^ (e - 1) = 2 ^ (e - 1075) * 2 ^ 1074 := by
        rw [← pow_add]
        congr 1
        omega
      rw [Rat.ofInt_eq_cast, Int.cast_mul, ← Rat.ofInt_eq_cast, hsig, ← Rat.ofInt_eq_cast, hpow,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp]
      field_simp
    · rw [if_neg hle, hsig, hpow]
      have hp : (2 : ℚ) ^ 1074 = 2 ^ (1075 - e) * 2 ^ (e - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp]
      field_simp

/-- **The exact value of a pattern read as finite**: its sign times its magnitude's units, in
units of `2^-1074`. -/
theorem finiteFloatRat_eq (b : UInt64) :
    finiteFloatRat b = (if signBit b then -1 else 1) * (units (mag b) : ℚ) / 2 ^ 1074 := by
  unfold finiteFloatRat
  rw [finiteFloatRat_formula, exponentBits_eq, fractionBits_eq]
  rfl

/-! ## IEEE 754's `totalOrder` -/

/-- **IEEE 754's `totalOrder` on binary64, by its key**: a pattern with the sign bit clear reads
as its magnitude, one with the sign bit set as minus its magnitude, less one. -/
def totalKey (b : UInt64) : ℤ := if b.toNat < 2 ^ 63 then b.toNat else 2 ^ 63 - 1 - b.toNat

/-- IEEE 754's `totalOrder` predicate. -/
def totalOrder (b c : UInt64) : Prop := totalKey b ≤ totalKey c

instance : DecidableRel totalOrder := fun b c =>
  inferInstanceAs (Decidable (totalKey b ≤ totalKey c))

theorem mag_lt (b : UInt64) : mag b < 2 ^ 63 := Nat.mod_lt _ (by norm_num)

theorem totalKey_eq (b : UInt64) :
    totalKey b = if signBit b then -(mag b : ℤ) - 1 else (mag b : ℤ) := by
  have hlt := UInt64.toNat_lt b
  have hs := signBit_iff b
  unfold totalKey mag
  cases h : signBit b <;> rw [h] at hs <;> simp only [Bool.false_eq_true, false_iff, true_iff,
    not_le, if_true, if_false] at hs ⊢
  · rw [if_pos hs]
    omega
  · rw [if_neg (by omega)]
    omega

theorem totalKey_injective : Function.Injective totalKey := by
  intro b c h
  rw [totalKey_eq, totalKey_eq] at h
  cases hb : signBit b <;> cases hc : signBit c <;> rw [hb, hc] at h <;>
    simp only [Bool.false_eq_true, if_true, if_false] at h
  · exact eq_of_sign_mag (hb.trans hc.symm) (by omega)
  · omega
  · omega
  · exact eq_of_sign_mag (hb.trans hc.symm) (by omega)

theorem mag_le_of_not_nan {b : UInt64} (h : isNaNBits b = false) : mag b ≤ infMag := by
  have := (isNaNBits_iff b).not
  rw [h] at this
  simpa using this

theorem mag_lt_of_finite {b : UInt64} (hn : isNaNBits b = false) (hi : isInfinityBits b = false) :
    mag b < infMag := by
  have h1 := mag_le_of_not_nan hn
  have h2 : mag b ≠ infMag := fun e => by
    rw [← isInfinityBits_iff, hi] at e
    exact Bool.false_ne_true e
  omega

/-- **The encoding orders values as `totalOrder` does**: a smaller key reads as a smaller
finite value, but for `-0.0` against `0.0`. -/
theorem finiteFloatRat_lt_of_key {b c : UInt64} (h : totalKey b < totalKey c) :
    finiteFloatRat b < finiteFloatRat c ∨
      (signBit b = true ∧ mag b = 0 ∧ signBit c = false ∧ mag c = 0) := by
  rw [finiteFloatRat_eq, finiteFloatRat_eq]
  rw [totalKey_eq, totalKey_eq] at h
  have hP : (0 : ℚ) < 2 ^ 1074 := by positivity
  cases hb : signBit b <;> cases hc : signBit c <;> rw [hb, hc] at h <;>
    simp only [Bool.false_eq_true, if_true, if_false] at h ⊢
  · left
    have := units_strictMono (by omega : mag b < mag c)
    rw [one_mul, one_mul]
    exact div_lt_div_of_pos_right (by exact_mod_cast this) hP
  · omega
  · by_cases h0 : mag b = 0 ∧ mag c = 0
    · exact Or.inr ⟨trivial, h0.1, trivial, h0.2⟩
    · left
      have hsum : 0 < units (mag b) + units (mag c) := by
        by_contra h'
        apply h0
        constructor <;> rw [← units_eq_zero] <;> omega
      rw [div_lt_div_iff_of_pos_right hP]
      have : (0 : ℚ) < units (mag b) + units (mag c) := by exact_mod_cast hsum
      linarith
  · left
    have := units_strictMono (by omega : mag c < mag b)
    rw [div_lt_div_iff_of_pos_right hP, neg_one_mul, neg_one_mul, neg_lt_neg_iff]
    exact_mod_cast this

/-! ## The number a pattern stands for -/

/-- The `-0.0` pattern. -/
def negZeroBits : UInt64 := 0x8000000000000000

/-- The value of a pattern on the extended line: an infinity's, or the exact value of a
pattern read as finite. -/
def patVal (b : UInt64) : XR :=
  if isInfinityBits b then (if signBit b then ⊥ else ⊤) else ofQ (finiteFloatRat b)

/-- **The number a binary64 pattern stands for**: NaN, `-0.0`, or the point of its value. -/
def bitsNum (b : UInt64) : Num :=
  if isNaNBits b then .flt .nan
  else if b = negZeroBits then .flt .negZero
  else .flt (.pt (patVal b))

theorem patVal_negZero : patVal negZeroBits = 0 := by decide +kernel

theorem patVal_zero : patVal 0 = 0 := by decide +kernel

theorem isNaN_bitsNum {b : UInt64} : isNaN (bitsNum b) = isNaNBits b := by
  unfold bitsNum
  cases h : isNaNBits b
  · simp only [Bool.false_eq_true, if_false]
    split_ifs <;> rfl
  · rfl

theorem valOf_bitsNum {b : UInt64} (hb : isNaNBits b = false) : valOf (bitsNum b) = patVal b := by
  unfold bitsNum
  rw [hb]
  simp only [Bool.false_eq_true, if_false]
  split_ifs with h
  · rw [h, patVal_negZero]
    rfl
  · rfl

theorem inf_sign_of_lt {b c : UInt64} (hc : isNaNBits c = false) (hb : isInfinityBits b = true)
    (h : totalKey b < totalKey c) : signBit b = true := by
  have hm := (isInfinityBits_iff b).mp hb
  have hcm := mag_le_of_not_nan hc
  rw [totalKey_eq, totalKey_eq] at h
  cases hsb : signBit b
  · cases hsc : signBit c <;> rw [hsb, hsc] at h <;>
      simp only [Bool.false_eq_true, if_true, if_false] at h <;> omega
  · rfl

theorem inf_sign_of_gt {b c : UInt64} (hc : isNaNBits c = false) (hb : isInfinityBits b = true)
    (h : totalKey c < totalKey b) : signBit b = false := by
  have hm := (isInfinityBits_iff b).mp hb
  have hcm := mag_le_of_not_nan hc
  rw [totalKey_eq, totalKey_eq] at h
  cases hsb : signBit b
  · rfl
  · cases hsc : signBit c <;> rw [hsb, hsc] at h <;>
      simp only [Bool.false_eq_true, if_true, if_false] at h <;> omega

/-- **On patterns that are not NaN, the value follows the key**: a smaller key reads as a
smaller value, but for `-0.0` against `0.0`. -/
theorem patVal_lt_of_key {b c : UInt64} (hb : isNaNBits b = false) (hc : isNaNBits c = false)
    (h : totalKey b < totalKey c) : patVal b < patVal c ∨ (b = negZeroBits ∧ c = 0) := by
  have hne : b ≠ c := fun e => lt_irrefl _ (e ▸ h)
  unfold patVal
  cases hib : isInfinityBits b
  · cases hic : isInfinityBits c
    · simp only [Bool.false_eq_true, if_false]
      rcases finiteFloatRat_lt_of_key h with h' | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h'))
      · right
        exact ⟨eq_of_sign_mag (h1.trans (by decide)) (h2.trans (by decide)),
          eq_of_sign_mag (h3.trans (by decide)) (h4.trans (by decide))⟩
    · have hs : signBit c = false := inf_sign_of_gt hb hic h
      simp only [Bool.false_eq_true, if_false, if_true, hs]
      exact Or.inl (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))
  · have hs : signBit b = true := inf_sign_of_lt hc hib h
    simp only [if_true, hs]
    cases hic : isInfinityBits c
    · exact Or.inl (WithBot.bot_lt_coe _)
    · have hsc : signBit c = false := by
        by_contra hsc
        rw [Bool.not_eq_false] at hsc
        exact hne (eq_of_sign_mag (hs.trans hsc.symm)
          (((isInfinityBits_iff b).mp hib).trans ((isInfinityBits_iff c).mp hic).symm))
      simp only [if_true, hsc, Bool.false_eq_true, if_false]
      exact Or.inl (WithBot.bot_lt_coe _)

/-- **The number of a pattern follows the key**: on patterns that are not NaN, SWI's order of
their numbers is the order of their keys. -/
theorem rankKey_bitsNum_lt {b c : UInt64} (hb : isNaNBits b = false) (hc : isNaNBits c = false)
    (h : totalKey b < totalKey c) :
    rankKey swiRank (bitsNum b) < rankKey swiRank (bitsNum c) := by
  have hb' : isNaN (bitsNum b) = false := by rw [isNaN_bitsNum, hb]
  have hc' : isNaN (bitsNum c) = false := by rw [isNaN_bitsNum, hc]
  rw [rankKey_lt hb' hc', valOf_bitsNum hb, valOf_bitsNum hc]
  rcases patVal_lt_of_key hb hc h with h' | ⟨rfl, rfl⟩
  · exact Or.inl h'
  · right
    exact ⟨by rw [patVal_negZero, patVal_zero], by decide +kernel⟩

/-! ## SWI's order of floats is `totalOrder` off NaN -/

theorem compareRat_eq (x y : ℚ) : compareRat x y = compare x y := by
  unfold compareRat
  rcases lt_trichotomy x y with h | rfl | h
  · rw [if_pos h, compare_lt_iff_lt.mpr h]
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), compare_eq_iff_eq.mpr rfl]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, compare_gt_iff_gt.mpr h]

theorem compareInt_eq (m n : ℤ) : compareInt m n = compare m n := by
  unfold compareInt
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_pos h, compare_lt_iff_lt.mpr h]
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), compare_eq_iff_eq.mpr rfl]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, compare_gt_iff_gt.mpr h]

theorem finiteFloatRat_zeros {b c : UInt64} (hb : mag b = 0) (hc : mag c = 0) :
    finiteFloatRat b = finiteFloatRat c := by
  rw [finiteFloatRat_eq, finiteFloatRat_eq, hb, hc, units_zero]
  simp

theorem compareFloatBits_lt {b c : UInt64} (hb : isNaNBits b = false) (hc : isNaNBits c = false)
    (h : totalKey b < totalKey c) : compareFloatBits b c = .lt := by
  have hne : b ≠ c := fun e => lt_irrefl _ (e ▸ h)
  unfold compareFloatBits
  rw [if_neg hne, hb, hc]
  simp only [Bool.false_eq_true, if_false]
  cases hib : isInfinityBits b
  · cases hic : isInfinityBits c
    · simp only [Bool.false_eq_true, if_false]
      rcases finiteFloatRat_lt_of_key h with h' | ⟨h1, h2, _, h4⟩
      · rw [compareRat_eq, compare_lt_iff_lt.mpr h']
      · rw [finiteFloatRat_zeros h2 h4, compareRat_eq, compare_eq_iff_eq.mpr rfl, h1]
        rfl
    · simp [inf_sign_of_gt hb hic h]
  · simp [inf_sign_of_lt hc hib h]

theorem compareFloatBits_gt {b c : UInt64} (hb : isNaNBits b = false) (hc : isNaNBits c = false)
    (h : totalKey c < totalKey b) : compareFloatBits b c = .gt := by
  have hne : b ≠ c := fun e => lt_irrefl _ (e ▸ h)
  unfold compareFloatBits
  rw [if_neg hne, hb, hc]
  simp only [Bool.false_eq_true, if_false]
  cases hib : isInfinityBits b
  · cases hic : isInfinityBits c
    · simp only [Bool.false_eq_true, if_false]
      rcases finiteFloatRat_lt_of_key h with h' | ⟨_, h2, h3, h4⟩
      · rw [compareRat_eq, compare_gt_iff_gt.mpr h']
      · rw [finiteFloatRat_zeros h4 h2, compareRat_eq, compare_eq_iff_eq.mpr rfl, h3]
        rfl
    · simp [inf_sign_of_lt hb hic h]
  · simp [inf_sign_of_gt hc hib h]

/-- **SWI's order of floats is IEEE 754's `totalOrder` on every pair of patterns that are not
NaN**: SourceTermOrder's `compareFloatBits` compares their `totalOrder` keys. -/
theorem compareFloatBits_eq_totalKey {b c : UInt64} (hb : isNaNBits b = false)
    (hc : isNaNBits c = false) : compareFloatBits b c = compare (totalKey b) (totalKey c) := by
  rcases lt_trichotomy (totalKey b) (totalKey c) with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compareFloatBits_lt hb hc h]
  · rw [totalKey_injective h, compare_eq_iff_eq.mpr rfl]
    unfold compareFloatBits
    rw [if_pos rfl]
  · rw [compare_gt_iff_gt.mpr h, compareFloatBits_gt hb hc h]

/-- **SWI puts every NaN first**: SourceTermOrder places a NaN pattern before every pattern
that is not NaN, whatever its sign. -/
theorem compareFloatBits_nan {b c : UInt64} (hb : isNaNBits b = true) (hc : isNaNBits c = false) :
    compareFloatBits b c = .lt := by
  have hne : b ≠ c := fun e => by rw [e, hc] at hb; exact Bool.false_ne_true hb
  unfold compareFloatBits
  rw [if_neg hne, hb, hc]
  rfl

/-! ## IEEE 754's clauses for `totalOrder` -/

/-- **`totalOrder` follows the numeric order** (clause a): on patterns that are not NaN, a
smaller value has a smaller key. -/
theorem totalKey_lt_of_patVal_lt {b c : UInt64} (hb : isNaNBits b = false)
    (hc : isNaNBits c = false) (h : patVal b < patVal c) : totalKey b < totalKey c := by
  by_contra hle
  rcases lt_or_eq_of_le (not_lt.mp hle) with h' | h'
  · rcases patVal_lt_of_key hc hb h' with h'' | ⟨rfl, rfl⟩
    · exact lt_asymm h h''
    · rw [patVal_negZero, patVal_zero] at h
      exact lt_irrefl _ h
  · rw [totalKey_injective h'] at h
    exact lt_irrefl _ h

/-- **`totalOrder` puts `-0` before `+0`** (clause b). -/
theorem totalKey_zeros : totalKey negZeroBits < totalKey 0 := by decide +kernel

/-- **`totalOrder` puts negative NaNs first and positive NaNs last** (clause c): a NaN with the
sign bit set is below every pattern that is not NaN, one with it clear above. -/
theorem totalKey_nan {b c : UInt64} (hb : isNaNBits b = true) (hc : isNaNBits c = false) :
    (signBit b = true → totalKey b < totalKey c) ∧ (signBit b = false → totalKey c < totalKey b) := by
  have hbm := (isNaNBits_iff b).mp hb
  have hcm := mag_le_of_not_nan hc
  rw [totalKey_eq, totalKey_eq]
  constructor <;> intro hs <;> rw [hs] <;> cases signBit c <;>
    simp only [Bool.false_eq_true, if_true, if_false] <;> omega

/-- Among NaNs `totalOrder` puts the negative ones first; positive NaNs come by payload, the
negative ones by payload reversed (clause c). -/
theorem totalKey_nans {b c : UInt64} (hb : isNaNBits b = true) (hc : isNaNBits c = true) :
    (signBit b = true → signBit c = false → totalKey b < totalKey c) ∧
      (signBit b = false → signBit c = false →
        (totalKey b < totalKey c ↔ fractionBits b < fractionBits c)) ∧
      (signBit b = true → signBit c = true →
        (totalKey b < totalKey c ↔ fractionBits c < fractionBits b)) := by
  have hbm := (isNaNBits_iff b).mp hb
  have hcm := (isNaNBits_iff c).mp hc
  have hb2 := mag_lt b
  have hc2 := mag_lt c
  simp only [infMag] at hbm hcm
  rw [totalKey_eq, totalKey_eq, fractionBits_eq, fractionBits_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false] <;> omega

/-! ## NaN payloads -/

open private nanPayloadRat from Mettapedia.Logic.Prolog.SourceTermOrder

theorem testBit_payloadMask (i : ℕ) :
    (0x800fffffffffffff : ℕ).testBit i = (decide (i < 52) || decide (i = 63)) := by
  rcases lt_or_ge i 63 with hi | hi
  · rw [show (0x800fffffffffffff : ℕ) = 2 ^ 63 + (2 ^ 52 - 1) by norm_num,
      Nat.testBit_two_pow_add_gt hi, Nat.testBit_two_pow_sub_one]
    simp [show i ≠ 63 by omega]
  · rcases eq_or_lt_of_le hi with rfl | hi
    · decide
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (0x800fffffffffffff : ℕ) < 2 ^ 64)
        (Nat.pow_le_pow_right (by norm_num) hi))]
      simp [show ¬ i < 52 by omega, show i ≠ 63 by omega]

theorem testBit_biasExponent (i : ℕ) :
    (1023 * 2 ^ 52 : ℕ).testBit i = (decide (52 ≤ i) && decide (i - 52 < 10)) := by
  rw [Nat.testBit_mul_two_pow, show (1023 : ℕ) = 2 ^ 10 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]

/-- **SourceTermOrder reads a NaN's payload as the finite pattern of its sign, the bias exponent
and its fraction.** -/
theorem payload_fields (b : UInt64) :
    signBit ((b &&& UInt64.ofNat 0x800fffffffffffff) ||| (UInt64.ofNat 0x3ff <<< 52)) =
        signBit b ∧
      mag ((b &&& UInt64.ofNat 0x800fffffffffffff) ||| (UInt64.ofNat 0x3ff <<< 52)) =
        1023 * 2 ^ 52 + fractionBits b := by
  have hn := UInt64.toNat_lt b
  have hx := UInt64.toNat_lt ((b &&& UInt64.ofNat 0x800fffffffffffff) |||
    (UInt64.ofNat 0x3ff <<< 52))
  have htoNat : ((b &&& UInt64.ofNat 0x800fffffffffffff) ||| (UInt64.ofNat 0x3ff <<< 52)).toNat =
      (b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52 := by
    rw [UInt64.toNat_or, UInt64.toNat_and]
    rfl
  have hbit : ∀ i, ((b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52).testBit i =
      ((b.toNat.testBit i && (decide (i < 52) || decide (i = 63))) ||
        (decide (52 ≤ i) && decide (i - 52 < 10))) := fun i => by
    rw [Nat.testBit_or, Nat.testBit_and, testBit_payloadMask, testBit_biasExponent]
  rw [htoNat] at hx
  have hlow : ((b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52) % 2 ^ 52 =
      b.toNat % 2 ^ 52 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, hbit]
    by_cases hi : i < 52
    · simp [hi, show ¬ 52 ≤ i by omega]
    · simp [hi]
  have hexp : ((b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52) / 2 ^ 52 % 2 ^ 11 = 1023 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hbit,
      show (1023 : ℕ) = 2 ^ 10 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 10
    · simp [hi, show i < 11 by omega]
    · by_cases hi' : i < 11
      · simp [show i = 10 by omega]
      · simp [hi, hi']
  have hsign : (2 ^ 63 ≤ (b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52) ↔ 2 ^ 63 ≤ b.toNat := by
    have h63 : ((b.toNat &&& 0x800fffffffffffff) ||| 1023 * 2 ^ 52).testBit 63 =
        b.toNat.testBit 63 := by
      rw [hbit]
      simp
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_decide] at h63
    omega
  refine ⟨?_, ?_⟩
  · rw [Bool.eq_iff_iff, signBit_iff, signBit_iff, htoNat]
    exact hsign
  · unfold mag
    rw [htoNat, fractionBits_eq]
    unfold mag
    omega

/-- **SourceTermOrder's value of a NaN payload**: the payload's sign times its fraction's units
in the bias exponent. -/
theorem nanPayloadRat_eq (b : UInt64) :
    nanPayloadRat b =
      (if signBit b then -1 else 1) * (units (1023 * 2 ^ 52 + fractionBits b) : ℚ) / 2 ^ 1074 := by
  unfold nanPayloadRat
  dsimp only
  rw [finiteFloatRat_eq, (payload_fields b).1, (payload_fields b).2]

/-- **SWI's order of NaNs is `totalOrder`'s**: SourceTermOrder compares two NaN patterns by
their payloads' values, which order them by sign, then payload, the negative ones reversed. -/
theorem compareFloatBits_nans {b c : UInt64} (hb : isNaNBits b = true) (hc : isNaNBits c = true) :
    compareFloatBits b c = compare (totalKey b) (totalKey c) := by
  by_cases hbc : b = c
  · subst hbc
    unfold compareFloatBits
    rw [if_pos rfl, compare_eq_iff_eq.mpr rfl]
  have hbm := (isNaNBits_iff b).mp hb
  have hcm := (isNaNBits_iff c).mp hc
  have hb2 := mag_lt b
  have hc2 := mag_lt c
  simp only [infMag] at hbm hcm
  have hfb := fractionBits_eq b
  have hfc := fractionBits_eq c
  have hP : (0 : ℚ) < 2 ^ 1074 := by positivity
  have hub : 0 < units (1023 * 2 ^ 52 + fractionBits b) :=
    lt_of_le_of_lt (Nat.zero_le _) (units_strictMono (by omega : 0 < 1023 * 2 ^ 52 +
      fractionBits b)) |>.trans_eq' units_zero.symm
  have huc : 0 < units (1023 * 2 ^ 52 + fractionBits c) :=
    lt_of_le_of_lt (Nat.zero_le _) (units_strictMono (by omega : 0 < 1023 * 2 ^ 52 +
      fractionBits c)) |>.trans_eq' units_zero.symm
  unfold compareFloatBits
  rw [if_neg hbc, hb, hc]
  simp only [if_true]
  rw [compareRat_eq, nanPayloadRat_eq, nanPayloadRat_eq, totalKey_eq, totalKey_eq]
  have cmp : ∀ (p q : ℚ) (k l : ℤ), (p < q ↔ k < l) → (q < p ↔ l < k) → compare p q = compare k l :=
    fun p q k l h1 h2 => by
      rcases lt_trichotomy k l with h | h | h
      · rw [compare_lt_iff_lt.mpr (h1.mpr h), compare_lt_iff_lt.mpr h]
      · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq]
        exact le_antisymm (not_lt.mp fun h' => lt_irrefl l (h ▸ h2.mp h'))
          (not_lt.mp fun h' => lt_irrefl l (h ▸ h1.mp h'))
      · rw [compare_gt_iff_gt.mpr (h2.mpr h), compare_gt_iff_gt.mpr h]
  have hub' : (0 : ℚ) < units (1023 * 2 ^ 52 + fractionBits b) := by exact_mod_cast hub
  have huc' : (0 : ℚ) < units (1023 * 2 ^ 52 + fractionBits c) := by exact_mod_cast huc
  have mono : ∀ f g : ℕ, f < g → (units (1023 * 2 ^ 52 + f) : ℚ) < units (1023 * 2 ^ 52 + g) :=
    fun f g h => by exact_mod_cast units_strictMono (by omega)
  have mono' : ∀ f g : ℕ, (units (1023 * 2 ^ 52 + f) : ℚ) < units (1023 * 2 ^ 52 + g) → f < g :=
    fun f g h => by
      by_contra hfg
      rcases eq_or_lt_of_le (not_lt.mp hfg) with e | e
      · rw [e] at h
        exact lt_irrefl _ h
      · exact lt_asymm h (mono g f e)
  apply cmp <;> rw [div_lt_div_iff_of_pos_right hP] <;>
    cases hsb : signBit b <;> cases hsc : signBit c <;>
    simp only [Bool.false_eq_true, if_true, if_false, one_mul, neg_one_mul, neg_lt_neg_iff] <;>
    constructor <;> intro h <;>
    first | linarith | omega | (have := mono' _ _ h; omega) | exact mono _ _ (by omega)

theorem compareFloatBits_nan_right {b c : UInt64} (hb : isNaNBits b = false)
    (hc : isNaNBits c = true) : compareFloatBits b c = .gt := by
  have hne : b ≠ c := fun e => by rw [e, hc] at hb; exact Bool.noConfusion hb
  unfold compareFloatBits
  rw [if_neg hne, hb, hc]
  rfl

/-- **SWI's order of floats against IEEE 754's `totalOrder`, on every pair of patterns**: they
agree except on a positive NaN against a pattern that is not NaN, which SWI puts first and
`totalOrder` last. -/
theorem compareFloatBits_eq_totalKey_iff (b c : UInt64) :
    compareFloatBits b c = compare (totalKey b) (totalKey c) ↔
      ¬ ((isNaNBits b = true ∧ signBit b = false ∧ isNaNBits c = false) ∨
        (isNaNBits c = true ∧ signBit c = false ∧ isNaNBits b = false)) := by
  cases hb : isNaNBits b <;> cases hc : isNaNBits c
  · simp only [compareFloatBits_eq_totalKey hb hc, Bool.false_eq_true, false_and, or_self,
      not_false_eq_true]
  · rw [compareFloatBits_nan_right hb hc]
    have := totalKey_nan hc hb
    cases hs : signBit c
    · rw [compare_lt_iff_lt.mpr (this.2 hs)]
      simp
    · rw [compare_gt_iff_gt.mpr (this.1 hs)]
      simp
  · rw [compareFloatBits_nan hb hc]
    have := totalKey_nan hb hc
    cases hs : signBit b
    · rw [compare_gt_iff_gt.mpr (this.2 hs)]
      simp
    · rw [compare_lt_iff_lt.mpr (this.1 hs)]
      simp
  · simp only [compareFloatBits_nans hb hc, Bool.true_eq_false, and_false, or_self,
      not_false_eq_true]

/-! ## SWI's order of numbers on the Prolog heap -/

open Mettapedia.Logic.Prolog.SourceSignature (Constant)

/-- SWI's three-way comparison of numbers, by its key. -/
def swiCompare (x y : Num) : Ordering := compare (rankKey swiRank x) (rankKey swiRank y)

theorem swiCompare_bitsNum {b c : UInt64} (hb : isNaNBits b = false) (hc : isNaNBits c = false) :
    swiCompare (bitsNum b) (bitsNum c) = compare (totalKey b) (totalKey c) := by
  unfold swiCompare
  rcases lt_trichotomy (totalKey b) (totalKey c) with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (rankKey_bitsNum_lt hb hc h)]
  · rw [totalKey_injective h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (rankKey_bitsNum_lt hc hb h)]

theorem rankKey_nan (rank : Num → ℕ) : rankKey rank (.flt .nan) = ⊥ := rfl

theorem rankKey_ne_bot {rank : Num → ℕ} {x : Num} (hx : isNaN x = false) : rankKey rank x ≠ ⊥ := by
  simp [rankKey, hx]

/-- **SWI's order of floats on the heap is SWI's order of their numbers**, on every pair of
patterns but two different NaNs. -/
theorem compareFloatBits_eq_swiCompare {b c : UInt64}
    (h : ¬ (isNaNBits b = true ∧ isNaNBits c = true ∧ b ≠ c)) :
    compareFloatBits b c = swiCompare (bitsNum b) (bitsNum c) := by
  by_cases hbc : b = c
  · subst hbc
    unfold compareFloatBits swiCompare
    rw [if_pos rfl, compare_eq_iff_eq.mpr rfl]
  cases hb : isNaNBits b <;> cases hc : isNaNBits c
  · rw [compareFloatBits_eq_totalKey hb hc, swiCompare_bitsNum hb hc]
  · have hb' : isNaN (bitsNum b) = false := by rw [isNaN_bitsNum, hb]
    have hc' : bitsNum c = .flt .nan := by simp [bitsNum, hc]
    unfold compareFloatBits swiCompare
    rw [if_neg hbc, hb, hc, hc', rankKey_nan, compare_gt_iff_gt.mpr
      (bot_lt_iff_ne_bot.mpr (rankKey_ne_bot hb'))]
    rfl
  · have hc' : isNaN (bitsNum c) = false := by rw [isNaN_bitsNum, hc]
    have hb' : bitsNum b = .flt .nan := by simp [bitsNum, hb]
    rw [compareFloatBits_nan hb hc]
    unfold swiCompare
    rw [hb', rankKey_nan, compare_lt_iff_lt.mpr (bot_lt_iff_ne_bot.mpr (rankKey_ne_bot hc'))]
  · exact absurd ⟨hb, hc, hbc⟩ h

theorem compareFloatInt_eq_swiCompare (b : UInt64) (n : ℤ) :
    compareFloatInt b n = swiCompare (bitsNum b) (.int n) := by
  unfold compareFloatInt swiCompare
  cases hb : isNaNBits b
  · have hb' : isNaN (bitsNum b) = false := by rw [isNaN_bitsNum, hb]
    have hv := valOf_bitsNum hb
    simp only [Bool.false_eq_true, if_false]
    cases hib : isInfinityBits b
    · simp only [Bool.false_eq_true, if_false]
      have hpv : patVal b = ofQ (finiteFloatRat b) := by simp [patVal, hib]
      rw [compareRat_eq, Rat.ofInt_eq_cast]
      rcases lt_trichotomy (finiteFloatRat b) (n : ℚ) with h | h | h
      · rw [compare_lt_iff_lt.mpr h]
        refine (compare_lt_iff_lt.mpr ((rankKey_lt hb' rfl).mpr (Or.inl ?_))).symm
        rw [hv, hpv]
        exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)
      · rw [compare_eq_iff_eq.mpr h]
        refine (compare_lt_iff_lt.mpr ((rankKey_lt hb' rfl).mpr (Or.inr ⟨?_, ?_⟩))).symm
        · rw [hv, hpv, h]
          rfl
        · unfold bitsNum
          rw [hb]
          simp only [Bool.false_eq_true, if_false]
          split_ifs <;> simp [swiRank]
      · rw [compare_gt_iff_gt.mpr h]
        refine (compare_gt_iff_gt.mpr ((rankKey_lt rfl hb').mpr (Or.inl ?_))).symm
        rw [hv, hpv]
        exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)
    · have hpv : patVal b = if signBit b then ⊥ else ⊤ := by simp [patVal, hib]
      cases hs : signBit b
      · simp only [if_true, Bool.false_eq_true, if_false]
        refine (compare_gt_iff_gt.mpr ((rankKey_lt rfl hb').mpr (Or.inl ?_))).symm
        rw [hv, hpv, hs]
        exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
      · simp only [if_true]
        refine (compare_lt_iff_lt.mpr ((rankKey_lt hb' rfl).mpr (Or.inl ?_))).symm
        rw [hv, hpv, hs]
        exact WithBot.bot_lt_coe _
  · have hb' : bitsNum b = .flt .nan := by simp [bitsNum, hb]
    rw [hb', rankKey_nan, compare_lt_iff_lt.mpr (bot_lt_iff_ne_bot.mpr (rankKey_ne_bot rfl))]
    rfl

theorem swiCompare_swap (x y : Num) : swiCompare y x = (swiCompare x y).swap := by
  unfold swiCompare
  exact Std.OrientedCmp.eq_swap

theorem swiCompare_int (m n : ℤ) : swiCompare (.int m) (.int n) = compare m n := by
  unfold swiCompare
  rcases lt_trichotomy m n with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr
      ((rankKey_lt (x := .int m) (y := .int n) rfl rfl).mpr
        (Or.inl (MinMaxSelection.ofQ_lt_ofQ.mpr (Int.cast_lt.mpr h))))]
  · rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr
      ((rankKey_lt (x := .int n) (y := .int m) rfl rfl).mpr
        (Or.inl (MinMaxSelection.ofQ_lt_ofQ.mpr (Int.cast_lt.mpr h))))]

theorem reverseOrdering_eq (o : Ordering) : reverseOrdering o = o.swap := by
  cases o <;> rfl

/-- The number a number constant of the Prolog heap stands for. -/
def constNum : Constant → Option Num
  | .integer n => some (.int n)
  | .floatBits b => some (bitsNum b)
  | _ => none

/-- **SourceTermOrder's number case is SWI's order of numbers**: on every two number constants
of the Prolog heap, integers and binary64 patterns, but two different NaN patterns, the heap's
comparison of constants answers SWI's comparison of the numbers they stand for. -/
theorem compareConstants_eq_swiCompare {c d : Constant} {x y : Num} (hc : constNum c = some x)
    (hd : constNum d = some y)
    (hn : ¬ ∃ b e, c = .floatBits b ∧ d = .floatBits e ∧ isNaNBits b = true ∧
      isNaNBits e = true ∧ b ≠ e) :
    compareConstants c d = .ok (swiCompare x y) := by
  cases c <;> cases d <;> simp only [constNum, reduceCtorEq, Option.some.injEq] at hc hd <;>
    subst hc hd
  · rename_i m n
    show Except.ok (compareInt m n) = _
    rw [compareInt_eq, swiCompare_int]
  · rename_i n b
    show Except.ok (reverseOrdering (compareFloatInt b n)) = _
    rw [reverseOrdering_eq, compareFloatInt_eq_swiCompare, ← swiCompare_swap]
  · rename_i b n
    show Except.ok (compareFloatInt b n) = _
    rw [compareFloatInt_eq_swiCompare]
  · rename_i b e
    show Except.ok (compareFloatBits b e) = _
    rw [compareFloatBits_eq_swiCompare fun h => hn ⟨b, e, rfl, rfl, h⟩]

/-! ## Controls -/

namespace Controls

open MinMaxSWI.Controls (dq)

/-- `1.0`, `-1.0`, `0.5`, the least subnormal `2^-1074`, the infinities, a positive and a
negative quiet NaN, and a positive NaN of another payload. -/
def one : UInt64 := 0x3ff0000000000000
def negOne : UInt64 := 0xbff0000000000000
def half : UInt64 := 0x3fe0000000000000
def leastSubnormal : UInt64 := 1
def posInf : UInt64 := 0x7ff0000000000000
def negInf : UInt64 := 0xfff0000000000000
def posNaN : UInt64 := 0x7ff8000000000000
def negNaN : UInt64 := 0xfff8000000000000
def posNaN' : UInt64 := 0x7ff8000000000001

/-- **The numbers of patterns.** -/
theorem decode :
    bitsNum one = dq 1 ∧ bitsNum negOne = dq (-1) ∧ bitsNum half = dq (1 / 2) ∧
      bitsNum leastSubnormal = dq (1 / 2 ^ 1074) ∧ bitsNum 0 = dq 0 ∧
      bitsNum negZeroBits = .flt .negZero ∧ bitsNum posInf = .flt (.pt ⊤) ∧
      bitsNum negInf = .flt (.pt ⊥) ∧ bitsNum posNaN = .flt .nan ∧ bitsNum negNaN = .flt .nan := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The encoding is monotone**: the keys of `-inf, -1.0, -0.0, 0.0, 2^-1074, 0.5, 1.0, inf`
increase, and so do their values, but for the two zeros, of one value. -/
theorem monotone_keys :
    totalKey negInf < totalKey negOne ∧ totalKey negOne < totalKey negZeroBits ∧
      totalKey negZeroBits < totalKey 0 ∧ totalKey 0 < totalKey leastSubnormal ∧
      totalKey leastSubnormal < totalKey half ∧ totalKey half < totalKey one ∧
      totalKey one < totalKey posInf ∧
      patVal negInf < patVal negOne ∧ patVal negOne < patVal negZeroBits ∧
      patVal negZeroBits = patVal 0 ∧ patVal 0 < patVal leastSubnormal ∧
      patVal leastSubnormal < patVal half ∧ patVal half < patVal one ∧
      patVal one < patVal posInf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **SWI and `totalOrder` agree off NaN**: both put `-0.0` before `0.0`, `-inf` before
`-1.0`, and `1.0` before `inf`. -/
theorem agree_off_nan :
    compareFloatBits negZeroBits 0 = .lt ∧ compare (totalKey negZeroBits) (totalKey 0) = .lt ∧
      compareFloatBits negInf negOne = .lt ∧ compare (totalKey negInf) (totalKey negOne) = .lt ∧
      compareFloatBits posInf one = .gt ∧ compare (totalKey posInf) (totalKey one) = .gt := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Where they differ, a positive NaN**: SWI puts it before `1.0`, `totalOrder` after `1.0`
and after `inf`. -/
theorem positive_nan_differs :
    compareFloatBits posNaN one = .lt ∧ compare (totalKey posNaN) (totalKey one) = .gt ∧
      compareFloatBits posNaN negInf = .lt ∧
      compare (totalKey posNaN) (totalKey posInf) = .gt := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **A negative NaN**: both put it before `1.0` and before `-inf`. -/
theorem negative_nan_agrees :
    compareFloatBits negNaN one = .lt ∧ compare (totalKey negNaN) (totalKey one) = .lt ∧
      compareFloatBits negNaN negInf = .lt ∧
      compare (totalKey negNaN) (totalKey negInf) = .lt := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **NaN payloads, the one pair the numbers do not cover**: SourceTermOrder orders two NaN
payloads, and the numbers they stand for are one NaN. -/
theorem nan_payloads :
    compareFloatBits posNaN posNaN' = .lt ∧ bitsNum posNaN = bitsNum posNaN' ∧
      swiCompare (bitsNum posNaN) (bitsNum posNaN') = .eq := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **`1` and `1.0` on the heap**: SourceTermOrder puts `1.0` before `1`, as SWI's order of
their numbers does; `-1.0` comes after `-9`, by value. -/
theorem one_and_one_point_zero :
    compareConstants (.floatBits one) (.integer 1) = .ok .lt ∧
      compareConstants (.integer 1) (.floatBits one) = .ok .gt ∧
      swiCompare (dq 1) (.int 1) = .lt ∧
      compareConstants (.floatBits negOne) (.integer (-9)) = .ok .gt := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### The theorems on the controls' inputs -/

theorem instances :
    compareFloatBits negZeroBits 0 = compare (totalKey negZeroBits) (totalKey 0) ∧
      compareFloatBits negNaN posNaN = compare (totalKey negNaN) (totalKey posNaN) ∧
      compareFloatBits posNaN one ≠ compare (totalKey posNaN) (totalKey one) ∧
      compareConstants (.floatBits one) (.integer 1) = .ok (swiCompare (bitsNum one) (.int 1)) ∧
      (finiteFloatRat half < finiteFloatRat one ∨
        (signBit half = true ∧ mag half = 0 ∧ signBit one = false ∧ mag one = 0)) :=
  ⟨compareFloatBits_eq_totalKey (by decide) (by decide),
    compareFloatBits_nans (by decide) (by decide),
    fun h => absurd ((compareFloatBits_eq_totalKey_iff _ _).mp h)
      (not_not.mpr (Or.inl ⟨by decide, by decide, by decide⟩)),
    compareConstants_eq_swiCompare rfl rfl (by rintro ⟨b, e, -, h, -⟩; cases h),
    finiteFloatRat_lt_of_key (by decide)⟩

end Controls

end Mettapedia.Machines.AdmissionRewriting.Binary64Order
