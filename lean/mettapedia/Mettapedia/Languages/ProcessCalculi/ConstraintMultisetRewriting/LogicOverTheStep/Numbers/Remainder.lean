import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower
import Mathlib.Data.Rat.Floor

/-!
# HE's remainder meets every law

Measured on hyperon-experimental, one call per file: `(% -7 2)` is `-1`, `(% 7 -2)` is `1`,
`(% 5.0 2)` is `1.0`, `(% 5.5 2)` is `1.5`. The remainder truncates toward zero on whole values and
on fractions alike, whatever the storage.

* **Truncation of a rational** (`truncQ`) and **the truncated remainder of rationals** (`remQ`:
  `a - b * truncQ (a / b)`).
* **On whole values it is the remainder of the integers** (`truncQ_div`: the truncation of `m / n` is
  `m.tdiv n`; `remQ_whole`), so the remainder commutes with the conversion from whole numbers to
  rationals.
* **A model of measured behaviour, HE's `%`** (`heRem`: on two stored integers the integer remainder,
  otherwise the truncated remainder of the values) **respects the value lens**: for every nonzero
  divisor its value is `remQ` of the values, however stored (`heRem_value`, `heRem_respects`). The
  measured rows are reproduced (`heRem_rows`).

So among the measured operations `%` meets every law, while the storage-dependent `/` breaks the
value law and coherence (`NumberLens.storedQuotient_not_respects`,
`Coherence.storageDiv_incoherent`), and `+`, `-`, `*` break the value law only at the 64-bit width
(`FastPaths.checkedMul_not_respects`, `Dialects.no_cliffs`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Remainder

open Distinctions.ObserverConcepts Distinctions.NumberLens Tower

/-- **Truncation toward zero** of a rational. -/
def truncQ (q : ℚ) : ℤ := if 0 ≤ q then ⌊q⌋ else ⌈q⌉

/-- **The truncated remainder** of rationals. -/
def remQ (a b : ℚ) : ℚ := a - b * truncQ (a / b)

theorem truncQ_div_nat (m : ℤ) {d : ℕ} (positive : 0 < d) : truncQ ((m : ℚ) / d) = m.tdiv d := by
  unfold truncQ
  by_cases nonneg : 0 ≤ m
  · have quotientNonneg : (0 : ℚ) ≤ (m : ℚ) / d :=
      div_nonneg (by exact_mod_cast nonneg) (Nat.cast_nonneg d)
    rw [if_pos quotientNonneg, Rat.floor_intCast_div_natCast, Int.tdiv_eq_ediv_of_nonneg nonneg]
  · have negative : m < 0 := lt_of_not_ge nonneg
    have quotientNeg : ¬ (0 : ℚ) ≤ (m : ℚ) / d := by
      rw [not_le]
      exact div_neg_of_neg_of_pos (by exact_mod_cast negative) (by exact_mod_cast positive)
    have flip : m.tdiv d = -((-m).tdiv d) := by
      rw [Int.neg_tdiv, neg_neg]
    rw [if_neg quotientNeg, Rat.ceil_intCast_div_natCast, flip,
      Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ -m by omega)]

/-- **The truncation of `m / n` is the integer quotient toward zero.** -/
theorem truncQ_div (m n : ℤ) (nonzero : n ≠ 0) : truncQ ((m : ℚ) / n) = m.tdiv n := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = -(d : ℤ) := ⟨(-n).toNat, by omega⟩
    have positiveD : 0 < d := by omega
    have rewritten : (m : ℚ) / ((-(d : ℤ) : ℤ) : ℚ) = ((-m : ℤ) : ℚ) / (d : ℚ) := by
      push_cast
      rw [div_neg, neg_div]
    rw [rewritten, truncQ_div_nat (-m) positiveD, Int.tdiv_neg, Int.neg_tdiv]
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = (d : ℤ) := ⟨n.toNat, by omega⟩
    have positiveD : 0 < d := by omega
    rw [Int.cast_natCast]
    exact truncQ_div_nat m positiveD

/-- **On whole values the truncated remainder of rationals is the remainder of the integers.** -/
theorem remQ_whole (m n : ℤ) (nonzero : n ≠ 0) : remQ m n = ((m.tmod n : ℤ) : ℚ) := by
  unfold remQ
  rw [truncQ_div m n nonzero, Int.tmod_def, Int.cast_sub, Int.cast_mul]

/-- **A model of measured behaviour, HE's `%`**: on two stored integers the integer remainder, with
the dividend's sign; otherwise the truncated remainder of the values. -/
def heRem (x y : Stored) : Stored :=
  match x, y with
  | .int m, .int n => .int (m.tmod n)
  | x, y => .frac (remQ (value x) (value y))

/-- **Its value is the truncated remainder of the values**, for every nonzero divisor, however
stored. -/
theorem heRem_value (x y : Stored) (nonzero : value y ≠ 0) :
    value (heRem x y) = remQ (value x) (value y) := by
  cases x with
  | int m =>
      cases y with
      | int n =>
          have whole : n ≠ 0 := by
            rintro rfl
            exact nonzero (by simp [value])
          exact (remQ_whole m n whole).symm
      | frac q => rfl
  | frac p => cases y <;> rfl

/-- **HE's `%` respects the value lens.** -/
theorem heRem_respects (x x' y y' : Stored) (first : value x = value x') (second : value y = value y')
    (nonzero : value y ≠ 0) : value (heRem x y) = value (heRem x' y') := by
  have nonzero' : value y' ≠ 0 := by
    rw [← second]
    exact nonzero
  rw [heRem_value x y nonzero, heRem_value x' y' nonzero', first, second]

/-- **The measured rows**: `(% -7 2)` is `-1`, `(% 7 -2)` is `1`, `(% 5.0 2)` is `1`, `(% 5.5 2)`
is `3/2`, `(% -5.5 2)` is `-3/2`. -/
theorem heRem_rows :
    heRem (.int (-7)) (.int 2) = .int (-1) ∧ heRem (.int 7) (.int (-2)) = .int 1 ∧
      value (heRem (.frac 5) (.int 2)) = 1 ∧ value (heRem (.frac (11 / 2)) (.int 2)) = 3 / 2 ∧
      value (heRem (.frac (-11 / 2)) (.int 2)) = -3 / 2 := by
  refine ⟨congrArg Stored.int (by decide : Int.tmod (-7) 2 = -1),
    congrArg Stored.int (by decide : Int.tmod 7 (-2) = 1), ?_, ?_, ?_⟩
  · show remQ 5 ((2 : ℤ) : ℚ) = 1
    rw [show (5 : ℚ) = ((5 : ℤ) : ℚ) by norm_num, remQ_whole 5 2 (by decide),
      show Int.tmod 5 2 = 1 by decide]
    norm_num
  · show remQ (11 / 2) ((2 : ℤ) : ℚ) = 3 / 2
    have quotient : truncQ ((11 / 2 : ℚ) / ((2 : ℤ) : ℚ)) = 2 := by
      unfold truncQ
      rw [if_pos (show (0 : ℚ) ≤ (11 / 2 : ℚ) / ((2 : ℤ) : ℚ) by norm_num), Int.floor_eq_iff]
      norm_num
    unfold remQ
    rw [quotient]
    norm_num
  · show remQ (-11 / 2) ((2 : ℤ) : ℚ) = -3 / 2
    have quotient : truncQ ((-11 / 2 : ℚ) / ((2 : ℤ) : ℚ)) = -2 := by
      unfold truncQ
      rw [if_neg (show ¬ (0 : ℚ) ≤ (-11 / 2 : ℚ) / ((2 : ℤ) : ℚ) by norm_num), Int.ceil_eq_iff]
      norm_num
    unfold remQ
    rw [quotient]
    norm_num

#print axioms truncQ_div_nat
#print axioms truncQ_div
#print axioms remQ_whole
#print axioms heRem_value
#print axioms heRem_respects
#print axioms heRem_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Remainder
