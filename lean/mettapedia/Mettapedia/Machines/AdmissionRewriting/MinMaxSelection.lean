import Mettapedia.Machines.AdmissionRewriting.MinMaxSWI

/-!
# PeTTa's `min` and `max` as selections (CeTTa, DIFF-17)

CeTTa's PeTTa lane computes `(min a b)` and `(max a b)` as a **selection** of one of their
operands, by a ruling that PeTTa's semantics follow mathematical coherence (DIFF-17 of its
PeTTa conformance list, entry 17 of its `swi_differences` test); SWI-PeTTa computes them
as arithmetic (`MinMaxSWI`). The rule:
* the answer is an operand itself, never a new value: `(min pi 4)` is `pi`;
* operands are ordered by the exact value they stand for, a constant by the double it reads
  as, integers and doubles compared exactly, and `-0.0` below `0` and `0.0` (`keyOf`);
* a NaN operand propagates, the first one (IEEE 754-2019 `minimum` and `maximum`);
* on a tie `min` answers its first operand and `max` its second.

**The laws** (`selMin`, `selMax`, over operands of any type read as numbers):
* each answers one of its operands (`selMin_mem`, `selMax_mem`), is idempotent
  (`selMin_idem`, `selMax_idem`), is associative exactly, NaN included (`selMin_assoc`,
  `selMax_assoc`), and answers NaN exactly when an operand is NaN (`selMin_nan`,
  `selMax_nan`);
* each is commutative up to equivalence, equal keys or both NaN (`selMin_comm`,
  `selMax_comm`);
* on operands that are not NaN, `(min a b, max a b)` is the stable sort of `(a, b)`: `(b, a)`
  where `b` is strictly below `a`, `(a, b)` otherwise (`stable_sort`, `sort_perm`), and
  absorption holds (`absorb_min_max`, `absorb_max_min`).
A NaN breaks the stable sort and absorption by design, since both answer it
(`Controls.nan_propagates`).

**The C** (`petta_numeric_min_max`, modelled by `cSel`): NaN first; then an exact
comparison of two machine integers, of two doubles, or of a machine integer and a double
(`grounded_int_float_order`, modelled by `cmpIntDblQ`, exact on every machine integer, the
`2^63` edges included: `cmpIntDblQ_exact`); a big integer compared exactly with every other
number (`num_arg_compare_value`; beside a double, the infinities first, then the exact order
of rationals: `cmpExactXR`, `cmpExactXR_exact`); then `-0.0` below the other zeros, then the
tie rule. It is the selection on every pair (`c_select_eq`), so on every pair of PeTTa's
operands (integers, doubles, and the constants `inf`, `-inf`, `nan`, `pi`, `e`, `epsilon`:
`c_select_operands`). The prepared intrinsic's integer path (`min` takes the first where
`a <= b`, `max` the first where `a > b`), the open-equation machine's primitive, and the
native fold on integers are the selection there (`int_paths`).

**A big integer beside a double, compared as doubles** (`cSelLossy`, the C's earlier
fallback to PeTTa's `<` and `>`), breaks the selection. Where the integer rounds to the
double without being equal to it, that comparison takes a tie: `(min 9223372036854775809
9.223372036854775808e18)` answers the integer, though the double is below it, and with the
operands swapped answers the double; `(min (min a b) c)` and `(min a (min b c))` differ for
`a = 2^63 + 1`, `b = 2^63` as a double and `c = 2^63`; `(min inf 10^309)` is `inf` and
`(max inf 10^309)` the integer (`Controls.big_double_inexact`). The C answers the selection
on each (`Controls.big_double_exact`).

**Controls of the other rules.** SWI's rule answers `2.0` for both `(min 2 2.0)` and
`(max 2 2.0)`, and the earlier test rule (`min` the first where `<=` holds, `max` the first
where `>=` holds) answers `2` for both: neither is a stable sort
(`Controls.swi_breaks_sort`, `Controls.le_rule_breaks_sort`). The test `(if (<= x y) x y)`,
comparing as PeTTa's `<=` does, is the selection at a mixed tie but not at signed zeros, at
a NaN first operand, or at an integer and a double equal only as doubles
(`Controls.le_test_differs`), and no test that is false at NaN spells the selection, in
either orientation (`Controls.no_single_test`).

**Not modelled.** Rationals, which no PeTTa program reaches (`MinMaxSWI`), and operands
that are not numbers, which keep the comparison path.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.MinMaxSelection

open MinMaxSWI (XR ofQ Dbl Num Cmp cmpOf cmpOf_lt cmpOf_gt cmpOf_self cmpOf_swap negZ isNaN)

/-! ## The selection -/

/-- The value a number that is not NaN stands for. -/
def valOf : Num → XR
  | .int n => ofQ n
  | .flt .negZero => 0
  | .flt (.pt x) => x
  | .flt .nan => 0

/-- **The order key**: the exact value, then `-0.0` below the other zeros. -/
def keyOf (n : Num) : XR ×ₗ Bool := toLex (valOf n, !negZ n)

/-- `(m, M)` is `(x, y)` or `(y, x)`. -/
def IsPerm {β : Type} (x y m M : β) : Prop := (m = x ∧ M = y) ∨ (m = y ∧ M = x)

instance decidableIsPerm {β : Type} [DecidableEq β] (x y m M : β) :
    Decidable (IsPerm x y m M) :=
  inferInstanceAs (Decidable (_ ∨ _))

section Spec

variable {α : Type} (num : α → Num)

/-- **CeTTa's `min`**: the first NaN operand, else the operand with the lower key, the
first on a tie. -/
def selMin (x y : α) : α :=
  if isNaN (num x) then x else if isNaN (num y) then y
  else if keyOf (num y) < keyOf (num x) then y else x

/-- **CeTTa's `max`**: the first NaN operand, else the operand with the higher key, the
second on a tie. -/
def selMax (x y : α) : α :=
  if isNaN (num x) then x else if isNaN (num y) then y
  else if keyOf (num y) < keyOf (num x) then x else y

theorem selMin_mem (x y : α) : selMin num x y = x ∨ selMin num x y = y := by
  unfold selMin
  split_ifs <;> simp

theorem selMax_mem (x y : α) : selMax num x y = x ∨ selMax num x y = y := by
  unfold selMax
  split_ifs <;> simp

theorem selMin_idem (x : α) : selMin num x x = x := by
  unfold selMin
  split_ifs <;> rfl

theorem selMax_idem (x : α) : selMax num x x = x := by
  unfold selMax
  split_ifs <;> rfl

/-- **The stable sort**: on operands that are not NaN, `(min a b, max a b)` is `(b, a)`
where `b` is strictly below `a`, and `(a, b)` otherwise. -/
theorem stable_sort {x y : α} (hx : isNaN (num x) = false) (hy : isNaN (num y) = false) :
    (selMin num x y, selMax num x y) =
      if keyOf (num y) < keyOf (num x) then (y, x) else (x, y) := by
  unfold selMin selMax
  simp only [hx, hy, Bool.false_eq_true, if_false]
  split_ifs <;> rfl

/-- The stable sort is a permutation of the operands. -/
theorem sort_perm {x y : α} (hx : isNaN (num x) = false) (hy : isNaN (num y) = false) :
    IsPerm x y (selMin num x y) (selMax num x y) := by
  have h := stable_sort num hx hy
  unfold IsPerm
  split_ifs at h
  · right
    simp only [Prod.mk.injEq] at h
    exact h
  · left
    simp only [Prod.mk.injEq] at h
    exact h

/-- Two operands are equivalent: both NaN, or neither NaN with one key. -/
def Equiv (x y : α) : Prop :=
  (isNaN (num x) = true ∧ isNaN (num y) = true) ∨
    (isNaN (num x) = false ∧ isNaN (num y) = false ∧ keyOf (num x) = keyOf (num y))

theorem selMin_comm (x y : α) : Equiv num (selMin num x y) (selMin num y x) := by
  unfold selMin Equiv
  cases hx : isNaN (num x) <;> cases hy : isNaN (num y) <;>
    simp only [hx, hy, Bool.false_eq_true, if_true, if_false, and_true, true_or]
  by_cases h1 : keyOf (num y) < keyOf (num x)
  · have h2 : ¬ keyOf (num x) < keyOf (num y) := not_lt.mpr h1.le
    simp [h1, h2, hy]
  · by_cases h2 : keyOf (num x) < keyOf (num y)
    · simp [h1, h2, hx]
    · have := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      simp [hx, hy, this]

theorem selMax_comm (x y : α) : Equiv num (selMax num x y) (selMax num y x) := by
  unfold selMax Equiv
  cases hx : isNaN (num x) <;> cases hy : isNaN (num y) <;>
    simp only [hx, hy, Bool.false_eq_true, if_true, if_false, and_true, true_or]
  by_cases h1 : keyOf (num y) < keyOf (num x)
  · have h2 : ¬ keyOf (num x) < keyOf (num y) := not_lt.mpr h1.le
    simp [h1, h2, hx]
  · by_cases h2 : keyOf (num x) < keyOf (num y)
    · simp [h1, h2, hy]
    · have := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      simp [hx, hy, this]

theorem selMin_nan (x y : α) :
    isNaN (num (selMin num x y)) = (isNaN (num x) || isNaN (num y)) := by
  unfold selMin
  cases hx : isNaN (num x)
  · cases hy : isNaN (num y)
    · simp only [Bool.false_eq_true, if_false, Bool.or_false]
      split_ifs <;> assumption
    · simp [hy]
  · simp [hx]

theorem selMax_nan (x y : α) :
    isNaN (num (selMax num x y)) = (isNaN (num x) || isNaN (num y)) := by
  unfold selMax
  cases hx : isNaN (num x)
  · cases hy : isNaN (num y)
    · simp only [Bool.false_eq_true, if_false, Bool.or_false]
      split_ifs <;> assumption
    · simp [hy]
  · simp [hx]

/-- **`min` is associative exactly**: both groupings answer the first NaN, or the first
operand with the lowest key. -/
theorem selMin_assoc (x y z : α) :
    selMin num (selMin num x y) z = selMin num x (selMin num y z) := by
  unfold selMin
  cases hx : isNaN (num x) <;> cases hy : isNaN (num y) <;> cases hz : isNaN (num z) <;>
    simp only [hx, hy, hz, Bool.false_eq_true, if_true, if_false]
  all_goals
    first
    | rfl
    | (by_cases h1 : keyOf (num y) < keyOf (num x) <;>
        by_cases h2 : keyOf (num z) < keyOf (num y) <;>
        by_cases h3 : keyOf (num z) < keyOf (num x) <;> simp [hx, hy, hz, h1, h2, h3] <;>
        first
        | exact absurd (h2.trans h1) h3
        | exact absurd h3 (not_lt.mpr ((not_lt.mp h1).trans (not_lt.mp h2))))

/-- **`max` is associative exactly**: both groupings answer the first NaN, or the last
operand with the highest key. -/
theorem selMax_assoc (x y z : α) :
    selMax num (selMax num x y) z = selMax num x (selMax num y z) := by
  unfold selMax
  cases hx : isNaN (num x) <;> cases hy : isNaN (num y) <;> cases hz : isNaN (num z) <;>
    simp only [hx, hy, hz, Bool.false_eq_true, if_true, if_false]
  all_goals
    first
    | rfl
    | (by_cases h1 : keyOf (num y) < keyOf (num x) <;>
        by_cases h2 : keyOf (num z) < keyOf (num y) <;>
        by_cases h3 : keyOf (num z) < keyOf (num x) <;> simp [hx, hy, hz, h1, h2, h3] <;>
        first
        | exact absurd (h2.trans h1) h3
        | exact absurd h3 (not_lt.mpr ((not_lt.mp h1).trans (not_lt.mp h2))))

/-- **Absorption**, on operands that are not NaN. -/
theorem absorb_min_max {x y : α} (hx : isNaN (num x) = false) (hy : isNaN (num y) = false) :
    selMin num x (selMax num x y) = x := by
  unfold selMax selMin
  simp only [hx, hy, Bool.false_eq_true, if_false]
  by_cases h : keyOf (num y) < keyOf (num x)
  · simp [h, hx]
  · simp [h, hy]

theorem absorb_max_min {x y : α} (hx : isNaN (num x) = false) (hy : isNaN (num y) = false) :
    selMax num x (selMin num x y) = x := by
  unfold selMax selMin
  simp only [hx, hy, Bool.false_eq_true, if_false]
  by_cases h : keyOf (num y) < keyOf (num x)
  · simp [h, hy]
  · simp [h, hx]

end Spec

/-! ## The C -/

/-- Truncation toward zero (C's `trunc`). -/
def truncQ (q : ℚ) : ℤ := if 0 ≤ q then ⌊q⌋ else ⌈q⌉

/-- `grounded_int_float_order` past its range checks: the integer against the double's
whole part, then the fraction, which `d - trunc(d)` computes exactly. -/
def cmpIntRat (i : ℤ) (q : ℚ) : Cmp :=
  if i < truncQ q then .lt else if truncQ q < i then .gt
  else if 0 < q - truncQ q then .lt else if q - truncQ q < 0 then .gt else .eq

theorem trunc_bounds (q : ℚ) : (truncQ q : ℚ) - 1 < q ∧ q < (truncQ q : ℚ) + 1 := by
  unfold truncQ
  split_ifs with h
  · exact ⟨by linarith [Int.floor_le q], Int.lt_floor_add_one q⟩
  · exact ⟨by linarith [Int.ceil_lt_add_one q], by linarith [Int.le_ceil q]⟩

/-- **The whole part and the fraction compare exactly.** -/
theorem cmpIntRat_exact (i : ℤ) (q : ℚ) : cmpIntRat i q = cmpOf (i : ℚ) q := by
  obtain ⟨hlo, hhi⟩ := trunc_bounds q
  unfold cmpIntRat
  by_cases h1 : i < truncQ q
  · rw [if_pos h1]
    have : (i : ℚ) ≤ (truncQ q : ℚ) - 1 := by
      have := (Int.cast_le (R := ℚ)).mpr (show i ≤ truncQ q - 1 by omega)
      simpa using this
    exact (cmpOf_lt (by linarith)).symm
  · rw [if_neg h1]
    by_cases h2 : truncQ q < i
    · rw [if_pos h2]
      have : (truncQ q : ℚ) + 1 ≤ (i : ℚ) := by
        have := (Int.cast_le (R := ℚ)).mpr (show truncQ q + 1 ≤ i by omega)
        simpa using this
      exact (cmpOf_gt (by linarith)).symm
    · rw [if_neg h2]
      have hi : (i : ℚ) = truncQ q := by
        have : i = truncQ q := by omega
        rw [this]
      by_cases h3 : 0 < q - truncQ q
      · rw [if_pos h3]
        exact (cmpOf_lt (by linarith)).symm
      · rw [if_neg h3]
        by_cases h4 : q - truncQ q < 0
        · rw [if_pos h4]
          exact (cmpOf_gt (by linarith)).symm
        · rw [if_neg h4]
          have : q = (i : ℚ) := by linarith
          rw [this, cmpOf_self]

/-- `grounded_int_float_order` on a finite double: from `2^63` on the machine integer is
below, under `-2^63` above, else the whole part and the fraction decide. -/
def cmpIntDblQ (i : ℤ) (q : ℚ) : Cmp :=
  if (2 : ℚ) ^ 63 ≤ q then .lt else if q < -(2 : ℚ) ^ 63 then .gt else cmpIntRat i q

/-- A machine integer. -/
abbrev Fits64 (i : ℤ) : Prop := -(2 : ℤ) ^ 63 ≤ i ∧ i < 2 ^ 63

/-- **`grounded_int_float_order` is exact on every machine integer.** -/
theorem cmpIntDblQ_exact {i : ℤ} (hi : Fits64 i) (q : ℚ) :
    cmpIntDblQ i q = cmpOf (i : ℚ) q := by
  obtain ⟨lo, hi'⟩ := hi
  have lo' : -(2 : ℚ) ^ 63 ≤ (i : ℚ) := by exact_mod_cast lo
  have hi'' : (i : ℚ) < (2 : ℚ) ^ 63 := by exact_mod_cast hi'
  unfold cmpIntDblQ
  split_ifs with h1 h2
  · exact (cmpOf_lt (by linarith)).symm
  · exact (cmpOf_gt (by linarith)).symm
  · exact cmpIntRat_exact i q

/-- The C's comparison of a machine integer with a double that is not NaN: `inf` above,
`-inf` below, a finite double by `cmpIntDblQ`. -/
def cmpIntXR (i : ℤ) : XR → Cmp :=
  WithBot.recBotCoe .gt (fun y => WithTop.recTopCoe .lt (fun q => cmpIntDblQ i q) y)

theorem ofQ_lt_ofQ {a b : ℚ} : ofQ a < ofQ b ↔ a < b := by
  unfold ofQ
  simp

theorem cmpOf_ofQ (a b : ℚ) : cmpOf (ofQ a) (ofQ b) = cmpOf a b := by
  simp only [cmpOf, ofQ_lt_ofQ]

theorem cmpIntXR_exact {i : ℤ} (hi : Fits64 i) (x : XR) : cmpIntXR i x = cmpOf (ofQ i) x := by
  induction x using WithBot.recBotCoe with
  | bot =>
      unfold cmpIntXR
      simp only [WithBot.recBotCoe_bot]
      exact (cmpOf_gt (WithBot.bot_lt_coe _)).symm
  | coe y =>
      induction y using WithTop.recTopCoe with
      | top =>
          unfold cmpIntXR
          simp only [WithBot.recBotCoe_coe, WithTop.recTopCoe_top]
          refine (cmpOf_lt ?_).symm
          unfold ofQ
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
      | coe q =>
          unfold cmpIntXR
          simp only [WithBot.recBotCoe_coe, WithTop.recTopCoe_coe]
          rw [cmpIntDblQ_exact hi q]
          exact (cmpOf_ofQ (i : ℚ) q).symm

/-- `num_arg_compare_value` on an exact number `q` against a double that is not NaN: `inf`
above, `-inf` below, a finite double by the exact order of rationals (`mpq_set_d`, then
`mpq_cmp`). -/
def cmpExactXR (q : ℚ) : XR → Cmp :=
  WithBot.recBotCoe .gt (fun y => WithTop.recTopCoe .lt (fun r => cmpOf q r) y)

/-- **`num_arg_compare_value` is exact beside a double.** -/
theorem cmpExactXR_exact (q : ℚ) (x : XR) : cmpExactXR q x = cmpOf (ofQ q) x := by
  induction x using WithBot.recBotCoe with
  | bot =>
      unfold cmpExactXR
      simp only [WithBot.recBotCoe_bot]
      exact (cmpOf_gt (WithBot.bot_lt_coe _)).symm
  | coe y =>
      induction y using WithTop.recTopCoe with
      | top =>
          unfold cmpExactXR
          simp only [WithBot.recBotCoe_coe, WithTop.recTopCoe_top]
          refine (cmpOf_lt ?_).symm
          unfold ofQ
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
      | coe r =>
          unfold cmpExactXR
          simp only [WithBot.recBotCoe_coe, WithTop.recTopCoe_coe]
          exact (cmpOf_ofQ q r).symm

/-- How the C reads an operand (`get_numeric_arg`): a machine integer, a big integer, or a
double (a constant reads as its double). -/
inductive CRead where
  | small (n : ℤ)
  | big (n : ℤ)
  | dbl (d : Dbl)
  deriving DecidableEq

/-- The number a reading stands for. -/
def CRead.num : CRead → Num
  | .small n => .int n
  | .big n => .int n
  | .dbl d => .flt d

/-- A reading `get_numeric_arg` gives: a machine integer is in range. -/
def CRead.WF : CRead → Prop
  | .small m => Fits64 m
  | .big _ => True
  | .dbl _ => True

/-- **The C's comparison** of two operands that are not NaN: machine integers exactly,
doubles as doubles, a machine integer and a double by `grounded_int_float_order`, and a big
integer beside any other number by `num_arg_compare_value`, exactly: as rationals beside an
integer, by `cmpExactXR` beside a double. -/
def cCmp : CRead → CRead → Cmp
  | .small m, .small n => cmpOf m n
  | .dbl d, .dbl e => cmpOf (valOf (.flt d)) (valOf (.flt e))
  | .small m, .dbl e => cmpIntXR m (valOf (.flt e))
  | .dbl d, .small n => (cmpIntXR n (valOf (.flt d))).swap
  | .big m, .big n => cmpOf m n
  | .big m, .small n => cmpOf m n
  | .small m, .big n => cmpOf m n
  | .big m, .dbl e => cmpExactXR m (valOf (.flt e))
  | .dbl d, .big n => (cmpExactXR n (valOf (.flt d))).swap

/-- The C's earlier comparison: as `cCmp`, but a big integer beside a double through
PeTTa's `<` and `>`, as doubles (`rnd` rounds an integer to its double, as `strtod`
does). -/
def cCmpLossy (rnd : ℤ → XR) : CRead → CRead → Cmp
  | .big m, .dbl e => cmpOf (rnd m) (valOf (.flt e))
  | .dbl d, .big n => cmpOf (valOf (.flt d)) (rnd n)
  | a, b => cCmp a b

/-- `-0.0` below `0` and `0.0` on a tie. -/
def zeroTie (c : Cmp) (a b : Num) : Cmp :=
  if c = .eq ∧ negZ a ≠ negZ b then (if negZ a then .lt else .gt) else c

section C

variable {α : Type} (read : α → CRead)

/-- `petta_numeric_min_max` over a comparison `cmp`: the operand itself, by NaN, then the
comparison, then the zeros, then the tie rule. -/
def selectBy (cmp : CRead → CRead → Cmp) (minimum : Bool) (x y : α) : α :=
  if isNaN (read x).num then x
  else if isNaN (read y).num then y
  else
    match zeroTie (cmp (read x) (read y)) (read x).num (read y).num with
    | .eq => if minimum then x else y
    | .lt => if minimum then x else y
    | .gt => if minimum then y else x
    | .unord => if minimum then x else y

/-- **CeTTa's `petta_numeric_min_max`** for `min` (`minimum` true) and `max`. -/
def cSel (minimum : Bool) (x y : α) : α := selectBy read cCmp minimum x y

/-- The C with its earlier comparison, `cCmpLossy`. -/
def cSelLossy (rnd : ℤ → XR) (minimum : Bool) (x y : α) : α :=
  selectBy read (cCmpLossy rnd) minimum x y

end C

theorem cmpOf_int_ofQ (m n : ℤ) : cmpOf m n = cmpOf (ofQ m) (ofQ n) := by
  rw [cmpOf_ofQ]
  simp only [cmpOf, Int.cast_lt]

/-- **The C's comparison is the exact order of values.** -/
theorem cCmp_exact {a b : CRead} (ha : a.WF) (hb : b.WF) :
    cCmp a b = cmpOf (valOf a.num) (valOf b.num) := by
  cases a with
  | small m =>
      cases b with
      | small n => exact cmpOf_int_ofQ m n
      | big n => exact cmpOf_int_ofQ m n
      | dbl e => exact cmpIntXR_exact (i := m) ha _
  | big m =>
      cases b with
      | small n => exact cmpOf_int_ofQ m n
      | big n => exact cmpOf_int_ofQ m n
      | dbl e => exact cmpExactXR_exact m _
  | dbl d =>
      cases b with
      | small n =>
          show (cmpIntXR n (valOf (.flt d))).swap = cmpOf (valOf (.flt d)) (ofQ n)
          rw [cmpIntXR_exact (i := n) hb, ← cmpOf_swap]
      | big n =>
          show (cmpExactXR n (valOf (.flt d))).swap = cmpOf (valOf (.flt d)) (ofQ n)
          rw [cmpExactXR_exact, ← cmpOf_swap]
      | dbl e => rfl

/-- **The value order with `-0.0` below the other zeros is the key order.** -/
theorem zeroTie_key (a b : Num) :
    zeroTie (cmpOf (valOf a) (valOf b)) a b = cmpOf (keyOf a) (keyOf b) := by
  unfold zeroTie keyOf
  rcases lt_trichotomy (valOf a) (valOf b) with h | h | h
  · rw [cmpOf_lt h, cmpOf_lt (Prod.Lex.toLex_lt_toLex.mpr (.inl h))]
    simp
  · rw [h, cmpOf_self]
    cases ha : negZ a <;> cases hb : negZ b <;>
      simp [cmpOf, Prod.Lex.toLex_lt_toLex]
  · rw [cmpOf_gt h, cmpOf_gt (Prod.Lex.toLex_lt_toLex.mpr (.inl h))]
    simp

/-- **The C is the selection**: `petta_numeric_min_max` answers `selMin` for `min` and
`selMax` for `max`, on every pair. -/
theorem c_select_eq {α : Type} (read : α → CRead) (x y : α) (hx : (read x).WF)
    (hy : (read y).WF) :
    cSel read true x y = selMin (fun z => (read z).num) x y ∧
      cSel read false x y = selMax (fun z => (read z).num) x y := by
  simp only [cSel, selectBy, selMin, selMax]
  cases hnx : isNaN (read x).num
  · cases hny : isNaN (read y).num
    · rw [cCmp_exact hx hy, zeroTie_key]
      simp only [Bool.false_eq_true, if_false]
      rcases lt_trichotomy (keyOf (read x).num) (keyOf (read y).num) with h | h | h
      · rw [cmpOf_lt h]
        simp [not_lt.mpr h.le]
      · rw [h, cmpOf_self]
        simp
      · rw [cmpOf_gt h]
        simp [h]
    · simp
  · simp

/-- **The integer paths are the selection on integers**: the prepared intrinsic on machine
integers (`min` the first where `a <= b`; `max` the first where `a > b`, else the second),
the open-equation machine's primitive and the native fold's (`a < b ? a : b`,
`a > b ? a : b`, one value either way on a tie), and the native fold's big integers
(`mpz_cmp` at most zero for `min`, at least zero for `max`). -/
theorem int_paths (m n : ℤ) :
    (if m ≤ n then Num.int m else Num.int n) = selMin id (Num.int m) (Num.int n) ∧
      (if n < m then Num.int m else Num.int n) = selMax id (Num.int m) (Num.int n) ∧
      Num.int (if m < n then m else n) = selMin id (Num.int m) (Num.int n) ∧
      Num.int (if n < m then m else n) = selMax id (Num.int m) (Num.int n) ∧
      (if n ≤ m then Num.int m else Num.int n) = selMax id (Num.int m) (Num.int n) := by
  have key : keyOf (Num.int n) < keyOf (Num.int m) ↔ n < m := by
    simp only [keyOf, valOf, negZ, Bool.not_false, Prod.Lex.toLex_lt_toLex, ofQ_lt_ofQ,
      Int.cast_lt, lt_self_iff_false, and_false, or_false]
  have h := stable_sort id (x := Num.int m) (y := Num.int n) rfl rfl
  simp only [id, key] at h
  by_cases hnm : n < m
  · rw [if_pos hnm, Prod.mk.injEq] at h
    rw [h.1, h.2]
    simp [hnm, hnm.le, not_le.mpr hnm, not_lt.mpr hnm.le]
  · rw [if_neg hnm, Prod.mk.injEq] at h
    rw [h.1, h.2]
    have hmn : m ≤ n := not_lt.mp hnm
    rcases eq_or_lt_of_le hmn with e | e
    · subst e
      simp
    · simp [hnm, hmn, e, not_le.mpr e]

/-! ## PeTTa's operands -/

/-- The symbols the C reads as numbers in the PeTTa lane (`get_numeric_arg`). -/
inductive Const where
  | inf
  | negInf
  | nan
  | pi
  | e
  | epsilon
  deriving DecidableEq

/-- The double a constant reads as: the infinities, NaN, `acos(-1.0)` (the double nearest
π), `exp(1.0)` (the double nearest e) and `DBL_EPSILON`. -/
def Const.dbl : Const → Dbl
  | .inf => .pt ⊤
  | .negInf => .pt ⊥
  | .nan => .nan
  | .pi => .pt (ofQ (884279719003555 / 2 ^ 48))
  | .e => .pt (ofQ (6121026514868073 / 2 ^ 51))
  | .epsilon => .pt (ofQ (1 / 2 ^ 52))

/-- An operand of `min` or `max` in a PeTTa program: an integer (a machine integer or a big
one), a double, or a constant. -/
inductive Operand where
  | int (n : ℤ)
  | dbl (d : Dbl)
  | const (c : Const)
  deriving DecidableEq

/-- The number an operand stands for. -/
def Operand.num : Operand → Num
  | .int n => .int n
  | .dbl d => .flt d
  | .const c => .flt c.dbl

/-- `get_numeric_arg` on an operand. -/
def Operand.read : Operand → CRead
  | .int n => if Fits64 n then .small n else .big n
  | .dbl d => .dbl d
  | .const c => .dbl c.dbl

theorem read_num (o : Operand) : o.read.num = o.num := by
  cases o with
  | int n =>
      show (if Fits64 n then CRead.small n else CRead.big n).num = .int n
      split_ifs <;> rfl
  | dbl d => rfl
  | const c => rfl

/-- `get_numeric_arg` reads an operand as a machine integer only in range. -/
theorem read_wf (o : Operand) : o.read.WF := by
  cases o with
  | int n =>
      show (if Fits64 n then CRead.small n else CRead.big n).WF
      split_ifs with h
      · exact h
      · exact True.intro
  | dbl d => exact True.intro
  | const c => exact True.intro

/-- **On PeTTa's operands the C is the selection.** -/
theorem c_select_operands (x y : Operand) :
    cSel Operand.read true x y = selMin Operand.num x y ∧
      cSel Operand.read false x y = selMax Operand.num x y := by
  have e : (fun z => (Operand.read z).num) = Operand.num := funext read_num
  rw [← e]
  exact c_select_eq Operand.read x y (read_wf x) (read_wf y)

/-! ## Controls -/

namespace Controls

open MinMaxSWI (swiMin swiMax)
open MinMaxSWI.Controls (nearest dq ieeeLe leSelect)

/-- **`(min pi 4)` is `pi`**, the operand itself, in the selection and in the C. -/
theorem pi_selected :
    selMin Operand.num (.const .pi) (.int 4) = .const .pi ∧
      cSel Operand.read true (.const .pi) (.int 4) = .const .pi := by
  constructor <;> decide +kernel

/-- **SWI's rule is no stable sort**: `(min 2 2.0)` and `(max 2 2.0)` are both `2.0`; the
selection answers `2` and `2.0`. -/
theorem swi_breaks_sort :
    swiMin nearest (.int 2) (dq 2) = dq 2 ∧ swiMax nearest (.int 2) (dq 2) = dq 2 ∧
      ¬ IsPerm (Num.int 2) (dq 2) (swiMin nearest (.int 2) (dq 2))
        (swiMax nearest (.int 2) (dq 2)) ∧
      selMin id (Num.int 2) (dq 2) = .int 2 ∧ selMax id (Num.int 2) (dq 2) = dq 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **On SWI's signed-zero and NaN cases the rules agree**: `(min -0.0 0)` is `-0.0`,
`(max -0.0 0)` is `0`, `(min 0.0 -0.0)` is `-0.0`, `(max 0.0 -0.0)` is `0.0`, `(max nan 1)`
is NaN. -/
theorem swi_agrees :
    selMin id (Num.flt .negZero) (.int 0) = swiMin nearest (.flt .negZero) (.int 0) ∧
      selMax id (Num.flt .negZero) (.int 0) = swiMax nearest (.flt .negZero) (.int 0) ∧
      selMin id (dq 0) (.flt .negZero) = swiMin nearest (dq 0) (.flt .negZero) ∧
      selMax id (dq 0) (.flt .negZero) = swiMax nearest (dq 0) (.flt .negZero) ∧
      selMax id (Num.flt .nan) (.int 1) = swiMax nearest (.flt .nan) (.int 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The test select for `max`, `(if (>= x y) x y)`. -/
def geSelect (x y : Num) : Num := if ieeeLe nearest y x then x else y

/-- **The earlier test rule is no stable sort**: `min` the first where `<=` holds and `max`
the first where `>=` holds answer `2` for both `(min 2 2.0)` and `(max 2 2.0)`. -/
theorem le_rule_breaks_sort :
    leSelect nearest (.int 2) (dq 2) = .int 2 ∧ geSelect (.int 2) (dq 2) = .int 2 ∧
      ¬ IsPerm (Num.int 2) (dq 2) (leSelect nearest (.int 2) (dq 2))
        (geSelect (.int 2) (dq 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **NaN propagates through both**, so it breaks the stable sort and absorption by design:
`(min nan 1)` and `(max nan 1)` are both `nan`, and `(min 1 (max 1 nan))` is `nan`. -/
theorem nan_propagates :
    selMin id (Num.flt .nan) (.int 1) = .flt .nan ∧
      selMax id (Num.flt .nan) (.int 1) = .flt .nan ∧
      ¬ IsPerm (Num.flt .nan) (.int 1) (selMin id (Num.flt .nan) (.int 1))
        (selMax id (Num.flt .nan) (.int 1)) ∧
      selMin id (Num.int 1) (selMax id (Num.int 1) (.flt .nan)) = .flt .nan := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The comparison test is not the selection**: `(if (<= x y) x y)`, comparing as PeTTa's
`<=` does, answers the first operand at `(min 0.0 -0.0)`, `(min nan 1)` and `(min
9007199254740993 9007199254740992.0)`, where the selection answers `-0.0`, `nan` and the
double; at the mixed tie `(min 1 1.0)` both answer `1`. -/
theorem le_test_differs :
    leSelect nearest (dq 0) (.flt .negZero) = dq 0 ∧
      selMin id (dq 0) (.flt .negZero) = .flt .negZero ∧
      leSelect nearest (.flt .nan) (.int 1) = .int 1 ∧
      selMin id (Num.flt .nan) (.int 1) = .flt .nan ∧
      leSelect nearest (.int 9007199254740993) (dq 9007199254740992) = .int 9007199254740993 ∧
      selMin id (Num.int 9007199254740993) (dq 9007199254740992) = dq 9007199254740992 ∧
      leSelect nearest (.int 1) (dq 1) = .int 1 ∧ selMin id (Num.int 1) (dq 1) = .int 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **No single test spells the selection**: an `if` on one test that is false at NaN
answers a number where the selection answers NaN, in either orientation. -/
theorem no_single_test (cmp : Num → Num → Bool)
    (h : ∀ x, cmp (.flt .nan) x = false ∧ cmp x (.flt .nan) = false) :
    (∃ x y : Num, (if cmp x y then x else y) ≠ selMin id x y) ∧
      ∃ x y : Num, (if cmp y x then y else x) ≠ selMin id x y := by
  refine ⟨⟨.flt .nan, .int 1, ?_⟩, ⟨.int 1, .flt .nan, ?_⟩⟩ <;>
    simp [(h (.int 1)).1, selMin, isNaN]

/-- `2^63 + 1`, `2^63` as a double, `2^63`, and `10^309`. -/
def aBig : Operand := .int (2 ^ 63 + 1)
def bDbl : Operand := .dbl (.pt (ofQ (2 ^ 63)))
def cBig : Operand := .int (2 ^ 63)
def huge : Operand := .int (10 ^ 309)

/-- **A big integer beside a double, compared as a double, breaks the selection**: with
that comparison `(min 9223372036854775809 9.223372036854775808e18)` answers the integer,
though the double is below it, the swapped call answers the double, `max` answers the
double, the two groupings of `(min a b c)` differ, and `(min inf 10^309)` is `inf` while
`(max inf 10^309)` is the integer. -/
theorem big_double_inexact :
    cSelLossy Operand.read nearest true aBig bDbl = aBig ∧
      selMin Operand.num aBig bDbl = bDbl ∧
      cSelLossy Operand.read nearest true bDbl aBig = bDbl ∧
      cSelLossy Operand.read nearest false aBig bDbl = bDbl ∧
      selMax Operand.num aBig bDbl = aBig ∧
      cSelLossy Operand.read nearest true (cSelLossy Operand.read nearest true aBig bDbl) cBig =
        cBig ∧
      cSelLossy Operand.read nearest true aBig (cSelLossy Operand.read nearest true bDbl cBig) =
        aBig ∧
      cSelLossy Operand.read nearest true (.const .inf) huge = .const .inf ∧
      selMin Operand.num (.const .inf) huge = huge ∧
      cSelLossy Operand.read nearest false (.const .inf) huge = huge ∧
      selMax Operand.num (.const .inf) huge = .const .inf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The C answers the selection there**: `(min 9223372036854775809
9.223372036854775808e18)` is the double in either order, and their `max` the integer; both
groupings of `(min a b c)` are the double; `(min inf 10^309)` is the integer and
`(max inf 10^309)` is `inf`. -/
theorem big_double_exact :
    cSel Operand.read true aBig bDbl = bDbl ∧ cSel Operand.read true bDbl aBig = bDbl ∧
      cSel Operand.read false aBig bDbl = aBig ∧
      cSel Operand.read true (cSel Operand.read true aBig bDbl) cBig = bDbl ∧
      cSel Operand.read true aBig (cSel Operand.read true bDbl cBig) = bDbl ∧
      cSel Operand.read true (.const .inf) huge = huge ∧
      cSel Operand.read false (.const .inf) huge = .const .inf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- An integer, a double by its rational value, and `-0.0`, as operands. -/
def ti (n : ℤ) : Operand := .int n
def tf (q : ℚ) : Operand := .dbl (.pt (ofQ q))
def tnz : Operand := .dbl .negZero

/-- The calls of CeTTa's test `tests/petta/minmax_selection` of one `min` (`true`) or `max` on
two literals, with the answer it expects; `3.141592653589793` is the double `pi` reads as.
Its calls through user functions repeat these. -/
def testCases : List (Bool × Operand × Operand × Operand) := [
  (true, ti 2, tf 2, ti 2), (true, tf 2, ti 2, tf 2),
  (false, ti 2, tf 2, tf 2), (false, tf 2, ti 2, ti 2),
  (true, tnz, tf 0, tnz), (true, tf 0, tnz, tnz),
  (false, tnz, tf 0, tf 0), (false, tf 0, tnz, tf 0),
  (true, ti 0, tnz, tnz), (true, tnz, ti 0, tnz),
  (false, ti 0, tnz, ti 0), (false, tnz, ti 0, ti 0),
  (true, tf 0, ti 0, tf 0), (false, ti 0, tf 0, tf 0),
  (true, ti 1, tf (5 / 2), ti 1), (true, ti 3, tf (5 / 2), tf (5 / 2)),
  (true, ti (2 ^ 63 - 1), ti (2 ^ 63), ti (2 ^ 63 - 1)),
  (false, ti 9007199254740993, tf 9007199254740992, ti 9007199254740993),
  (true, ti (2 ^ 63 + 1), tf (2 ^ 63), tf (2 ^ 63)),
  (false, tf (2 ^ 63), ti (2 ^ 63 + 1), ti (2 ^ 63 + 1)),
  (true, ti (-2 ^ 63), tf (-2 ^ 63), ti (-2 ^ 63)),
  (false, ti (-2 ^ 63), tf (-2 ^ 63), tf (-2 ^ 63)),
  (true, .const .inf, ti (10 ^ 50), ti (10 ^ 50)),
  (false, .const .negInf, ti (-10 ^ 50), ti (-10 ^ 50)),
  (true, .const .pi, tf (884279719003555 / 2 ^ 48), .const .pi),
  (true, .const .pi, ti 4, .const .pi), (false, .const .e, ti 1, .const .e),
  (true, ti 4, .const .pi, .const .pi),
  (false, .const .nan, tf 1, .const .nan), (true, tf 1, .const .nan, .const .nan),
  (true, .const .inf, ti 1, ti 1), (true, ti 3, ti 3, ti 3)]

/-- **The answers `tests/petta/minmax_selection` expects are the selection's**, its two
nested calls included; by `c_select_operands` they are the C's. -/
theorem test_expected :
    testCases.all (fun ⟨m, a, b, r⟩ =>
        (if m then selMin Operand.num a b else selMax Operand.num a b) == r) = true ∧
      selMin Operand.num (selMin Operand.num (ti (2 ^ 63 + 1)) (tf (2 ^ 63))) (ti (2 ^ 63)) =
        tf (2 ^ 63) ∧
      selMin Operand.num (ti (2 ^ 63 + 1)) (selMin Operand.num (tf (2 ^ 63)) (ti (2 ^ 63))) =
        tf (2 ^ 63) := by
  decide +kernel

end Controls

end Mettapedia.Machines.AdmissionRewriting.MinMaxSelection
