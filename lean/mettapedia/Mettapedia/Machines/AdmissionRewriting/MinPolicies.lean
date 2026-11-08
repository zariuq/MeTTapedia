import Mathlib.Tactic

/-!
# `min` on numbers: ties, signed zeros, NaN, and which `if` spellings are sound

The admission rule rewrites `(min a b)` to `(let $x a (let $y b (if (<= $x $y) $x $y)))`.
Its soundness needs the dialect's `min` to be that test on every pair of values
(`Semantics.MinProtocol`).  This file models numbers with integers, floats (a rational
value; zero carries a sign), and NaN, and compares the policies a dialect may choose.

**The comparisons** are IEEE's: every comparison with NaN is false, and `-0.0` and `0.0`
are equal (neither is less).  Integers and floats compare by value, so `1` and `1.0` are
equal.

**The policies.**
* `minLe x y`: `x` if `x <= y`, else `y`: CeTTa's PeTTa lane on numbers before it computed
  SWI's `min` (`MinMaxSWI`) and then the selection (`MinMaxSelection`), measured on the
  probes then:
  `(min 0.0 -0.0)` is `0.0`, `(min -0.0 0.0)` is `-0.0`, `(min 1 1.0)` is `1`, `(min 1.0 1)`
  is `1.0`, `(min nan 1)` is `1`, `(min 1 nan)` is `nan`.
* `minLt x y`: `y` if `y < x`, else `x`.
* `minNum` (IEEE 754-2008): the number when one operand is NaN, NaN only when both are.
* `minimum` (IEEE 754-2019): NaN when either is NaN, and `-0.0` below `0.0`.  CeTTa's PeTTa
  lane now selects an operand (`MinMaxSelection`, DIFF-17), which keeps both: a NaN operand
  propagates, and `-0.0` is below `0` and `0.0`.

This file proves:
* `minLe_ties_first`, `minLt_ties_first`: on equal values both answer the first argument:
  the choice CeTTa made (`(min 0.0 -0.0)` was `0.0`; `(min 1 1.0)` is still `1`);
* `minLe_eq_minLt`: off NaN the two spellings agree; `nan_controls`: on NaN they differ,
  each from the other and from `minNum` and `minimum`;
* `no_single_test_minNum`, `no_single_test_minimum`: no `if` on one comparison that is false
  at NaN computes `minNum` or `minimum`, in either orientation: a dialect choosing either
  needs a NaN test before the comparison, or no rule;
* `error_order`: on operands that are not numbers, `min` raises on its first operand that
  is not a number; `(<= $x $y)` raises on the same one, and `(< $y $x)` raises on the
  second when neither is a number.

So for CeTTa's `min` as it was, the rule's spelling must be `(<= $x $y)`, not `(< $y $x)`.
The NaN policy itself is a choice of the dialect; the rule follows it.  CeTTa's PeTTa lane
now selects an operand (`MinMaxSelection`): like `minimum` it propagates NaN and puts `-0.0`
below the other zeros, so no single test spells it (`MinMaxSelection.Controls.no_single_test`,
as `no_single_test_minimum` here), and on doubles the rule is not the dialect's `min`
(`MinMaxSelection.Controls.le_test_differs`); CeTTa runs `min` as an intrinsic.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.MinPolicies

/-- Numbers: an integer, a float (its value; `negZero` marks `-0.0`), or NaN. -/
inductive Num
  | int (n : ℤ)
  | flt (q : ℚ) (negZero : Bool)
  | nan
  deriving DecidableEq

/-- The value of a number that is not NaN. -/
def Num.val : Num → Option ℚ
  | .int n => some n
  | .flt q _ => some q
  | .nan => none

/-- IEEE `<`: false whenever an operand is NaN. -/
def lt (x y : Num) : Bool :=
  match x.val, y.val with
  | some a, some b => decide (a < b)
  | _, _ => false

/-- IEEE `<=`: false whenever an operand is NaN. -/
def le (x y : Num) : Bool :=
  match x.val, y.val with
  | some a, some b => decide (a ≤ b)
  | _, _ => false

/-- `x` if `x <= y`, else `y`. -/
def minLe (x y : Num) : Num := if le x y then x else y

/-- `y` if `y < x`, else `x`. -/
def minLt (x y : Num) : Num := if lt y x then y else x

/-- IEEE 754-2008 `minNum`: the number when one operand is NaN. -/
def minNum (x y : Num) : Num :=
  match x, y with
  | .nan, _ => y
  | _, .nan => x
  | _, _ => minLe x y

/-- IEEE 754-2019 `minimum`: NaN when either is NaN; `-0.0` below `0.0`. -/
def minimum (x y : Num) : Num :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .flt 0 false, .flt 0 true => y
  | _, _ => minLe x y

/-- `0.0`, `-0.0`, `1`, `1.0`. -/
abbrev zero : Num := .flt 0 false
abbrev negZero : Num := .flt 0 true
abbrev one : Num := .int 1
abbrev oneF : Num := .flt 1 false

theorem minLe_ties_first {x y : Num} (hx : x.val.isSome) (h : x.val = y.val) : minLe x y = x := by
  cases hv : x.val with
  | none => simp [hv] at hx
  | some a =>
    rw [hv] at h
    simp [minLe, le, hv, ← h]

theorem minLt_ties_first {x y : Num} (h : x.val = y.val) : minLt x y = x := by
  unfold minLt lt
  cases hv : x.val with
  | none => cases hw : y.val <;> simp
  | some a =>
    rw [hv] at h
    rw [← h]
    simp

/-- Signed zeros and mixed numbers: the first argument on ties. -/
theorem ties_controls :
    minLe zero negZero = zero ∧ minLe negZero zero = negZero ∧ minLe one oneF = one ∧
      minLe oneF one = oneF ∧ minLt zero negZero = zero ∧ minLt one oneF = one := by
  decide

theorem val_of_ne_nan {x : Num} (h : x ≠ .nan) : ∃ a, x.val = some a := by
  cases x with
  | int n => exact ⟨n, rfl⟩
  | flt q z => exact ⟨q, rfl⟩
  | nan => exact absurd rfl h

/-- Off NaN the two spellings agree. -/
theorem minLe_eq_minLt {x y : Num} (hx : x ≠ .nan) (hy : y ≠ .nan) : minLe x y = minLt x y := by
  obtain ⟨a, ha⟩ := val_of_ne_nan hx
  obtain ⟨b, hb⟩ := val_of_ne_nan hy
  unfold minLe minLt le lt
  rw [ha, hb]
  by_cases h : a ≤ b
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]

/-- On NaN the policies part: `minLe` follows NaN in the second place, `minLt` in the
first, `minNum` drops it, `minimum` keeps it, and only `minimum` puts `-0.0` below `0.0`. -/
theorem nan_controls :
    minLe .nan one = one ∧ minLe one .nan = .nan ∧
      minLt .nan one = .nan ∧ minLt one .nan = one ∧
      minNum .nan one = one ∧ minNum one .nan = one ∧
      minimum .nan one = .nan ∧ minimum one .nan = .nan ∧
      minimum zero negZero = negZero ∧ minLe zero negZero = zero := by
  decide

/-- A comparison false whenever an operand is NaN, as every IEEE comparison is. -/
def NaNFalse (cmp : Num → Num → Bool) : Prop := ∀ x, cmp .nan x = false ∧ cmp x .nan = false

/-- No `if` on one such comparison computes `minNum`, in either orientation. -/
theorem no_single_test_minNum (cmp : Num → Num → Bool) (h : NaNFalse cmp) :
    (¬ ∀ x y, (if cmp x y then x else y) = minNum x y) ∧
      ¬ ∀ x y, (if cmp y x then y else x) = minNum x y := by
  constructor
  · intro hall
    have := hall one .nan
    rw [(h one).2] at this
    exact absurd this (by decide)
  · intro hall
    have := hall .nan one
    rw [(h one).2] at this
    exact absurd this (by decide)

/-- No `if` on one such comparison computes `minimum`, in either orientation. -/
theorem no_single_test_minimum (cmp : Num → Num → Bool) (h : NaNFalse cmp) :
    (¬ ∀ x y, (if cmp x y then x else y) = minimum x y) ∧
      ¬ ∀ x y, (if cmp y x then y else x) = minimum x y := by
  constructor
  · intro hall
    have := hall .nan one
    rw [(h one).1] at this
    exact absurd this (by decide)
  · intro hall
    have := hall one .nan
    rw [(h one).1] at this
    exact absurd this (by decide)

theorem le_nanFalse : NaNFalse le := fun x => by cases x <;> exact ⟨rfl, rfl⟩

theorem lt_nanFalse : NaNFalse lt := fun x => by cases x <;> exact ⟨rfl, rfl⟩

/-! ## Operands that are not numbers -/

/-- Values: a number or a symbol. -/
inductive V
  | num (x : Num)
  | sym (s : ℕ)
  deriving DecidableEq

/-- A number, or the error naming a symbol. -/
def num? : V → Except ℕ Num
  | .num x => .ok x
  | .sym s => .error s

/-- An arithmetic operation evaluates its operands left to right and raises on the first
that is not a number. -/
def binop {α : Type} (f : Num → Num → α) (a b : V) : Except ℕ α := do
  let x ← num? a
  let y ← num? b
  pure (f x y)

/-- `min` on values. -/
def minOp (a b : V) : Except ℕ V := binop (fun x y => V.num (minLe x y)) a b

/-- The protocol spelling with `(<= $x $y)`. -/
def viaLe (a b : V) : Except ℕ V := do
  let c ← binop le a b
  pure (if c then a else b)

/-- The spelling with `(< $y $x)`. -/
def viaLt (a b : V) : Except ℕ V := do
  let c ← binop lt b a
  pure (if c then b else a)

/-- **The `<=` spelling is `min` on every pair of values**, errors included. -/
theorem viaLe_eq_minOp (a b : V) : viaLe a b = minOp a b := by
  cases a with
  | sym s => rfl
  | num x =>
    cases b with
    | sym t => rfl
    | num y =>
      simp only [viaLe, minOp, binop, num?, minLe, bind, Except.bind, pure, Except.pure]
      cases le x y <;> rfl

/-- The `<` spelling raises on the second operand when neither is a number, where `min`
raises on the first. -/
theorem error_order :
    minOp (.sym 1) (.sym 2) = .error 1 ∧ viaLe (.sym 1) (.sym 2) = .error 1 ∧
      viaLt (.sym 1) (.sym 2) = .error 2 := by
  refine ⟨rfl, rfl, rfl⟩

end Mettapedia.Machines.AdmissionRewriting.MinPolicies
