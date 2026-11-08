import Mathlib.Tactic

/-!
# SWI-Prolog's `min` and `max`, and where CeTTa's PeTTa lane departs from them

SWI-PeTTa evaluates `(min x y)` and `(max x y)` by SWI-Prolog's arithmetic functions
(`ar_min`, `ar_max`). CeTTa's PeTTa lane computed them so, in one C function
(`petta_numeric_min_max`) that its prepared machine's intrinsic, its search machine's
goal and its open-equation machine's ready step all call on numbers, until a ruling that
PeTTa's semantics follow mathematical coherence: `min` and `max` now select one of their
operands by the exact order (`MinMaxSelection`), a ruled difference from SWI-PeTTa
(DIFF-17 of CeTTa's PeTTa conformance list, entry 17 of its `swi_differences` test).
This file records SWI's rule, the C that computed it (`cMinMax`), and where the two
rules part.

**The numbers** PeTTa reaches are integers (small or big: PeTTa has no rational
literal or operation) and doubles: NaN, `-0.0`, or another point of the extended
line (`Dbl`). An integer beside a double is read as a double by one rounding
`rnd` (to nearest, ties to even, `±inf` past the largest double): SWI's
`(double)i` and `mpz_to_double` and CeTTa's `(double)ival` and `strtod` all round
so.

**SWI's functions** (`swiMin`, `swiMax`, after `cmpNumbers`): integers compare
exactly, an integer and a double as doubles, doubles by IEEE; a NaN gives NaN; on
a tie `min` answers an operand that is `-0.0`, `max` the other operand, and
otherwise the first operand, as a double when the other is one.

**Theorem** (`c_min_eq`, `c_max_eq`): CeTTa's case analysis before DIFF-17 (`cMinMax`:
NaN first; integers exactly, otherwise as doubles; on a tie the `-0.0` rule, then the
double, then the first) is SWI's on every pair of numbers, and so were its integer paths:
the prepared intrinsic's `a <= b` select (`int_select`), and the open-equation machine's
primitive and the native fold's `a < b ? a : b` (`int_prim`).

**Where the rules part.** SWI answers a value, the selection an operand: SWI's `(min pi
4)` is the double `3.141592653589793`, so `(== pi (min pi 4))` fails, where the selection
answers `pi`. At a mixed tie SWI answers the double for both `(min 2 2.0)` and `(max 2
2.0)`, which is no stable sort (`MinMaxSelection.Controls.swi_breaks_sort`). SWI compares
an integer beside a double as doubles (`Controls.big_tie`), the selection exactly. On the
signed zeros and NaN of `Controls.swi_cases` the two agree
(`MinMaxSelection.Controls.swi_agrees`).

**Controls**, with IEEE's rounding of integers (`nearest`): `(max
9007199254740993 9007199254740992.0)` is the double, a tie as doubles
(`Controls.big_tie`); `(min 2 2.0)` is `2.0`, `(min -0.0 0)` is `-0.0`, `(max -0.0
0)` is `0`, `(max nan 1)` is NaN (`Controls.swi_cases`). The comparison select
`(if (<= x y) x y)` CeTTa computed before differs at each of a mixed tie, signed
zeros and NaN (`Controls.le_select_differs`), so the admission rule spelling `min`
as that test holds for SWI's `min` on integers only.

**Constants.** CeTTa's PeTTa lane reads `inf`, `nan`, `pi`, `e` and `epsilon` as
SWI does, and `-inf` as the constant −∞, the dual of `inf` (the identity of
`max`, as `inf` is of `min`). This is a ruled difference from SWI-PeTTa, whose
reader leaves `-inf` an atom its evaluator rejects (DIFF-16 of CeTTa's PeTTa
conformance list, entry 16 of its `swi_differences` test):
`Controls.numeric_atoms_differ` records it as the one constant the two read
differently.

**Not modelled.** Rationals: SWI reads one beside a double by its nearest double
(`mpq_to_double`), the C by `mpq_get_d`, which truncates (`(min 1r10 0.1)` is `0.1`
in SWI); no PeTTa program reaches a rational.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.MinMaxSWI

/-- The extended line: `⊥` is `-inf`, `⊤` is `inf`. -/
abbrev XR := WithBot (WithTop ℚ)

/-- A rational on the extended line. -/
def ofQ (q : ℚ) : XR := ((q : WithTop ℚ) : WithBot (WithTop ℚ))

/-- An IEEE double as `min` and `max` read it: NaN, `-0.0`, or another point of the
extended line (`pt 0` is `0.0`). -/
inductive Dbl where
  | nan
  | negZero
  | pt (x : XR)
  deriving DecidableEq

/-- A double's point; NaN has none, and `-0.0` is `0`. -/
def Dbl.val : Dbl → Option XR
  | .nan => none
  | .negZero => some 0
  | .pt x => some x

/-- A number PeTTa reaches: an integer or a double. -/
inductive Num where
  | int (n : ℤ)
  | flt (d : Dbl)
  deriving DecidableEq

/-- A comparison's outcome; `unord` when a NaN takes part. -/
inductive Cmp where
  | lt
  | eq
  | gt
  | unord
  deriving DecidableEq

/-- Three-way comparison in a linear order. -/
def cmpOf {α : Type} [LinearOrder α] (a b : α) : Cmp :=
  if a < b then .lt else if b < a then .gt else .eq

theorem cmpOf_eq {α : Type} [LinearOrder α] {a b : α} (h : cmpOf a b = .eq) : a = b := by
  unfold cmpOf at h
  split_ifs at h with h1 h2
  exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)

theorem cmpOf_ne_unord {α : Type} [LinearOrder α] (a b : α) : cmpOf a b ≠ .unord := by
  unfold cmpOf
  split_ifs <;> simp

theorem cmpOf_lt {α : Type} [LinearOrder α] {a b : α} (h : a < b) : cmpOf a b = .lt := by
  simp [cmpOf, h]

theorem cmpOf_gt {α : Type} [LinearOrder α] {a b : α} (h : b < a) : cmpOf a b = .gt := by
  simp [cmpOf, h, not_lt.mpr h.le]

theorem cmpOf_self {α : Type} [LinearOrder α] (a : α) : cmpOf a a = .eq := by
  simp [cmpOf]

/-- A comparison read the other way round. -/
def Cmp.swap : Cmp → Cmp
  | .lt => .gt
  | .gt => .lt
  | c => c

theorem cmpOf_swap {α : Type} [LinearOrder α] (a b : α) : cmpOf b a = (cmpOf a b).swap := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [cmpOf_gt h, cmpOf_lt h]
    rfl
  · rw [cmpOf_self]
    rfl
  · rw [cmpOf_lt h, cmpOf_gt h]
    rfl

/-- IEEE's comparison of doubles: NaN is unordered, `-0.0` equals `0.0`. -/
def dcmp (d e : Dbl) : Cmp :=
  match d.val, e.val with
  | some a, some b => cmpOf a b
  | _, _ => .unord

section Spec

variable (rnd : ℤ → XR)

/-- **SWI's `cmpNumbers`**: integers exactly; an integer beside a double as a
double (`cmpFloatNumbers`); doubles by IEEE. -/
def swiCmp : Num → Num → Cmp
  | .int m, .int n => cmpOf m n
  | .int m, .flt e => dcmp (.pt (rnd m)) e
  | .flt d, .int n => dcmp d (.pt (rnd n))
  | .flt d, .flt e => dcmp d e

/-- Whether a number is `-0.0`. -/
def negZ : Num → Bool
  | .flt .negZero => true
  | _ => false

/-- `make_same_type_numbers`, then the first operand: an integer beside a double
becomes a double. -/
def sameTypeFirst : Num → Num → Num
  | .int m, .flt _ => .flt (.pt (rnd m))
  | x, _ => x

/-- **SWI's `min`** (`ar_min`). -/
def swiMin (x y : Num) : Num :=
  match swiCmp rnd x y with
  | .unord => .flt .nan
  | .eq => if negZ x then x else if negZ y then y else sameTypeFirst rnd x y
  | .lt => x
  | .gt => y

/-- **SWI's `max`** (`ar_max`). -/
def swiMax (x y : Num) : Num :=
  match swiCmp rnd x y with
  | .unord => .flt .nan
  | .eq => if negZ x then y else if negZ y then x else sameTypeFirst rnd x y
  | .lt => y
  | .gt => x

/-- Whether a number is NaN. -/
def isNaN : Num → Bool
  | .flt .nan => true
  | _ => false

/-- Whether a number is a double. -/
def isFlt : Num → Bool
  | .flt _ => true
  | .int _ => false

/-- The double the C reads of a number (`NumArg.val`). -/
def asDbl : Num → Dbl
  | .int n => .pt (rnd n)
  | .flt d => d

/-- The C's comparison, NaN set aside before it: integers exactly, otherwise the
two doubles. -/
def cCmp : Num → Num → Cmp
  | .int m, .int n => cmpOf m n
  | x, y =>
      match (asDbl rnd x).val, (asDbl rnd y).val with
      | some a, some b => cmpOf a b
      | _, _ => .eq

/-- **CeTTa's `petta_numeric_min_max` before DIFF-17**: a NaN operand is the answer; otherwise
the comparison decides; on a tie, `min` takes an operand that is `-0.0` and `max`
the other, then a double over an integer, then the first. -/
def cMinMax (minimum : Bool) (x y : Num) : Num :=
  if isNaN x then x
  else if isNaN y then y
  else
    match cCmp rnd x y with
    | .lt => if minimum then x else y
    | .gt => if minimum then y else x
    | _ =>
        if negZ x ≠ negZ y then (if (if minimum then negZ x else negZ y) then x else y)
        else if isFlt x ≠ isFlt y then (if isFlt x then x else y)
        else x

/-! ## The C before DIFF-17 is SWI -/

/-- **The C's `min` before DIFF-17 is SWI's** on every pair of numbers. -/
theorem c_min_eq (x y : Num) : cMinMax rnd true x y = swiMin rnd x y := by
  cases x with
  | int m =>
      cases y with
      | int n =>
          simp only [cMinMax, isNaN, cCmp, swiMin, swiCmp, negZ, isFlt, sameTypeFirst]
          generalize hc : cmpOf m n = c
          cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
      | flt e =>
          cases e with
          | nan => simp [cMinMax, isNaN, swiMin, swiCmp, dcmp, Dbl.val]
          | negZero =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (rnd m) 0 = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | pt b =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (rnd m) b = c
              cases c
              · simp
              · simp [cmpOf_eq hc]
              · simp
              · exact absurd hc (cmpOf_ne_unord _ _)
  | flt d =>
      cases d with
      | nan =>
          cases y with
          | int n => simp [cMinMax, isNaN, swiMin, swiCmp, dcmp, Dbl.val]
          | flt e => simp [cMinMax, isNaN, swiMin, swiCmp, dcmp, Dbl.val]
      | negZero =>
          cases y with
          | int n =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (0 : XR) (rnd n) = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | flt e =>
              cases e with
              | nan => simp [cMinMax, isNaN, swiMin, swiCmp, dcmp, Dbl.val]
              | negZero =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf (0 : XR) 0 = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
              | pt b =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf (0 : XR) b = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
      | pt a =>
          cases y with
          | int n =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf a (rnd n) = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | flt e =>
              cases e with
              | nan => simp [cMinMax, isNaN, swiMin, swiCmp, dcmp, Dbl.val]
              | negZero =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf a 0 = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
              | pt b =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMin, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf a b = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp

/-- **The C's `max` before DIFF-17 is SWI's** on every pair of numbers. -/
theorem c_max_eq (x y : Num) : cMinMax rnd false x y = swiMax rnd x y := by
  cases x with
  | int m =>
      cases y with
      | int n =>
          simp only [cMinMax, isNaN, cCmp, swiMax, swiCmp, negZ, isFlt, sameTypeFirst]
          generalize hc : cmpOf m n = c
          cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
      | flt e =>
          cases e with
          | nan => simp [cMinMax, isNaN, swiMax, swiCmp, dcmp, Dbl.val]
          | negZero =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (rnd m) 0 = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | pt b =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (rnd m) b = c
              cases c
              · simp
              · simp [cmpOf_eq hc]
              · simp
              · exact absurd hc (cmpOf_ne_unord _ _)
  | flt d =>
      cases d with
      | nan =>
          cases y with
          | int n => simp [cMinMax, isNaN, swiMax, swiCmp, dcmp, Dbl.val]
          | flt e => simp [cMinMax, isNaN, swiMax, swiCmp, dcmp, Dbl.val]
      | negZero =>
          cases y with
          | int n =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf (0 : XR) (rnd n) = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | flt e =>
              cases e with
              | nan => simp [cMinMax, isNaN, swiMax, swiCmp, dcmp, Dbl.val]
              | negZero =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf (0 : XR) 0 = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
              | pt b =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf (0 : XR) b = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
      | pt a =>
          cases y with
          | int n =>
              simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                sameTypeFirst]
              generalize hc : cmpOf a (rnd n) = c
              cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
          | flt e =>
              cases e with
              | nan => simp [cMinMax, isNaN, swiMax, swiCmp, dcmp, Dbl.val]
              | negZero =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf a 0 = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp
              | pt b =>
                  simp only [cMinMax, isNaN, cCmp, asDbl, Dbl.val, swiMax, swiCmp, dcmp, negZ, isFlt,
                    sameTypeFirst]
                  generalize hc : cmpOf a b = c
                  cases c <;> first | exact absurd hc (cmpOf_ne_unord _ _) | simp

/-- **The prepared intrinsic's integer path before DIFF-17 is SWI's**: two machine integers, the
first where `a <= b` for `min` (`a >= b` for `max`). -/
theorem int_select (m n : ℤ) :
    (if m ≤ n then Num.int m else Num.int n) = swiMin rnd (.int m) (.int n) ∧
      (if n ≤ m then Num.int m else Num.int n) = swiMax rnd (.int m) (.int n) := by
  simp only [swiMin, swiMax, swiCmp, negZ, sameTypeFirst, cmpOf]
  constructor
  · by_cases h1 : m < n
    · simp [h1, h1.le]
    · by_cases h2 : n < m
      · simp [h1, h2, not_le.mpr h2]
      · have : m = n := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst this
        simp
  · by_cases h1 : m < n
    · simp [h1, not_le.mpr h1]
    · by_cases h2 : n < m
      · simp [h1, h2, h2.le]
      · have : m = n := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst this
        simp

/-- **The open-equation machine's primitive and the native fold are SWI's** on
integers: `a < b ? a : b` for `min`, `a > b ? a : b` for `max`. -/
theorem int_prim (m n : ℤ) :
    Num.int (if m < n then m else n) = swiMin rnd (.int m) (.int n) ∧
      Num.int (if n < m then m else n) = swiMax rnd (.int m) (.int n) := by
  simp only [swiMin, swiMax, swiCmp, negZ, sameTypeFirst, cmpOf]
  constructor
  · by_cases h1 : m < n
    · simp [h1]
    · by_cases h2 : n < m
      · simp [h1, h2]
      · have : m = n := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst this
        simp
  · by_cases h1 : m < n
    · simp [h1, not_lt.mpr h1.le]
    · by_cases h2 : n < m
      · simp [h1, h2]
      · have : m = n := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst this
        simp

end Spec

/-! ## Controls -/

namespace Controls

/-- The number of bits of a natural number below `2 ^ fuel`. -/
def bitLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLen fuel (n / 2) + 1

/-- **IEEE's rounding of an integer to a double**: to 53 significant bits, ties to
even, `±inf` from `2 ^ 1024` on. -/
def nearest (n : ℤ) : XR :=
  let a := n.natAbs
  let s := bitLen 1100 a
  if s ≤ 53 then ofQ n
  else
    let e := s - 53
    let q := a / 2 ^ e
    let r := a % 2 ^ e
    let half := 2 ^ (e - 1)
    let q' := if half < r ∨ (r = half ∧ q % 2 = 1) then q + 1 else q
    let m := q' * 2 ^ e
    if 2 ^ 1024 ≤ m then (if n < 0 then ⊥ else ⊤)
    else ofQ (if n < 0 then -(m : ℤ) else (m : ℤ))

/-- A double by its rational value. -/
def dq (q : ℚ) : Num := .flt (.pt (ofQ q))

/-- **Integers and doubles compare as doubles**: `9007199254740993` rounds to
`9007199254740992.0`, so `max` ties and answers the double, and `min` the double
too. -/
theorem big_tie :
    nearest 9007199254740993 = ofQ 9007199254740992 ∧
      swiMax nearest (.int 9007199254740993) (dq 9007199254740992) = dq 9007199254740992 ∧
      swiMin nearest (.int 9007199254740993) (dq 9007199254740992) = dq 9007199254740992 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **SWI's cases** (stable-fixed PeTTa's answers): `(min 2 2.0)` is `2.0`, `(min
-0.0 0)` is `-0.0`, `(max -0.0 0)` is `0`, `(min 0.0 -0.0)` is `-0.0`, `(max 0.0
-0.0)` is `0.0`, `(max nan 1)` is NaN, `(min 1 2.5)` is `1`. -/
theorem swi_cases :
    swiMin nearest (.int 2) (dq 2) = dq 2 ∧
      swiMin nearest (.flt .negZero) (.int 0) = .flt .negZero ∧
      swiMax nearest (.flt .negZero) (.int 0) = .int 0 ∧
      swiMin nearest (dq 0) (.flt .negZero) = .flt .negZero ∧
      swiMax nearest (dq 0) (.flt .negZero) = dq 0 ∧
      swiMax nearest (.flt .nan) (.int 1) = .flt .nan ∧
      swiMin nearest (.int 1) (dq (5 / 2)) = .int 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- IEEE's `<=` of two numbers: false when a NaN takes part. -/
def ieeeLe (rnd : ℤ → XR) (x y : Num) : Bool :=
  match (asDbl rnd x).val, (asDbl rnd y).val with
  | some a, some b => decide (a ≤ b)
  | _, _ => false

/-- The comparison select `(if (<= x y) x y)`. -/
def leSelect (rnd : ℤ → XR) (x y : Num) : Num := if ieeeLe rnd x y then x else y

/-- **The comparison select is not SWI's `min`**: at the mixed tie `(min 1 1.0)`,
the signed zeros `(min 0.0 -0.0)`, and NaN `(min nan 1)`. -/
theorem le_select_differs :
    leSelect nearest (.int 1) (dq 1) = .int 1 ∧ swiMin nearest (.int 1) (dq 1) = dq 1 ∧
      leSelect nearest (dq 0) (.flt .negZero) = dq 0 ∧
      swiMin nearest (dq 0) (.flt .negZero) = .flt .negZero ∧
      leSelect nearest (.flt .nan) (.int 1) = .int 1 ∧
      swiMin nearest (.flt .nan) (.int 1) = .flt .nan := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The symbols CeTTa's `get_numeric_arg` reads as numbers in its PeTTa lane;
`-inf` is the constant −∞ (DIFF-16). -/
def cNumericAtoms : List String := ["inf", "-inf", "nan", "pi", "e", "epsilon"]

/-- The atoms SWI-Prolog 10 evaluates as number constants among them (probes:
`(max inf 1)`, `(max nan nan)`, `(min pi 4)`, `(max e 1)`, `(max epsilon 0)`
evaluate; `(min -inf 1)` raises a type error). -/
def swiNumericAtoms : List String := ["inf", "nan", "pi", "e", "epsilon"]

/-- **The readings differ at `-inf` only**: CeTTa reads it as the constant −∞, by
the ruled difference DIFF-16, where SWI rejects it. -/
theorem numeric_atoms_differ : cNumericAtoms.filter (· ∉ swiNumericAtoms) = ["-inf"] ∧
    swiNumericAtoms.filter (· ∉ cNumericAtoms) = [] := by
  decide

end Controls

end Mettapedia.Machines.AdmissionRewriting.MinMaxSWI
