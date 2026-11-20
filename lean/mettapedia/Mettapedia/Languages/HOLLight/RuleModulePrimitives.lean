/-!
# Native names and numerals for the HOL Light kernel rule module

The HOL Light kernel is stated as a rule module: big-step rewrite rules over constructor data.
Its data layer spells a name (sort `Str`) as a list of bytes, each byte as two hexadecimal digits
(sort `Nib`), and compares names digit by digit and bit by bit.  It spells a numeral (sort `Nat`
of the module, `BNat` here) in binary, least significant digit first: `nz` is zero, `nb0 n` is
`2 n`, `nb1 n` is `2 n + 1`, and `nb0` never wraps `nz`.

A rule compiler replaces these two families of rules by native operations.

* A name becomes a byte string.  Comparison becomes `memcmp` over the common length, and when one
  string is a prefix of the other the shorter comes first.  Equality and priming (appending the
  byte `0x27`, the character `'`) become native too.
* A numeral becomes a native natural number.  Comparison and increment become native, and
  matching `nz`, `nb0 m`, `nb1 m` against a native `n` reads `n` as: `0` is `nz`; a positive
  even `n` is `nb0 (n / 2)`; an odd `n` is `nb1 (n / 2)`.

This file transcribes the replaced rules, one Lean equation per rule (each equation is labelled
with the name of its rule), and proves that every native operation computes what the rules
compute.

* Names.  `decodeStr` is a bijection between the module's names and byte strings
  (`decodeStr_injective`, `decodeStr_surjective`).  `cmpStr`, `strEq` and `strPrime` commute with
  it (`cmpStr_refines`, `strEq_refines`, `strPrime_refines`), where the native comparison
  `nativeCmp` is the unsigned lexicographic order on bytes, and `nativeCmp_eq_memcmp` shows it is
  the formula `c = memcmp (a, b, min la lb); if c ≠ 0 then c else compare la lb`.
* Numerals.  A numeral `a` stands for the number `n` when `a` is canonical (`Canon a`) and
  `val a = n`; equivalently `a = enc n` (`enc_val`, `canon_enc`, `val_enc`).  `natInc` and
  `cmpNat` commute with this relation (`natInc_refines`, `cmpNat_refines`), and the native reading
  of a number as `nz`, `nb0 m` or `nb1 m` is the canonical one (`enc_eq_nz_iff`, `enc_eq_nb0_iff`,
  `enc_eq_nb1_iff`).  Canonicity is needed: `nb0 nz` has value `0` yet compares above `nz`
  (`cmpNat_refines_needs_canon`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModulePrimitives

/-! ## The module's data -/

/-- Sort `Flag`. -/
inductive Flag
  | yes
  | no
  deriving DecidableEq, Repr

/-- Sort `Ord`: the result of a comparison (the module's sort, not Lean's `Ord` class). -/
inductive Ord
  | lt
  | eq
  | gt
  deriving DecidableEq, Repr

/-- Sort `Nib`: a hexadecimal digit. -/
inductive Nib
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | xa | xb | xc | xd | xe | xf
  deriving DecidableEq, Repr

/-- Sort `Bits4`: four bits, most significant first. -/
inductive Bits4
  | bits4 (b3 b2 b1 b0 : Flag)
  deriving DecidableEq, Repr

/-- Sort `Byte`: the high digit, then the low digit. -/
inductive Byte
  | byte (hi lo : Nib)
  deriving DecidableEq, Repr

/-- Sort `Str`: a name, as a list of bytes. -/
inductive Str
  | nnil
  | ncons (x : Byte) (xs : Str)
  deriving DecidableEq, Repr

/-- Sort `Nat` of the module: a binary numeral, least significant digit first. -/
inductive BNat
  | nz
  | nb0 (n : BNat)
  | nb1 (n : BNat)
  deriving DecidableEq, Repr

/-! ## The rules

Premises of a rule are calls evaluated left to right; they appear below as `let`s in the same
order. -/

/-- `"then-lt"`, `"then-eq"`, `"then-gt"`: the first comparison decides unless it is `eq`. -/
def Ord.then : Ord → Ord → Ord
  | .lt, _ => .lt  -- "then-lt"
  | .eq, o => o    -- "then-eq"
  | .gt, _ => .gt  -- "then-gt"

/-- `"ord-is-eq-*"`. -/
def ordIsEq : Ord → Flag
  | .lt => .no   -- "ord-is-eq-lt"
  | .eq => .yes  -- "ord-is-eq-eq"
  | .gt => .no   -- "ord-is-eq-gt"

/-- `"cmp-flag-*"`: `no` before `yes`. -/
def cmpFlag : Flag → Flag → Ord
  | .no, .no => .eq    -- "cmp-flag-nn"
  | .no, .yes => .lt   -- "cmp-flag-ny"
  | .yes, .no => .gt   -- "cmp-flag-yn"
  | .yes, .yes => .eq  -- "cmp-flag-yy"

/-- `"nib-0"` … `"nib-f"`: a hexadecimal digit as four bits, most significant first. -/
def nibBits : Nib → Bits4
  | .x0 => .bits4 .no .no .no .no      -- "nib-0"
  | .x1 => .bits4 .no .no .no .yes     -- "nib-1"
  | .x2 => .bits4 .no .no .yes .no     -- "nib-2"
  | .x3 => .bits4 .no .no .yes .yes    -- "nib-3"
  | .x4 => .bits4 .no .yes .no .no     -- "nib-4"
  | .x5 => .bits4 .no .yes .no .yes    -- "nib-5"
  | .x6 => .bits4 .no .yes .yes .no    -- "nib-6"
  | .x7 => .bits4 .no .yes .yes .yes   -- "nib-7"
  | .x8 => .bits4 .yes .no .no .no     -- "nib-8"
  | .x9 => .bits4 .yes .no .no .yes    -- "nib-9"
  | .xa => .bits4 .yes .no .yes .no    -- "nib-a"
  | .xb => .bits4 .yes .no .yes .yes   -- "nib-b"
  | .xc => .bits4 .yes .yes .no .no    -- "nib-c"
  | .xd => .bits4 .yes .yes .no .yes   -- "nib-d"
  | .xe => .bits4 .yes .yes .yes .no   -- "nib-e"
  | .xf => .bits4 .yes .yes .yes .yes  -- "nib-f"

/-- `"cmp-nib"`. -/
def cmpNib (a b : Nib) : Ord :=
  match nibBits a, nibBits b with
  | .bits4 a3 a2 a1 a0, .bits4 b3 b2 b1 b0 =>
    let o3 := cmpFlag a3 b3
    let o2 := cmpFlag a2 b2
    let o1 := cmpFlag a1 b1
    let o0 := cmpFlag a0 b0
    let r1 := o1.then o0
    let r2 := o2.then r1
    let r3 := o3.then r2
    r3

/-- `"cmp-byte"`. -/
def cmpByte : Byte → Byte → Ord
  | .byte h1 l1, .byte h2 l2 =>
    let oh := cmpNib h1 h2
    let ol := cmpNib l1 l2
    oh.then ol

/-- `"cmp-str-nn"`, `"cmp-str-nc"`, `"cmp-str-cn"`, and `"cmp-str-cc"` with its continuation
`"cmp-str-k-*"` unfolded in place; `cmpStr_ncons_ncons` restates `"cmp-str-cc"` as the module
writes it, through `cmpStrK`. -/
def cmpStr : Str → Str → Ord
  | .nnil, .nnil => .eq                -- "cmp-str-nn"
  | .nnil, .ncons _ _ => .lt           -- "cmp-str-nc"
  | .ncons _ _, .nnil => .gt           -- "cmp-str-cn"
  | .ncons x xs, .ncons y ys =>        -- "cmp-str-cc"
    match cmpByte x y with
    | .lt => .lt                       -- "cmp-str-k-lt"
    | .gt => .gt                       -- "cmp-str-k-gt"
    | .eq => cmpStr xs ys              -- "cmp-str-k-eq"

/-- `"cmp-str-k-*"`. -/
def cmpStrK : Ord → Str → Str → Ord
  | .lt, _, _ => .lt              -- "cmp-str-k-lt"
  | .gt, _, _ => .gt              -- "cmp-str-k-gt"
  | .eq, xs, ys => cmpStr xs ys   -- "cmp-str-k-eq"

/-- `"cmp-str-cc"` as the module states it. -/
theorem cmpStr_ncons_ncons (x y : Byte) (xs ys : Str) :
    cmpStr (.ncons x xs) (.ncons y ys) = cmpStrK (cmpByte x y) xs ys := by
  simp only [cmpStr]
  cases cmpByte x y <;> rfl

/-- `"str-eq"`. -/
def strEq (a b : Str) : Flag :=
  let o := cmpStr a b
  ordIsEq o

/-- `"str-prime-*"`: append the byte `27`, the character `'`. -/
def strPrime : Str → Str
  | .nnil => .ncons (.byte .x2 .x7) .nnil  -- "str-prime-nil"
  | .ncons x xs =>                         -- "str-prime-cons"
    let ys := strPrime xs
    .ncons x ys

/-- `"inc-*"`. -/
def natInc : BNat → BNat
  | .nz => .nb1 .nz     -- "inc-z"
  | .nb0 n => .nb1 n    -- "inc-0"
  | .nb1 n =>           -- "inc-1"
    let m := natInc n
    .nb0 m

/-- `"cmp-nat-*"`. -/
def cmpNat : BNat → BNat → Ord
  | .nz, .nz => .eq          -- "cmp-nat-zz"
  | .nz, .nb0 _ => .lt       -- "cmp-nat-z0"
  | .nz, .nb1 _ => .lt       -- "cmp-nat-z1"
  | .nb0 _, .nz => .gt       -- "cmp-nat-0z"
  | .nb1 _, .nz => .gt       -- "cmp-nat-1z"
  | .nb0 n, .nb0 m =>        -- "cmp-nat-00"
    let o := cmpNat n m
    o
  | .nb1 n, .nb1 m =>        -- "cmp-nat-11"
    let o := cmpNat n m
    o
  | .nb0 n, .nb1 m =>        -- "cmp-nat-01"
    let o := cmpNat n m
    let r := o.then .lt
    r
  | .nb1 n, .nb0 m =>        -- "cmp-nat-10"
    let o := cmpNat n m
    let r := o.then .gt
    r

/-! ## Comparing natural numbers -/

/-- The module's `Ord` for a Lean `Ordering`. -/
def ordOfCompare : Ordering → Ord
  | .lt => .lt
  | .eq => .eq
  | .gt => .gt

theorem ordOfCompare_of_lt {a b : Nat} (h : a < b) : ordOfCompare (compare a b) = .lt := by
  rw [Nat.compare_eq_lt.mpr h]; rfl

theorem ordOfCompare_of_eq {a b : Nat} (h : a = b) : ordOfCompare (compare a b) = .eq := by
  rw [Nat.compare_eq_eq.mpr h]; rfl

theorem ordOfCompare_of_gt {a b : Nat} (h : b < a) : ordOfCompare (compare a b) = .gt := by
  rw [Nat.compare_eq_gt.mpr h]; rfl

theorem ordOfCompare_eq_eq_iff {a b : Nat} : ordOfCompare (compare a b) = .eq ↔ a = b := by
  rw [← Nat.compare_eq_eq]
  cases compare a b <;> decide

/-- A comparison of natural numbers depends only on which of `<`, `=`, `>` holds. -/
theorem ordOfCompare_congr {a b c d : Nat} (hlt : a < b → c < d) (heq : a = b → c = d)
    (hgt : b < a → d < c) : ordOfCompare (compare a b) = ordOfCompare (compare c d) := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [ordOfCompare_of_lt h, ordOfCompare_of_lt (hlt h)]
  · rw [ordOfCompare_of_eq h, ordOfCompare_of_eq (heq h)]
  · rw [ordOfCompare_of_gt h, ordOfCompare_of_gt (hgt h)]

theorem ordOfCompare_succ (x y : Nat) :
    ordOfCompare (compare (x + 1) (y + 1)) = ordOfCompare (compare x y) :=
  ordOfCompare_congr (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)

theorem ordOfCompare_double (x y : Nat) :
    ordOfCompare (compare (2 * x) (2 * y)) = ordOfCompare (compare x y) :=
  ordOfCompare_congr (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)

theorem ordOfCompare_double_add_one (x y : Nat) :
    ordOfCompare (compare (2 * x + 1) (2 * y + 1)) = ordOfCompare (compare x y) :=
  ordOfCompare_congr (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)

theorem then_lt_double (x y : Nat) :
    (ordOfCompare (compare x y)).then .lt = ordOfCompare (compare (2 * x) (2 * y + 1)) := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · rw [ordOfCompare_of_lt h, ordOfCompare_of_lt (show 2 * x < 2 * y + 1 by omega)]; rfl
  · rw [ordOfCompare_of_eq h, ordOfCompare_of_lt (show 2 * x < 2 * y + 1 by omega)]; rfl
  · rw [ordOfCompare_of_gt h, ordOfCompare_of_gt (show 2 * y + 1 < 2 * x by omega)]; rfl

theorem then_gt_double (x y : Nat) :
    (ordOfCompare (compare x y)).then .gt = ordOfCompare (compare (2 * x + 1) (2 * y)) := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · rw [ordOfCompare_of_lt h, ordOfCompare_of_lt (show 2 * x + 1 < 2 * y by omega)]; rfl
  · rw [ordOfCompare_of_eq h, ordOfCompare_of_gt (show 2 * y < 2 * x + 1 by omega)]; rfl
  · rw [ordOfCompare_of_gt h, ordOfCompare_of_gt (show 2 * y < 2 * x + 1 by omega)]; rfl

/-! ## Names -/

/-- The value `0 … 15` of a hexadecimal digit. -/
def Nib.val : Nib → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .xa => 10 | .xb => 11 | .xc => 12 | .xd => 13 | .xe => 14 | .xf => 15

/-- The digit of value `n`, for `n < 16`. -/
def Nib.ofVal : Nat → Nib
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | 8 => .x8 | 9 => .x9 | 10 => .xa | 11 => .xb | 12 => .xc | 13 => .xd | 14 => .xe | _ => .xf

theorem Nib.val_lt (a : Nib) : a.val < 16 := by
  cases a <;> decide

theorem Nib.ofVal_val (a : Nib) : Nib.ofVal a.val = a := by
  cases a <;> rfl

theorem Nib.val_ofVal : ∀ n, n < 16 → (Nib.ofVal n).val = n := by
  decide

/-- `"cmp-nib"` compares the values of the digits. -/
theorem cmpNib_spec (a b : Nib) : cmpNib a b = ordOfCompare (compare a.val b.val) := by
  cases a <;> cases b <;> rfl

/-- The value of a byte: sixteen times the high digit plus the low digit. -/
def decodeByte : Byte → UInt8
  | .byte hi lo => UInt8.ofNat (16 * hi.val + lo.val)

/-- The bytes of a name. -/
def decodeStr : Str → List UInt8
  | .nnil => []
  | .ncons x xs => decodeByte x :: decodeStr xs

theorem decodeByte_toNat (hi lo : Nib) :
    (decodeByte (.byte hi lo)).toNat = 16 * hi.val + lo.val := by
  have := hi.val_lt
  have := lo.val_lt
  simp only [decodeByte, UInt8.toNat_ofNat']
  omega

/-- `"cmp-byte"` compares the values of the bytes, unsigned. -/
theorem cmpByte_spec (x y : Byte) :
    cmpByte x y = ordOfCompare (compare (decodeByte x).toNat (decodeByte y).toNat) := by
  cases x with
  | byte h1 l1 =>
  cases y with
  | byte h2 l2 =>
  rw [decodeByte_toNat, decodeByte_toNat]
  show (cmpNib h1 h2).then (cmpNib l1 l2) = _
  rw [cmpNib_spec, cmpNib_spec]
  have := l1.val_lt
  have := l2.val_lt
  rcases Nat.lt_trichotomy h1.val h2.val with h | h | h
  · rw [ordOfCompare_of_lt h,
      ordOfCompare_of_lt (show 16 * h1.val + l1.val < 16 * h2.val + l2.val by omega)]
    rfl
  · rw [ordOfCompare_of_eq h]
    exact ordOfCompare_congr (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
  · rw [ordOfCompare_of_gt h,
      ordOfCompare_of_gt (show 16 * h2.val + l2.val < 16 * h1.val + l1.val by omega)]
    rfl

/-! ### The native comparison -/

/-- Comparison of byte strings as C performs it: bytes from the first, compared as unsigned
numbers; the first difference decides; when one string is a prefix of the other, the shorter
comes first. -/
def nativeCmp : List UInt8 → List UInt8 → Ord
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a.toNat b.toNat with
    | .lt => .lt
    | .gt => .gt
    | .eq => nativeCmp as bs

/-- **Names, comparison.**  `"cmp-str"` is the native comparison of the bytes. -/
theorem cmpStr_refines (xs ys : Str) :
    cmpStr xs ys = nativeCmp (decodeStr xs) (decodeStr ys) := by
  induction xs generalizing ys with
  | nnil => cases ys <;> rfl
  | ncons x xs ih =>
    cases ys with
    | nnil => rfl
    | ncons y ys =>
      simp only [cmpStr, decodeStr, nativeCmp, cmpByte_spec]
      cases compare (decodeByte x).toNat (decodeByte y).toNat <;> simp only [ordOfCompare, ih]

/-- The sign of C's `memcmp (a, b, n)`, as the C standard specifies it: among the first `n`
positions, the first pair of bytes that differ decides, both read as unsigned; `eq` when there is
no such pair. -/
def memcmp (a b : List UInt8) (n : Nat) : Ord :=
  match ((a.take n).zip (b.take n)).find? (fun p => decide (p.1 ≠ p.2)) with
  | none => .eq
  | some (x, y) => ordOfCompare (compare x.toNat y.toNat)

theorem memcmp_zero (a b : List UInt8) : memcmp a b 0 = .eq := by
  simp [memcmp]

theorem memcmp_cons_cons (x y : UInt8) (xs ys : List UInt8) (n : Nat) :
    memcmp (x :: xs) (y :: ys) (n + 1) =
      if x = y then memcmp xs ys n else ordOfCompare (compare x.toNat y.toNat) := by
  by_cases h : x = y
  · subst h
    simp [memcmp, List.take_succ_cons, List.zip_cons_cons]
  · simp [memcmp, List.take_succ_cons, List.zip_cons_cons, h]

/-- The native comparison is the C formula
`c = memcmp (a, b, min la lb); if c ≠ 0 then c else compare la lb`. -/
theorem nativeCmp_eq_memcmp (a b : List UInt8) :
    nativeCmp a b =
      let c := memcmp a b (min a.length b.length)
      if c ≠ .eq then c else ordOfCompare (compare a.length b.length) := by
  dsimp only
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys =>
      have hlt : ordOfCompare (compare ([] : List UInt8).length (y :: ys).length) = .lt :=
        ordOfCompare_of_lt (by simp)
      rw [hlt, List.length_nil, Nat.zero_min, memcmp_zero, if_neg (fun h => h rfl)]
      rfl
  | cons x xs ih =>
    cases b with
    | nil =>
      have hgt : ordOfCompare (compare (x :: xs).length ([] : List UInt8).length) = .gt :=
        ordOfCompare_of_gt (by simp)
      rw [hgt, List.length_nil, Nat.min_zero, memcmp_zero, if_neg (fun h => h rfl)]
      rfl
    | cons y ys =>
      rw [List.length_cons, List.length_cons, Nat.add_min_add_right, memcmp_cons_cons,
        ordOfCompare_succ]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl, ← ih ys]
        simp only [nativeCmp, Nat.compare_eq_eq.mpr (rfl : x.toNat = x.toNat)]
      · rw [if_neg hxy]
        have hne : x.toNat ≠ y.toNat := fun h => hxy (UInt8.toNat_inj.mp h)
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · simp [nativeCmp, Nat.compare_eq_lt.mpr h, ordOfCompare]
        · simp [nativeCmp, Nat.compare_eq_gt.mpr h, ordOfCompare]

/-- **Names, comparison, as the C code computes it.** -/
theorem cmpStr_eq_memcmp (xs ys : Str) :
    cmpStr xs ys =
      let a := decodeStr xs
      let b := decodeStr ys
      let c := memcmp a b (min a.length b.length)
      if c ≠ .eq then c else ordOfCompare (compare a.length b.length) := by
  rw [cmpStr_refines, nativeCmp_eq_memcmp]

theorem nativeCmp_eq_eq_iff (a b : List UInt8) : nativeCmp a b = .eq ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [nativeCmp]
  | cons x xs ih =>
    cases b with
    | nil => simp [nativeCmp]
    | cons y ys =>
      simp only [nativeCmp, List.cons.injEq]
      rcases Nat.lt_trichotomy x.toNat y.toNat with h | h | h
      · rw [Nat.compare_eq_lt.mpr h]
        refine ⟨fun h' => (nomatch h'), fun ⟨hxy, _⟩ => ?_⟩
        subst hxy
        exact absurd h (Nat.lt_irrefl _)
      · rw [Nat.compare_eq_eq.mpr h, ih ys, UInt8.toNat_inj.mp h]
        simp
      · rw [Nat.compare_eq_gt.mpr h]
        refine ⟨fun h' => (nomatch h'), fun ⟨hxy, _⟩ => ?_⟩
        subst hxy
        exact absurd h (Nat.lt_irrefl _)

/-- Equality of byte strings as C tests it: equal lengths, and `memcmp` finds no difference. -/
theorem eq_iff_memcmp (a b : List UInt8) :
    a = b ↔ a.length = b.length ∧ memcmp a b a.length = .eq := by
  rw [← nativeCmp_eq_eq_iff, nativeCmp_eq_memcmp]
  dsimp only
  constructor
  · intro h
    by_cases hc : memcmp a b (min a.length b.length) = .eq
    · rw [if_neg (fun h' => h' hc), ordOfCompare_eq_eq_iff] at h
      refine ⟨h, ?_⟩
      rwa [← h, Nat.min_self] at hc
    · rw [if_pos hc] at h
      exact absurd h hc
  · rintro ⟨hlen, hc⟩
    rw [← hlen, Nat.min_self, hc, if_neg (fun h' => h' rfl)]
    exact ordOfCompare_of_eq rfl

/-! ### The bijection between names and byte strings -/

/-- The byte of a value. -/
def encodeByte (u : UInt8) : Byte :=
  .byte (Nib.ofVal (u.toNat / 16)) (Nib.ofVal (u.toNat % 16))

/-- The name of a byte string. -/
def encodeStr : List UInt8 → Str
  | [] => .nnil
  | u :: us => .ncons (encodeByte u) (encodeStr us)

theorem decodeByte_encodeByte (u : UInt8) : decodeByte (encodeByte u) = u := by
  apply UInt8.toNat_inj.mp
  have hu := u.toNat_lt
  have h1 : u.toNat / 16 < 16 := by omega
  have h2 : u.toNat % 16 < 16 := by omega
  simp only [encodeByte, decodeByte_toNat, Nib.val_ofVal _ h1, Nib.val_ofVal _ h2]
  omega

theorem encodeByte_decodeByte (b : Byte) : encodeByte (decodeByte b) = b := by
  cases b with
  | byte hi lo =>
    have := hi.val_lt
    have := lo.val_lt
    simp only [encodeByte, decodeByte_toNat]
    rw [show (16 * hi.val + lo.val) / 16 = hi.val by omega,
      show (16 * hi.val + lo.val) % 16 = lo.val by omega, Nib.ofVal_val, Nib.ofVal_val]

theorem decodeStr_encodeStr (bs : List UInt8) : decodeStr (encodeStr bs) = bs := by
  induction bs with
  | nil => rfl
  | cons u us ih => simp only [encodeStr, decodeStr, decodeByte_encodeByte, ih]

theorem encodeStr_decodeStr (xs : Str) : encodeStr (decodeStr xs) = xs := by
  induction xs with
  | nnil => rfl
  | ncons x xs ih => simp only [decodeStr, encodeStr, encodeByte_decodeByte, ih]

/-- Distinct names have distinct bytes. -/
theorem decodeStr_injective : Function.Injective decodeStr := fun xs ys h => by
  rw [← encodeStr_decodeStr xs, h, encodeStr_decodeStr]

/-- Every byte string is the bytes of a name. -/
theorem decodeStr_surjective : Function.Surjective decodeStr :=
  fun bs => ⟨encodeStr bs, decodeStr_encodeStr bs⟩

theorem cmpStr_eq_eq_iff (xs ys : Str) : cmpStr xs ys = .eq ↔ xs = ys := by
  rw [cmpStr_refines, nativeCmp_eq_eq_iff]
  exact ⟨fun h => decodeStr_injective h, fun h => h ▸ rfl⟩

/-! ### Equality and priming -/

/-- **Names, equality.**  `"str-eq"` answers `yes` exactly when the bytes are equal. -/
theorem strEq_refines (xs ys : Str) : strEq xs ys = .yes ↔ decodeStr xs = decodeStr ys := by
  rw [← nativeCmp_eq_eq_iff, ← cmpStr_refines]
  show ordIsEq (cmpStr xs ys) = .yes ↔ _
  cases cmpStr xs ys <;> decide

theorem strEq_eq_yes_iff (xs ys : Str) : strEq xs ys = .yes ↔ xs = ys :=
  (strEq_refines xs ys).trans ⟨fun h => decodeStr_injective h, fun h => h ▸ rfl⟩

/-- **Names, priming.**  `"str-prime"` appends the byte `0x27`. -/
theorem strPrime_refines (xs : Str) : decodeStr (strPrime xs) = decodeStr xs ++ [0x27] := by
  induction xs with
  | nnil => decide
  | ncons x xs ih => simp only [strPrime, decodeStr, ih, List.cons_append]

/-! ## Numerals -/

/-- The number a numeral stands for. -/
def val : BNat → Nat
  | .nz => 0
  | .nb0 n => 2 * val n
  | .nb1 n => 2 * val n + 1

/-- Canonical numerals: `nb0` never wraps `nz`. -/
inductive Canon : BNat → Prop
  | nz : Canon .nz
  | nb0 {n : BNat} : Canon n → n ≠ .nz → Canon (.nb0 n)
  | nb1 {n : BNat} : Canon n → Canon (.nb1 n)

instance Canon.decidable : DecidablePred Canon
  | .nz => isTrue .nz
  | .nb0 n =>
    match Canon.decidable n, decEq n .nz with
    | isTrue h, isFalse hz => isTrue (.nb0 h hz)
    | isFalse h, _ => isFalse fun | .nb0 h' _ => h h'
    | _, isTrue hz => isFalse fun | .nb0 _ hz' => hz' hz
  | .nb1 n =>
    match Canon.decidable n with
    | isTrue h => isTrue (.nb1 h)
    | isFalse h => isFalse fun | .nb1 h' => h h'

/-- Building `nb0 m` keeps a numeral canonical only when `m ≠ nz`. -/
theorem canon_nb0_iff {m : BNat} : Canon (.nb0 m) ↔ Canon m ∧ m ≠ .nz :=
  ⟨fun | .nb0 h hne => ⟨h, hne⟩, fun ⟨h, hne⟩ => .nb0 h hne⟩

theorem canon_nb1_iff {m : BNat} : Canon (.nb1 m) ↔ Canon m :=
  ⟨fun | .nb1 h => h, .nb1⟩

theorem val_pos {a : BNat} (h : Canon a) (hne : a ≠ .nz) : 0 < val a := by
  induction h with
  | nz => exact absurd rfl hne
  | nb0 _ hn ih =>
    have := ih hn
    simp only [val]
    omega
  | nb1 _ _ =>
    simp only [val]
    omega

theorem natInc_ne_nz (a : BNat) : natInc a ≠ .nz := by
  cases a <;> simp [natInc]

theorem val_natInc (a : BNat) : val (natInc a) = val a + 1 := by
  induction a with
  | nz => rfl
  | nb0 n _ => rfl
  | nb1 n ih =>
    simp only [natInc, val, ih]
    omega

theorem canon_natInc {a : BNat} (h : Canon a) : Canon (natInc a) := by
  induction h with
  | nz => exact .nb1 .nz
  | nb0 hn _ _ => exact .nb1 hn
  | nb1 _ ih => exact .nb0 ih (natInc_ne_nz _)

/-- **Numerals, increment.**  `"nat-inc"` adds one and keeps a numeral canonical. -/
theorem natInc_refines (a : BNat) : val (natInc a) = val a + 1 ∧ (Canon a → Canon (natInc a)) :=
  ⟨val_natInc a, canon_natInc⟩

/-- The canonical numeral of a number. -/
def enc : Nat → BNat
  | 0 => .nz
  | n + 1 => natInc (enc n)

theorem enc_succ (n : Nat) : enc (n + 1) = natInc (enc n) := rfl

theorem val_enc (n : Nat) : val (enc n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [enc_succ, val_natInc, ih]

theorem canon_enc (n : Nat) : Canon (enc n) := by
  induction n with
  | zero => exact .nz
  | succ n ih => exact canon_natInc ih

theorem enc_double (n : Nat) :
    enc (2 * n + 1) = .nb1 (enc n) ∧ (0 < n → enc (2 * n) = .nb0 (enc n)) := by
  induction n with
  | zero => exact ⟨rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ n ih =>
    have h2 : enc (2 * (n + 1)) = .nb0 (enc (n + 1)) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, enc_succ, ih.1]
      rfl
    refine ⟨?_, fun _ => h2⟩
    rw [enc_succ, h2]
    rfl

/-! ### Reading a native number as a numeral -/

theorem enc_zero : enc 0 = .nz := rfl

theorem enc_of_even {n : Nat} (hpos : 0 < n) (heven : n % 2 = 0) :
    enc n = .nb0 (enc (n / 2)) := by
  have h := (enc_double (n / 2)).2 (by omega)
  rwa [show 2 * (n / 2) = n by omega] at h

theorem enc_of_odd {n : Nat} (hodd : n % 2 = 1) : enc n = .nb1 (enc (n / 2)) := by
  have h := (enc_double (n / 2)).1
  rwa [show 2 * (n / 2) + 1 = n by omega] at h

/-- A canonical numeral is the canonical numeral of its value. -/
theorem enc_val {a : BNat} (h : Canon a) : enc (val a) = a := by
  induction h with
  | nz => rfl
  | nb0 hn hne ih =>
    show enc (2 * val _) = _
    rw [(enc_double _).2 (val_pos hn hne), ih]
  | nb1 _ ih =>
    show enc (2 * val _ + 1) = _
    rw [(enc_double _).1, ih]

theorem canon_iff_enc_val {a : BNat} : Canon a ↔ enc (val a) = a :=
  ⟨enc_val, fun h => h ▸ canon_enc _⟩

theorem canon_eq_of_val_eq {a b : BNat} (ha : Canon a) (hb : Canon b) (h : val a = val b) :
    a = b := by
  rw [← enc_val ha, ← enc_val hb, h]

/-- Matching `nz` against a native number succeeds exactly on `0`. -/
theorem enc_eq_nz_iff {n : Nat} : enc n = .nz ↔ n = 0 := by
  constructor
  · intro h
    have hv := val_enc n
    rw [h] at hv
    exact hv.symm
  · rintro rfl
    rfl

/-- Matching `nb0 m` against a native number succeeds exactly on positive even numbers, and
binds `m` to half of it. -/
theorem enc_eq_nb0_iff {n : Nat} {m : BNat} :
    enc n = .nb0 m ↔ 0 < n ∧ n % 2 = 0 ∧ m = enc (n / 2) := by
  constructor
  · intro h
    have hc := canon_enc n
    rw [h] at hc
    obtain ⟨hm, hne⟩ := canon_nb0_iff.mp hc
    have hv := val_enc n
    rw [h] at hv
    simp only [val] at hv
    have := val_pos hm hne
    refine ⟨by omega, by omega, ?_⟩
    rw [show n / 2 = val m by omega, enc_val hm]
  · rintro ⟨hpos, heven, rfl⟩
    exact enc_of_even hpos heven

/-- Matching `nb1 m` against a native number succeeds exactly on odd numbers, and binds `m` to
half of it. -/
theorem enc_eq_nb1_iff {n : Nat} {m : BNat} :
    enc n = .nb1 m ↔ n % 2 = 1 ∧ m = enc (n / 2) := by
  constructor
  · intro h
    have hc := canon_enc n
    rw [h] at hc
    have hm := canon_nb1_iff.mp hc
    have hv := val_enc n
    rw [h] at hv
    simp only [val] at hv
    refine ⟨by omega, ?_⟩
    rw [show n / 2 = val m by omega, enc_val hm]
  · rintro ⟨hodd, rfl⟩
    exact enc_of_odd hodd

/-! ### Comparison -/

/-- **Numerals, comparison.**  On canonical numerals `"cmp-nat"` compares the values. -/
theorem cmpNat_refines {a b : BNat} (ha : Canon a) (hb : Canon b) :
    cmpNat a b = ordOfCompare (compare (val a) (val b)) := by
  induction ha generalizing b with
  | nz =>
    cases hb with
    | nz => rfl
    | @nb0 m hm hne =>
      have := val_pos hm hne
      exact (ordOfCompare_of_lt (show 0 < 2 * val m by omega)).symm
    | @nb1 m _ =>
      exact (ordOfCompare_of_lt (show 0 < 2 * val m + 1 by omega)).symm
  | @nb0 n hn hne ih =>
    have := val_pos hn hne
    cases hb with
    | nz =>
      exact (ordOfCompare_of_gt (show 0 < 2 * val n by omega)).symm
    | @nb0 m hm _ =>
      show cmpNat n m = ordOfCompare (compare (2 * val n) (2 * val m))
      rw [ih hm, ordOfCompare_double]
    | @nb1 m hm =>
      show (cmpNat n m).then .lt = ordOfCompare (compare (2 * val n) (2 * val m + 1))
      rw [ih hm, then_lt_double]
  | @nb1 n hn ih =>
    cases hb with
    | nz =>
      exact (ordOfCompare_of_gt (show 0 < 2 * val n + 1 by omega)).symm
    | @nb0 m hm _ =>
      show (cmpNat n m).then .gt = ordOfCompare (compare (2 * val n + 1) (2 * val m))
      rw [ih hm, then_gt_double]
    | @nb1 m hm =>
      show cmpNat n m = ordOfCompare (compare (2 * val n + 1) (2 * val m + 1))
      rw [ih hm, ordOfCompare_double_add_one]

/-- `"cmp-nat"` answers `eq` exactly on equal numerals, canonical or not. -/
theorem cmpNat_eq_iff (a b : BNat) : cmpNat a b = .eq ↔ a = b := by
  induction a generalizing b with
  | nz => cases b <;> simp [cmpNat]
  | nb0 n ih =>
    cases b with
    | nz => simp [cmpNat]
    | nb0 m => simp only [cmpNat, BNat.nb0.injEq]; exact ih m
    | nb1 m =>
      simp only [cmpNat, reduceCtorEq, iff_false]
      cases cmpNat n m <;> decide
  | nb1 n ih =>
    cases b with
    | nz => simp [cmpNat]
    | nb0 m =>
      simp only [cmpNat, reduceCtorEq, iff_false]
      cases cmpNat n m <;> decide
    | nb1 m => simp only [cmpNat, BNat.nb1.injEq]; exact ih m

/-- On canonical numerals, `"cmp-nat"` answers `eq` exactly when the values are equal. -/
theorem cmpNat_eq_iff_val {a b : BNat} (ha : Canon a) (hb : Canon b) :
    cmpNat a b = .eq ↔ val a = val b := by
  rw [cmpNat_refines ha hb, ordOfCompare_eq_eq_iff]

/-! ## Examples -/

namespace Examples

/-- The name `bool`: bytes `62 6f 6f 6c`. -/
def nameBool : Str :=
  .ncons (.byte .x6 .x2) (.ncons (.byte .x6 .xf) (.ncons (.byte .x6 .xf) (.ncons (.byte .x6 .xc)
    .nnil)))

/-- The name `fun`: bytes `66 75 6e`. -/
def nameFun : Str :=
  .ncons (.byte .x6 .x6) (.ncons (.byte .x7 .x5) (.ncons (.byte .x6 .xe) .nnil))

/-- The name `x`: byte `78`. -/
def nameX : Str :=
  .ncons (.byte .x7 .x8) .nnil

/-- The one-byte name `80`, a byte at or above `0x80`. -/
def nameHigh : Str :=
  .ncons (.byte .x8 .x0) .nnil

/-- The one-byte name `7f`. -/
def nameLow : Str :=
  .ncons (.byte .x7 .xf) .nnil

example : decodeStr nameBool = [0x62, 0x6f, 0x6f, 0x6c] := by decide
example : decodeStr nameFun = [0x66, 0x75, 0x6e] := by decide

-- `bool` before `fun`: the first byte decides, though `bool` is longer.
example : cmpStr nameBool nameFun = .lt := by decide
example : nativeCmp [0x62, 0x6f, 0x6f, 0x6c] [0x66, 0x75, 0x6e] = .lt := by decide
example : memcmp [0x62, 0x6f, 0x6f, 0x6c] [0x66, 0x75, 0x6e] 3 = .lt := by decide
-- and not the other way round
example : cmpStr nameFun nameBool = .gt := by decide

-- A proper prefix comes first: `x` before `x'`.
example : decodeStr (strPrime nameX) = [0x78, 0x27] := by decide
example : cmpStr nameX (strPrime nameX) = .lt := by decide
example : cmpStr (strPrime nameX) nameX = .gt := by decide
-- `memcmp` over the common length finds no difference, so the lengths decide.
example : memcmp [0x78] [0x78, 0x27] 1 = .eq := by decide

-- Bytes compare unsigned: `0x80` after `0x7f` ...
example : cmpStr nameHigh nameLow = .gt := by decide
-- ... while a signed reading of the same bytes would put `0x80` first.
example : (0x80 : UInt8).toInt8 < (0x7f : UInt8).toInt8 := by decide

-- Equality.
example : strEq nameBool nameBool = .yes := by decide
example : strEq nameX (strPrime nameX) = .no := by decide

-- The high digit comes first in a byte.
example : decodeByte (.byte .x2 .x7) = 0x27 := by decide
example : decodeByte (.byte .x7 .x2) ≠ 0x27 := by decide

-- `7 + 1 = 8`.
example : natInc (.nb1 (.nb1 (.nb1 .nz))) = .nb0 (.nb0 (.nb0 (.nb1 .nz))) := rfl
example : val (.nb1 (.nb1 (.nb1 .nz))) = 7 := rfl
example : val (natInc (.nb1 (.nb1 (.nb1 .nz)))) = 8 := rfl
example : enc 8 = .nb0 (.nb0 (.nb0 (.nb1 .nz))) := by decide
-- A canonical result does not make the argument canonical: `natInc (nb0 nz) = nb1 nz`.
example : Canon (natInc (.nb0 .nz)) ∧ ¬ Canon (.nb0 .nz) := by decide

-- Canonical and not.
example : Canon (.nb0 (.nb0 (.nb0 (.nb1 .nz)))) := by decide
example : ¬ Canon (.nb0 .nz) := by decide
example : ¬ Canon (.nb1 (.nb0 .nz)) := by decide
-- Doubling `0` gives `nz`, not `nb0 nz`.
example : enc (2 * 0) ≠ .nb0 (enc 0) := by decide

-- Comparison of canonical numerals: `2 < 3`, `3 > 2`.
example : cmpNat (.nb0 (.nb1 .nz)) (.nb1 (.nb1 .nz)) = .lt := rfl
example : cmpNat (.nb1 (.nb1 .nz)) (.nb0 (.nb1 .nz)) = .gt := rfl

-- The non-canonical `nb0 nz` has value `0`, the value of `nz`, yet compares above `nz`.
example : val (.nb0 .nz) = val .nz := rfl
example : cmpNat .nz (.nb0 .nz) = .lt := rfl

end Examples

/-- `cmpNat_refines` needs canonicity: without it the conclusion fails at `nz`, `nb0 nz`. -/
theorem cmpNat_refines_needs_canon :
    ¬ ∀ a b : BNat, cmpNat a b = ordOfCompare (compare (val a) (val b)) :=
  fun h => absurd (h .nz (.nb0 .nz)) (by decide)

/-- `canon_eq_of_val_eq` needs canonicity: `nz` and `nb0 nz` have the same value. -/
theorem canon_eq_of_val_eq_needs_canon : ¬ ∀ a b : BNat, val a = val b → a = b :=
  fun h => absurd (h .nz (.nb0 .nz) rfl) (by decide)

end Mettapedia.Languages.HOLLight.RuleModulePrimitives

#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.cmpStr_refines
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.nativeCmp_eq_memcmp
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.cmpStr_eq_memcmp
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.eq_iff_memcmp
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.decodeStr_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.decodeStr_surjective
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.strEq_refines
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.strPrime_refines
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.natInc_refines
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.cmpNat_refines
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.cmpNat_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.enc_val
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.canon_eq_of_val_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.enc_eq_nb0_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModulePrimitives.enc_eq_nb1_iff
