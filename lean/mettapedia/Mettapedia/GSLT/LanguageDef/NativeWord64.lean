import Mathlib.Data.BitVec
import Mathlib.Tactic.SplitIfs

/-!
# Unsigned primitives for the native operational fragment

The source carrier is a bounded natural number.  The target carrier is a
bit-vector, evaluated with its unsigned arithmetic and bit operations.  The
two evaluators are defined independently.  Division by zero and a shift count
of at least 64 are faults, even though the underlying bit-vector operations
are total.

This is a primitive profile for the generated native operational fragment;
it does not assert refinement by an ISO C implementation or by a processor.
Returned placeholder values after a physical context fault are not successful
results in this profile.  Storage and reference identity are separate profiles.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeWord64

abbrev Bounded (width : Nat) := Fin (2 ^ width)
abbrev Word := Bounded 64
abbrev Byte := Bounded 8

def bound : Nat := 2 ^ 64

def bounded (width value : Nat) : Bounded width :=
  ⟨value % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

def encode {width : Nat} (value : Bounded width) : BitVec width :=
  BitVec.ofFin value

def observe {ε : Type} {width : Nat} (result : Except ε (BitVec width)) :
    Except ε (Bounded width) :=
  result.map BitVec.toFin

/-- The non-success fault tags of the physical shared operational context. -/
inductive Fault where
  | invalidRequest
  | resourceFault
  | lengthOverflow
  | nullReference
  | indexOutOfBounds
  | divisionByZero
  | shiftOutOfRange
  | notOwned
  deriving DecidableEq, Repr

/-- Unsigned binary operations admitted on `u64` by the operational compiler. -/
inductive WordOp where
  | add | sub | mul | div | mod | shl | shr | band | bor | bxor
  deriving DecidableEq, Repr

/-- Comparisons admitted on either `u64` or `byte`. -/
inductive Comparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

def sourceBinary (op : WordOp) (a b : Word) : Except Fault Word :=
  match op with
  | .add => .ok (bounded 64 (a.val + b.val))
  | .sub => .ok (bounded 64 ((2 ^ 64 - b.val) + a.val))
  | .mul => .ok (bounded 64 (a.val * b.val))
  | .div => if b.val = 0 then .error .divisionByZero
      else .ok ⟨a.val / b.val, Nat.div_lt_of_lt a.isLt⟩
  | .mod => if b.val = 0 then .error .divisionByZero
      else .ok ⟨a.val % b.val, Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt⟩
  | .shl => if 64 ≤ b.val then .error .shiftOutOfRange
      else .ok (bounded 64 (a.val * 2 ^ b.val))
  | .shr => if 64 ≤ b.val then .error .shiftOutOfRange
      else .ok ⟨a.val / 2 ^ b.val, Nat.div_lt_of_lt a.isLt⟩
  | .band => .ok ⟨a.val &&& b.val, Nat.and_lt_two_pow _ b.isLt⟩
  | .bor => .ok ⟨a.val ||| b.val, Nat.or_lt_two_pow a.isLt b.isLt⟩
  | .bxor => .ok ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow a.isLt b.isLt⟩

def targetBinary (op : WordOp) (a b : BitVec 64) : Except Fault (BitVec 64) :=
  match op with
  | .add => .ok (a + b)
  | .sub => .ok (a - b)
  | .mul => .ok (a * b)
  | .div => if b = 0 then .error .divisionByZero else .ok (a / b)
  | .mod => if b = 0 then .error .divisionByZero else .ok (a % b)
  | .shl => if b ≥ (64 : BitVec 64) then .error .shiftOutOfRange
      else .ok (a <<< b.toNat)
  | .shr => if b ≥ (64 : BitVec 64) then .error .shiftOutOfRange
      else .ok (a >>> b.toNat)
  | .band => .ok (a &&& b)
  | .bor => .ok (a ||| b)
  | .bxor => .ok (a ^^^ b)

def sourceComparison {width : Nat} (op : Comparison) (a b : Bounded width) : Bool :=
  match op with
  | .eq => decide (a.val = b.val)
  | .ne => decide (a.val ≠ b.val)
  | .lt => decide (a.val < b.val)
  | .le => decide (a.val ≤ b.val)
  | .gt => decide (b.val < a.val)
  | .ge => decide (b.val ≤ a.val)

def targetComparison {width : Nat} (op : Comparison) (a b : BitVec width) : Bool :=
  match op with
  | .eq => a == b
  | .ne => !(a == b)
  | .lt => a.ult b
  | .le => a.ule b
  | .gt => b.ult a
  | .ge => b.ule a

def sourceComplement (a : Word) : Word :=
  ⟨(2 ^ 64 - 1) ^^^ a.val, Nat.xor_lt_two_pow (by decide +kernel) a.isLt⟩

def targetComplement (a : BitVec 64) : BitVec 64 := ~~~a

def sourceToByte (a : Word) : Byte := bounded 8 a.val
def targetToByte (a : BitVec 64) : BitVec 8 := a.setWidth 8

def sourceToWord (a : Byte) : Word :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt (by decide +kernel)⟩

def targetToWord (a : BitVec 8) : BitVec 64 := a.setWidth 64

@[simp] theorem encode_toNat {width : Nat} (a : Bounded width) :
    (encode a).toNat = a.val := rfl

@[simp] theorem encode_toFin {width : Nat} (a : Bounded width) :
    (encode a).toFin = a := rfl

@[simp] theorem encode_eq_zero (a : Word) : encode a = 0 ↔ a.val = 0 := by
  rw [← BitVec.toNat_inj]
  simp

@[simp] theorem encode_shift_guard (b : Word) :
    (64 : BitVec 64) ≤ encode b ↔ 64 ≤ b.val := by
  rw [BitVec.le_def]
  simp

/-- All ten binary primitives preserve both successful results and faults. -/
theorem binary_correspondence (op : WordOp) (a b : Word) :
    observe (targetBinary op (encode a) (encode b)) = sourceBinary op a b := by
  cases op <;> simp only [sourceBinary, targetBinary, encode_eq_zero, encode_shift_guard,
    observe]
  all_goals try split_ifs
  all_goals simp only [Except.map]
  all_goals first
  | rfl
  | apply congrArg Except.ok
    apply Fin.ext
    simp only [BitVec.val_toFin, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      encode_toNat, bounded, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-- Comparisons agree at every bit width, including bytes after C promotion. -/
theorem comparison_correspondence {width : Nat} (op : Comparison)
    (a b : Bounded width) :
    targetComparison op (encode a) (encode b) = sourceComparison op a b := by
  have heq : (encode a == encode b) = decide (a.val = b.val) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, encode_toNat]
  cases op <;> simp [targetComparison, sourceComparison, BitVec.ult, BitVec.ule, heq]

theorem complement_correspondence (a : Word) :
    (targetComplement (encode a)).toFin = sourceComplement a := by
  apply Fin.ext
  simp only [targetComplement, BitVec.val_toFin, BitVec.not_def, BitVec.toNat_xor,
    BitVec.toNat_allOnes, encode_toNat, sourceComplement]

theorem toByte_correspondence (a : Word) :
    (targetToByte (encode a)).toFin = sourceToByte a := by
  apply Fin.ext
  simp [targetToByte, sourceToByte, bounded]

theorem toWord_correspondence (a : Byte) :
    (targetToWord (encode a)).toFin = sourceToWord a := by
  apply Fin.ext
  change (targetToWord (encode a)).toNat = a.val
  rw [targetToWord, BitVec.toNat_setWidth_of_le (by decide +kernel : 8 ≤ 64), encode_toNat]

theorem byte_promotion_comparison (op : Comparison) (a b : Byte) :
    targetComparison op (targetToWord (encode a)) (targetToWord (encode b)) =
      sourceComparison op a b := by
  have ha : targetToWord (encode a) = encode (sourceToWord a) :=
    BitVec.eq_of_toFin_eq (toWord_correspondence a)
  have hb : targetToWord (encode b) = encode (sourceToWord b) :=
    BitVec.eq_of_toFin_eq (toWord_correspondence b)
  rw [ha, hb, comparison_correspondence]
  cases op <;> rfl

/-- Natural inputs are accepted exactly when representable; no wrapping admission. -/
def admitWord (value : Nat) : Option Word :=
  if h : value < 2 ^ 64 then some ⟨value, h⟩ else none

theorem admitWord_some_iff (value : Nat) (word : Word) :
    admitWord value = some word ↔ value = word.val := by
  unfold admitWord
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h; exact congrArg Fin.val h
    · intro h; exact Fin.ext h
  · constructor
    · simp
    · intro h; subst value; exact False.elim (‹¬ word.val < 2 ^ 64› word.isLt)

theorem admitWord_none_iff (value : Nat) :
    admitWord value = none ↔ 2 ^ 64 ≤ value := by
  simp [admitWord]

/-- First fault wins in the shared physical context. -/
def recordFault (prior : Option Fault) (next : Fault) : Option Fault :=
  match prior with
  | none => some next
  | some old => some old

@[simp] theorem recordFault_first (old next : Fault) :
    recordFault (some old) next = some old := rfl

@[simp] theorem recordFault_empty (next : Fault) : recordFault none next = some next := rfl

/-- Source sequencing uses monadic left-to-right evaluation. -/
def sourceOrdered (op : WordOp) (left : Except Fault Word)
    (right : Unit → Except Fault Word) : Except Fault Word := do
  let a ← left
  let b ← right ()
  sourceBinary op a b

/-- Target sequencing makes the two emitted temporaries and their fault checks explicit. -/
def targetOrdered (op : WordOp) (left : Except Fault (BitVec 64))
    (right : Unit → Except Fault (BitVec 64)) : Except Fault (BitVec 64) :=
  match left with
  | .error fault => .error fault
  | .ok a => match right () with
      | .error fault => .error fault
      | .ok b => targetBinary op a b

theorem ordered_correspondence (op : WordOp)
    (sl : Except Fault Word) (tl : Except Fault (BitVec 64))
    (sr : Unit → Except Fault Word) (tr : Unit → Except Fault (BitVec 64))
    (hl : observe tl = sl) (hr : ∀ u, observe (tr u) = sr u) :
    observe (targetOrdered op tl tr) = sourceOrdered op sl sr := by
  cases tl with
  | error fault =>
      have hl' : sl = .error fault := by simpa [observe, Except.map] using hl.symm
      rw [hl']
      rfl
  | ok a =>
      have hl' : sl = .ok a.toFin := by simpa [observe, Except.map] using hl.symm
      cases htr : tr () with
      | error fault =>
          have hr' : sr () = .error fault := by
            simpa [observe, Except.map, htr] using (hr ()).symm
          rw [hl']
          simp only [targetOrdered, htr, observe, Except.map]
          change Except.error fault = (sr ()).bind (sourceBinary op a.toFin)
          rw [hr']
          rfl
      | ok b =>
          have hr' : sr () = .ok b.toFin := by
            simpa [observe, Except.map, htr] using (hr ()).symm
          rw [hl']
          simp only [targetOrdered, htr]
          change observe (targetBinary op a b) = (sr ()).bind (sourceBinary op a.toFin)
          rw [hr']
          exact binary_correspondence op a.toFin b.toFin

theorem observe_ok_iff {width : Nat} (result : Except Fault (BitVec width))
    (value : Bounded width) :
    observe result = .ok value ↔ result = .ok (encode value) := by
  cases result with
  | error fault => simp [observe, Except.map]
  | ok target =>
      simp only [observe, Except.map, Except.ok.injEq]
      constructor
      · intro h
        exact BitVec.eq_of_toFin_eq (h.trans (encode_toFin value).symm)
      · intro h
        exact congrArg BitVec.toFin h

theorem observe_error_iff {width : Nat} (result : Except Fault (BitVec width))
    (fault : Fault) : observe result = .error fault ↔ result = .error fault := by
  cases result <;> simp [observe, Except.map]

/-- Reflection as well as preservation: no extra target successful result. -/
theorem binary_success_iff (op : WordOp) (a b result : Word) :
    targetBinary op (encode a) (encode b) = .ok (encode result) ↔
      sourceBinary op a b = .ok result := by
  rw [← observe_ok_iff, binary_correspondence]

theorem binary_fault_iff (op : WordOp) (a b : Word) (fault : Fault) :
    targetBinary op (encode a) (encode b) = .error fault ↔
      sourceBinary op a b = .error fault := by
  rw [← observe_error_iff, binary_correspondence]

/-- The exact domain of refusal, excluding faults from unrelated primitives. -/
theorem binary_refusal_iff (op : WordOp) (a b : Word) (fault : Fault) :
    sourceBinary op a b = .error fault ↔
      ((op = .div ∨ op = .mod) ∧ b.val = 0 ∧ fault = .divisionByZero) ∨
      ((op = .shl ∨ op = .shr) ∧ 64 ≤ b.val ∧ fault = .shiftOutOfRange) := by
  cases op <;> simp [sourceBinary, eq_comm]
  all_goals split_ifs <;> simp_all

/-- Detecting a carry by comparing the wrapped sum to its first operand. -/
theorem add_carry_iff (a b : Word) :
    (encode a + encode b).toNat < a.val ↔ 2 ^ 64 ≤ a.val + b.val := by
  rw [BitVec.toNat_add, encode_toNat, encode_toNat, Nat.add_mod_eq_sub,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]
  split_ifs <;> constructor <;> intro h <;> have := a.isLt <;> have := b.isLt <;> omega

theorem add_no_carry_value (a b : Word) (h : a.val + b.val < 2 ^ 64) :
    (encode a + encode b).toNat = a.val + b.val := by
  rw [BitVec.toNat_add, encode_toNat, encode_toNat, Nat.mod_eq_of_lt h]

/-- Non-null physical context execution, including its failure-return placeholder. -/
structure ContextWordResult where
  returned : BitVec 64
  fault : Option Fault

def targetWithContext (op : WordOp) (prior : Option Fault) (a b : BitVec 64) :
    ContextWordResult :=
  match prior with
  | some fault => ⟨0, some fault⟩
  | none => match targetBinary op a b with
      | .ok value => ⟨value, none⟩
      | .error fault => ⟨0, recordFault none fault⟩

def observeContext (result : ContextWordResult) : Except Fault Word :=
  match result.fault with
  | some fault => .error fault
  | none => .ok result.returned.toFin

def sourceWithContext (op : WordOp) (prior : Option Fault) (a b : Word) : Except Fault Word :=
  match prior with
  | some fault => .error fault
  | none => sourceBinary op a b

theorem context_correspondence (op : WordOp) (prior : Option Fault) (a b : Word) :
    observeContext (targetWithContext op prior (encode a) (encode b)) =
      sourceWithContext op prior a b := by
  cases prior with
  | some fault => rfl
  | none =>
      cases ht : targetBinary op (encode a) (encode b) <;>
        simpa [targetWithContext, sourceWithContext, ht, observeContext, observe,
          Except.map] using binary_correspondence op a b

theorem context_prior_fault_preserved (op : WordOp) (fault : Fault) (a b : BitVec 64) :
    observeContext (targetWithContext op (some fault) a b) = .error fault := rfl

theorem context_zero_placeholder_refused (op : WordOp) (a b : BitVec 64) (fault : Fault)
    (h : targetBinary op a b = .error fault) :
    (targetWithContext op none a b).returned = 0 ∧
      observeContext (targetWithContext op none a b) = .error fault := by
  simp [targetWithContext, h, observeContext]

end Mettapedia.GSLT.LanguageDef.NativeWord64
