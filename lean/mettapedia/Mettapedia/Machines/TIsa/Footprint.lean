import Lean.Elab.Tactic.Omega
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Basic

/-!
# The minimal byte-range interface for native lowering

Range endpoints are natural numbers before conversion to machine pointers.
This keeps bounds proofs independent of address wraparound. These records
describe footprints of existing transform resources, not new store authority.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

structure ByteRange where
  base : Nat
  length : Nat
  deriving DecidableEq, Repr

def ByteRange.stop (range : ByteRange) : Nat := range.base + range.length

def ByteRange.Contains (range : ByteRange) (address : Nat) : Prop :=
  range.base ≤ address ∧ address < range.stop

instance (range : ByteRange) (address : Nat) : Decidable (range.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ByteRange.Separate (left right : ByteRange) : Prop :=
  left.stop ≤ right.base ∨ right.stop ≤ left.base

instance (left right : ByteRange) : Decidable (left.Separate right) :=
  inferInstanceAs (Decidable (_ ∨ _))

def ByteRange.valid64 (range : ByteRange) : Bool :=
  decide (range.base < 2 ^ 64 ∧ range.stop ≤ 2 ^ 64)

def ByteRange.bytes (range : ByteRange) : Finset Nat :=
  Finset.Ico range.base range.stop

theorem ByteRange.mem_bytes (range : ByteRange) (address : Nat) :
    address ∈ range.bytes ↔ range.Contains address := by
  simp [bytes, Contains]

theorem ByteRange.separate_symm (left right : ByteRange) :
    left.Separate right ↔ right.Separate left := by
  exact Or.comm

theorem ByteRange.no_overlap (left right : ByteRange) (separate : left.Separate right)
    (address : Nat) (inLeft : left.Contains address) : ¬right.Contains address := by
  unfold Separate stop at separate
  unfold Contains stop at *
  omega

theorem ByteRange.disjoint_bytes (left right : ByteRange) (separate : left.Separate right) :
    Disjoint left.bytes right.bytes := by
  apply Finset.disjoint_left.mpr
  intro address inLeft inRight
  exact left.no_overlap right separate address ((left.mem_bytes address).mp inLeft)
    ((right.mem_bytes address).mp inRight)

/-- Offset/width checks are subtraction-free and do not wrap machine words. -/
def ByteRange.access? (range : ByteRange) (offset width : Nat) : Option Nat :=
  if range.valid64 ∧ offset + width ≤ range.length then some (range.base + offset) else none

theorem ByteRange.access?_iff (range : ByteRange) (offset width address : Nat) :
    range.access? offset width = some address ↔
      range.base < 2 ^ 64 ∧ range.stop ≤ 2 ^ 64 ∧
      offset + width ≤ range.length ∧ address = range.base + offset := by
  unfold access?
  by_cases permitted : range.valid64 = true ∧ offset + width ≤ range.length
  · rw [if_pos permitted]
    have bounds : range.base < 2 ^ 64 ∧ range.stop ≤ 2 ^ 64 := by
      exact of_decide_eq_true permitted.1
    constructor
    · intro equal
      exact ⟨bounds.1, bounds.2, permitted.2, (Option.some.inj equal).symm⟩
    · rintro ⟨_, _, _, equal⟩
      rw [equal]
  · rw [if_neg permitted]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨base, stop, within, _⟩
      exact False.elim (permitted ⟨by exact decide_eq_true ⟨base, stop⟩, within⟩)

theorem ByteRange.access?_no_wrap (range : ByteRange) (offset width address : Nat)
    (admitted : range.access? offset width = some address) :
    address + width ≤ 2 ^ 64 := by
  obtain ⟨_, bounded, within, rfl⟩ := (range.access?_iff offset width address).mp admitted
  unfold stop at bounded
  omega

theorem ByteRange.access?_inside (range : ByteRange) (offset width address index : Nat)
    (admitted : range.access? offset width = some address) (inWidth : index < width) :
    range.Contains (address + index) := by
  obtain ⟨_, _, within, rfl⟩ := (range.access?_iff offset width address).mp admitted
  unfold Contains stop
  omega

abbrev ByteMemory := Nat → Option (BitVec 8)

/-- Independent byte readback of a finite transform write footprint. -/
def writeBytes (memory : ByteMemory) : Nat → List (BitVec 8) → ByteMemory
  | _, [] => memory
  | address, byte :: later => writeBytes (Function.update memory address (some byte)) (address + 1) later

def readBytes (memory : ByteMemory) : Nat → Nat → Option (List (BitVec 8))
  | _, 0 => some []
  | address, length + 1 => do
      let byte ← memory address
      let later ← readBytes memory (address + 1) length
      pure (byte :: later)

theorem writeBytes_outside (memory : ByteMemory) (address : Nat) (bytes : List (BitVec 8))
    (other : Nat) (outside : other < address ∨ address + bytes.length ≤ other) :
    writeBytes memory address bytes other = memory other := by
  induction bytes generalizing memory address with
  | nil => rfl
  | cons byte later ih =>
      rw [writeBytes, ih]
      · apply Function.update_of_ne
        simp only [List.length_cons] at outside
        omega
      · simp only [List.length_cons] at outside
        omega

theorem readBytes_after_write (memory : ByteMemory) (address : Nat) (bytes : List (BitVec 8)) :
    readBytes (writeBytes memory address bytes) address bytes.length = some bytes := by
  induction bytes generalizing memory address with
  | nil => rfl
  | cons byte later ih =>
      simp only [List.length_cons, writeBytes, readBytes]
      rw [writeBytes_outside _ _ later address (Or.inl (by omega))]
      simp only [Function.update_self, ih]
      rfl

namespace FootprintControls

example : (ByteRange.mk 18446744073709551612 8).access? 0 8 = none := by decide

example : (ByteRange.mk 100 8).access? 4 8 = none := by decide

example : (ByteRange.mk 100 8).access? 4 4 = some 104 := by decide

example : ¬(ByteRange.mk 100 8).Separate ⟨104, 8⟩ := by decide

example : (ByteRange.mk 100 8).Separate ⟨108, 8⟩ := by decide

example : readBytes (writeBytes (fun _ => none) 2 [1, 2, 3]) 2 3 = some [1, 2, 3] := by decide

end FootprintControls

end Mettapedia.Machines.TIsa
