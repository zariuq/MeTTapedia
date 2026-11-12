import Mettapedia.Machines.TIsa.Scalar
import Mettapedia.Machines.TIsa.Footprint
import Mathlib.Tactic.IntervalCases

/-!
# Little-endian words at the native byte boundary

The resource semantics addresses bytes. This interface proves the concrete
word packing used by load/store templates, including signed and unsigned
32-bit reads. The proofs use bitwise extensionality and kernel reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

def packBytes : List (BitVec 8) → Word
  | [] => 0
  | byte :: later => byte.zeroExtend 64 ||| BitVec.shiftLeft (packBytes later) 8

def unpackBytes : Nat → Word → List (BitVec 8)
  | 0, _ => []
  | count + 1, value => value.extractLsb' 0 8 :: unpackBytes count (BitVec.ushiftRight value 8)

theorem unpackBytes_length (count : Nat) (value : Word) :
    (unpackBytes count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [unpackBytes, ih]

theorem pack_unpack64 (value : Word) : packBytes (unpackBytes 8 value) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  interval_cases index <;> simp [unpackBytes, packBytes]

theorem pack_unpack32 (value : Word) :
    packBytes (unpackBytes 4 value) = (value.extractLsb' 0 32).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  interval_cases index <;> simp [unpackBytes, packBytes]

theorem pack_unpack8 (value : Word) :
    packBytes (unpackBytes 1 value) = (value.extractLsb' 0 8).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  interval_cases index <;> simp [unpackBytes, packBytes]

def load32Signed (bytes : List (BitVec 8)) : Word :=
  ((packBytes bytes).extractLsb' 0 32).signExtend 64

theorem load32Signed_unpack (value : Word) :
    load32Signed (unpackBytes 4 value) = (value.extractLsb' 0 32).signExtend 64 := by
  rw [load32Signed, pack_unpack32]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have within : index < 64 := by omega
  simp [bound, within]

theorem word_read_after_write (memory : ByteMemory) (address : Nat) (value : Word) :
    (readBytes (writeBytes memory address (unpackBytes 8 value)) address 8).map packBytes = some value := by
  have readback := readBytes_after_write memory address (unpackBytes 8 value)
  rw [unpackBytes_length] at readback
  rw [readback]
  simpa using congrArg some (pack_unpack64 value)

theorem word_write_preserves_outside (memory : ByteMemory) (address : Nat) (value : Word)
    (other : Nat) (outside : other < address ∨ address + 8 ≤ other) :
    writeBytes memory address (unpackBytes 8 value) other = memory other := by
  apply writeBytes_outside
  simpa [unpackBytes_length] using outside

namespace ByteControls

example : unpackBytes 4 305419896 = [120, 86, 52, 18] := by decide

example : packBytes [120, 86, 52, 18] = 305419896 := by decide

example : load32Signed [255, 255, 255, 255] = 18446744073709551615 := by decide

example : packBytes [255, 255, 255, 255] = 4294967295 := by decide

end ByteControls

#print axioms pack_unpack64
#print axioms word_read_after_write

end Mettapedia.Machines.TIsa
