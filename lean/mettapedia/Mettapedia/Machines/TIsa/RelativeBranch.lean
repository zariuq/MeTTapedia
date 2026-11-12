import Mettapedia.Machines.TIsa.Bytes
import Mettapedia.Machines.TIsa.Widths

/-!
# Exact signed relative-displacement bytes

The x86 near-branch displacement is measured from the end of its four-byte
field. This interface checks actual field bytes and nonwrapping target
arithmetic. It does not replace instruction decoding or flag semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.RelativeBranch

def encode32 (value : BitVec 32) : List (BitVec 8) := unpackBytes 4 (value.zeroExtend 64)

def decode32 (bytes : List (BitVec 8)) : BitVec 32 := low32 (packBytes bytes)

theorem encode32_length (value : BitVec 32) : (encode32 value).length = 4 := unpackBytes_length _ _

theorem decode_encode32 (value : BitVec 32) : decode32 (encode32 value) = value := by
  rw [decode32, encode32, pack_unpack32]
  change low32 (extend32 false (low32 (extend32 false value))) = value
  simp only [low32_extend32]

def displacement (fieldOffset target : Nat) : Int := (target : Int) - ((fieldOffset : Int) + 4)

def Fits32 (value : Int) : Prop := -(2 ^ 31 : Int) ≤ value ∧ value < 2 ^ 31

instance (value : Int) : Decidable (Fits32 value) := inferInstanceAs (Decidable (_ ∧ _))

def encodeNear? (fieldOffset target : Nat) : Option (List (BitVec 8)) :=
  if Fits32 (displacement fieldOffset target) then
    some (encode32 (BitVec.ofInt 32 (displacement fieldOffset target))) else none

def decodedTarget (fieldOffset : Nat) (bytes : List (BitVec 8)) : Int :=
  (fieldOffset : Int) + 4 + (decode32 bytes).toInt

theorem encodeNear?_iff (fieldOffset target : Nat) (bytes : List (BitVec 8)) :
    encodeNear? fieldOffset target = some bytes ↔
      Fits32 (displacement fieldOffset target) ∧
      bytes = encode32 (BitVec.ofInt 32 (displacement fieldOffset target)) := by
  unfold encodeNear?
  by_cases fits : Fits32 (displacement fieldOffset target)
  · simp [fits, eq_comm]
  · simp [fits]

theorem encoded_target_exact (fieldOffset target : Nat) (bytes : List (BitVec 8))
    (encoded : encodeNear? fieldOffset target = some bytes) :
    decodedTarget fieldOffset bytes = target := by
  obtain ⟨fits, rfl⟩ := (encodeNear?_iff fieldOffset target bytes).mp encoded
  rw [decodedTarget, decode_encode32, BitVec.toInt_ofInt_eq_self (by decide) fits.1 fits.2]
  simp [displacement]

/-- Byte mutation must still satisfy the actual branch target equation. -/
def fieldCheck (image : List (BitVec 8)) (fieldOffset target : Nat) : Bool :=
  decide (fieldOffset + 4 ≤ image.length ∧ target ≤ image.length ∧
    decodedTarget fieldOffset ((image.drop fieldOffset).take 4) = (target : Int))

theorem fieldCheck_target (image : List (BitVec 8)) (fieldOffset target : Nat)
    (checked : fieldCheck image fieldOffset target = true) :
    fieldOffset + 4 ≤ image.length ∧ target ≤ image.length ∧
      decodedTarget fieldOffset ((image.drop fieldOffset).take 4) = (target : Int) :=
  of_decide_eq_true checked

namespace Controls

example : encodeNear? 2 0 = some [250, 255, 255, 255] := by decide
example : decodedTarget 2 [250, 255, 255, 255] = 0 := by decide
example : fieldCheck [15, 133, 250, 255, 255, 255] 2 0 = true := by decide
example : fieldCheck [15, 133, 251, 255, 255, 255] 2 0 = false := by decide
example : encodeNear? 0 2147483652 = none := by decide
example : fieldCheck [233, 0, 0, 0, 0] 1 9 = false := by decide

end Controls

end Mettapedia.Machines.TIsa.RelativeBranch
