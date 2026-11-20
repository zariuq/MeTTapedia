import Mettapedia.Machines.TIsa.X86P1LoadBounds
import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86AddImmediate
import Mettapedia.Machines.TIsa.X86SubByteImmediate
import Mettapedia.Machines.TIsa.P1Memory

/-!
# Shared facts for the p1 full-word bounds checks

The full-word bounded-load spans of the p1 images are instances of the
parameterized bounds template of `X86Bounds` followed by the original qword MOV
(`X86BoundedLoad` with `wide := true`); their bytes, rejection targets and
executions live there. This module keeps the readable data word of a
displacement-16 qword load, the handler table, the carry and above flag senses
used by every bounds template, and the source-access agreement of the
displacement-16 range test.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1QwordBounds
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev writes : Finset Register := {.rip,.rflags,.r14,.r15}

theorem writes_data : writes ⊆ dataRegisters := by decide

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86P1LoadBounds.baseHandlers other
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86P1LoadBounds.handlers other extra

structure Readable (state : State) (pointer value : Word) where
  dataAddress : BitVec 48
  effective : pointer + 16 = dataAddress.signExtend 64
  upper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  aligned : dataAddress &&& (7#48) = (0#48)
  bytes : ∀ index < 8,
    state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)

theorem above_sense (left right : Word) (flags : BitVec 32)
    (carry : Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (left.toNat < right.toNat))
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec (left - right).toNat) :
    X86BranchCondition.value .above flags = decide (right.toNat < left.toNat) :=
  X86P1LoadBounds.above_sense left right flags carry zero

theorem carry_bit_sense (predicate : Bool) : ((1#1) == Functions.bool_to_bits predicate) = predicate := by
  cases predicate <;> rfl

theorem length_remaining (length : Word) (enough : 8 ≤ length.toNat) :
    (length - (8#64)).toNat = length.toNat - 8 :=
  BitVec.toNat_sub_of_le (by change 8 ≤ length.toNat; exact enough)

theorem offset_nat (pointer base : Word) (noWrap : (pointer - base).toNat + 16 < 2 ^ 64) :
    (pointer - base + 16).toNat = (pointer - base).toNat + 16 := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt noWrap

theorem source_guard (base length pointer : Word) (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat) (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat) :
    (pointer - base).toNat + 24 ≤ length.toNat ↔
      Memory.access? base length pointer (16#32).toInt 8 = some (pointer.toNat + 16) := by
  have subtract : (pointer - base).toNat = pointer.toNat - base.toNat :=
    BitVec.toNat_sub_of_le (by change base.toNat ≤ pointer.toNat; exact pointerLower)
  rw [subtract,P1Memory.access?_iff_inside base length pointer (16#32) 8 (pointer.toNat + 16)
    rangeFits pointerLower pointerUpper]
  change pointer.toNat - base.toNat + 24 ≤ length.toNat ↔
    (base.toNat : Int) ≤ (pointer.toNat : Int) + 16 ∧
    (pointer.toNat : Int) + 16 + 8 ≤ (base.toNat : Int) + length.toNat ∧
    pointer.toNat + 16 = ((pointer.toNat : Int) + 16).toNat
  have formed : ((pointer.toNat : Int) + 16).toNat = pointer.toNat + 16 := by omega
  simp only [formed,and_true]
  omega

end Mettapedia.Machines.TIsa.X86P1QwordBounds
