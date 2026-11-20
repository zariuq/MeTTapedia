import Mettapedia.Machines.TIsa.X86SubImmediate
import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86BranchCondition
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86FrameArithmetic

/-!
# Shared observation records for p1 bounds checks

The bounded-load spans of the p1 images are instances of the parameterized
bounds template of `X86Bounds` followed by the original MOV load
(`X86BoundedLoad`); their bytes, rejection targets and executions live there.
This module keeps the observation records those spans consume: the frame,
region-descriptor and pointer facts at a fetch position with an explicit image
extent, the readable data word of a U32 load, the handler table and the
unsigned-above flag sense used by the range test.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1LoadBounds

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev writes : Finset Register := {.rip,.rflags,.r14,.r15}

theorem writes_data : writes ⊆ dataRegisters := by decide

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameIncrement.linkedHandlers (X86Funding.Placed.baseHandlers other)
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (baseHandlers other) extra

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) (extent : Nat) where
  upper : origin.address.toInt + extent < (2 ^ 47 : Int)
  frame : Word
  base : Word
  pointer : Word
  length : Word
  baseAddress : BitVec 48
  lengthAddress : BitVec 48
  controls : Vector (BitVec 64) 17
  visible : Vector (BitVec 16) 6
  flags : BitVec 32
  frameKnown : lookup state 7 = some frame
  pointerKnown : lookup state 6 = some pointer
  baseEffective : frame = baseAddress.signExtend 64
  lengthEffective : frame + (8#32).signExtend 64 = lengthAddress.signExtend 64
  baseUpper : baseAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  lengthUpper : lengthAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  baseAligned : baseAddress &&& (7#48) = (0#48)
  lengthAligned : lengthAddress &&& (7#48) = (0#48)
  controlKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  baseBytes : ∀ index < 8,
    state.mem.get? ((address baseAddress.toInt index).signExtend 52).toNat =
      some (base.extractLsb' (8 * index) 8)
  lengthBytes : ∀ index < 8,
    state.mem.get? ((address lengthAddress.toInt index).signExtend 52).toNat =
      some (length.extractLsb' (8 * index) 8)

structure Readable (state : State) (pointer : Word) (value : BitVec 32) where
  dataAddress : BitVec 48
  effective : pointer = dataAddress.signExtend 64
  upper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int)
  aligned : dataAddress &&& (3#48) = (0#48)
  bytes : ∀ index < 4,
    state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)

theorem above_sense (left right : Word) (flags : BitVec 32)
    (carry : Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (left.toNat < right.toNat))
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec (left - right).toNat) :
    X86BranchCondition.value .above flags = decide (right.toNat < left.toNat) := by
  have zeroEq : (left - right).toNat = 0 ↔ left = right := by
    constructor
    · intro zero
      apply BitVec.eq_of_toNat_eq
      have := left.isLt
      have := right.isLt
      have := BitVec.toNat_sub left right
      omega
    · intro same
      subst right
      simp only [BitVec.sub_self]
      rfl
  simp only [X86BranchCondition.value, carry, zero]
  by_cases below : left.toNat < right.toNat
  · have notAbove : ¬ right.toNat < left.toNat := by omega
    simp [Functions.bool_to_bits, below, notAbove]
  · by_cases same : left = right
    · subst right
      simp [Functions.bool_to_bits, Functions.zf_spec]
    · have notZero : (left - right).toNat ≠ 0 := fun zero => same (zeroEq.mp zero)
      have notSame : left.toNat ≠ right.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      have above : right.toNat < left.toNat := by omega
      have zflag : Functions.zf_spec (left - right).toNat = (0#1) := by
        simp only [Functions.zf_spec, show ((left - right).toNat == 0) = false from beq_eq_false_iff_ne.mpr notZero,
          Bool.false_eq_true, ite_false]
      rw [zflag]
      simp [Functions.bool_to_bits, below, above]

theorem length_remaining (length : Word) (enough : 4 ≤ length.toNat) :
    (length - (4#64)).toNat = length.toNat - 4 := by
  change (length - (4#64)).toNat = length.toNat - (4#64).toNat
  exact BitVec.toNat_sub_of_le (by change 4 ≤ length.toNat; exact enough)

end Mettapedia.Machines.TIsa.X86P1LoadBounds
