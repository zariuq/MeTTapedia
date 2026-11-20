import Mettapedia.Machines.TIsa.X86SibQword
import Mettapedia.Machines.TIsa.X86SubImmediate

/-!
# Address construction by prepared indexed LEA

The imported operation comes from the same generated Sail model as
the other instruction handlers. The SIB byte selects R13 and an index. The
displacement is sign-extended from the emitted byte. LEA has no data-memory access and leaves the
capability check to the preceding prepared address sequence.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/LeaFunctions.lean.inc"
  sha256 "41d1f4237f9902080a1a2f6d082b5c7245197cce20d3bf97ff0faedc9a2323a8"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86PreparedLea

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86DwordLoad (loadRex)
local instance : MemoryPrimitives := X86Memory.ordinary

/-- A low index register with the SIB no-index encoding excluded. -/
abbrev Index := { reg : Fin 8 // reg.val ≠ 4 }

def Index.register (index : Index) : Fin 16 :=
  ⟨index.val.val, index.val.isLt.trans (by decide)⟩

def Index.sib (index : Index) : BitVec 8 := .ofNat 8 (8 * index.val.val + 5)

private theorem Index.fields (index : Index) :
    Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base index.sib) (0x4d#8) (0#2)) =
        (13 : Int) ∧
      Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index index.sib) (0x4d#8) (1#2)) 4 = false ∧
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index index.sib) (0x4d#8) (1#2)) =
        (index.register.val : Int) ∧
      Sail.BitVec.toNatInt (Functions._get_sib_scale index.sib) = 0 := by
  have all : ∀ i : Fin 8, ∀ distinct : i.val ≠ 4,
      let index : Index := ⟨i, distinct⟩
      Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_base index.sib) (0x4d#8) (0#2)) =
          (13 : Int) ∧
        Functions.eq_bits_nat (Functions.reg_index (Functions._get_sib_index index.sib) (0x4d#8) (1#2)) 4 = false ∧
        Sail.BitVec.toNatInt (Functions.reg_index (Functions._get_sib_index index.sib) (0x4d#8) (1#2)) =
          (index.register.val : Int) ∧
        Sail.BitVec.toNatInt (Functions._get_sib_scale index.sib) = 0 := by decide +kernel
  exact all index.val index.property

private theorem reads_displacement (state : State) (atByte : BitVec 48) (pointer : Word) (displacement : BitVec 8)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (ip : state.regs.get? .rip = some pointer)
    (byte : state.mem.get? (atByte.signExtend 52).toNat = some displacement) :
    (Functions.rime_size .Mode_64bit 8 1 (atByte.signExtend 64) none 1 ":X" false false).run state =
      .ok (displacement.signExtend 64) state := by
  unfold Functions.rime_size
  change (do
    let value ← Functions.rme08 .Mode_64bit 8 (atByte.signExtend 64) none 1 ":X"
    pure (Sail.BitVec.signExtend value 64) : SailM Word).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state atByte pointer attributes displacement
    segments application ip byte]
  rfl

theorem effective (state : State) (index : Index) (atByte : BitVec 48) (pointer base offset : Word) (displacement : BitVec 8)
    (attributes : Vector (BitVec 16) 6) (prefixes : BitVec 52)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (ip : state.regs.get? .rip = some pointer)
    (byte : state.mem.get? (atByte.signExtend 52).toNat = some displacement)
    (baseKnown : lookup state 13 = some base) (offsetKnown : lookup state index.register = some offset) :
    (Functions.x86_effective_addr .Mode_64bit prefixes atByte (0x4d#8) (4#3) (1#2) index.sib (0#3)).run state =
      .ok (base + offset + displacement.signExtend 64, (1 : Int)) state := by
  unfold Functions.x86_effective_addr
  rw [addressOverride]
  simp only [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride],
    pure_bind, show ((2 : Int) == 8) = false from rfl, Bool.false_eq_true, ite_false]
  unfold Functions.x86_effective_addr_32_64 Functions.x86_effective_addr_from_sib
  simp only [show Functions.eq_bits_nat (1#2) 0 = false from rfl,
    show Functions.eq_bits_nat (1#2) 1 = true from rfl,
    show Functions.eq_bits_nat (4#3) 4 = true from rfl,
    show Functions.select_address_size .Mode_64bit none = (pure 8 : SailM Int) from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,
    Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  rw [show Sail.BitVec.signExtend atByte 64 = atByte.signExtend 64 from rfl,
    run_bind, reads_displacement state atByte pointer displacement attributes segments application ip byte]
  dsimp only
  simp only [Functions.in_64bit_mode, ite_true, index.fields.1, run_bind]
  have baseRead : (Functions.rgfi (13 : Int)).run state = .ok base state :=
    rgfi_exact state 13 base baseKnown
  rw [baseRead]
  dsimp only
  simp only [run_pure, index.fields.2.1, index.fields.2.2.1, Bool.false_eq_true, ite_false]
  have indexRead : (Functions.rgfi (index.register.val : Int)).run state = .ok offset state :=
    rgfi_exact state index.register offset offsetKnown
  rw [indexRead]
  dsimp only
  rw [if_neg (by decide : ¬ ((103#8) == (0#8)) = true)]
  have scaled : Functions.ash_left_int offset.toInt
      (Sail.BitVec.toNatInt (Functions._get_sib_scale index.sib)).toNat = offset.toInt := by
    rw [index.fields.2.2.2]
    change offset.toInt * (1 : Int) = _
    exact Int.mul_one _
  rw [scaled]
  simp only [X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt]

theorem handler (state : State) (index : Index) (start atByte next : BitVec 48) (pointer base offset : Word) (displacement : BitVec 8)
    (attributes : Vector (BitVec 16) 6) (prefixes : BitVec 52)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : atByte.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (ip : state.regs.get? .rip = some pointer)
    (byte : state.mem.get? (atByte.signExtend 52).toNat = some displacement)
    (baseKnown : lookup state 13 = some base) (offsetKnown : lookup state index.register = some offset)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_lea .Mode_64bit start atByte prefixes (0x4d#8) (0x8d#8) (0x44#8) index.sib).run state =
      .ok () (X86Move.putPointer (put state 8 (base + offset + displacement.signExtend 64)) next) := by
  unfold Functions.x86_lea
  rw [show Functions.select_operand_size .Mode_64bit false (0x4d#8) false prefixes false false false =
    (pure 8 : SailM Int) from X86Move.operand_size64 (8 : Fin 16) 13 prefixes]
  simp only [pure_bind, show Functions.check_range 2 8 8 = (pure 8 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_r_m (0x44#8) = (4#3) from rfl,
    show Functions._get_modr_m_mod (0x44#8) = (1#2) from rfl,
    run_bind, effective state index atByte pointer base offset displacement attributes prefixes addressOverride
      segments application ip byte baseKnown offsetKnown]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 1 3) 48 = (1#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state atByte (1#48) next (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  have roundtrip : Functions.sail_mask 64 (Functions.trunc_signed 8 (base + offset + displacement.signExtend 64)) =
      base + offset + displacement.signExtend 64 := by
    unfold Functions.trunc_signed Functions.sail_mask Functions.sail_mask_signed
    simp [Sail.BitVec.truncate]
  rw [show Int.toNat (8 : Int) = 8 from rfl, roundtrip, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    show Functions.reg_index (Functions._get_modr_m_reg (0x44#8)) (0x4d#8) (2#2) = (8#4) from rfl,
    run_bind]
  have written : (Functions.write_rgfi_size (8#4) (8#4) (base + offset + displacement.signExtend 64) (0x4d#8)).run state =
      .ok () (put state 8 (base + offset + displacement.signExtend 64)) := X86QwordLoad.write_destination64 state 8 13 _ quiet
  rw [written]
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

noncomputable abbrev linked (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  {other with x86_lea := Functions.x86_lea}

theorem fetched_displaced (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State) (index : Index)
    (origin : X86LegacyFetch.Basis state) (atByte next : BitVec 48) (base offset : Word) (displacement : BitVec 8)
    (beforeByte : origin.next.toInt + 1 = atByte.toInt) (advance : atByte.toInt + 1 = next.toInt)
    (baseKnown : lookup state 13 = some base) (offsetKnown : lookup state index.register = some offset)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x4d#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8d#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x44#8))
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some index.sib)
    (dispByte : state.mem.get? (atByte.signExtend 52).toNat = some displacement) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 8 (base + offset + displacement.signExtend 64)) next) := by
  let : OtherOpcodeHandlers := linked other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x8d#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide +kernel)
  rw [X86SibStore.fetch_to_dispatch_sib (0x8d#8) shape true state origin atByte 8 13
    (0x44#8) index.sib (by decide +kernel) beforeByte rexByte opcodeByte modrmByte sibByte]
  have length : Functions.check_instruction_length origin.address next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 5 (by decide)
    have := origin.step3
    have := origin.step2
    omega
  exact handler state index origin.address atByte next (origin.address.signExtend 64) base offset displacement origin.attributes
    (X86LegacyFetch.packet (0x8d#8)) (X86LegacyFetch.packet_address _) advance length origin.segments
    origin.application origin.rip dispByte baseKnown offsetKnown quiet

theorem fetched_indexed (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State) (index : Index)
    (origin : X86LegacyFetch.Basis state) (atByte next : BitVec 48) (base offset : Word)
    (beforeByte : origin.next.toInt + 1 = atByte.toInt) (advance : atByte.toInt + 1 = next.toInt)
    (baseKnown : lookup state 13 = some base) (offsetKnown : lookup state index.register = some offset)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x4d#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8d#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x44#8))
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some index.sib)
    (dispByte : state.mem.get? (atByte.signExtend 52).toNat = some (0#8)) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 8 (base + offset)) next) := by
  have ran := fetched_displaced other vector state index origin atByte next base offset 0 beforeByte advance
    baseKnown offsetKnown quiet rexByte opcodeByte modrmByte sibByte dispByte
  have exactWord : base + offset + (0 : BitVec 8).signExtend 64 = base + offset := BitVec.add_zero _
  rw [exactWord] at ran
  exact ran

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (state : State)
    (origin : X86LegacyFetch.Basis state) (atByte next : BitVec 48) (base offset : Word)
    (beforeByte : origin.next.toInt + 1 = atByte.toInt) (advance : atByte.toInt + 1 = next.toInt)
    (baseKnown : lookup state 13 = some base) (offsetKnown : lookup state 3 = some offset)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x4d#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8d#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x44#8))
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some (0x1d#8))
    (dispByte : state.mem.get? (atByte.signExtend 52).toNat = some (0#8)) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 8 (base + offset)) next) :=
  fetched_indexed other vector state ⟨3, by decide⟩ origin atByte next base offset beforeByte advance
    baseKnown offsetKnown quiet rexByte opcodeByte modrmByte sibByte dispByte

end Mettapedia.Machines.TIsa.X86PreparedLea
