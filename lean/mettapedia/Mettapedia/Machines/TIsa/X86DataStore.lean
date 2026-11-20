import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86FrameStore

/-!
# Fetched REX-prefixed data stores with exact byte effects

The original MOV handler and seven-byte fetch cover full-word and low-dword
stores for arbitrary source/base registers, signed disp32 and canonical data
addresses in the no-SIB/default-data-segment form. Only RIP and the declared
four or eight data bytes change. Flags and all data registers are retained.

The encoding includes a REX prefix. SIB, default stack-segment and unprefixed
forms, capability admission, surrounding bounds checks and complete consumer
composition retain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86DataStore
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

theorem memory_operand_rm (width : Nat) (value : BitVec 128) (pointer : Word) (prefixes : BitVec 52)
    (rexByte : BitVec 8) (rm : BitVec 3) :
    Functions.x86_operand_to_reg_mem .Mode_64bit width true false value 3 pointer prefixes rexByte rm (2#2) (0#8) =
      Functions.x86_operand_to_reg_mem .Mode_64bit width true false value 3 pointer prefixes rexByte (7#3) (2#2) (0#8) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((2#2) == (3#2)) = false from rfl,Bool.false_eq_true,ite_false,
    Functions.select_base_register]

theorem write_operand64_checked (state : State) (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer value : Word) (flags : BitVec 32) (rexByte : BitVec 8) (rm : BitVec 3)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48)) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rexByte rm (2#2) (0#8)).run state =
      .ok () (X86WriteWords.storeBytes 8 state dataAddress value) := by
  rw [memory_operand_rm]
  exact X86FrameIncrement.write_frame_checked state dataAddress prefixes attributes visible controls pointer value flags rexByte
    addressOverride upper segments application rip controlKnown flagsKnown visibleKnown safe

theorem write_operand64 (state : State) (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer value : Word) (flags : BitVec 32) (rexByte : BitVec 8) (rm : BitVec 3)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (aligned : dataAddress &&& (7#48) = (0#48)) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rexByte rm (2#2) (0#8)).run state =
      .ok () (X86WriteWords.storeBytes 8 state dataAddress value) := by
  exact write_operand64_checked state dataAddress prefixes attributes visible controls pointer value
    flags rexByte rm addressOverride upper segments application rip controlKnown flagsKnown visibleKnown
    (Or.inr aligned)

theorem handler64_checked (state : State) (source base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer baseValue value : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start displacementAddress prefixes
      (loadRex true source base) (0x89#8) (loadModRM source base) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) next) := by
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl,X86Move.operand_size64,run_bind,run_pure]
  dsimp only
  rw [X86QwordLoad.destination64,show Functions.bits_of_int 8 4 = (8#4) from rfl,
    run_bind,X86Move.read_register64 state source _ value sourceKnown]
  dsimp only
  rw [load_mod,load_rm]
  simp only [show ((2#2) == (3#2)) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,effective_memory state true source base noSib displacementAddress prefixes attributes pointer baseValue
    displacement addressOverride codeUpper segments application rip baseKnown codePresent]
  dsimp only
  rw [segment_data prefixes base noSib noStack segmentOverride addressOverride,run_bind,run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind,X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [show Int.toNat (8 : Int) = 8 from rfl,effective]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (loadRex true source base) (BitVec.ofNat 3 base.val) (2#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,write_operand64_checked state dataAddress prefixes attributes visible controls pointer value flags
    (loadRex true source base) (BitVec.ofNat 3 base.val) addressOverride dataUpper segments application rip
    controlKnown flagsKnown visibleKnown safe]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 8 state dataAddress value).registers_equal]
  exact quiet

theorem handler64 (state : State) (source base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer baseValue value : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start displacementAddress prefixes
      (loadRex true source base) (0x89#8) (loadModRM source base) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) next) := by
  exact handler64_checked state source base noSib noStack start displacementAddress next dataAddress
    prefixes attributes visible controls pointer baseValue value flags displacement segmentOverride
    addressOverride advance length codeUpper dataUpper segments application rip baseKnown sourceKnown
    controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) codePresent

theorem dispatch_store (other : OtherOpcodeHandlers) (wide : Bool) (source base : Fin 16)
    (start next : BitVec 48) :
    letI : OtherOpcodeHandlers := other
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x89#8))
      (loadRex wide source base) (0x89#8) (loadModRM source base) (0#8) =
      Functions.x86_mov_op_en_mr .Mode_64bit start next (X86LegacyFetch.packet (0x89#8))
        (loadRex wide source base) (0x89#8) (loadModRM source base) (0#8) := by
  rfl

theorem fetched64_checked (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt) (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex true source base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM source base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) finish) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x89#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x89#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes source base (loadModRM source base)
    (no_sib source base noSib) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [dispatch_store]
  apply handler64_checked state source base noSib noStack origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x89#8)) origin.attributes visible controls (origin.address.signExtend 64)
    baseValue value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) advance
  · apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact baseKnown
  · exact sourceKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact safe
  · exact codePresent

theorem fetched64 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt) (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex true source base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM source base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) finish) := by
  exact fetched64_checked other vector state source base noSib noStack origin finish dataAddress
    visible controls baseValue value flags displacement advance dataUpper baseKnown sourceKnown
    controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) prefixByte opcodeByte
    modrmByte codePresent

theorem read_register32 (state : State) (index : Fin 16) (value : Word) (rexByte : BitVec 8)
    (known : lookup state index = some value) :
    (Functions.rgfi_size (4#4) (BitVec.ofNat 4 index.val) rexByte).run state =
      .ok ((low32 value).zeroExtend 64) state := by
  unfold Functions.rgfi_size
  simp only [show Functions.eq_bits_nat (4#4) 1 = false from rfl,
    show Functions.eq_bits_nat (4#4) 2 = false from rfl,
    show Functions.eq_bits_nat (4#4) 4 = true from rfl,Bool.false_eq_true,ite_false,ite_true]
  unfold Functions.rr32
  have indexNat : Sail.BitVec.toNatInt (BitVec.ofNat 4 index.val) = index.val := by simp [Sail.BitVec.toNatInt]
  rw [indexNat]
  simp only [run_bind,rgfi_exact state index value known,run_pure]
  rfl

theorem widen32 (value : BitVec 32) : Sail.BitVec.zeroExtend (value.zeroExtend 64) 128 = value.zeroExtend 128 := by
  change (value.setWidth 64).setWidth 128 = value.setWidth 128
  exact BitVec.setWidth_setWidth (by decide)

theorem cut32 (value : BitVec 32) : Sail.BitVec.truncate (value.zeroExtend 128) 32 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [Sail.BitVec.truncate,within]

theorem store_dword_exact (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32) (alignment : Bool)
    (upper : base.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : alignment = false ∨ base &&& (3#48) = (0#48)) :
    (Functions.store_bytes_to_ea .Mode_64bit 8 4 (base.signExtend 64) baseRegister 3 value alignment false).run state =
      .ok () (X86WriteWords.storeBytes 4 state base value) := by
  unfold Functions.store_bytes_to_ea
  rw [run_bind,readRegister_exact,segments]
  dsimp only
  simp only [Functions.in_64bit_mode,Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false,pure_bind]
  rw [run_bind,X86ReadWords.data_linear_address]
  dsimp only
  rw [dword_access_check base baseRegister ":W" alignment safe]
  exact X86WriteWords.wb_exact 4 state base pointer value ":W" upper application rip

theorem write_operand32_checked (state : State) (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer : Word) (value : BitVec 32) (flags : BitVec 32) (rexByte : BitVec 8) (rm : BitVec 3)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48)) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rexByte rm (2#2) (0#8)).run state =
      .ok () (X86WriteWords.storeBytes 4 state dataAddress value) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((2#2) == (3#2)) = false from rfl,Bool.false_eq_true,ite_false,bind_assoc,pure_bind,Bool.true_and]
  rw [run_bind,X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressOverride]
  rw [size]
  simp only [pure_bind,Functions.select_base_register]
  unfold Functions.wme_size
  change (Functions.store_bytes_to_ea .Mode_64bit 8 4 (dataAddress.signExtend 64) none 3
    (Sail.BitVec.truncate (value.zeroExtend 128) 32)
    (X86FrameLoad.alignmentEnabled controls flags visible) false).run state = _
  rw [cut32]
  exact store_dword_exact state dataAddress none attributes pointer value
    (X86FrameLoad.alignmentEnabled controls flags visible) upper segments application rip safe

theorem write_operand32 (state : State) (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer : Word) (value : BitVec 32) (flags : BitVec 32) (rexByte : BitVec 8) (rm : BitVec 3)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (aligned : dataAddress &&& (3#48) = (0#48)) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rexByte rm (2#2) (0#8)).run state =
      .ok () (X86WriteWords.storeBytes 4 state dataAddress value) := by
  exact write_operand32_checked state dataAddress prefixes attributes visible controls pointer value
    flags rexByte rm addressOverride upper segments application rip controlKnown flagsKnown visibleKnown
    (Or.inr aligned)

theorem handler32_checked (state : State) (source base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer baseValue value : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start displacementAddress prefixes
      (loadRex false source base) (0x89#8) (loadModRM source base) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) next) := by
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl,operand_size32 source base prefixes operandOverride,run_bind,run_pure]
  dsimp only
  rw [load_destination,show Functions.bits_of_int 4 4 = (4#4) from rfl,
    run_bind,read_register32 state source value _ sourceKnown]
  dsimp only
  rw [load_mod,load_rm]
  simp only [show ((2#2) == (3#2)) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,effective_memory state false source base noSib displacementAddress prefixes attributes pointer baseValue
    displacement addressOverride codeUpper segments application rip baseKnown codePresent]
  dsimp only
  rw [segment_data prefixes base noSib noStack segmentOverride addressOverride,run_bind,run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind,X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [show Int.toNat (4 : Int) = 4 from rfl,effective]
  rw [widen32]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false ((low32 value).zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (loadRex false source base) (BitVec.ofNat 3 base.val) (2#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,write_operand32_checked state dataAddress prefixes attributes visible controls pointer (low32 value) flags
    (loadRex false source base) (BitVec.ofNat 3 base.val) addressOverride dataUpper segments application rip
    controlKnown flagsKnown visibleKnown safe]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 4 state dataAddress (low32 value)).registers_equal]
  exact quiet

theorem handler32 (state : State) (source base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer baseValue value : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start displacementAddress prefixes
      (loadRex false source base) (0x89#8) (loadModRM source base) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) next) := by
  exact handler32_checked state source base noSib noStack start displacementAddress next dataAddress
    prefixes attributes visible controls pointer baseValue value flags displacement segmentOverride
    addressOverride operandOverride advance length codeUpper dataUpper segments application rip
    baseKnown sourceKnown controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) codePresent

theorem fetched32_checked (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt) (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex false source base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM source base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) finish) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x89#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x89#8) shape false state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes source base (loadModRM source base)
    (no_sib source base noSib) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [dispatch_store]
  apply handler32_checked state source base noSib noStack origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x89#8)) origin.attributes visible controls (origin.address.signExtend 64)
    baseValue value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _) advance
  · apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact baseKnown
  · exact sourceKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact safe
  · exact codePresent

theorem fetched32 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt) (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex false source base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM source base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) finish) := by
  exact fetched32_checked other vector state source base noSib noStack origin finish dataAddress
    visible controls baseValue value flags displacement advance dataUpper baseKnown sourceKnown
    controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) prefixByte opcodeByte
    modrmByte codePresent

def byteCount (wide : Bool) : Nat := if wide then 8 else 4

def payload : (wide : Bool) → Word → BitVec (8 * byteCount wide)
  | true,value => value
  | false,value => low32 value

def code (wide : Bool) (source base : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(loadRex wide source base).toNat,0x89,(loadModRM source base).toNat] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

theorem code_length (wide : Bool) (source base : Fin 16) (displacement : BitVec 32) :
    (code wide source base displacement).length = 7 := by simp [code]

def result (wide : Bool) (state : State) (dataAddress next : BitVec 48) (value : Word) : State :=
  X86Move.putPointer (X86WriteWords.storeBytes (byteCount wide) state dataAddress (payload wide value)) next

def writes (wide : Bool) (dataAddress : BitVec 48) : Finset Nat :=
  X86WriteWords.written dataAddress (List.range (byteCount wide))

theorem result_frame (wide : Bool) (state : State) (dataAddress next : BitVec 48) (value : Word) :
    X86StateFrame.Frame {.rip} (writes wide dataAddress) state (result wide state dataAddress next value) := by
  exact ((X86WriteWords.storeBytes_frame (byteCount wide) state dataAddress (payload wide value)).trans
    (X86StateFrame.registerOnly (pointer_frame _ next))).mono (by simp) (by simp [writes])

structure Inputs (state : State) (wide : Bool) (source base : Fin 16) (displacement : BitVec 32)
    extends X86LegacyFetch.Basis state where
  noSib : base.val % 8 ≠ 4
  noStack : base.val % 8 ≠ 5
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  baseValue : Word
  value : Word
  flags : BitVec 32
  dataAddress : BitVec 48
  baseKnown : lookup state base = some baseValue
  sourceKnown : lookup state source = some value
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 7 < (2 ^ 47 : Int)
  dataUpper : dataAddress.toInt + byteCount wide ≤ (2 ^ 47 : Int)
  effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64
  aligned : dataAddress &&& BitVec.ofNat 48 (byteCount wide - 1) = (0#48)
  loaded : codeLoaded state address.toInt (code wide source base displacement)

structure CheckedInputs (state : State) (wide : Bool) (source base : Fin 16) (displacement : BitVec 32)
    extends X86LegacyFetch.Basis state where
  noSib : base.val % 8 ≠ 4
  noStack : base.val % 8 ≠ 5
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  baseValue : Word
  value : Word
  flags : BitVec 32
  dataAddress : BitVec 48
  baseKnown : lookup state base = some baseValue
  sourceKnown : lookup state source = some value
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 7 < (2 ^ 47 : Int)
  dataUpper : dataAddress.toInt + byteCount wide ≤ (2 ^ 47 : Int)
  effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64
  safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨
    dataAddress &&& BitVec.ofNat 48 (byteCount wide - 1) = (0#48)
  loaded : codeLoaded state address.toInt (code wide source base displacement)

theorem executes_checked (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (wide : Bool) (source base : Fin 16) (displacement : BitVec 32)
    (input : CheckedInputs state wide source base displacement) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run state =
        .ok () (result wide state input.dataAddress (address input.address.toInt 7) input.value) ∧
      X86StateFrame.Frame {.rip} (writes wide input.dataAddress) state
        (result wide state input.dataAddress (address input.address.toInt 7) input.value) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  let site := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let finish := address input.address.toInt 7
  have at3 : site.next.toInt = input.address.toInt + 3 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 3 (by decide)
  have at7 : finish.toInt = input.address.toInt + 7 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 7 (by decide)
  have present : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8) := by
    intro index within
    rw [at3]
    have shift : address (input.address.toInt + 3) index = address input.address.toInt (3 + index) := by
      simp [address,Int.add_assoc]
    rw [shift]
    have byte : (code wide source base displacement)[3 + index]? =
        some (displacement.extractLsb' (8 * index) 8).toNat := by interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.loaded _ _ byte
  have prefixByte : state.mem.get? (site.address.signExtend 52).toNat = some (loadRex wide source base) := by
    simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 0 (loadRex wide source base).toNat (by simp [code])
  have opcodeByte := input.loaded 1 0x89 (by simp [code])
  have modrmByte : state.mem.get? (site.modrmAddress.signExtend 52).toNat = some (loadModRM source base) := by
    simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 2 (loadModRM source base).toNat (by simp [code])
  have run : (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (result wide state input.dataAddress finish input.value) := by
    cases wide with
    | true =>
        exact fetched64_checked other vector state source base input.noSib input.noStack site finish input.dataAddress
          input.visible input.controls input.baseValue input.value input.flags displacement (by omega) input.dataUpper
          input.baseKnown input.sourceKnown input.controlKnown input.flagsKnown input.visibleKnown input.quiet
          input.effective input.safe prefixByte opcodeByte modrmByte present
    | false =>
        exact fetched32_checked other vector state source base input.noSib input.noStack site finish input.dataAddress
          input.visible input.controls input.baseValue input.value input.flags displacement (by omega) input.dataUpper
          input.baseKnown input.sourceKnown input.controlKnown input.flagsKnown input.visibleKnown input.quiet
          input.effective input.safe prefixByte opcodeByte modrmByte present
  exact ⟨X86FuelPrefix.fetches_one state _ run,result_frame wide state input.dataAddress finish input.value⟩

def Inputs.checked {state : State} {wide : Bool} {source base : Fin 16} {displacement : BitVec 32}
    (input : Inputs state wide source base displacement) : CheckedInputs state wide source base displacement :=
  { input with safe := Or.inr input.aligned }

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (wide : Bool) (source base : Fin 16) (displacement : BitVec 32)
    (input : Inputs state wide source base displacement) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run state =
        .ok () (result wide state input.dataAddress (address input.address.toInt 7) input.value) ∧
      X86StateFrame.Frame {.rip} (writes wide input.dataAddress) state
        (result wide state input.dataAddress (address input.address.toInt 7) input.value) := by
  exact executes_checked other vector state wide source base displacement input.checked

theorem store_dword_byte (state : State) (base : BitVec 48) (value : BitVec 32)
    (upper : base.toInt + 4 ≤ (2 ^ 47 : Int)) (offset : Nat) (within : offset < 4) :
    (X86WriteWords.storeBytes 4 state base value).mem.get? (X86WriteWords.physicalAddress base offset) =
      some (value.extractLsb' (8 * offset) 8) := by
  have sameKey (left right : Nat) (leftWithin : left < 4) (rightWithin : right < 4) :
      X86WriteWords.physicalAddress base left = X86WriteWords.physicalAddress base right ↔ left = right :=
    ⟨X86WriteWords.physicalAddress_injective 4 base upper left right leftWithin rightWithin,by rintro rfl; rfl⟩
  interval_cases offset <;>
    simp [X86WriteWords.storeBytes,List.range_succ,X86WriteWords.putByte,Std.ExtHashMap.getElem_insert,sameKey]

theorem byte_readback (state : State) (wide : Bool) (dataAddress next : BitVec 48) (value : Word)
    (upper : dataAddress.toInt + byteCount wide ≤ (2 ^ 47 : Int)) (offset : Nat) (within : offset < byteCount wide) :
    (result wide state dataAddress next value).mem.get? (X86WriteWords.physicalAddress dataAddress offset) =
      some ((payload wide value).extractLsb' (8 * offset) 8) := by
  cases wide with
  | true => exact X86WriteWords.store_word_byte state dataAddress value upper offset within
  | false => exact store_dword_byte state dataAddress (low32 value) upper offset within

theorem code_preserved (state : State) (wide : Bool) (dataAddress next : BitVec 48) (value : Word)
    (base : Int) (bytes : List Nat) (loaded : codeLoaded state base bytes)
    (apart : ∀ index byte, bytes[index]? = some byte →
      ((address base index).signExtend 52).toNat ∉ writes wide dataAddress) :
    codeLoaded (result wide state dataAddress next value) base bytes :=
  (result_frame wide state dataAddress next value).codeLoaded base bytes loaded apart

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0

private def cells (wide : Bool) (displacement : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 7).map (fun offset => (4096 + offset,BitVec.ofNat 8 (((code wide 10 2 displacement)[offset]?).getD 0))) ++
    ((List.range 12).map (fun offset => (12304 + offset,0xa5#8)) ++ [(12303,0x5a#8)])

private theorem distinct (wide : Bool) (displacement : BitVec 32) :
    (cells wide displacement).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells wide displacement).map Prod.fst).Nodup := by
    simp only [cells,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil]
    decide
  simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map,beq_eq_false_iff_ne] using keys

private noncomputable def before (wide : Bool) (displacement : BitVec 32) (baseValue value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdx baseValue
  let registers := registers.insert .r10 value
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells wide displacement),(),0,#[]⟩

private theorem cell (wide : Bool) (displacement : BitVec 32) (baseValue value : Word)
    (key : Nat) (byte : BitVec 8) (member : (key,byte) ∈ cells wide displacement) :
    (before wide displacement baseValue value).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct wide displacement) member

private theorem code_point : ∀ index : Fin 7,
    ((address 4096 index.val).signExtend 52).toNat = 4096 + index.val := by decide

private noncomputable def input (wide : Bool) (displacement : BitVec 32) (baseValue value : Word)
    (effective : baseValue + displacement.signExtend 64 = (12304#48).signExtend 64) :
    Inputs (before wide displacement baseValue value) wide 10 2 displacement where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
  noSib := by decide
  noStack := by decide
  visible := visible
  controls := controls
  baseValue := baseValue
  value := value
  flags := 0x246#32
  dataAddress := 12304#48
  baseKnown := by
    change ((before wide displacement baseValue value).regs.get? .rdx).map (fun word : Word => word) = _
    simp [before,Std.ExtDHashMap.get?_insert]
  sourceKnown := by
    change ((before wide displacement baseValue value).regs.get? .r10).map (fun word : Word => word) = _
    simp [before,Std.ExtDHashMap.get?_insert]
  controlKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  dataUpper := by cases wide <;> decide
  effective := effective
  aligned := by cases wide <;> decide
  loaded := by
    change codeLoaded (before wide displacement baseValue value) 4096 (code wide 10 2 displacement)
    intro index byte present
    have within : index < 7 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
    rw [code_point ⟨index,within⟩]
    apply cell
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩

private theorem written_lower (wide : Bool) (key : Nat) (member : key ∈ writes wide (12304#48)) : 12304 ≤ key := by
  obtain ⟨offset,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have small : byteCount wide ≤ 8 := by cases wide <;> decide
  have bounded : offset < 8 := by have := List.mem_range.mp within; omega
  have point : ∀ index : Fin 8, X86WriteWords.physicalAddress (12304#48) index.val = 12304 + index.val := by decide
  rw [← same,point ⟨offset,bounded⟩]
  omega

private theorem outside (wide : Bool) (key : Nat) (below : key < 12304) : key ∉ writes wide (12304#48) := by
  intro member
  have := written_lower wide key member
  omega

theorem control (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (wide : Bool) (displacement : BitVec 32) (baseValue value : Word)
    (effective : baseValue + displacement.signExtend 64 = (12304#48).signExtend 64) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run (before wide displacement baseValue value) =
        .ok () (result wide (before wide displacement baseValue value) (12304#48) (4103#48) value) ∧
      X86StateFrame.Frame {.rip} (writes wide (12304#48)) (before wide displacement baseValue value)
        (result wide (before wide displacement baseValue value) (12304#48) (4103#48) value) ∧
      codeLoaded (result wide (before wide displacement baseValue value) (12304#48) (4103#48) value)
        4096 (code wide 10 2 displacement) := by
  have proved := executes other vector (before wide displacement baseValue value) wide 10 2 displacement
    (input wide displacement baseValue value effective)
  change (X86FuelPrefix.fetches 1).run (before wide displacement baseValue value) =
      .ok () (result wide (before wide displacement baseValue value) (12304#48) (4103#48) value) ∧
    X86StateFrame.Frame {.rip} (writes wide (12304#48)) (before wide displacement baseValue value)
      (result wide (before wide displacement baseValue value) (12304#48) (4103#48) value) at proved
  refine ⟨proved.1,proved.2,code_preserved _ _ _ _ _ _ _ (input wide displacement baseValue value effective).loaded ?_⟩
  intro index byte present
  have within : index < 7 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
  rw [code_point ⟨index,within⟩]
  exact outside wide _ (by omega)

theorem dword_writes_only_low (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before false (16#32) (12288#64) (0x1234567889abcdef#64)) = .ok () after ∧
      after.mem.get? 12304 = some (0xef#8) ∧ after.mem.get? 12307 = some (0x89#8) ∧
      after.mem.get? 12308 = some (0xa5#8) ∧ after.mem.get? 12303 = some (0x5a#8) ∧
      after.regs.get? .r10 = some (0x1234567889abcdef#64) ∧ after.regs.get? .rflags = some (0x246#32) ∧
      after.regs.get? .rsp = some (16384#64) := by
  obtain ⟨run,frame,_⟩ := control other vector false (16#32) (12288#64) (0x1234567889abcdef#64) (by decide)
  refine ⟨_,run,?_,?_,?_,?_,?_,?_,?_⟩
  · exact byte_readback _ false _ _ _ (by decide) 0 (by decide)
  · exact byte_readback _ false _ _ _ (by decide) 3 (by decide)
  · rw [frame.memory 12308 (by decide)]
    apply cell
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨4,by decide,rfl⟩
  · rw [frame.memory 12303 (by decide)]
    apply cell
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_singleton_self _
  · rw [frame.registers .r10 (by decide)]
    simp [before,Std.ExtDHashMap.get?_insert]
  · rw [frame.registers .rflags (by decide)]
    simp [before,Std.ExtDHashMap.get?_insert]
  · rw [frame.registers .rsp (by decide)]
    simp [before,Std.ExtDHashMap.get?_insert]

theorem qword_writes_high (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before true (16#32) (12288#64) (0x1234567889abcdef#64)) = .ok () after ∧
      after.mem.get? 12308 = some (0x78#8) ∧ after.mem.get? 12311 = some (0x12#8) ∧
      after.mem.get? 12312 = some (0xa5#8) := by
  obtain ⟨run,frame,_⟩ := control other vector true (16#32) (12288#64) (0x1234567889abcdef#64) (by decide)
  refine ⟨_,run,?_,?_,?_⟩
  · exact byte_readback _ true _ _ _ (by decide) 4 (by decide)
  · exact byte_readback _ true _ _ _ (by decide) 7 (by decide)
  · rw [frame.memory 12312 (by decide)]
    apply cell
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨8,by decide,rfl⟩

theorem negative_displacement (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before true (0xfffffff0#32) (12320#64) (0x1234567889abcdef#64)) = .ok () after ∧
      after.mem.get? 12308 = some (0x78#8) ∧ after.mem.get? 12311 = some (0x12#8) := by
  obtain ⟨run,_,_⟩ := control other vector true (0xfffffff0#32) (12320#64) (0x1234567889abcdef#64) (by decide)
  exact ⟨_,run,byte_readback _ true _ _ _ (by decide) 4 (by decide),
    byte_readback _ true _ _ _ (by decide) 7 (by decide)⟩

private noncomputable def changedWidth : State :=
  { before false (16#32) (12288#64) (0x1234567889abcdef#64) with
    mem := (before false (16#32) (12288#64) (0x1234567889abcdef#64)).mem.insert 4096 (0x4c#8) }

theorem changed_width_rejected : ¬ codeLoaded changedWidth 4096 (code false 10 2 (16#32)) := by
  intro loaded
  have wrong := loaded 0 0x44 (by rfl)
  simp [changedWidth,address] at wrong

end Controls

#print axioms executes
#print axioms byte_readback
#print axioms handler32
#print axioms fetched32
#print axioms handler64
#print axioms fetched64

end Mettapedia.Machines.TIsa.X86DataStore
