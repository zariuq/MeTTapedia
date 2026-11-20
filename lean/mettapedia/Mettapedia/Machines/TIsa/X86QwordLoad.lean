import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86FuelPrefix

/-!
# Fetched 64-bit no-SIB memory loads

The original MOV handler computes the signed displacement, selects the data
segment, checks alignment, reads eight bytes, writes the full destination and
advances RIP. The seven-byte fetch proof derives the original decoder inputs
from loaded bytes and canonical geometry. Only destination and RIP may change.

The general contract covers the no-SIB data-segment form, with base low bits
neither four nor five. The concrete control is the consumer's R10/RSI+16 form;
arbitrary full-word values retain their high bits, including 2^32 whose low
dword is zero. It preserves memory, flags, source pointer and stack, and a
changed destination invalidates the byte certificate.

This instruction contract does not assume the caller's capability-bounds
validation. That surrounding span, source access relation, consumer and ABI
remain separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86QwordLoad
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

theorem destination64 : ∀ destination base : Fin 16,
    Functions.reg_index (Functions._get_modr_m_reg (loadModRM destination base))
      (loadRex true destination base) (2#2) = BitVec.ofNat 4 destination.val := by decide

theorem cut128 (value : Word) : Sail.BitVec.truncate (value.zeroExtend 128) 64 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [Sail.BitVec.truncate,within]

theorem operand_qword_checked (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4)
    (displacementAddress dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3 prefixes
      displacementAddress (loadRex true destination base) (BitVec.ofNat 3 base.val) (2#2) (0#8) (0#3)).run state =
      .ok (value.zeroExtend 128,(4 : Int),dataAddress.signExtend 64) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((2#2) == (3#2)) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,effective_memory state true destination base noSib displacementAddress prefixes attributes
    pointer baseValue displacement addressOverride codeUpper segments application rip baseKnown codePresent]
  dsimp only
  rw [effective]
  simp only [bind_assoc,pure_bind,Bool.true_and]
  rw [run_bind,X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressOverride]
  rw [size]
  simp only [pure_bind,Functions.select_base_register,show Int.toNat (8 : Int) = 8 from rfl]
  unfold Functions.rme_size
  rw [run_bind,run_bind,X86ReadWords.load_word_exact state dataAddress none attributes pointer value ":R"
    (X86FrameLoad.alignmentEnabled controls flags visible) false dataUpper segments application rip safe dataPresent]
  rfl

theorem operand_qword (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4)
    (displacementAddress dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3 prefixes
      displacementAddress (loadRex true destination base) (BitVec.ofNat 3 base.val) (2#2) (0#8) (0#3)).run state =
      .ok (value.zeroExtend 128,(4 : Int),dataAddress.signExtend 64) state := by
  exact operand_qword_checked state destination base noSib displacementAddress dataAddress prefixes
    attributes visible controls pointer baseValue value flags displacement addressOverride codeUpper
    dataUpper segments application rip baseKnown controlKnown flagsKnown visibleKnown effective
    (Or.inr aligned) codePresent dataPresent

theorem write_destination64 (state : State) (destination base : Fin 16) (value : Word)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value (loadRex true destination base)).run state =
      .ok () (put state destination value) := by
  have bound : destination.val < 2 ^ 4 := destination.isLt
  simpa [Functions.write_rgfi_size,Functions.eq_bits_nat,Functions.wr64,Sail.BitVec.toNatInt,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] using write_rgfi_exact state destination value quiet

theorem handler_qword_checked (state : State) (destination base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress prefixes (loadRex true destination base)
      (0x8b#8) (loadModRM destination base) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  have size : Functions.select_operand_size .Mode_64bit false (loadRex true destination base) false prefixes
      false false false = (pure 8 : SailM Int) := X86Move.operand_size64 destination base prefixes
  unfold Functions.x86_mov_op_en_rm
  dsimp only
  rw [show ((0x8b#8) == (0x8a#8)) = false from rfl,size,run_bind,run_pure]
  dsimp only
  rw [load_mod,load_rm,segment_data prefixes base noSib noStack segmentOverride addressOverride,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,run_bind,
    operand_qword_checked state destination base noSib displacementAddress dataAddress prefixes attributes visible controls
      pointer baseValue value flags displacement addressOverride codeUpper dataUpper segments application rip baseKnown
      controlKnown flagsKnown visibleKnown effective safe codePresent dataPresent]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,run_bind,
    X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length,if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl,destination64,X86QwordLoad.cut128]
  rw [run_bind,write_destination64 state destination base value quiet]
  exact X86Move.write_pointer64 _ next (by simpa only [diagnostic_put] using quiet)

theorem handler_qword (state : State) (destination base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress prefixes (loadRex true destination base)
      (0x8b#8) (loadModRM destination base) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  exact handler_qword_checked state destination base noSib noStack start displacementAddress next
    dataAddress prefixes attributes visible controls pointer baseValue value flags displacement
    segmentOverride addressOverride advance length codeUpper dataUpper segments application rip
    baseKnown controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) codePresent dataPresent

theorem fetched_qword_checked (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex true destination base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM destination base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) finish) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x8b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x8b#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes destination base (loadModRM destination base)
    (no_sib destination base noSib) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [dispatch_load other (loadRex true destination base) (loadModRM destination base)]
  apply handler_qword_checked state destination base noSib noStack origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x8b#8)) origin.attributes visible controls (origin.address.signExtend 64)
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
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact safe
  · exact codePresent
  · exact dataPresent

theorem fetched_qword (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex true destination base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM destination base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) finish) := by
  exact fetched_qword_checked other vector state destination base noSib noStack origin finish
    dataAddress visible controls baseValue value flags displacement advance dataUpper baseKnown
    controlKnown flagsKnown visibleKnown quiet effective (Or.inr aligned) prefixByte opcodeByte
    modrmByte codePresent dataPresent

theorem result_frame (state : State) (destination : Fin 16) (value : Word) (finish : BitVec 48) :
    RegisterFrame {key destination,.rip} state (X86Move.putPointer (put state destination value) finish) :=
  ((put_frame state destination value).trans (pointer_frame _ finish)).mono (by simp)

def code (destination base : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(loadRex true destination base).toNat,0x8b,(loadModRM destination base).toNat] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

theorem code_length (destination base : Fin 16) (displacement : BitVec 32) :
    (code destination base displacement).length = 7 := by simp [code]

structure Inputs (state : State) (destination base : Fin 16) (displacement : BitVec 32)
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
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 7 < (2 ^ 47 : Int)
  dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64
  aligned : dataAddress &&& (7#48) = (0#48)
  loaded : codeLoaded state address.toInt (code destination base displacement)
  dataPresent : ∀ index < 8,
    state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination base : Fin 16) (displacement : BitVec 32)
    (input : Inputs state destination base displacement) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination,.rip} state after ∧ lookup after destination = some input.value ∧
      after.regs.get? .rip = some ((address input.address.toInt 7).signExtend 64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
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
    have byte : (code destination base displacement)[3 + index]? =
        some (displacement.extractLsb' (8 * index) 8).toNat := by interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.loaded _ _ byte
  have run := fetched_qword other vector state destination base input.noSib input.noStack site finish input.dataAddress
    input.visible input.controls input.baseValue input.value input.flags displacement (by omega)
    input.dataUpper input.baseKnown input.controlKnown input.flagsKnown input.visibleKnown input.quiet input.effective input.aligned
    (by simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 0 (loadRex true destination base).toNat (by simp [code]))
    (input.loaded 1 0x8b (by simp [code]))
    (by simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 2 (loadModRM destination base).toNat (by simp [code])) present input.dataPresent
  let after := X86Move.putPointer (put state destination input.value) finish
  refine ⟨after,X86FuelPrefix.fetches_one state after run,result_frame _ _ _ _,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    rfl

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0

private def cells (value : Word) : List (Nat × BitVec 8) :=
  (List.range 7).map (fun offset => (4096 + offset,BitVec.ofNat 8 (((code 10 6 (16#32))[offset]?).getD 0))) ++
    ((List.range 8).map (fun offset => (12304 + offset,value.extractLsb' (8 * offset) 8)) ++ [(8192,42#8)])

private theorem distinct (value : Word) :
    (cells value).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells value).map Prod.fst).Nodup := by
    simp only [cells,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil]
    decide
  simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map,beq_eq_false_iff_ne] using keys
private theorem code_point : ∀ offset : Fin 7,
    ((address 4096 offset.val).signExtend 52).toNat = 4096 + offset.val := by decide
private theorem data_point : ∀ offset : Fin 8,
    ((address 12304 offset.val).signExtend 52).toNat = 12304 + offset.val := by decide

private noncomputable def before (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rsi (12288#64)
  let registers := registers.insert .r10 (0xdeadbeefcafebabe#64)
  let registers := registers.insert .rsp (16384#64)
  ⟨registers,(),Std.ExtHashMap.ofList (cells value),(),0,#[]⟩

private theorem cell (value : Word) (key : Nat) (byte : BitVec 8) (member : (key,byte) ∈ cells value) :
    (before value).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct value) member

private def input (value : Word) : Inputs (before value) 10 6 (16#32) where
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
  baseValue := 12288#64
  value := value
  flags := 0x246#32
  dataAddress := 12304#48
  baseKnown := by simp [lookup,before,key,Std.ExtDHashMap.get?_insert]; rfl
  controlKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before,Std.ExtDHashMap.get?_insert]
  upper := by decide
  dataUpper := by decide
  effective := by decide
  aligned := by decide
  loaded := by
    change codeLoaded (before value) 4096 (code 10 6 (16#32))
    intro offset byte present
    have within : offset < 7 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
    rw [code_point ⟨offset,within⟩]
    apply cell value
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
  dataPresent := by
    intro offset within
    change (before value).mem.get? ((address 12304 offset).signExtend 52).toNat =
      some (value.extractLsb' (8 * offset) 8)
    rw [data_point ⟨offset,within⟩]
    apply cell value
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨offset,List.mem_range.mpr within,rfl⟩

theorem full_word (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before value) = .ok () after ∧
      lookup after 10 = some value ∧ after.mem = (before value).mem ∧
      after.regs.get? .rflags = some (0x246#32) ∧ after.regs.get? .rip = some (4103#64) ∧
      lookup after 6 = some (12288#64) ∧ after.regs.get? .rsp = some (16384#64) := by
  obtain ⟨after,run,frame,result,rip⟩ := executes other vector (before value) 10 6 (16#32) (input value)
  refine ⟨after,run,result,frame.memory,?_,rip,?_,?_⟩
  · rw [frame.registers .rflags (by decide)]
    simp [before,Std.ExtDHashMap.get?_insert]
  · rw [frame.lookup 6 (by decide)]
    simp [lookup,before,key,Std.ExtDHashMap.get?_insert]
    rfl
  · rw [frame.registers .rsp (by decide)]
    simp [before]

theorem high_word_not_truncated (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before (0x100000000#64)) = .ok () after ∧
      lookup after 10 = some (0x100000000#64) ∧ lookup after 10 ≠ some (0#64) := by
  obtain ⟨after,run,result,_⟩ := full_word other vector (0x100000000#64)
  exact ⟨after,run,result,by rw [result]; decide⟩

private noncomputable def changed : State :=
  { before 0 with mem := (before 0).mem.insert 4098 (0x9e#8) }

theorem changed_destination_rejected : ¬codeLoaded changed 4096 (code 10 6 (16#32)) := by
  intro loaded
  have wrong := loaded 2 0x96 (by decide)
  simp [changed,address] at wrong

example : code 10 6 (16#32) = [0x4c,0x8b,0x96,16,0,0,0] := by decide

end Controls
end Mettapedia.Machines.TIsa.X86QwordLoad

#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.handler_qword
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.fetched_qword
#print axioms Mettapedia.Machines.TIsa.X86QwordLoad.result_frame
