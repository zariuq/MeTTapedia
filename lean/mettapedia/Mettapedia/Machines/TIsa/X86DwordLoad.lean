import Mettapedia.Machines.TIsa.X86FrameLoad

/-!
# Fetched 32-bit no-SIB memory loads in the original Sail model

The original MOV memory-to-register handler computes its signed displacement,
checks the selected segment and alignment, reads four individual bytes,
zero-extends the result into the destination and advances RIP. The theorem
covers ordinary data-segment bases with a disp32 ModRM form; SIB and default
stack-segment forms retain separate obligations.

The full fetch theorem reads the actual REX/opcode/ModRM/displacement bytes
and assumes no handler execution or compiler correctness. Controls distinguish
zero from sign extension and execute a changed destination byte. Bounds-check
prefixes, complete images and ABI composition remain separate joins.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86DwordLoad

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
local instance : MemoryPrimitives := X86Memory.ordinary

theorem dword_alignment (base : BitVec 48) :
    Functions.address_aligned_p base 4 false =
      (pure ((base &&& (3#48)) == (0#48)) : SailM Bool) := by
  unfold Functions.address_aligned_p
  have mask : Functions.check_range 0 65 3 = (pure 3 : SailM Int) := rfl
  change (do let mask ← Functions.check_range 0 65 3
             pure ((base &&& Functions.bits_of_int mask 48) == (0#48))) = _
  rw [mask, pure_bind]
  rfl

theorem dword_access_check (base : BitVec 48) (baseRegister : Option Nat) (access : String)
    (checkAlignment : Bool) (safe : checkAlignment = false ∨ base &&& (3#48) = (0#48)) :
    Functions.check_linear_memory_access .Mode_64bit 8 4 (base.signExtend 64)
      baseRegister 3 access checkAlignment false = (pure () : SailM Unit) := by
  unfold Functions.check_linear_memory_access
  rw [X86ReadWords.truncate48, dword_alignment]
  simp only [pure_bind]
  rcases safe with disabled | aligned
  · subst checkAlignment
    rfl
  · simp only [aligned, beq_self_eq_true, Bool.or_true, Bool.not_true, Bool.false_eq_true, ite_false]

theorem load_dword_exact (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32) (access : String)
    (checkAlignment : Bool) (upper : base.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : checkAlignment = false ∨ base &&& (3#48) = (0#48))
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 4 (base.signExtend 64) baseRegister 3 access
      checkAlignment false).run state = .ok value state := by
  unfold Functions.load_bytes_from_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  change (do
    let linear ← Functions.ea_to_la .Mode_64bit (base.signExtend 64) 3 4
    Functions.check_linear_memory_access .Mode_64bit 8 4 linear baseRegister 3 access checkAlignment false
    Functions.rb 4 linear access : SailM (BitVec 32)).run state = _
  rw [run_bind, X86ReadWords.data_linear_address]
  dsimp only
  rw [dword_access_check base baseRegister access checkAlignment safe]
  exact X86ReadWords.rb_dword_exact state base pointer value access upper application rip present

abbrev loadRex (wide : Bool) (destination base : Fin 16) : BitVec 8 := rex wide destination base
def loadModRM (destination base : Fin 16) : BitVec 8 :=
  BitVec.ofNat 8 (128 + (destination.val % 8) * 8 + base.val % 8)

theorem load_mod : ∀ destination base : Fin 16,
    Functions._get_modr_m_mod (loadModRM destination base) = (2#2) := by decide
theorem load_rm : ∀ destination base : Fin 16,
    Functions._get_modr_m_r_m (loadModRM destination base) = BitVec.ofNat 3 base.val := by decide
theorem load_base : ∀ wide : Bool, ∀ destination base : Fin 16,
    Functions.reg_index (BitVec.ofNat 3 base.val) (loadRex wide destination base) (0#2) =
      BitVec.ofNat 4 base.val := by decide

theorem load_rex32 : ∀ destination base : Fin 16,
    Functions.logbitp_bits 3 (loadRex false destination base) = false := by decide

theorem operand_size32 (destination base : Fin 16) (prefixes : BitVec 52)
    (ordinary : Functions._get_prefixes_opr prefixes = (0#8)) :
    Functions.select_operand_size .Mode_64bit false (loadRex false destination base)
      false prefixes false false false = (pure 4 : SailM Int) := by
  simp [Functions.select_operand_size, Functions.in_64bit_mode, load_rex32, ordinary]

theorem effective_disp32 (state : State) (wide : Bool) (destination base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (displacementAddress : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer baseValue : Word) (displacement : BitVec 32)
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr_32_64 .Mode_64bit false displacementAddress (loadRex wide destination base)
      (BitVec.ofNat 3 base.val) (2#2) (0#8) (0#3)).run state =
      .ok (baseValue + displacement.signExtend 64, (4 : Int)) state := by
  have noSibBits : Functions.eq_bits_nat (BitVec.ofNat 3 base.val) 4 = false := by
    simp [Functions.eq_bits_nat, Sail.BitVec.toNatInt]
    omega
  unfold Functions.x86_effective_addr_32_64
  simp only [show Functions.eq_bits_nat (2#2) 0 = false from rfl,
    show Functions.eq_bits_nat (2#2) 1 = false from rfl,
    show Functions.eq_bits_nat (2#2) 2 = true from rfl, noSibBits,
    Bool.false_eq_true, ite_false, ite_true]
  rw [show Functions.select_address_size .Mode_64bit none = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, bind_assoc, Sail.BitVec.signExtend, show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind, X86ReadWords.signed_displacement_exact state displacementAddress attributes pointer displacement
    upper segments application rip present]
  dsimp only
  simp only [Functions.in_64bit_mode, ite_true]
  rw [load_base]
  have baseIndex : Sail.BitVec.toNatInt (BitVec.ofNat 4 base.val) = base.val := by
    simp [Sail.BitVec.toNatInt]
  rw [baseIndex]
  have readBase : (Functions.rgfi base.val).run state = .ok baseValue state :=
    rgfi_exact state base baseValue baseKnown
  rw [run_bind, readBase]
  dsimp only
  rw [X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

theorem effective_memory (state : State) (wide : Bool) (destination base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (displacementAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6)
    (pointer baseValue : Word) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr .Mode_64bit prefixes displacementAddress (loadRex wide destination base)
      (BitVec.ofNat 3 base.val) (2#2) (0#8) (0#3)).run state =
      .ok (baseValue + displacement.signExtend 64, (4 : Int)) state := by
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  unfold Functions.x86_effective_addr
  rw [size]
  simp only [pure_bind, addressOverride]
  exact effective_disp32 state wide destination base noSib displacementAddress attributes pointer baseValue
    displacement upper segments application rip baseKnown present

theorem operand_dword (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4)
    (displacementAddress dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue : Word) (value : BitVec 32) (flags : BitVec 32) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 4 true false 3 prefixes
      displacementAddress (loadRex false destination base) (BitVec.ofNat 3 base.val) (2#2) (0#8) (0#3)).run state =
      .ok (value.zeroExtend 128, (4 : Int), dataAddress.signExtend 64) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, effective_memory state false destination base noSib displacementAddress prefixes attributes
    pointer baseValue displacement addressOverride codeUpper segments application rip baseKnown codePresent]
  dsimp only
  rw [effective]
  simp only [bind_assoc, pure_bind, Bool.true_and]
  rw [run_bind, X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [size]
  simp only [pure_bind, Functions.select_base_register, show Int.toNat (8 : Int) = 8 from rfl]
  unfold Functions.rme_size
  rw [run_bind, run_bind, load_dword_exact state dataAddress none attributes pointer value ":R"
    (X86FrameLoad.alignmentEnabled controls flags visible) dataUpper segments application rip (Or.inr aligned) dataPresent]
  rfl

theorem cut32 (value : BitVec 32) :
    Sail.BitVec.truncate (value.zeroExtend 64) 32 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [Sail.BitVec.truncate, within]

theorem cut128 (value : BitVec 32) :
    Sail.BitVec.truncate (value.zeroExtend 128) 64 = value.zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  by_cases low : index < 32 <;> simp [Sail.BitVec.truncate, within, low]

theorem write_destination32 (state : State) (destination base : Fin 16) (value : BitVec 32)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (4#4) (BitVec.ofNat 4 destination.val) (value.zeroExtend 64)
      (loadRex false destination base)).run state = .ok () (put state destination (value.zeroExtend 64)) := by
  simp only [Functions.write_rgfi_size, Functions.eq_bits_nat]
  change (Functions.wr32 (BitVec.ofNat 4 destination.val) (Sail.BitVec.truncate (value.zeroExtend 64) 32)).run state = _
  rw [cut32]
  simpa [Functions.wr32, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt] using
    write_rgfi_exact state destination (value.zeroExtend 64) quiet

theorem load_destination : ∀ destination base : Fin 16,
    Functions.reg_index (Functions._get_modr_m_reg (loadModRM destination base))
      (loadRex false destination base) (2#2) = BitVec.ofNat 4 destination.val := by decide

theorem not_stack_bits : ∀ base : Fin 16, base.val % 8 ≠ 5 →
    ((BitVec.ofNat 3 base.val) == (5#3)) = false := by decide

theorem not_sib_bits : ∀ base : Fin 16, base.val % 8 ≠ 4 →
    ((BitVec.ofNat 3 base.val) == (4#3)) = false := by decide

theorem segment_data (prefixes : BitVec 52) (base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8)) :
    Functions.select_segment_register .Mode_64bit prefixes (2#2) (BitVec.ofNat 3 base.val) (0#8) =
      (pure 3 : SailM Nat) := by
  have stackBits := not_stack_bits base noStack
  have sibBits := not_sib_bits base noSib
  simp [Functions.select_segment_register, Functions.select_address_size, Functions.in_64bit_mode,
    segmentOverride, addressOverride, Functions.eq_bits_nat, Sail.BitVec.toNatInt, stackBits, sibBits]

theorem handler_dword (state : State) (destination base : Fin 16)
    (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer baseValue : Word) (value : BitVec 32) (flags : BitVec 32) (displacement : BitVec 32)
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
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress prefixes (loadRex false destination base)
      (0x8b#8) (loadModRM destination base) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination (value.zeroExtend 64)) next) := by
  unfold Functions.x86_mov_op_en_rm
  dsimp only
  rw [show ((0x8b#8) == (0x8a#8)) = false from rfl,
    operand_size32 destination base prefixes operandOverride, run_bind, run_pure]
  dsimp only
  rw [load_mod, load_rm, segment_data prefixes base noSib noStack segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (4 : Int) = 4 from rfl, run_bind,
    operand_dword state destination base noSib displacementAddress dataAddress prefixes attributes visible controls pointer
      baseValue value flags displacement addressOverride codeUpper dataUpper segments application rip baseKnown
      controlKnown flagsKnown visibleKnown effective aligned codePresent dataPresent]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [show Functions.bits_of_int 4 4 = (4#4) from rfl, load_destination, cut128]
  rw [run_bind, write_destination32 state destination base value quiet]
  change (Functions.write_iptr .Mode_64bit next).run (put state destination (value.zeroExtend 64)) = _
  exact X86Move.write_pointer64 _ next (by simpa only [diagnostic_put] using quiet)

theorem no_sib (destination base : Fin 16) (noSib : base.val % 8 ≠ 4) (address16 : Bool) :
    Functions.x86_decode_sib_p (loadModRM destination base) address16 = false := by
  simp [Functions.x86_decode_sib_p, load_rm, not_sib_bits base noSib]

theorem packet_operand : ∀ opcode : BitVec 8,
    Functions._get_prefixes_opr (X86LegacyFetch.packet opcode) = (0#8) := by decide

set_option maxRecDepth 4096 in
theorem dispatch_load (other : OtherOpcodeHandlers) (rexByte modrm : BitVec 8)
    (start displacementAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start displacementAddress (X86LegacyFetch.packet (0x8b#8))
      rexByte (0x8b#8) modrm (0#8) =
      Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress (X86LegacyFetch.packet (0x8b#8))
        rexByte (0x8b#8) modrm (0#8) := by rfl

theorem fetched_dword (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
    (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue : Word) (value : BitVec 32) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state base = some baseValue)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (3#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex false destination base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM destination base))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination (value.zeroExtend 64)) finish) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x8b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x8b#8) shape false state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes destination base (loadModRM destination base)
    (no_sib destination base noSib) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [dispatch_load other (loadRex false destination base) (loadModRM destination base)]
  apply handler_dword state destination base noSib noStack origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x8b#8)) origin.attributes visible controls (origin.address.signExtend 64)
    baseValue value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    (packet_operand _) advance
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
  · exact aligned
  · exact codePresent
  · exact dataPresent

theorem result_frame (state : State) (destination : Fin 16) (value : BitVec 32) (finish : BitVec 48) :
    X86Execution.RegisterFrame {key destination, Register.rip} state
      (X86Move.putPointer (put state destination (value.zeroExtend 64)) finish) := by
  simpa using (X86Execution.put_frame state destination (value.zeroExtend 64)).trans
    (X86Execution.pointer_frame _ finish)

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0

private def mapped (destination : Fin 16) (value : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rsi (0x2000#64)
  let registers := registers.insert .r10 (0xffffffffffffffff#64)
  let registers := registers.insert .r11 (33#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (loadRex false destination 6)
  let memory := memory.insert 4097 (0x8b#8)
  let memory := memory.insert 4098 (loadModRM destination 6)
  let memory := memory.insert 4099 0
  let memory := memory.insert 4100 0
  let memory := memory.insert 4101 0
  let memory := memory.insert 4102 0
  let memory := memory.insert 8192 (value.extractLsb' 0 8)
  let memory := memory.insert 8193 (value.extractLsb' 8 8)
  let memory := memory.insert 8194 (value.extractLsb' 16 8)
  let memory := memory.insert 8195 (value.extractLsb' 24 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (destination : Fin 16) (value : BitVec 32) :
    X86LegacyFetch.Basis (mapped destination value) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := control
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [mapped, Std.ExtDHashMap.get?_insert]
  fault := by simp [mapped, Std.ExtDHashMap.get?_insert]
  msrs := by simp [mapped, Std.ExtDHashMap.get?_insert]
  segments := by simp [mapped, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [mapped, Std.ExtDHashMap.get?_insert]
  rip := by simp [mapped, Std.ExtDHashMap.get?_insert]

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (value : BitVec 32) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped destination value) =
      .ok () (X86Move.putPointer (put (mapped destination value) destination (value.zeroExtend 64)) (0x1007#48)) := by
  apply fetched_dword other vector (mapped destination value) destination 6 (by decide) (by decide)
    (origin destination value) (0x1007#48) (0x2000#48) visible controls (0x2000#64) value (0x200#32) (0#32)
  · change (0x1003#48).toInt + 4 = (0x1007#48).toInt
    decide
  · decide
  · change ((mapped destination value).regs.get? .rsi).map (fun word : Word => word) = _
    simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · decide
  · decide
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [origin, mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem high_dword_zero_extended (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) = some (0x89abcdef#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  simp [X86Move.lookup_putPointer, lookup_put_same]

theorem sign_extension_rejected (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) ≠ some (0xffffffff89abcdef#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [high_dword_zero_extended]
  decide

theorem changed_modrm_changes_destination (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 11 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) = some (0xffffffffffffffff#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  dsimp only
  rw [X86Move.lookup_putPointer, lookup_put_other _ 11 10 _ (by decide)]
  change ((mapped 11 (0x89abcdef#32)).regs.get? .r10).map (fun word : Word => word) = _
  simp [mapped, Std.ExtDHashMap.get?_insert]

end Controls


end Mettapedia.Machines.TIsa.X86DwordLoad
