import Mettapedia.Machines.TIsa.X86DataStore

/-!
# Fetched R12-based dword stores

The p1 adapter emits an explicit SIB byte for R12-based stores. The original
Sail fetch reads that byte, the effective-address routine selects R12 with no
index, and MOV writes exactly the low four source bytes. The contracts cover
arbitrary source registers and signed disp32 values, retaining alignment as
an explicit architectural obligation. All other registers and memory bytes
are preserved. Bounds validation, the surrounding source transition and the
public call remain separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86SibStore
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

theorem base_index : ∀ wide : Bool, ∀ source : Fin 16,
    Functions.reg_index (Functions._get_sib_base (0x24#8)) (loadRex wide source 12) (0#2) = (12#4) := by decide

theorem index_absent : ∀ wide : Bool, ∀ source : Fin 16,
    Functions.reg_index (Functions._get_sib_index (0x24#8)) (loadRex wide source 12) (1#2) = (4#4) := by decide

theorem segment_stack (prefixes : BitVec 52)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8)) :
    Functions.select_segment_register .Mode_64bit prefixes (2#2) (4#3) (0x24#8) =
      (pure 2 : SailM Nat) := by
  simp [Functions.select_segment_register, segmentOverride, Functions.select_address_size,
    Functions.in_64bit_mode, addressOverride, Functions.eq_bits_nat, Sail.BitVec.toNatInt,
    show Functions._get_sib_base (0x24#8) = (4#3) from rfl]

theorem effective_disp32 (state : State) (wide : Bool) (source : Fin 16)
    (displacementAddress : BitVec 48) (attributes : Vector (BitVec 16) 6)
    (pointer baseValue : Word) (displacement : BitVec 32)
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state 12 = some baseValue)
    (present : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr_32_64 .Mode_64bit false displacementAddress
      (loadRex wide source 12) (4#3) (2#2) (0x24#8) (0#3)).run state =
      .ok (baseValue + displacement.signExtend 64, (4 : Int)) state := by
  unfold Functions.x86_effective_addr_32_64
  simp only [show Functions.eq_bits_nat (2#2) 0 = false from rfl,
    show Functions.eq_bits_nat (2#2) 1 = false from rfl,
    show Functions.eq_bits_nat (2#2) 2 = true from rfl,
    show Functions.eq_bits_nat (4#3) 4 = true from rfl,
    Bool.false_eq_true, ite_false, ite_true]
  unfold Functions.x86_effective_addr_from_sib
  simp only [show Functions.eq_bits_nat (2#2) 0 = false from rfl,
    show Functions.eq_bits_nat (2#2) 1 = false from rfl,
    show Functions.eq_bits_nat (2#2) 2 = true from rfl,
    Bool.false_eq_true, ite_false, ite_true]
  rw [show Functions.select_address_size .Mode_64bit none = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, bind_assoc, Sail.BitVec.signExtend, show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind, X86ReadWords.signed_displacement_exact state displacementAddress attributes pointer displacement
    upper segments application rip present]
  dsimp only
  simp only [Functions.in_64bit_mode, ite_true, base_index, index_absent,
    show Sail.BitVec.toNatInt (12#4) = (12 : Int) from rfl]
  have readBase : (Functions.rgfi 12).run state = .ok baseValue state := rgfi_exact state 12 baseValue baseKnown
  simp only [bind_assoc, pure_bind, run_bind]
  rw [readBase]
  simp only [show Functions.eq_bits_nat (4#4) 4 = true from rfl, ite_true, run_pure]
  rw [show Functions.ash_left_int (0#64).toInt
    (Sail.BitVec.toNatInt (Functions._get_sib_scale (0x24#8))).toNat = 0 from rfl, Int.add_zero]
  change EStateM.Result.ok (Functions.bits_of_int (baseValue.toInt + (displacement.signExtend 64).toInt) 64, (4 : Int)) state = _
  rw [X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem effective_memory (state : State) (wide : Bool) (source : Fin 16)
    (displacementAddress : BitVec 48) (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6)
    (pointer baseValue : Word) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (baseKnown : lookup state 12 = some baseValue)
    (present : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr .Mode_64bit prefixes displacementAddress
      (loadRex wide source 12) (4#3) (2#2) (0x24#8) (0#3)).run state =
      .ok (baseValue + displacement.signExtend 64, (4 : Int)) state := by
  unfold Functions.x86_effective_addr
  simp only [addressOverride, show ((0x67#8) == (0#8)) = false from rfl]
  rw [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]]
  simp only [pure_bind, show ((2 : Int) == 8) = false from rfl, Bool.false_eq_true, ite_false]
  exact effective_disp32 state wide source displacementAddress attributes pointer baseValue displacement
    upper segments application rip baseKnown present

theorem stack_operand (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (rexByte : BitVec 8) (value : BitVec 32) :
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 2
      (dataAddress.signExtend 64) prefixes rexByte (4#3) (2#2) (0x24#8) =
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rexByte (7#3) (2#2) (0#8) := by rfl

theorem fetch_to_dispatch_sib [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : X86LegacyFetch.RegularOpcode opcode) (wide : Bool)
    (state : State) (origin : X86LegacyFetch.Basis state) (displacementAddress : BitVec 48)
    (source base : Fin 16) (modrm sib : BitVec 8)
    (requiresSib : Functions.x86_decode_sib_p modrm false = true)
    (advance : origin.next.toInt + 1 = displacementAddress.toInt)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex wide source base))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some opcode)
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some modrm)
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some sib) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit origin.address displacementAddress
        (X86LegacyFetch.packet opcode) (rex wide source base) opcode modrm sib).run state := by
  open X86LegacyFetch X86PrefixRead in
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, origin.status]
  dsimp only
  rw [run_bind, readRegister_exact, origin.fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state origin.control origin.attributes
    origin.msrs origin.segments origin.longMode origin.codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state origin.address origin.rip]
  dsimp only
  change (do let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15
             _ : SailM Unit).run state = _
  rw [run_bind, rex_then_opcode opcode shape state origin.address origin.opcodeAddress
    (origin.address.signExtend 64) origin.attributes wide source base (0#8) origin.step1
    origin.segments origin.application origin.rip prefixByte opcodeByte]
  dsimp only
  simp only [Functions.Mk_prefixes, packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit origin.address (2#48)
             _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state origin.address (2#48) origin.modrmAddress (by simpa using origin.step2)]
  dsimp only
  simp only [packet_opcode, shape.modrm, shape.notVex2, shape.notVex3, shape.notEvex,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, ite_true, pure_bind]
  rw [packet_address_size]
  simp only [pure_bind, Functions.Mk_modr_m, bind_pure, Sail.BitVec.signExtend]
  have readModrm : (Functions.rme08 .Mode_64bit (Int.toNat (8 : Int)) (origin.modrmAddress.signExtend 64) none 1 ":X").run state =
      .ok modrm state := X86EffectiveFetch.effective_read_exact state origin.modrmAddress
        (origin.address.signExtend 64) origin.attributes modrm origin.segments origin.application origin.rip modrmByte
  rw [run_bind, readModrm]
  dsimp only
  rw [run_bind, add_pointer_checked state origin.modrmAddress (1#48) origin.next (by simpa using origin.step3)]
  dsimp only
  simp only [show ((2 : Int) == 8) = false from rfl, requiresSib, Bool.and_true, ite_true]
  have readSib : (Functions.rme08 .Mode_64bit (Int.toNat (8 : Int)) (origin.next.signExtend 64) none 1 ":X").run state =
      .ok sib state := X86EffectiveFetch.effective_read_exact state origin.next
        (origin.address.signExtend 64) origin.attributes sib origin.segments origin.application origin.rip sibByte
  simp only [Functions.Mk_sib, bind_assoc, pure_bind]
  rw [run_bind, readSib]
  dsimp only
  rw [run_bind, add_pointer_checked state origin.next (1#48) displacementAddress (by simpa using advance)]

theorem handler32 (state : State) (source : Fin 16)
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
    (baseKnown : lookup state 12 = some baseValue) (sourceKnown : lookup state source = some value)
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
      (loadRex false source 12) (0x89#8) (loadModRM source 12) (0x24#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) next) := by
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl, operand_size32 source 12 prefixes operandOverride,
    run_bind, run_pure]
  dsimp only
  rw [load_destination, show Functions.bits_of_int 4 4 = (4#4) from rfl,
    run_bind, X86DataStore.read_register32 state source value _ sourceKnown]
  dsimp only
  rw [load_mod, load_rm]
  rw [show BitVec.ofNat 3 (12 : Fin 16).val = (4#3) from rfl]
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, effective_memory state false source displacementAddress prefixes attributes pointer baseValue
    displacement addressOverride codeUpper segments application rip baseKnown codePresent]
  dsimp only
  rw [segment_stack prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [show Int.toNat (4 : Int) = 4 from rfl, effective, X86DataStore.widen32]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false ((low32 value).zeroExtend 128) 2
      (dataAddress.signExtend 64) prefixes (loadRex false source 12) (4#3) (2#2) (0x24#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [stack_operand, run_bind, X86DataStore.write_operand32_checked state dataAddress prefixes attributes
    visible controls pointer (low32 value) flags (loadRex false source 12) (7#3) addressOverride dataUpper
    segments application rip controlKnown flagsKnown visibleKnown safe]
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 4 state dataAddress (low32 value)).registers_equal]
  exact quiet

theorem requires_sib : ∀ source : Fin 16, Functions.x86_decode_sib_p (loadModRM source 12) false = true := by decide

theorem dispatch_store (other : OtherOpcodeHandlers) (source : Fin 16)
    (start next : BitVec 48) :
    letI : OtherOpcodeHandlers := other
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x89#8))
      (loadRex false source 12) (0x89#8) (loadModRM source 12) (0x24#8) =
      Functions.x86_mov_op_en_mr .Mode_64bit start next (X86LegacyFetch.packet (0x89#8))
        (loadRex false source 12) (0x89#8) (loadModRM source 12) (0x24#8) := by rfl

theorem fetched32 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (origin : X86LegacyFetch.Basis state)
    (displacementAddress finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (sibAdvance : origin.next.toInt + 1 = displacementAddress.toInt)
    (advance : displacementAddress.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (baseKnown : lookup state 12 = some baseValue) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (loadRex false source 12))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (loadModRM source 12))
    (sibByte : state.mem.get? (origin.next.signExtend 52).toNat = some (0x24#8))
    (codePresent : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 state dataAddress (low32 value)) finish) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x89#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [fetch_to_dispatch_sib (0x89#8) shape false state origin displacementAddress source 12
    (loadModRM source 12) (0x24#8) (requires_sib source) sibAdvance prefixByte opcodeByte modrmByte sibByte]
  rw [dispatch_store]
  apply handler32 state source origin.address displacementAddress finish dataAddress
    (X86LegacyFetch.packet (0x89#8)) origin.attributes visible controls (origin.address.signExtend 64)
    baseValue value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    (X86DwordLoad.packet_operand _) advance
  · apply X86FrameLoad.length_from_distance _ _ 8 (by decide)
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

def code (source : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(loadRex false source 12).toNat, 0x89, (loadModRM source 12).toNat, 0x24] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

theorem code_length (source : Fin 16) (displacement : BitVec 32) : (code source displacement).length = 8 := by
  simp [code]

abbrev result (state : State) (dataAddress next : BitVec 48) (value : Word) : State :=
  X86DataStore.result false state dataAddress next value

abbrev writes (dataAddress : BitVec 48) : Finset Nat := X86DataStore.writes false dataAddress

structure Inputs (state : State) (source : Fin 16) (displacement : BitVec 32)
    extends X86LegacyFetch.Basis state where
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  baseValue : Word
  value : Word
  flags : BitVec 32
  dataAddress : BitVec 48
  baseKnown : lookup state 12 = some baseValue
  sourceKnown : lookup state source = some value
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 8 < (2 ^ 47 : Int)
  dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int)
  effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64
  safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48)
  loaded : codeLoaded state address.toInt (code source displacement)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (displacement : BitVec 32) (input : Inputs state source displacement) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run state =
        .ok () (result state input.dataAddress (address input.address.toInt 8) input.value) ∧
      X86StateFrame.Frame {.rip} (writes input.dataAddress) state
        (result state input.dataAddress (address input.address.toInt 8) input.value) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  let site := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let displacementAddress := address input.address.toInt 4
  let finish := address input.address.toInt 8
  have at3 : site.next.toInt = input.address.toInt + 3 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 3 (by decide)
  have at4 : displacementAddress.toInt = input.address.toInt + 4 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 4 (by decide)
  have at8 : finish.toInt = input.address.toInt + 8 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 8 (by decide)
  have present : ∀ index < 4,
      state.mem.get? ((address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8) := by
    intro index within
    rw [at4]
    have shift : address (input.address.toInt + 4) index = address input.address.toInt (4 + index) := by
      simp [address, Int.add_assoc]
    rw [shift]
    have byte : (code source displacement)[4 + index]? = some (displacement.extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded _ _ byte
  have prefixByte : state.mem.get? (site.address.signExtend 52).toNat = some (loadRex false source 12) := by
    simpa only [site, rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      input.loaded 0 (loadRex false source 12).toNat (by simp [code])
  have opcodeByte := input.loaded 1 0x89 (by simp [code])
  have modrmByte : state.mem.get? (site.modrmAddress.signExtend 52).toNat = some (loadModRM source 12) := by
    simpa only [site, rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      input.loaded 2 (loadModRM source 12).toNat (by simp [code])
  have sibByte : state.mem.get? (site.next.signExtend 52).toNat = some (0x24#8) :=
    input.loaded 3 0x24 (by simp [code])
  have run := fetched32 other vector state source site displacementAddress finish input.dataAddress
    input.visible input.controls input.baseValue input.value input.flags displacement (by omega) (by omega)
    input.dataUpper input.baseKnown input.sourceKnown input.controlKnown input.flagsKnown input.visibleKnown
    input.quiet input.effective input.safe prefixByte opcodeByte modrmByte sibByte present
  exact ⟨X86FuelPrefix.fetches_one state _ run,
    X86DataStore.result_frame false state input.dataAddress finish input.value⟩

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0

private def cells (displacement : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 8).map (fun offset => (4096 + offset, BitVec.ofNat 8 (((code 13 displacement)[offset]?).getD 0))) ++
    ((List.range 12).map (fun offset => (12304 + offset, 0xa5#8)) ++ [(12303, 0x5a#8)])

private theorem distinct (displacement : BitVec 32) :
    (cells displacement).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells displacement).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (displacement : BitVec 32) (baseValue value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r12 baseValue
  let registers := registers.insert .r13 value
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells displacement), (), 0, #[]⟩

private theorem cell (displacement : BitVec 32) (baseValue value : Word)
    (key : Nat) (byte : BitVec 8) (member : (key, byte) ∈ cells displacement) :
    (before displacement baseValue value).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct displacement) member

private theorem code_point : ∀ index : Fin 8,
    ((address 4096 index.val).signExtend 52).toNat = 4096 + index.val := by decide

private noncomputable def input (displacement : BitVec 32) (baseValue value : Word)
    (effective : baseValue + displacement.signExtend 64 = (12304#48).signExtend 64) :
    Inputs (before displacement baseValue value) 13 displacement where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  visible := visible
  controls := controls
  baseValue := baseValue
  value := value
  flags := 0x40246#32
  dataAddress := 12304#48
  baseKnown := by
    change ((before displacement baseValue value).regs.get? .r12).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  sourceKnown := by
    change ((before displacement baseValue value).regs.get? .r13).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  controlKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  dataUpper := by decide
  effective := effective
  safe := Or.inr (by decide)
  loaded := by
    change codeLoaded (before displacement baseValue value) 4096 (code 13 displacement)
    intro index byte present
    have within : index < 8 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
    rw [code_point ⟨index, within⟩]
    apply cell
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩

theorem control (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (displacement : BitVec 32) (baseValue value : Word)
    (effective : baseValue + displacement.signExtend 64 = (12304#48).signExtend 64) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run (before displacement baseValue value) =
        .ok () (result (before displacement baseValue value) (12304#48) (4104#48) value) ∧
      X86StateFrame.Frame {.rip} (writes (12304#48)) (before displacement baseValue value)
        (result (before displacement baseValue value) (12304#48) (4104#48) value) :=
  executes other vector (before displacement baseValue value) 13 displacement (input displacement baseValue value effective)

theorem dword_writes_only_low (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before (16#32) (12288#64) (0x1234567889abcdef#64)) = .ok () after ∧
      after.mem.get? 12304 = some (0xef#8) ∧ after.mem.get? 12307 = some (0x89#8) ∧
      after.mem.get? 12308 = some (0xa5#8) ∧ after.regs.get? .r13 = some (0x1234567889abcdef#64) ∧
      after.regs.get? .r12 = some (12288#64) ∧ after.regs.get? .rflags = some (0x40246#32) := by
  obtain ⟨run, frame⟩ := control other vector (16#32) (12288#64) (0x1234567889abcdef#64) (by decide)
  refine ⟨_, run, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact X86DataStore.byte_readback _ false _ _ _ (by decide) 0 (by decide)
  · exact X86DataStore.byte_readback _ false _ _ _ (by decide) 3 (by decide)
  · rw [frame.memory 12308 (by decide)]
    apply cell
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨4, by decide, rfl⟩
  · rw [frame.registers .r13 (by decide)]
    simp [before, Std.ExtDHashMap.get?_insert]
  · rw [frame.registers .r12 (by decide)]
    simp [before, Std.ExtDHashMap.get?_insert]
  · rw [frame.registers .rflags (by decide)]
    simp [before, Std.ExtDHashMap.get?_insert]

theorem negative_displacement (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 1).run (before (0xfffffff0#32) (12320#64) (42#64)) =
      .ok () (result (before (0xfffffff0#32) (12320#64) (42#64)) (12304#48) (4104#48) (42#64)) :=
  (control other vector (0xfffffff0#32) (12320#64) (42#64) (by decide)).1

theorem wrong_value_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 1).run (before (16#32) (12288#64) (0x1234567889abcdef#64)) = .ok () after ∧
      after.mem.get? 12304 = some (0x78#8) := by
  obtain ⟨after, run, byte, _⟩ := dword_writes_only_low other vector
  rintro ⟨wrong, wrongRun, wrongByte⟩
  rw [run] at wrongRun
  cases wrongRun
  rw [byte] at wrongByte
  contradiction

private noncomputable def changedSib : State :=
  let state := before (16#32) (12288#64) (42#64)
  { state with mem := state.mem.insert 4099 (0x2c#8) }

theorem changed_sib_refused : ¬ codeLoaded changedSib 4096 (code 13 (16#32)) := by
  intro loaded
  have byte := loaded 3 0x24 (by simp [code])
  change changedSib.mem.get? 4099 = some (0x24#8) at byte
  simp [changedSib] at byte

end Controls

end Mettapedia.Machines.TIsa.X86SibStore
