import Mettapedia.Machines.TIsa.X86FrameIncrement

/-!
# Fetched register and immediate stores into runtime-frame words

The original MOV handlers execute the emitted no-SIB RDI + disp32 forms:
a seven-byte register store and an eleven-byte sign-extended immediate store.
The proofs retain displacement and immediate reads, canonical addresses,
alignment checks, bytewise writes and RIP advancement. Register values and
flags are preserved, and the exact byte frame can protect a complete image.

Concrete controls execute the complete fetch path, check negative-immediate
sign extension and suffix preservation, and refuse zero extension of that
negative value. Whole-handler/program, emitter and ABI composition remain
separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/MoveImmediateFunctions.lean.inc"
  sha256 "e5006150efda0dde8e9c91a97d47041a2a02a5c5627f1b921f07269aaddd31ba"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86FrameStore
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

theorem read_dword (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (value : BitVec 32)
    (upper : address.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address address.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.rme_size .Mode_64bit 8 4 (address.signExtend 64) none 1 ":X" false false).run state =
      .ok (value.zeroExtend 128) state := by
  unfold Functions.rme_size
  rw [run_bind, X86ReadWords.code_dword_uses_rb state address attributes segments,
    X86ReadWords.rb_dword_exact state address pointer value ":X" upper application rip present]
  rfl

theorem handler_register (state : State) (source : Fin 16)
    (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer frame value : Word)
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
    (frameKnown : lookup state 7 = some frame)
    (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start displacementAddress prefixes
      (X86FrameLoad.frameRex source) (0x89#8) (X86FrameLoad.frameModRM source) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) next) := by
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl, X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [X86FrameLoad.frame_destination, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    run_bind, X86Move.read_register64 state source _ value sourceKnown]
  dsimp only
  rw [X86FrameLoad.frame_mod, X86FrameLoad.frame_rm]
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, X86FrameLoad.effective_frame state source displacementAddress prefixes attributes pointer frame
    displacement addressOverride codeUpper segments application rip frameKnown codePresent]
  dsimp only
  rw [X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [show Int.toNat (8 : Int) = 8 from rfl]
  rw [effective]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (X86FrameLoad.frameRex source) (7#3) (2#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, X86FrameIncrement.write_frame state dataAddress prefixes attributes visible controls
    pointer value flags (X86FrameLoad.frameRex source) addressOverride dataUpper segments application rip
    controlKnown flagsKnown visibleKnown aligned]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 8 state dataAddress value).registers_equal]
  exact quiet

theorem truncate_dword (value : BitVec 32) :
    Sail.BitVec.truncate (Sail.BitVec.zeroExtend value 128) 32 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [Sail.BitVec.truncate, Sail.BitVec.zeroExtend, within]

theorem handler_immediate (state : State)
    (start displacementAddress immediateAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer frame : Word)
    (flags : BitVec 32) (displacement immediate : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advanceDisplacement : displacementAddress.toInt + 4 = immediateAddress.toInt)
    (advanceImmediate : immediateAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : immediateAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (immediatePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediateAddress.toInt index).signExtend 52).toNat =
        some (immediate.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_mi .Mode_64bit start displacementAddress prefixes
      (0x48#8) (0xc7#8) (0x87#8) (0#8)).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress (immediate.signExtend 64)) next) := by
  have size : Functions.select_operand_size .Mode_64bit false (0x48#8) true prefixes
      false false false = (pure 4 : SailM Int) := by
    simp [Functions.select_operand_size, Functions.in_64bit_mode,
      show Functions.logbitp_bits 3 (0x48#8) = true from rfl]
  unfold Functions.x86_mov_op_en_mi
  dsimp only
  simp only [show ((0xc7#8) == (0xc6#8)) = false from rfl]
  rw [size, run_bind, run_pure]
  dsimp only
  rw [show Functions._get_modr_m_mod (0x87#8) = (2#2) from rfl,
    show Functions._get_modr_m_r_m (0x87#8) = (7#3) from rfl]
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [X86FrameIncrement.effective_frame_immediate_size]
  have rexZero : X86FrameLoad.frameRex (0 : Fin 16) = (0x48#8) := by decide
  rw [← rexZero, run_bind, X86FrameLoad.effective_frame state (0 : Fin 16) displacementAddress prefixes
    attributes pointer frame displacement addressOverride (by omega) segments application rip frameKnown codePresent]
  dsimp only
  rw [rexZero, X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) immediateAddress
      (by simpa using advanceDisplacement)]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [addressSize]
  simp only [pure_bind, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, read_dword state immediateAddress pointer attributes immediate codeUpper segments application rip
    immediatePresent]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state immediateAddress (4#48) next
      (by simpa using advanceImmediate)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false,
    show ((0xc7#8) == (0xc7#8)) = true from rfl,
    show Functions.logbitp_bits 3 (0x48#8) = true from rfl,
    Bool.and_self, ite_true, show ((8 : Int) == 8) = true from rfl]
  have narrowed : Sail.BitVec.truncate (immediate.zeroExtend 128) 32 = immediate := by
    exact truncate_dword immediate
  rw [narrowed, effective]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false ((immediate.signExtend 64).zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (0x48#8) (7#3) (2#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, X86FrameIncrement.write_frame state dataAddress prefixes attributes visible controls
    pointer (immediate.signExtend 64) flags (0x48#8) addressOverride dataUpper segments application rip
    controlKnown flagsKnown visibleKnown aligned]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 8 state dataAddress (immediate.signExtend 64)).registers_equal]
  exact quiet

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with
    x86_mov_op_en_mi := Functions.x86_mov_op_en_mi
    x86_mov_op_en_oi := Functions.x86_mov_op_en_oi }

theorem fetched_register (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame) (sourceKnown : lookup state source = some value)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (X86FrameLoad.frameRex source))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (X86FrameLoad.frameModRM source))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress value) finish) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x89#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x89#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes source 7 (X86FrameLoad.frameModRM source)
    (X86FrameLoad.frame_no_sib source) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change (Functions.x86_mov_op_en_mr .Mode_64bit origin.address origin.next
    (X86LegacyFetch.packet (0x89#8)) (X86FrameLoad.frameRex source) (0x89#8)
    (X86FrameLoad.frameModRM source) (0#8)).run state = _
  apply handler_register state source origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x89#8)) origin.attributes visible controls (origin.address.signExtend 64)
    frame value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) advance
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
  · exact frameKnown
  · exact sourceKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent

theorem fetched_immediate (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (immediateAddress finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame : Word) (flags : BitVec 32) (displacement immediate : BitVec 32)
    (advanceDisplacement : origin.next.toInt + 4 = immediateAddress.toInt)
    (advanceImmediate : immediateAddress.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x48#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0xc7#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x87#8))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (immediatePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediateAddress.toInt index).signExtend 52).toNat =
        some (immediate.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state dataAddress (immediate.signExtend 64)) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0xc7#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0xc7#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes (0 : Fin 16) 7
    (X86FrameLoad.frameModRM (0 : Fin 16)) (X86FrameLoad.frame_no_sib (0 : Fin 16))
    origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change (Functions.x86_mov_op_en_mi .Mode_64bit origin.address origin.next
    (X86LegacyFetch.packet (0xc7#8)) (0x48#8) (0xc7#8) (0x87#8) (0#8)).run state = _
  apply handler_immediate state origin.address origin.next immediateAddress finish dataAddress
    (X86LegacyFetch.packet (0xc7#8)) origin.attributes visible controls (origin.address.signExtend 64)
    frame flags displacement immediate (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advanceDisplacement advanceImmediate
  · apply X86FrameLoad.length_from_distance _ _ 11 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact frameKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent
  · exact immediatePresent

theorem result_frame (state : State) (base : BitVec 48) (value : Word) (finish : BitVec 48) :
    X86StateFrame.Frame {.rip} (X86WriteWords.written base (List.range 8)) state
      (X86Move.putPointer (X86WriteWords.storeBytes 8 state base value) finish) := by
  simpa using (X86WriteWords.storeBytes_frame 8 state base value).trans
    (X86StateFrame.registerOnly (X86Execution.pointer_frame _ finish))

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def code (immediate : BitVec 32) : List Nat :=
  [0x48, 0xc7, 0x87, 0, 0, 0, 0] ++ (List.range 4).map (fun index => (immediate.extractLsb' (8 * index) 8).toNat)
private def cells (immediate : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 11).map (fun index => (4096 + index, BitVec.ofNat 8 (((code immediate)[index]?).getD 0))) ++ [(8200, 42#8)]
private theorem distinct (immediate : BitVec 32) :
    (cells immediate).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells immediate).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys
private def mapped (immediate : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rdi (0x2000#64)
  let registers := registers.insert .rax (99#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells immediate), (), 0, #[]⟩
private theorem code_byte (immediate : BitVec 32) (index : Nat) (within : index < 11) :
    (mapped immediate).mem.get? (4096 + index) = some (BitVec.ofNat 8 (((code immediate)[index]?).getD 0)) := by
  have present : (4096 + index, BitVec.ofNat 8 (((code immediate)[index]?).getD 0)) ∈ cells immediate := by
    simp only [cells, List.mem_append, List.mem_map]
    exact Or.inl ⟨index, List.mem_range.mpr within, rfl⟩
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct immediate) present
private def origin (immediate : BitVec 32) : X86LegacyFetch.Basis (mapped immediate) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
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

theorem immediate_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (immediate : BitVec 32) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped immediate) =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 (mapped immediate) (0x2000#48)
        (immediate.signExtend 64)) (0x100b#48)) := by
  apply fetched_immediate other vector (mapped immediate) (origin immediate) (0x1007#48) (0x100b#48)
    (0x2000#48) visible controls (0x2000#64) (0#32) (0#32) immediate
    (by change (4099 : Int) + 4 = 4103; decide) (by decide) (by decide)
  · simp [mapped, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]
    rfl
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped]
  · rfl
  · decide
  · exact code_byte immediate 0 (by decide)
  · exact code_byte immediate 1 (by decide)
  · exact code_byte immediate 2 (by decide)
  · intro index within
    have got := code_byte immediate (3 + index) (by omega)
    interval_cases index <;> exact got
  · intro index within
    have got := code_byte immediate (7 + index) (by omega)
    have encoded : BitVec.ofNat 8 (((code immediate)[7 + index]?).getD 0) =
        immediate.extractLsb' (8 * index) 8 := by
      interval_cases index <;> apply BitVec.eq_of_toNat_eq <;>
        simp [code, show List.range 4 = [0, 1, 2, 3] from rfl]
    rw [encoded] at got
    interval_cases index <;> exact got

theorem negative_immediate_sign_extends (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (0xfffffff0#32)) = .ok () after ∧
      after.mem.get? 8199 = some (255#8) ∧ after.mem.get? 8200 = some (42#8) ∧
      after.regs.get? .rax = some (99#64) := by
  refine ⟨_, immediate_executes other vector (0xfffffff0#32), ?_, ?_, ?_⟩
  · change (X86WriteWords.storeBytes 8 (mapped (0xfffffff0#32)) (0x2000#48) (0xfffffffffffffff0#64)).mem.get? _ = _
    exact X86WriteWords.store_word_byte _ _ _ (by decide) 7 (by decide)
  · have outside : 8200 ∉ X86WriteWords.written (0x2000#48) (List.range 8) := by decide
    rw [show (X86Move.putPointer _ _).mem =
      (X86WriteWords.storeBytes 8 (mapped (0xfffffff0#32)) (0x2000#48) (0xfffffffffffffff0#64)).mem from rfl,
      (X86WriteWords.storeBytes_frame 8 (mapped (0xfffffff0#32)) (0x2000#48) (0xfffffffffffffff0#64)).memory 8200 outside]
    have present : (8200, 42#8) ∈ cells (0xfffffff0#32) := List.mem_append_right _ (by simp)
    exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct _) present
  · rw [(result_frame (mapped (0xfffffff0#32)) (0x2000#48) ((0xfffffff0#32).signExtend 64) (0x100b#48)).registers .rax
      (by decide)]
    simp [mapped, Std.ExtDHashMap.get?_insert]

theorem zero_extended_negative_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (after : State)
    (wrong : after.mem.get? 8199 = some (0#8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped (0xfffffff0#32)) ≠ .ok () after := by
  intro observed
  obtain ⟨proved, run, byte, _, _⟩ := negative_immediate_sign_extends other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at byte
  contradiction

end Controls
end Mettapedia.Machines.TIsa.X86FrameStore

#print axioms Mettapedia.Machines.TIsa.X86FrameStore.fetched_register
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.fetched_immediate
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.result_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.Controls.immediate_executes
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.Controls.negative_immediate_sign_extends
#print axioms Mettapedia.Machines.TIsa.X86FrameStore.Controls.zero_extended_negative_refused
