import Mettapedia.Machines.TIsa.X86SibStore

/-!
# Fetched qword accesses through R12

The base-only SIB encoding contributes one byte to the instruction.
Both operations read the four displacement bytes and use the same
aligned qword address. The store has exactly the eight-byte footprint.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86SibQword

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Access where
  | load | store
  deriving DecidableEq, Repr

def Access.opcode : Access → BitVec 8
  | .load => 0x8b | .store => 0x89

def code (access : Access) (register : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(loadRex true register 12).toNat, access.opcode.toNat, (loadModRM register 12).toNat, 0x24] ++
    (List.range 4).map fun index => (displacement.extractLsb' (8 * index) 8).toNat

theorem code_length (access : Access) (register : Fin 16) (displacement : BitVec 32) :
    (code access register displacement).length = 8 := by simp [code]

structure Inputs (state : State) (displacement : BitVec 32) extends X86LegacyFetch.Basis state where
  controls : Vector (BitVec 64) 17
  visible : Vector (BitVec 16) 6
  flags : BitVec 32
  baseValue : Word
  target : BitVec 48
  controlsRead : state.regs.get? .ctrs = some controls
  visibleRead : state.regs.get? .seg_visibles = some visible
  flagsRead : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  baseKnown : lookup state 12 = some baseValue
  effective : baseValue + displacement.signExtend 64 = target.signExtend 64
  upper : address.toInt + 8 < (2^47 : Int)
  dataUpper : target.toInt + 8 ≤ (2^47 : Int)
  aligned : target &&& (7#48) = (0#48)

private def displacementAt {state : State} {displacement : BitVec 32} (input : Inputs state displacement) :
    BitVec 48 := address input.address.toInt 4

def following {state : State} {displacement : BitVec 32} (input : Inputs state displacement) : BitVec 48 :=
  address input.address.toInt 8

private theorem displacement_point {state : State} {displacement : BitVec 32} (input : Inputs state displacement) :
    (displacementAt input).toInt = input.address.toInt + 4 :=
  address_toInt _ (BitVec.le_toInt _) input.upper 4 (by decide)

private theorem following_point {state : State} {displacement : BitVec 32} (input : Inputs state displacement) :
    (following input).toInt = input.address.toInt + 8 :=
  address_toInt _ (BitVec.le_toInt _) input.upper 8 (by decide)

private theorem displacement_bytes (access : Access) (state : State) (register : Fin 16)
    (displacement : BitVec 32) (input : Inputs state displacement)
    (loaded : codeLoaded state input.address.toInt (code access register displacement)) :
    ∀ index < 4, state.mem.get? ((address (displacementAt input).toInt index).signExtend 52).toNat =
      some (displacement.extractLsb' (8 * index) 8) := by
  intro index within
  rw [displacement_point]
  have point : address (input.address.toInt + 4) index = address input.address.toInt (4 + index) := by
    simp [address, Int.add_assoc]
  rw [point]
  have byte : (code access register displacement)[4 + index]? =
      some (displacement.extractLsb' (8 * index) 8).toNat := by
    interval_cases index <;> rfl
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ byte

private theorem use_sib (access : Access) (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (register : Fin 16) (displacement : BitVec 32) (input : Inputs state displacement)
    (loaded : codeLoaded state input.address.toInt (code access register displacement)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit input.address (displacementAt input)
        (X86LegacyFetch.packet access.opcode) (loadRex true register 12) access.opcode
        (loadModRM register 12) (0x24#8)).run state := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode access.opcode := by
    apply (X86LegacyFetch.checkOpcode_iff _).mp
    cases access <;> decide +kernel
  refine X86SibStore.fetch_to_dispatch_sib access.opcode shape true state input.toBasis _
    register 12 (loadModRM register 12) (0x24#8) (X86SibStore.requires_sib register) ?_ ?_ ?_ ?_ ?_
  · rw [displacement_point]
    have := input.step2
    have := input.step3
    omega
  · have point : address input.address.toInt 0 = input.address := by simp [address]
    simpa only [point, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded 0 (loadRex true register 12).toNat (by simp [code])
  · have point : input.opcodeAddress = address input.address.toInt 1 := by
      apply BitVec.eq_of_toInt_eq
      rw [address_toInt _ (BitVec.le_toInt _) input.upper 1 (by decide)]
      exact input.step1.symm
    rw [point]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded 1 access.opcode.toNat (by simp [code])
  · have point : input.modrmAddress = address input.address.toInt 2 := by
      apply BitVec.eq_of_toInt_eq
      rw [address_toInt _ (BitVec.le_toInt _) input.upper 2 (by decide)]
      exact input.step2.symm
    rw [point]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded 2 (loadModRM register 12).toNat (by simp [code])
  · have point : input.next = address input.address.toInt 3 := by
      apply BitVec.eq_of_toInt_eq
      rw [address_toInt _ (BitVec.le_toInt _) input.upper 3 (by decide)]
      have := input.step2
      have := input.step3
      omega
    rw [point]
    exact loaded 3 0x24 (by simp [code])

private theorem operand_reads (state : State) (register : Fin 16) (displacement : BitVec 32)
    (input : Inputs state displacement) (word : Word)
    (bytes : ∀ index < 4,
      state.mem.get? ((address (displacementAt input).toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (readback : ∀ index < 8, state.mem.get? ((address input.target.toInt index).signExtend 52).toNat =
      some (word.extractLsb' (8 * index) 8)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 2
      (X86LegacyFetch.packet (0x8b#8)) (displacementAt input) (loadRex true register 12)
      (4#3) (2#2) (0x24#8) (0#3)).run state =
      .ok (word.zeroExtend 128, (4 : Int), input.target.signExtend 64) state := by
  let prefixes := X86LegacyFetch.packet (0x8b#8)
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  have upper : (displacementAt input).toInt + 4 ≤ (2^47 : Int) := by
    rw [displacement_point]
    have := input.upper
    omega
  rw [run_bind, X86SibStore.effective_memory state true register _ prefixes input.attributes _
    input.baseValue displacement (X86LegacyFetch.packet_address _) upper input.segments input.application
    input.rip input.baseKnown bytes]
  dsimp only
  rw [input.effective]
  simp only [bind_assoc, pure_bind, Bool.true_and]
  rw [run_bind, X86FrameLoad.alignment_exact state input.controls input.flags input.visible
    input.controlsRead input.flagsRead input.visibleRead]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, prefixes, X86LegacyFetch.packet_address]
  rw [size]
  simp only [pure_bind, Functions.select_base_register, show Int.toNat (8 : Int) = 8 from rfl]
  unfold Functions.rme_size
  have loadSegment : Functions.load_bytes_from_ea .Mode_64bit 8 8 (input.target.signExtend 64) none 2
      ":R" (X86FrameLoad.alignmentEnabled input.controls input.flags input.visible) false =
      Functions.load_bytes_from_ea .Mode_64bit 8 8 (input.target.signExtend 64) none 3
        ":R" (X86FrameLoad.alignmentEnabled input.controls input.flags input.visible) false := rfl
  rw [loadSegment, run_bind, run_bind, X86ReadWords.load_word_exact state input.target none input.attributes
    _ word ":R" _ false input.dataUpper input.segments input.application input.rip (Or.inr input.aligned) readback]
  rfl

private theorem dispatch_load (other : OtherOpcodeHandlers)
    (start next : BitVec 48) (register : Fin 16) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next
      (X86LegacyFetch.packet Access.load.opcode) (loadRex true register 12)
        Access.load.opcode (loadModRM register 12) (0x24#8) =
    Functions.x86_mov_op_en_rm .Mode_64bit start next
      (X86LegacyFetch.packet (0x8b#8)) (loadRex true register 12)
        (0x8b#8) (loadModRM register 12) (0x24#8) := rfl

theorem fetched_load (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (displacement : BitVec 32) (input : Inputs state displacement)
    (loaded : codeLoaded state input.address.toInt (code .load destination displacement)) (word : Word)
    (known : ∀ index < 8, state.mem.get? ((address input.target.toInt index).signExtend 52).toNat =
      some (word.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination word) (following input)) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [use_sib .load (X86FrameLoad.linkedHandlers other) vector state destination displacement input loaded]
  rw [dispatch_load other]
  let prefixes := X86LegacyFetch.packet (0x8b#8)
  unfold Functions.x86_mov_op_en_rm
  dsimp only
  rw [show ((0x8b#8) == (0x8a#8)) = false from rfl, X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [load_mod, load_rm]
  change (do
    let segment ← Functions.select_segment_register .Mode_64bit prefixes (2#2) (4#3) (0x24#8)
    _ : SailM Unit).run state = _
  rw [X86SibStore.segment_stack prefixes (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _),
    run_bind, run_pure]
  dsimp only
  rw [show BitVec.ofNat 3 (12 : Fin 16).val = (4#3) from rfl]
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    operand_reads state destination displacement input word
      (displacement_bytes .load state destination displacement input loaded) known]
  dsimp only
  have advance : (displacementAt input).toInt + 4 = (following input).toInt := by
    rw [displacement_point, following_point]
    omega
  have length : Functions.check_instruction_length input.address (following input) (0#3) = none :=
    X86FrameLoad.length_from_distance _ _ 8 (by decide) (following_point input)
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state _ (4#48) _ (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬ Functions.is_some (none : Option Int) = true)]
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl, X86QwordLoad.destination64, X86QwordLoad.cut128]
  rw [run_bind, X86QwordLoad.write_destination64 state destination 12 word input.quiet]
  exact X86Move.write_pointer64 _ _ (by simpa only [diagnostic_put] using input.quiet)

private theorem dispatch_store (other : OtherOpcodeHandlers)
    (start next : BitVec 48) (register : Fin 16) :
    letI : OtherOpcodeHandlers := other
    Functions.one_byte_opcode_execute .Mode_64bit start next
      (X86LegacyFetch.packet Access.store.opcode) (loadRex true register 12)
        Access.store.opcode (loadModRM register 12) (0x24#8) =
    Functions.x86_mov_op_en_mr .Mode_64bit start next
      (X86LegacyFetch.packet (0x89#8)) (loadRex true register 12)
        (0x89#8) (loadModRM register 12) (0x24#8) := rfl

theorem fetched_store (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source : Fin 16) (displacement : BitVec 32) (input : Inputs state displacement)
    (loaded : codeLoaded state input.address.toInt (code .store source displacement)) (word : Word)
    (known : lookup state source = some word) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state input.target word) (following input)) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  rw [use_sib .store other vector state source displacement input loaded, dispatch_store other]
  let prefixes := X86LegacyFetch.packet (0x89#8)
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl, X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [X86QwordLoad.destination64, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    run_bind, X86Move.read_register64 state source _ word known]
  dsimp only
  rw [load_mod, load_rm]
  change (do
    let (effectiveAddress, used) ← Functions.x86_effective_addr .Mode_64bit prefixes (displacementAt input)
      (loadRex true source 12) (4#3) (2#2) (0x24#8) (0#3)
    _ : SailM Unit).run state = _
  have upper : (displacementAt input).toInt + 4 ≤ (2^47 : Int) := by
    rw [displacement_point]
    have := input.upper
    omega
  rw [run_bind, X86SibStore.effective_memory state true source _ prefixes input.attributes _
    input.baseValue displacement (X86LegacyFetch.packet_address _) upper input.segments input.application
    input.rip input.baseKnown (displacement_bytes .store state source displacement input loaded)]
  dsimp only
  rw [show BitVec.ofNat 3 (12 : Fin 16).val = (4#3) from rfl]
  rw [X86SibStore.segment_stack prefixes (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _),
    run_bind, run_pure]
  dsimp only
  have advance : (displacementAt input).toInt + 4 = (following input).toInt := by
    rw [displacement_point, following_point]
    omega
  have length : Functions.check_instruction_length input.address (following input) (0#3) = none :=
    X86FrameLoad.length_from_distance _ _ 8 (by decide) (following_point input)
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state _ (4#48) _ (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬ Functions.is_some (none : Option Int) = true)]
  rw [show Int.toNat (8 : Int) = 8 from rfl, input.effective]
  have operand : Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (word.zeroExtend 128) 2
      (input.target.signExtend 64) prefixes (loadRex true source 12) (4#3) (2#2) (0x24#8) =
      Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (word.zeroExtend 128) 3
        (input.target.signExtend 64) prefixes (loadRex true source 12) (7#3) (2#2) (0#8) := rfl
  rw [show Sail.BitVec.zeroExtend word 128 = word.zeroExtend 128 from rfl]
  dsimp only [prefixes] at operand
  rw [operand, run_bind, X86DataStore.write_operand64_checked state input.target prefixes input.attributes
    input.visible input.controls _ word input.flags (loadRex true source 12) (7#3)
    (X86LegacyFetch.packet_address _) input.dataUpper input.segments input.application input.rip
    input.controlsRead input.flagsRead input.visibleRead (Or.inr input.aligned)]
  apply X86Move.write_pointer64
  rw [(X86WriteWords.storeBytes_frame 8 state input.target word).registers_equal]
  exact input.quiet

end Mettapedia.Machines.TIsa.X86SibQword
