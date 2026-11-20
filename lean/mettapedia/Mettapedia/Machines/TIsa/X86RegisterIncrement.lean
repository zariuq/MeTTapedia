import Mettapedia.Machines.TIsa.X86ControlFlags
import Mettapedia.Machines.TIsa.X86FrameIncrement
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.Loop

/-!
# Fetched register counter increment from the original immediate handler

The four actual bytes encode REX.W ADD r64,imm8 with immediate one. The proof
retains the original operand read, immediate-byte fetch, signed immediate
normalization, instruction-length checks, arithmetic, flags and RIP update.
It applies to every physical register and includes modular wraparound.

The frame changes only the destination, arithmetic flags and RIP. Memory and
all other registers are preserved. Concrete all-register, high-word and changed
immediate controls are included. Source loop admission supplies the stronger
no-wrap condition; loop latch/backedge, body invariants and public ABI
composition remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86RegisterIncrement
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem operand_immediate (state : State) (destination : Fin 16) (value : Word)
    (prefixes : BitVec 52) (pointer : BitVec 48) (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer (rex true 0 destination)
      (Functions._get_modr_m_r_m (modRM 0 destination)) (3#2) (0#8) (1#3)).run state =
        .ok (Sail.BitVec.zeroExtend value 128, (0 : Int), (0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int ((8 : Nat) : Int) 4 = (8#4) from rfl, destination_register]
  rw [run_bind, run_bind, X86Move.read_register64 state destination _ value known]
  rfl

theorem handler (state : State) (destination : Fin 16) (start immediate next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : immediate.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (byte : state.mem.get? (immediate.signExtend 52).toNat = some (1#8)) :
    ∃ output, (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start immediate
      prefixes (rex true 0 destination) (0x83#8) (modRM 0 destination) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (value + 1)) (X86Flags.mergeFlags flags output)) next) := by
  obtain ⟨output, calculated⟩ := X86Alu.add_executes_defined state value (1#64) flags
  refine ⟨output, ?_⟩
  have size := X86Move.operand_size64 (0 : Fin 16) destination prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x83#8) == (0x80#8)) = false from rfl,
    show ((0x83#8) == (0x82#8)) = false from rfl,
    show ((0x83#8) == (0xf6#8)) = false from rfl,
    show ((0x83#8) == (0x83#8)) = true from rfl, Bool.false_or, Bool.true_or]
  rw [size, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit true (rex true 0 destination) true prefixes
      false false false = (pure 1 : SailM Int) from rfl]
  simp only [pure_bind, show Functions.check_range 1 4 1 = (pure 1 : SailM Int) from rfl]
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressSize, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    show Functions.bits_of_int 1 3 = (1#3) from rfl, run_bind,
    operand_immediate state destination value prefixes immediate known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl, run_bind, X86Move.add_pointer_zero]
  dsimp only
  have addressWidth : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressSize]
  rw [addressWidth]
  simp only [pure_bind, bind_assoc, show Int.toNat (1 : Int) = 1 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, X86FrameIncrement.read_immediate_one state immediate pointer attributes segments application rip byte]
  dsimp only
  rw [show Functions.ash_left_int 1 3 = 8 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate (1#128) 32) = 1 from rfl,
    run_bind, show (Functions.binary_logext 8 1).run state = .ok (1 : Int) state from rfl]
  dsimp only
  rw [show Functions.bits_of_int 1 48 = (1#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state immediate (1#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49, length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate]
  change (do
    let (result, resultFlags, undefined) ← Functions.gpr_add_spec_8 value (1#64) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (Sail.BitVec.zeroExtend result 128) 3
      (0#64) prefixes (rex true 0 destination)
      (Functions._get_modr_m_r_m (modRM 0 destination)) (3#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, calculated]
  dsimp only
  rw [run_bind, X86MovePrefix.write_operand_register64 state 0 destination (value + (1#64)) prefixes quiet]
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide), diagnostic_put]
  exact quiet

theorem dispatch (other : OtherOpcodeHandlers) (destination : Fin 16) (start immediate : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediate (X86LegacyFetch.packet (0x83#8))
      (rex true 0 destination) (0x83#8) (modRM 0 destination) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start immediate
        (X86LegacyFetch.packet (0x83#8)) (rex true 0 destination) (0x83#8) (modRM 0 destination) (0#8) := by
  fin_cases destination <;> rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (site : X86LegacyFetch.Window state (0x83#8) true 0 destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32)
    (advance : site.next.toInt + 1 = next.toInt)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (byte : state.mem.get? (site.next.signExtend 52).toNat = some (1#8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, Step state (X86Move.putPointer
      (X86Flags.putFlags (put state destination (value + 1)) (X86Flags.mergeFlags flags output)) next) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  simp only [Step]
  rw [X86LegacyFetch.Window.dispatches (0x83#8)
    ((X86LegacyFetch.checkOpcode_iff _).mp (by decide)) true state 0 destination site, dispatch]
  apply handler state destination site.address site.next next (X86LegacyFetch.packet (0x83#8)) site.attributes
    (site.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advance _ site.segments site.application site.rip known flagsKnown quiet byte
  apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
  have := site.step1
  have := site.step2
  have := site.step3
  omega

def code (destination : Fin 16) : List Nat :=
  [(rex true 0 destination).toNat,0x83,(modRM 0 destination).toNat,1]

def writes (destination : Fin 16) : Finset Register := {key destination,.rflags,.rip}

theorem writes_data (destination : Fin 16) : writes destination ⊆ dataRegisters := by
  intro register member
  simp only [writes, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact data_key destination
  · decide
  · decide

theorem result_frame (state : State) (destination : Fin 16) (value : Word) (flags : BitVec 32) (next : BitVec 48) :
    RegisterFrame (writes destination) state (X86Move.putPointer (X86Flags.putFlags (put state destination value) flags) next) := by
  exact (((put_frame state destination value).trans (flags_frame _ flags)).trans (pointer_frame _ next)).mono (by simp [writes])

structure Inputs (state : State) (destination : Fin 16) extends X86LegacyFetch.Basis state where
  value : Word
  flags : BitVec 32
  valueKnown : lookup state destination = some value
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 4 < (2 ^ 47 : Int)
  loaded : codeLoaded state address.toInt (code destination)

theorem executes_control (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (input : Inputs state destination) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧ lookup after destination = some (input.value + 1) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address input.address.toInt 4).signExtend 64) ∧
      X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let site := windowAt state state input.toBasis (RegisterFrame.refl dataRegisters state) input.upper 0 (by decide)
    (by simpa [address] using input.rip) (code destination) input.loaded 0 destination (0x83#8)
    (by rfl) (by rfl) (by rfl)
  let next := address input.address.toInt 4
  have at3 : site.next.toInt = input.address.toInt + 3 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 3 (by decide)
  have at4 : next.toInt = input.address.toInt + 4 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 4 (by decide)
  obtain ⟨output, run⟩ := fetched other vector state destination site next input.value input.flags (by omega)
    input.valueKnown input.flagsKnown input.quiet (input.loaded 3 1 (by rfl))
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination (input.value + 1)) flags) next
  refine ⟨after, flags, X86FuelPrefix.fetches_one state after run, result_frame _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [X86Move.lookup_putPointer, X86Flags.putFlags_gpr, lookup_put_same]
  · rw [(pointer_frame _ next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, next, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
  · unfold X86ControlFlags.Preserved
    have seen : after.regs.get? .rflags = some flags := by
      rw [(pointer_frame _ next).registers .rflags (by decide)]
      simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
    rw [seen,input.flagsKnown]
    simp only [Option.map_some,flags,X86ControlFlags.arithmetic_mask]


theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (input : Inputs state destination) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧ lookup after destination = some (input.value + 1) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address input.address.toInt 4).signExtend 64) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,read,rip,_control⟩ := executes_control other vector state destination input
  exact ⟨after,flags,run,frame,value,read,rip⟩


namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells (destination : Fin 16) : List (Nat × BitVec 8) :=
  (List.range 4).map fun index => (4096 + index, BitVec.ofNat 8 (((code destination)[index]?).getD 0))

private theorem distinct (destination : Fin 16) :
    (cells destination).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells destination).map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (destination : Fin 16) (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert (key destination) (cast (key_word destination).symm value)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells destination), (), 0, #[]⟩

private theorem image (destination : Fin 16) (value : Word) :
    codeLoaded (before destination value) 4096 (code destination) := by
  intro index byte present
  have within : index < 4 := (List.getElem?_eq_some_iff.mp present).1
  have point : ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells destination :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct destination) member

private def input (destination : Fin 16) (value : Word) : Inputs (before destination value) destination where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  fault := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  msrs := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  segments := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  rip := by fin_cases destination <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  value := value
  flags := 0x246#32
  valueKnown := by fin_cases destination <;> simp [lookup, before, key, Std.ExtDHashMap.get?_insert] <;> rfl
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  loaded := image destination value

theorem every_register (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (value : Word) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before destination value) = .ok () after ∧
      lookup after destination = some (value + 1) ∧ RegisterFrame (writes destination) (before destination value) after := by
  obtain ⟨after, _, run, framed, result, _⟩ := executes other vector _ destination (input destination value)
  exact ⟨after, run, result, framed⟩

theorem wraparound (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before 12 (0xffffffffffffffff#64)) = .ok () after ∧
      lookup after 12 = some (0#64) := by
  obtain ⟨after, run, result, _⟩ := every_register other vector 12 (0xffffffffffffffff#64)
  exact ⟨after, run, result⟩

theorem changed_destination : code 12 ≠ code 13 := by decide

private noncomputable def changed (destination : Fin 16) (value : Word) : State :=
  { before destination value with mem := (before destination value).mem.insert 4099 (2#8) }

theorem changed_immediate_rejected (destination : Fin 16) (value : Word) :
    ¬codeLoaded (changed destination value) 4096 (code destination) := by
  intro loaded
  have wrong := loaded 3 1 (by rfl)
  simp [changed, address] at wrong

end Controls
end Mettapedia.Machines.TIsa.X86RegisterIncrement
