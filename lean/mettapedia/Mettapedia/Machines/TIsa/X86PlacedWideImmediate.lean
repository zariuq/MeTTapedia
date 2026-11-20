import Mettapedia.Machines.TIsa.X86PlacedScalar

/-! # Fetched qword immediates at a placed instruction

A REX.W immediate supplies a complete destination word and preserves
the other registers, flags, and memory. The eight immediate bytes are
decoded by the ordinary instruction reader.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 650000

namespace Mettapedia.Machines.TIsa.X86PlacedWideImmediate

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86Immediate32 (opcode packet writes)
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (destination : Fin 16) (value : Word) : List Nat :=
  [(rex true 0 destination).toNat, (opcode destination).toNat] ++
    (List.range 8).map fun index => (value.extractLsb' (8 * index) 8).toNat

private theorem reads_immediate (state : State) (atByte : BitVec 48) (origin : X86LegacyFetch.Basis state)
    (value : Word) (upper : atByte.toInt + 8 ≤ (2^47 : Int))
    (present : ∀ index < 8, state.mem.get? ((address atByte.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)) :
    (Functions.rme_size .Mode_64bit 8 8 (atByte.signExtend 64) none 1 ":X" false false).run state =
      .ok (value.zeroExtend 128) state := by
  have access : Functions.check_linear_memory_access .Mode_64bit 8 8
      (atByte.signExtend 64) none 1 ":X" false false = (pure () : SailM Unit) := rfl
  have linear : (Functions.ea_to_la .Mode_64bit (atByte.signExtend 64) 1 8).run state =
      .ok (atByte.signExtend 64) state := X86EffectiveFetch.code_linear_address state atByte
  have raw := X86ReadWords.rb_word_exact state atByte _ value ":X" upper origin.application origin.rip present
  have load : (Functions.load_bytes_from_ea .Mode_64bit 8 8 (atByte.signExtend 64) none 1 ":X" false false).run state =
      (Functions.rb 8 (atByte.signExtend 64) ":X").run state := by
    unfold Functions.load_bytes_from_ea
    rw [run_bind, readRegister_exact, origin.segments]
    dsimp only
    change (do
      let addr ← Functions.ea_to_la .Mode_64bit (atByte.signExtend 64) 1 8
      Functions.check_linear_memory_access .Mode_64bit 8 8 addr none 1 ":X" false false
      Functions.rb 8 addr ":X" : SailM Word).run state = _
    rw [run_bind, linear]
    dsimp only
    rw [access]
    rfl
  unfold Functions.rme_size
  rw [run_bind, load, raw]
  rfl

private theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (value : Word) (advance : origin.modrmAddress.toInt + 8 = finish.toInt)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true 0 destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (opcode destination))
    (present : ∀ index < 8, state.mem.get? ((address origin.modrmAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    Step state (X86Move.putPointer (put state destination value) finish) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have opcodePlain : X86PlainFetch.PlainOpcode (opcode destination) :=
    (X86PlainFetch.checkOpcode_iff _).mp (by fin_cases destination <;> decide)
  have prefixScan : (Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15).run state =
      .ok (packet destination, rex true 0 destination) state := by
    rw [X86PrefixRead.rex_advances_scan state origin.address origin.opcodeAddress _ origin.attributes true 0 destination
      (0#8) 14 origin.step1 (by decide) (by decide) origin.segments origin.application origin.rip prefixByte]
    exact X86PlainFetch.opcode_stops_scan _ opcodePlain state origin.opcodeAddress _ origin.attributes
      (rex true 0 destination) 13 origin.segments origin.application origin.rip opcodeByte
  have dispatch : (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.x86_mov_op_en_oi .Mode_64bit origin.address origin.modrmAddress (packet destination)
        (rex true 0 destination) (opcode destination) (0#8) (0#8)).run state := by
    unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
    rw [run_bind, readRegister_exact, origin.status]
    dsimp only
    rw [run_bind, readRegister_exact, origin.fault]
    dsimp only
    change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
    rw [run_bind, X86InstructionFetch.operation_mode64 state origin.control origin.attributes origin.msrs
      origin.segments origin.longMode origin.codeMode]
    dsimp only
    rw [run_bind, X86InstructionFetch.read_pointer64 state origin.address origin.rip]
    dsimp only
    change (do let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15; _ : SailM Unit).run state = _
    rw [run_bind, prefixScan]
    dsimp only
    simp only [Functions.Mk_prefixes, packet, X86LegacyFetch.packet_count]
    change (do let next ← Functions.add_to_iptr .Mode_64bit origin.address (2#48); _ : SailM Unit).run state = _
    rw [run_bind, X86PrefixRead.add_pointer_checked state origin.address (2#48) origin.modrmAddress (by simpa using origin.step2)]
    dsimp only
    simp only [X86LegacyFetch.packet_opcode, opcodePlain.modrm, opcodePlain.notVex2, opcodePlain.notVex3, opcodePlain.notEvex,
      Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
    rw [X86LegacyFetch.packet_address_size]
    simp only [pure_bind, Bool.false_eq_true, ite_false]
    have move := X86OpcodeDispatch.immediate_dword_guarded .Mode_64bit origin.address origin.modrmAddress
      (X86LegacyFetch.packet (opcode destination)) (rex true 0 destination) (0#8) (0#8)
      (⟨destination.val % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
    change Functions.one_byte_opcode_execute .Mode_64bit origin.address origin.modrmAddress
      (X86LegacyFetch.packet (opcode destination)) (rex true 0 destination) (opcode destination) (0#8) (0#8) = _ at move
    rw [move, X86LegacyFetch.packet_lock]
    rfl
  have notByte : (((176 : Int) ≤b Sail.BitVec.toNatInt (opcode destination)) &&
      (Sail.BitVec.toNatInt (opcode destination) ≤b (183 : Int))) = false := by
    fin_cases destination <;> rfl
  have length : Functions.check_instruction_length origin.address finish (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 10 (by decide)
    have := origin.step2
    omega
  have encoded : Functions.reg_index (Sail.BitVec.truncate ((7#8) &&& opcode destination) 3)
      (rex true 0 destination) (0#2) = .ofNat 4 destination.val := by fin_cases destination <;> rfl
  have wordRead := reads_immediate state origin.modrmAddress origin value (by
    rw [advance]
    exact (BitVec.toInt_lt (x := finish)).le) present
  rw [Step, dispatch]
  unfold Functions.x86_mov_op_en_oi
  dsimp only
  rw [notByte, X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_address_size .Mode_64bit (some (packet destination)) = (pure 8 : SailM Int) from
    X86LegacyFetch.packet_address_size _]
  simp only [pure_bind, show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, wordRead]
  dsimp only
  rw [show Functions.bits_of_int 8 48 = (8#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state origin.modrmAddress (8#48) finish (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false, encoded]
  have narrow : Sail.BitVec.truncate (value.zeroExtend 128) 64 = value := by simp [Sail.BitVec.truncate]
  have written : (Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value (rex true 0 destination)).run state =
      .ok () (put state destination value) := by
    have range : destination.val < 2^4 := destination.isLt
    simpa [Functions.write_rgfi_size, Functions.eq_bits_nat, Functions.wr64, Sail.BitVec.toNatInt,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt range] using write_rgfi_exact state destination value quiet
  rw [narrow, show Functions.bits_of_int 8 4 = (8#4) from rfl, run_bind, written]
  exact X86Move.write_pointer64 _ finish (by simpa only [diagnostic_put] using quiet)

theorem materializes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start + 10 ≤ image.size)
    (destination : Fin 16) (value : Word) (code : Code image start (bytes destination value)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame (writes destination) state after ∧
      lookup after destination = some value ∧ Nonempty (At image after base (start + 10)) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let finish := address base.toInt (start + 10)
  have advance : origin.modrmAddress.toInt + 8 = finish.toInt := by
    change (address base.toInt (start + 2)).toInt + 8 = (address base.toInt (start + 10)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have read (index word : Nat) (encoded : (bytes destination value)[index]? = some word) :
      state.mem.get? ((address base.toInt (start + index)).signExtend 52).toNat = some (BitVec.ofNat 8 word) := by
    have got := point.bytes start (by omega) _ code index word encoded
    rwa [point.relative_address start index (by omega)] at got
  have rexRead : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true 0 destination) := by
    simpa only [origin, At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      read 0 (rex true 0 destination).toNat rfl
  have opcodeRead : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (opcode destination) := by
    simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using read 1 (opcode destination).toNat rfl
  have immediate : ∀ index < 8, state.mem.get? ((address origin.modrmAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8) := by
    intro index fit
    change state.mem.get? ((address (address base.toInt (start + 2)).toInt index).signExtend 52).toNat = _
    rw [point.relative_address (start + 2) index (by omega), Nat.add_assoc]
    have valueRead := read (2 + index) (value.extractLsb' (8 * index) 8).toNat (by interval_cases index <;> rfl)
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using valueRead
  let after := X86Move.putPointer (put state destination value) finish
  have ran := fetched other vector state destination origin finish value advance point.quiet rexRead opcodeRead immediate
  have frame : RegisterFrame (writes destination) state after :=
    ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by simp [writes])
  have flags : ∀ reg : Fin 16, Register.rflags ∉ writes reg := by decide
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame, by
    simp only [after, X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance frame (X86Immediate32.writes_data _) (X86FuelPrefix.pointer_rip _ _) point.flags
      ((frame.registers .rflags (flags _)).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedWideImmediate
