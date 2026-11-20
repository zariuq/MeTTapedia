import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86PlainFetch

/-!
# Five-byte immediate moves into the low x86 registers

The prepared emitter uses a bare B8+r opcode when the value fits unsigned
32 bits and the physical destination is below eight. This is the
no-prefix counterpart of the checked extended-register template.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Mettapedia.Machines.TIsa.X86BareImmediate32

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def register (destination : Fin 8) : Fin 16 := ⟨destination.val, by have := destination.isLt; omega⟩

def opcode (destination : Fin 8) : BitVec 8 := .ofNat 8 (184 + destination.val)

def packet (destination : Fin 8) : BitVec 52 := X86PlainFetch.packet (opcode destination) 0

def code (destination : Fin 8) (value : BitVec 32) : List Nat :=
  (opcode destination).toNat :: (List.range 4).map (fun k => (value.extractLsb' (8 * k) 8).toNat)

private theorem decode_register (destination : Fin 8) :
    Functions.reg_index (Sail.BitVec.truncate ((7#8) &&& opcode destination) 3) (0#8) (0#2) =
      BitVec.ofNat 4 destination.val := by fin_cases destination <;> rfl

theorem handler (native : State) (destination : Fin 8) (start first finish : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (value : BitVec 32)
    (advance : first.toInt + 4 = finish.toInt)
    (instructionLength : Functions.check_instruction_length start finish (0#3) = none)
    (segments : native.regs.get? .seg_hidden_attrs = some attributes)
    (application : native.regs.get? .app_view = some true)
    (rip : native.regs.get? .rip = some (start.signExtend 64))
    (quiet : native.regs.get? .log_register_writes = some false)
    (present : ∀ k < 4,
      native.mem.get? ((address first.toInt k).signExtend 52).toNat =
        some (value.extractLsb' (8 * k) 8)) :
    (Functions.x86_mov_op_en_oi .Mode_64bit start first (packet destination)
      (0#8) (opcode destination) (0#8) (0#8)).run native =
        .ok () (X86Move.putPointer (put native (register destination) (value.zeroExtend 64)) finish) := by
  have upper : first.toInt + 4 ≤ (2^47 : Int) := by have := BitVec.toInt_lt (x := finish); omega
  have wide : (((176 : Int) ≤b Sail.BitVec.toNatInt (opcode destination)) &&
      ((Sail.BitVec.toNatInt (opcode destination) ≤b (183 : Int)) : Bool)) = false := by
    fin_cases destination <;> rfl
  have chosen : Functions.select_operand_size .Mode_64bit false (0#8) false
      (packet destination) false false false = (pure 4 : SailM Int) := by
    fin_cases destination <;> rfl
  unfold Functions.x86_mov_op_en_oi
  dsimp only
  rw [wide, chosen, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_address_size .Mode_64bit (some (packet destination)) =
    (pure 8 : SailM Int) from X86PlainFetch.packet_address_size _ _]
  simp only [pure_bind, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, X86FrameStore.read_dword native first (start.signExtend 64) attributes value
    upper segments application rip present]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked native first (4#48) finish (by simpa using advance)]
  dsimp only
  rw [instructionLength]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [decode_register]
  change (do
    Functions.wr32 (BitVec.ofNat 4 destination.val)
      (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32)
    Functions.write_iptr .Mode_64bit finish).run native = _
  have moved := wr32_exact native (register destination) value quiet
  change (Functions.wr32 (BitVec.ofNat 4 destination.val) value).run native =
    .ok () (put native (register destination) (value.zeroExtend 64)) at moved
  rw [X86OutcomeLoad.narrowed, run_bind, moved]
  exact X86Move.write_pointer64 _ finish ((put_other_register native (register destination)
    (value.zeroExtend 64) .log_register_writes (key_ne_diagnostic _)).trans quiet)

private theorem mov_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (destination : Fin 8) (start first : BitVec 48) :
    Functions.one_byte_opcode_execute .Mode_64bit start first (packet destination)
      (0#8) (opcode destination) (0#8) (0#8) =
    OtherOpcodeHandlers.x86_mov_op_en_oi .Mode_64bit start first (packet destination)
      (0#8) (opcode destination) (0#8) (0#8) := by
  fin_cases destination <;> rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (destination : Fin 8) (origin : X86LegacyFetch.Basis native)
    (finish : BitVec 48) (value : BitVec 32)
    (advance : origin.opcodeAddress.toInt + 4 = finish.toInt)
    (quiet : native.regs.get? .log_register_writes = some false)
    (opcodeByte : native.mem.get? (origin.address.signExtend 52).toNat = some (opcode destination))
    (present : ∀ k < 4,
      native.mem.get? ((address origin.opcodeAddress.toInt k).signExtend 52).toNat =
        some (value.extractLsb' (8 * k) 8)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run native =
      .ok () (X86Move.putPointer (put native (register destination) (value.zeroExtend 64)) finish) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86PlainFetch.PlainOpcode (opcode destination) := by
    apply (X86PlainFetch.checkOpcode_iff _).mp
    fin_cases destination <;> decide
  rw [X86PlainFetch.fetch_to_dispatch (opcode destination) shape native origin.address origin.opcodeAddress
    origin.control origin.attributes origin.step1 origin.status origin.fault origin.msrs origin.segments
    origin.longMode origin.codeMode origin.application origin.rip opcodeByte]
  change (Functions.one_byte_opcode_execute .Mode_64bit origin.address origin.opcodeAddress
    (packet destination) (0#8) (opcode destination) (0#8) (0#8)).run native = _
  rw [mov_dispatch]
  change (Functions.x86_mov_op_en_oi .Mode_64bit origin.address origin.opcodeAddress (packet destination)
    (0#8) (opcode destination) (0#8) (0#8)).run native = _
  apply handler native destination origin.address origin.opcodeAddress finish origin.attributes value advance
  · apply X86FrameLoad.length_from_distance _ _ 5 (by decide)
    have := origin.step1
    omega
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact quiet
  · exact present

end Mettapedia.Machines.TIsa.X86BareImmediate32
