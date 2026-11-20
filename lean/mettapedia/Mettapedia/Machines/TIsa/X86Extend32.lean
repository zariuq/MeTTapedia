import Mettapedia.Machines.TIsa.X86Move32

/-!
# Original register MOVSXD at opcode 63

The pinned model names this handler x86_movsx. It reads the low 32 bits,
checks length, sign extends into the destination and advances RIP. The full
original definition is retained; unrelated handlers remain explicit parameters.
-/

set_option autoImplicit false
section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/Extend32Functions.lean.inc"
  sha256 "3423aab2b32eb459d2748b624e3a2e621fdc6a8e3a525d255855a70bae55a898"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86Extend32
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem operand_size (destination source : Fin 16) (prefixes : BitVec 52) :
    Functions.select_operand_size .Mode_64bit false (rex true destination source) true prefixes
      false false false = (pure 4 : SailM Int) := by
  simp [Functions.select_operand_size,Functions.in_64bit_mode,operand_width]

theorem operand_register (state : State) (destination source : Fin 16) (value : Word)
    (prefixes : BitVec 52) (pointer : BitVec 48) (known : lookup state source = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 4 true false 3 prefixes pointer
      (rex true destination source) (Functions._get_modr_m_r_m (modRM destination source))
      (3#2) (0#8) (0#3)).run state =
        .ok ((low32 value).zeroExtend 128,(0 : Int),(0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl,ite_true,pure_bind]
  rw [show Functions.bits_of_int ((4 : Nat) : Int) 4 = (4#4) from rfl,destination_register]
  rw [run_bind,run_bind,X86DataStore.read_register32 state source value _ known]
  simp only [X86DataStore.widen32]
  rfl

theorem write_register64 (state : State) (destination : Fin 16) (value : Word) (rexByte : BitVec 8)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value rexByte).run state =
      .ok () (put state destination value) := by
  have action : Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value rexByte =
      Functions.write_rgfi (Sail.BitVec.toNatInt (BitVec.ofNat 4 destination.val)) value := rfl
  rw [action]
  have index : Sail.BitVec.toNatInt (BitVec.ofNat 4 destination.val) = (destination.val : Int) := by
    simp [Sail.BitVec.toNatInt]
  rw [index]
  exact write_rgfi_exact state destination value quiet

theorem handler (state : State) (source destination : Fin 16) (value : Word)
    (start next : BitVec 48) (prefixes : BitVec 52)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_movsx .Mode_64bit start next prefixes (rex true destination source) (0x63#8)
      (modRM destination source) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination ((low32 value).signExtend 64)) next) := by
  unfold Functions.x86_movsx
  dsimp only
  rw [operand_size,run_bind,run_pure]
  dsimp only
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (4 : Int) = 4 from rfl,run_bind,
    operand_register state destination source value prefixes next known]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl,
    run_bind,X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false,
    operand_width,ite_true,show ((8 : Int) == 8) = true from rfl,X86DataStore.cut32]
  have widened : Sail.BitVec.truncate
      (Sail.BitVec.zeroExtend (Sail.BitVec.signExtend (low32 value) 64) 128) 64 =
        (low32 value).signExtend 64 := X86Move.widen_truncate ((low32 value).signExtend 64)
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl,source_register,widened,run_bind,
    write_register64 state destination ((low32 value).signExtend 64) _ quiet]
  apply X86Move.write_pointer64
  rw [diagnostic_put]
  exact quiet

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_movsx := Functions.x86_movsx }

theorem dispatch_original [OtherOpcodeHandlers] (start next : BitVec 48) (rexByte modrm sib : BitVec 8) :
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x63#8))
      rexByte (0x63#8) modrm sib =
      OtherOpcodeHandlers.x86_movsx .Mode_64bit start next (X86LegacyFetch.packet (0x63#8))
        rexByte (0x63#8) modrm sib := by rfl

theorem dispatch_linked (other : OtherOpcodeHandlers) (start next : BitVec 48) (rexByte modrm sib : BitVec 8) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x63#8))
      rexByte (0x63#8) modrm sib =
      Functions.x86_movsx .Mode_64bit start next (X86LegacyFetch.packet (0x63#8))
        rexByte (0x63#8) modrm sib := by
  let : OtherOpcodeHandlers := linkedHandlers other
  exact dispatch_original start next rexByte modrm sib

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16) (value : Word)
    (origin : X86LegacyFetch.Window state (0x63#8) true destination source)
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination ((low32 value).signExtend 64)) origin.next) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (0x63#8) ((X86LegacyFetch.checkOpcode_iff _).mp (by decide))
    true state destination source origin,dispatch_linked other]
  apply handler state source destination value origin.address origin.next (X86LegacyFetch.packet (0x63#8))
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) known quiet
  apply X86FrameLoad.length_from_distance _ _ 3 (by decide)
  have := origin.step2
  have := origin.step3
  omega

theorem result_frame (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) :
    RegisterFrame {key destination,.rip} state
      (X86Move.putPointer (put state destination ((low32 value).signExtend 64)) next) := by
  exact ((put_frame state destination ((low32 value).signExtend 64)).trans
    (pointer_frame _ next)).mono (by simp)

#print axioms handler
#print axioms fetched
#print axioms result_frame
end Mettapedia.Machines.TIsa.X86Extend32
