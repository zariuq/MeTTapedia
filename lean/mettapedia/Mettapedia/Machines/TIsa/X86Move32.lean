import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86BareFetch

/-!
# Original dword register MOV with optional REX

The source register is read at width 32 and the destination is zero extended.
The source and destination may alias; the MOV remains necessary in that case.
Both the bare and REX-prefixed emitted forms use the original decoder/handler.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Move32
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def bare (source destination : Fin 16) : Prop := source.val < 8 ∧ destination.val < 8
instance (source destination : Fin 16) : Decidable (bare source destination) :=
  inferInstanceAs (Decidable (source.val < 8 ∧ destination.val < 8))

def rex32 (source destination : Fin 16) : BitVec 8 :=
  if bare source destination then (0#8) else rex false source destination

theorem rex_w_zero : ∀ source destination : Fin 16, Functions.logbitp_bits 3 (rex32 source destination) = false := by decide

theorem decoded_source : ∀ source destination : Fin 16,
    Functions.reg_index (Functions._get_modr_m_reg (modRM source destination))
      (rex32 source destination) (2#2) = BitVec.ofNat 4 source.val := by decide

theorem decoded_destination : ∀ source destination : Fin 16,
    Functions.reg_index (Functions._get_modr_m_r_m (modRM source destination))
      (rex32 source destination) (0#2) = BitVec.ofNat 4 destination.val := by decide

theorem operand_size (source destination : Fin 16) (prefixes : BitVec 52)
    (ordinary : Functions._get_prefixes_opr prefixes = (0#8)) :
    Functions.select_operand_size .Mode_64bit false (rex32 source destination) false prefixes
      false false false = (pure 4 : SailM Int) := by
  simp [Functions.select_operand_size,Functions.in_64bit_mode,rex_w_zero,ordinary]

theorem write_action (source destination : Fin 16) (value : BitVec 32) (prefixes : BitVec 52) :
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3 (0#64) prefixes
      (rex32 source destination) (Functions._get_modr_m_r_m (modRM source destination)) (3#2) (0#8) =
      Functions.wr32 (BitVec.ofNat 4 destination.val) value := by
  have cut : Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32 = value := by
    change ((value.setWidth 128).setWidth 64).setWidth 32 = value
    rw [BitVec.setWidth_setWidth (by decide),BitVec.setWidth_setWidth (by decide),BitVec.setWidth_eq]
  change Functions.wr32
    (Functions.reg_index (Functions._get_modr_m_r_m (modRM source destination))
      (rex32 source destination) (0#2))
    (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32) = _
  rw [cut,decoded_destination]

theorem handler (state : State) (source destination : Fin 16) (value : Word)
    (start next : BitVec 48) (prefixes : BitVec 52)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (ordinary : Functions._get_prefixes_opr prefixes = (0#8))
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    (Functions.x86_mov_op_en_mr .Mode_64bit start next prefixes (rex32 source destination) (0x89#8)
      (modRM source destination) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination ((low32 value).zeroExtend 64)) next) := by
  unfold Functions.x86_mov_op_en_mr
  dsimp only
  rw [show ((0x89#8) == (0x88#8)) = false from rfl,operand_size source destination prefixes ordinary,
    run_bind,run_pure]
  dsimp only
  rw [decoded_source,show Functions.bits_of_int 4 4 = (4#4) from rfl,run_bind,
    X86DataStore.read_register32 state source value _ known]
  dsimp only
  rw [register_mode,if_pos (by decide : ((3#2) == (3#2)) = true),run_bind,run_pure]
  dsimp only
  rw [X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl,
    run_bind,X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [show Int.toNat (4 : Int) = 4 from rfl,X86DataStore.widen32,write_action]
  rw [run_bind,wr32_exact state destination (low32 value) quiet]
  apply X86Move.write_pointer64
  rw [diagnostic_put]
  exact quiet

theorem dispatch [OtherOpcodeHandlers] (mode : proc_mode) (start next : BitVec 48)
    (rexByte modrm sib : BitVec 8) (prefixCount : BitVec 4) :
    Functions.one_byte_opcode_execute mode start next (X86PlainFetch.packet (0x89#8) prefixCount)
      rexByte (0x89#8) modrm sib =
      Functions.x86_mov_op_en_mr mode start next (X86PlainFetch.packet (0x89#8) prefixCount)
        rexByte (0x89#8) modrm sib := by
  have lock : Functions._get_prefixes_lck (X86PlainFetch.packet (0x89#8) prefixCount) = (0#8) := by
    revert prefixCount
    decide
  change (do
    if ((0xf0#8) == Functions._get_prefixes_lck (X86PlainFetch.packet (0x89#8) prefixCount))
      then Functions.x86_fault "(:UD)" else pure ()
    Functions.x86_mov_op_en_mr mode start next (X86PlainFetch.packet (0x89#8) prefixCount)
      rexByte (0x89#8) modrm sib) = _
  rw [lock]
  rfl

theorem packet_rex : ∀ opcode : BitVec 8,
    X86LegacyFetch.packet opcode = X86PlainFetch.packet opcode (1#4) := by decide

theorem fetched_bare (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16) (value : Word) (low : bare source destination)
    (origin : X86BareFetch.Window state (0x89#8) (modRM source destination))
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination ((low32 value).zeroExtend 64)) origin.next) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  rw [X86BareFetch.fetch_to_dispatch (0x89#8) ((X86LegacyFetch.checkOpcode_iff _).mp (by decide))
    state _ origin (X86InstructionFetch.no_sib source destination),dispatch]
  have length : Functions.check_instruction_length origin.address origin.next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 2 (by decide)
    have := origin.step1
    have := origin.step2
    omega
  have run := handler state source destination value origin.address origin.next
    (X86PlainFetch.packet (0x89#8) (0#4)) (by decide) (X86PlainFetch.packet_address _ _)
    (by decide) known quiet length
  simpa only [rex32,if_pos low] using run

theorem fetched_rex (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16) (value : Word) (high : ¬bare source destination)
    (origin : X86LegacyFetch.Window state (0x89#8) false source destination)
    (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination ((low32 value).zeroExtend 64)) origin.next) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (0x89#8) ((X86LegacyFetch.checkOpcode_iff _).mp (by decide))
    false state source destination origin]
  have selected := dispatch .Mode_64bit origin.address origin.next (rex false source destination)
    (modRM source destination) (0#8) (1#4)
  change Functions.one_byte_opcode_execute .Mode_64bit origin.address origin.next (X86LegacyFetch.packet (0x89#8))
    (rex false source destination) (0x89#8) (modRM source destination) (0#8) = _ at selected
  rw [selected]
  have length : Functions.check_instruction_length origin.address origin.next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 3 (by decide)
    have := origin.step3
    have := origin.step2
    omega
  have run := handler state source destination value origin.address origin.next (X86LegacyFetch.packet (0x89#8))
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) (by decide) known quiet length
  rw [packet_rex] at run
  simpa only [rex32,if_neg high] using run

theorem result_frame (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) :
    RegisterFrame {key destination,.rip} state
      (X86Move.putPointer (put state destination ((low32 value).zeroExtend 64)) next) := by
  exact ((put_frame state destination ((low32 value).zeroExtend 64)).trans
    (pointer_frame _ next)).mono (by simp)

#print axioms handler
#print axioms fetched_bare
#print axioms fetched_rex
#print axioms result_frame
end Mettapedia.Machines.TIsa.X86Move32
