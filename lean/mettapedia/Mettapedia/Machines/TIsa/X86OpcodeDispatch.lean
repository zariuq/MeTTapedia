import Mettapedia.Machines.TIsa.X86Move

/-!
# The MOV branch of the pinned Sail opcode dispatcher

The complete upstream one-byte dispatcher body is retained. Handlers outside
the imported fragment are ordinary function parameters, without correctness
laws or default implementations. The MOV and LOCK-fault theorems hold for
every choice of those parameters. Importing/linking the other handlers and
proving instruction fetch remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

namespace X86Registers

/-- The remaining upstream handler symbols, used only as function data. -/
class OtherOpcodeHandlers where
  two_byte_opcode_decode_and_execute (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (escape_byte : (BitVec 8)) : SailM Unit
  x86_add_adc_sub_sbb_or_and_xor_cmp_g_e (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_add_adc_sub_sbb_or_and_xor_cmp_test_rax_i (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_call_e8_op_en_m (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_call_ff_2_op_en_m (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cbw_cwd_cdqe (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cmc_clc_stc_cld_std (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cmps (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cwd_cdq_cqo (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_div (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_far_jmp_op_en_d (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_hlt (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_idiv (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_imul_op_en_m (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_imul_op_en_rmi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_inc_dec_4x (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_inc_dec_fe_ff (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_jrcxz (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_lahf (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_lea (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_leave (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_loop (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_op_en_fd (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_op_en_mi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_op_en_oi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_op_en_td (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movs (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movsx (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mul (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_near_jmp_op_en_d (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_near_jmp_op_en_m (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_not_neg_f6_f7 (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_one_byte_jcc (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_one_byte_nop (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_pop_ev (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_pop_general_register (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_popa (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_popf (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_push_ev (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_push_general_register (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_push_i (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_push_segment_register (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_pusha (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_pushf (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_ret (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_sahf (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_sal_sar_shl_shr_rcl_rcr_rol_ror (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_stos (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_xchg (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit

end X86Registers

noncomputable section
variable [X86Registers.MemoryPrimitives] [X86Registers.OtherOpcodeHandlers]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/OpcodeDispatch.lean.inc"
  sha256 "4eaa2eb5a7efc4479d620fefc75317caf64d95d0cc5aae127f2836999fb7f665"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end

namespace Mettapedia.Machines.TIsa.X86OpcodeDispatch

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
variable [MemoryPrimitives] [OtherOpcodeHandlers]

theorem move_register64 (mode : proc_mode) (start next : BitVec 48)
    (rex modrm sib : BitVec 8) :
    Functions.one_byte_opcode_execute mode start next (0#52) rex (137#8) modrm sib =
      Functions.x86_mov_op_en_mr mode start next (0#52) rex (137#8) modrm sib := by
  rfl

theorem register64_three_bytes (state : State) (address : Int)
    (source destination : Fin 16) (value : Word)
    (lower : -(2 ^ 47 : Int) ≤ address) (upper : address + 3 < (2 ^ 47 : Int))
    (present : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.one_byte_opcode_execute .Mode_64bit
      (BitVec.ofInt 48 address) (BitVec.ofInt 48 (address + 3)) (0#52)
      (rex true source destination) (137#8) (modRM source destination) (0#8)).run state =
        .ok () (X86Move.putPointer (put state destination value)
          (BitVec.ofInt 48 (address + 3))) := by
  rw [move_register64]
  exact X86Move.register64_three_bytes state source destination value address lower upper present quiet

theorem locked_move_refused (state : State) (mode : proc_mode) (start next : BitVec 48)
    (rex modrm sib : BitVec 8) :
    (Functions.one_byte_opcode_execute mode start next (0xf00#52) rex (137#8) modrm sib).run state =
      .error (.User (.Emsg "Fault: (:UD)")) state := by
  rfl

end Mettapedia.Machines.TIsa.X86OpcodeDispatch
