import Mettapedia.Machines.TIsa.X86NearBranch

/-!
# Original two-byte dispatch for admitted conditional branches

The complete generated dispatcher and decoder bodies are retained, together
with the mandatory-prefix and ModRM lookup functions. Remaining instruction
handlers are ordinary function data without laws or implementations. The
conditional-branch selection proof holds for every such handler assignment.
The decoder reads the actual second opcode byte and advances its internal
pointer before entering the original near-branch handler.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace X86Registers
class OtherTwoByteHandlers where
  chk_exc_fn (decode_context : String) (type_id : String) (feature_flags : (List String)) (proc_mode : proc_mode) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_bt_0f_a3 (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_bt_0f_ba (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cmovcc (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_cmpxchg (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_imul_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_lgdt (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_lidt (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_lldt (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_mov_control_regs_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movaps_movapd_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movaps_movapd_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movd_movq_from_xmm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movd_movq_to_xmm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movhps_movhpd_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movhps_movhpd_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movlps_movlpd_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movlps_movlpd_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movss_movsd_op_en_mr (sp_dp : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movss_movsd_op_en_rm (sp_dp : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movsxd (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movups_movupd_movdqu_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movups_movupd_movdqu_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_movzx (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_setcc (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_shld_shrd (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_shufpd_op_en_rmi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_shufps_op_en_rmi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_syscall_both_views (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_sysret (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_two_byte_nop (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_unpck?pd_op_en_rm (high_low : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
  x86_unpck?ps_op_en_rm (high_low : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit
end X86Registers

noncomputable section
variable [X86Registers.MemoryPrimitives] [X86Registers.OtherOpcodeHandlers] [X86Registers.OtherTwoByteHandlers]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/TwoByteDispatchFunctions.lean.inc"
  sha256 "4f8413388e634c205bad81d2808a944772e10cf91e2f22773bbb78d50bd25ebc"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end


namespace Mettapedia.Machines.TIsa.X86TwoByteDispatch

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

def escapePacket : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) (0x0f#8)) (0#4)

theorem mandatory_zero (condition : X86BranchCondition.Condition) :
    Functions.compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit
      (X86BranchCondition.opcode condition) escapePacket = (0#8) := by
  cases condition <;> rfl

theorem no_modrm (condition : X86BranchCondition.Condition) :
    Functions.two_byte_opcode_modr_m_p .Mode_64bit (0#8)
      (X86BranchCondition.opcode condition) = false := by
  cases condition <;> rfl

variable [OtherOpcodeHandlers] [OtherTwoByteHandlers]

theorem selection [MemoryPrimitives] (condition : X86BranchCondition.Condition)
    (start base : BitVec 48) (rex : BitVec 8) :
    Functions.two_byte_opcode_execute .Mode_64bit start base escapePacket (0#8) rex
      (X86BranchCondition.opcode condition) (0#8) (0#8) =
      Functions.x86_two_byte_jcc .Mode_64bit start base escapePacket rex
        (X86BranchCondition.opcode condition) (0#8) (0#8) := by
  cases condition <;> rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem decode_to_branch (condition : X86BranchCondition.Condition) (state : State)
    (start opcodeAddress base : BitVec 48) (rex : BitVec 8)
    (attributes : Vector (BitVec 16) 6) (pointer : Word)
    (advance : opcodeAddress.toInt + 1 = base.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (opcodeAddress.signExtend 52).toNat =
      some (X86BranchCondition.opcode condition)) :
    (Functions.two_byte_opcode_decode_and_execute .Mode_64bit start opcodeAddress escapePacket rex (0x0f#8)).run state =
      (Functions.x86_two_byte_jcc .Mode_64bit start base escapePacket rex
        (X86BranchCondition.opcode condition) (0#8) (0#8)).run state := by
  have addressSize : Functions.select_address_size .Mode_64bit (some escapePacket) = (pure 8 : SailM Int) := rfl
  unfold Functions.two_byte_opcode_decode_and_execute
  rw [addressSize]
  simp only [pure_bind]
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    show Sail.BitVec.signExtend opcodeAddress 64 = opcodeAddress.signExtend 64 from rfl,
    run_bind, X86EffectiveFetch.effective_read_exact state opcodeAddress pointer attributes
      (X86BranchCondition.opcode condition) segments application rip present]
  dsimp only
  rw [run_bind, X86PrefixRead.add_pointer_checked state opcodeAddress (1#48) base (by simpa using advance)]
  dsimp only
  rw [mandatory_zero, no_modrm]
  simp only [Bool.false_eq_true, ite_false, pure_bind,
    Functions.Mk_modr_m, Functions.Mk_sib, Bool.false_and]
  rw [selection]

theorem decode_register
    (state : State) (start opcodeAddress modrmAddress finish : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (rex opcode modrm : BitVec 8)
    (step1 : opcodeAddress.toInt + 1 = modrmAddress.toInt) (step2 : modrmAddress.toInt + 1 = finish.toInt)
    (mandatory : Functions.compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit opcode
      (X86LegacyFetch.packet (0x0f#8)) = (0#8))
    (hasModrm : Functions.two_byte_opcode_modr_m_p .Mode_64bit (0#8) opcode = true)
    (noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p modrm address16 = false)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some opcode)
    (modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat = some modrm) :
    (Functions.two_byte_opcode_decode_and_execute .Mode_64bit start opcodeAddress
      (X86LegacyFetch.packet (0x0f#8)) rex (0x0f#8)).run state =
      (Functions.two_byte_opcode_execute .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
        (0#8) rex opcode modrm (0#8)).run state := by
  have addressSize := X86LegacyFetch.packet_address_size (0x0f#8)
  unfold Functions.two_byte_opcode_decode_and_execute
  rw [addressSize]
  simp only [pure_bind]
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    show Sail.BitVec.signExtend opcodeAddress 64 = opcodeAddress.signExtend 64 from rfl,
    run_bind, X86EffectiveFetch.effective_read_exact state opcodeAddress pointer attributes opcode
      segments application rip opcodeByte]
  dsimp only
  rw [run_bind, X86PrefixRead.add_pointer_checked state opcodeAddress (1#48) modrmAddress (by simpa using step1)]
  dsimp only
  rw [mandatory, hasModrm]
  simp only [ite_true]
  simp only [show Sail.BitVec.signExtend modrmAddress 64 = modrmAddress.signExtend 64 from rfl]
  rw [run_bind, run_bind, X86EffectiveFetch.effective_read_exact state modrmAddress pointer attributes modrm
    segments application rip modrmByte]
  dsimp only
  simp only [Functions.Mk_modr_m, run_pure]
  rw [run_bind, X86PrefixRead.add_pointer_checked state modrmAddress (1#48) finish (by simpa using step2)]
  dsimp only
  simp only [pure_bind, noSib, Bool.and_false, Bool.false_eq_true, ite_false, Functions.Mk_sib]

set_option maxRecDepth 8192 in
theorem select_sete (start finish : BitVec 48) :
    Functions.two_byte_opcode_execute .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
      (0#8) (0x41#8) (0x94#8) (0xc3#8) (0#8) =
      OtherTwoByteHandlers.x86_setcc .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
        (0x41#8) (0x94#8) (0xc3#8) (0#8) := by rfl

set_option maxRecDepth 8192 in
theorem select_movzx (start finish : BitVec 48) :
    Functions.two_byte_opcode_execute .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
      (0#8) (0x45#8) (0xb6#8) (0xdb#8) (0#8) =
      OtherTwoByteHandlers.x86_movzx .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
        (0x45#8) (0xb6#8) (0xdb#8) (0#8) := by rfl

end Mettapedia.Machines.TIsa.X86TwoByteDispatch

#print axioms Mettapedia.Machines.TIsa.X86TwoByteDispatch.decode_to_branch
