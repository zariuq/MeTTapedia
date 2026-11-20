import Mettapedia.Machines.TIsa.X86PlainFetch
import Mettapedia.Machines.TIsa.X86LegacyFetch

/-!
# Original regular ModRM fetch without a REX prefix

The opcode starts at RIP. The original prefix scanner, ModRM read and
dispatcher are retained. Address geometry and mode facts contain no assumed
execution property. The profile is useful for emitted narrow instructions.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BareFetch
open _root_.X86Registers X86RegisterRefinement X86PrefixRead
local instance : MemoryPrimitives := X86Memory.ordinary

structure Window (state : State) (opcode modrm : BitVec 8) extends X86PlainFetch.Facts state where
  address : BitVec 48
  modrmAddress : BitVec 48
  next : BitVec 48
  step1 : address.toInt + 1 = modrmAddress.toInt
  step2 : modrmAddress.toInt + 1 = next.toInt
  rip : state.regs.get? .rip = some (address.signExtend 64)
  opcodeByte : state.mem.get? (address.signExtend 52).toNat = some opcode
  modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat = some modrm

theorem fetch_to_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : X86LegacyFetch.RegularOpcode opcode) (state : State) (modrm : BitVec 8)
    (origin : Window state opcode modrm)
    (withoutSib : ∀ address16 : Bool, Functions.x86_decode_sib_p modrm address16 = false) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit origin.address origin.next
        (X86PlainFetch.packet opcode (0#4)) (0#8) opcode modrm (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind,readRegister_exact,origin.status]
  dsimp only
  rw [run_bind,readRegister_exact,origin.fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind,X86InstructionFetch.operation_mode64 state origin.control origin.attributes
    origin.msrs origin.segments origin.longMode origin.codeMode]
  dsimp only
  rw [run_bind,X86InstructionFetch.read_pointer64 state origin.address origin.rip]
  dsimp only
  change (do let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15
             _ : SailM Unit).run state = _
  have scan := X86LegacyFetch.opcode_stops_scan opcode shape state origin.address
    (origin.address.signExtend 64) origin.attributes (0#8) 14 origin.segments origin.application
    origin.rip origin.opcodeByte
  change (Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15).run state =
    .ok (X86PlainFetch.packet opcode (0#4),(0#8)) state at scan
  rw [run_bind,scan]
  dsimp only
  simp only [Functions.Mk_prefixes,X86PlainFetch.packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit origin.address (1#48)
             _ : SailM Unit).run state = _
  rw [run_bind,add_pointer_checked state origin.address (1#48) origin.modrmAddress (by simpa using origin.step1)]
  dsimp only
  simp only [X86PlainFetch.packet_opcode,shape.modrm,shape.notVex2,shape.notVex3,shape.notEvex,
    Bool.false_or,Bool.false_and,Bool.false_eq_true,ite_false,ite_true,pure_bind]
  rw [X86PlainFetch.packet_address_size]
  simp only [pure_bind,Functions.Mk_modr_m,bind_pure,Sail.BitVec.signExtend]
  have readModrm : (Functions.rme08 .Mode_64bit (Int.toNat (8 : Int))
      (origin.modrmAddress.signExtend 64) none 1 ":X").run state = .ok modrm state :=
    X86EffectiveFetch.effective_read_exact state origin.modrmAddress (origin.address.signExtend 64)
      origin.attributes modrm origin.segments origin.application origin.rip origin.modrmByte
  rw [run_bind,readModrm]
  dsimp only
  rw [run_bind,add_pointer_checked state origin.modrmAddress (1#48) origin.next (by simpa using origin.step2)]
  dsimp only
  simp only [pure_bind,withoutSib,Bool.and_false,Bool.false_eq_true,ite_false,Functions.Mk_sib,bind_pure]

#print axioms fetch_to_dispatch
end Mettapedia.Machines.TIsa.X86BareFetch
