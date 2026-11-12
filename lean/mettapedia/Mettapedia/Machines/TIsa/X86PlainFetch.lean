import Mettapedia.Machines.TIsa.X86LegacyFetch

/-!
# Full fetch and decode for opcodes without a ModRM byte

The profile checks the original prefix and ModRM tables. Both a bare opcode
and a REX/opcode pair are followed through the original scanner and dispatcher,
retaining architectural mode, code bytes and signed address geometry. The
handler result is not assumed. RET and POP controls are accepted; a ModRM MOV
and a REX byte treated as an opcode are refused.

Instruction effects, emitted-byte identity and program/ABI composition are
separate contracts. The theorem does not assign new instruction semantics.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86PlainFetch
open _root_.X86Registers X86RegisterRefinement X86PrefixRead
local instance : MemoryPrimitives := X86Memory.ordinary

/-- Architectural mode facts, independent of instruction length and RIP geometry. -/
structure Facts (state : State) where
  control : Vector (BitVec 64) 7
  attributes : Vector (BitVec 16) 6
  status : state.regs.get? .ms_reg = some false
  fault : state.regs.get? .fault_reg = some false
  msrs : state.regs.get? .msrs = some control
  segments : state.regs.get? .seg_hidden_attrs = some attributes
  longMode : Functions._get_ia32_eferbits_lma (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1)
  codeMode : Functions._get_code_segment_descriptor_attributesbits_l
    (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1)
  application : state.regs.get? .app_view = some true

def Facts.ofBasis {state : State} (origin : X86LegacyFetch.Basis state) : Facts state :=
  ⟨origin.control, origin.attributes, origin.status, origin.fault, origin.msrs, origin.segments,
    origin.longMode, origin.codeMode, origin.application⟩

def checkOpcode (opcode : BitVec 8) : Bool :=
  decide (Functions.get_one_byte_prefix_array_code opcode = 0) &&
    !(Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt opcode) (-4)) 4 == (0x4#4)) &&
    !(opcode == (0xc5#8)) && !(opcode == (0xc4#8)) && !(opcode == (0x62#8)) &&
    !(Functions.one_byte_opcode_modr_m_p .Mode_64bit opcode)

structure PlainOpcode (opcode : BitVec 8) : Prop where
  group : Functions.get_one_byte_prefix_array_code opcode = 0
  notRex : (Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt opcode) (-4)) 4 == (0x4#4)) = false
  notVex2 : (opcode == (0xc5#8)) = false
  notVex3 : (opcode == (0xc4#8)) = false
  notEvex : (opcode == (0x62#8)) = false
  modrm : Functions.one_byte_opcode_modr_m_p .Mode_64bit opcode = false

theorem checkOpcode_iff (opcode : BitVec 8) : checkOpcode opcode = true ↔ PlainOpcode opcode := by
  simp only [checkOpcode, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨group, notRex⟩, notVex2⟩, notVex3⟩, notEvex⟩, modrm⟩
    exact ⟨group, notRex, notVex2, notVex3, notEvex, modrm⟩
  · intro shape
    exact ⟨⟨⟨⟨⟨shape.group, shape.notRex⟩, shape.notVex2⟩, shape.notVex3⟩, shape.notEvex⟩, shape.modrm⟩

def packet (opcode : BitVec 8) (count : BitVec 4) : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) opcode) count

theorem packet_opcode : ∀ opcode : BitVec 8, ∀ count : BitVec 4, Functions._get_prefixes_nxt (packet opcode count) = opcode := by decide
theorem packet_count : ∀ opcode : BitVec 8, ∀ count : BitVec 4, Functions._get_prefixes_num (packet opcode count) = count := by decide
theorem packet_address : ∀ opcode : BitVec 8, ∀ count : BitVec 4, Functions._get_prefixes_adr (packet opcode count) = (0#8) := by decide
theorem packet_address_size (opcode : BitVec 8) (count : BitVec 4) :
    Functions.select_address_size .Mode_64bit (some (packet opcode count)) = (pure 8 : SailM Int) := by
  simp [Functions.select_address_size, Functions.in_64bit_mode, packet_address]

theorem opcode_stops_scan (opcode : BitVec 8) (shape : PlainOpcode opcode)
    (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (rex : BitVec 8) (count : Nat)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some opcode) :
    (Functions.get_prefixes .Mode_64bit address (0#52) rex (count + 1)).run state =
      .ok (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) opcode)
        (Functions.bits_of_int (15 - ((count + 1 : Nat) : Int)) 4), rex) state := by
  rw [X86Prefix.unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes opcode
    segments application rip present]
  dsimp only
  simp only [Functions.is_ext_prefix_byte, Bool.false_eq_true, ite_false,
    shape.group, Functions.in_64bit_mode, Bool.true_and, shape.notRex]
  rfl

theorem fetch_to_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : PlainOpcode opcode) (state : State) (start next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (advance : start.toInt + 1 = next.toInt)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true) (rip : state.regs.get? .rip = some (start.signExtend 64))
    (opcodeByte : state.mem.get? (start.signExtend 52).toNat = some opcode) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit start next (packet opcode (0#4)) (0#8) opcode (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state start rip]
  dsimp only
  change (do let decoded ← Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15; _ : SailM Unit).run state = _
  have scan := opcode_stops_scan opcode shape state start (start.signExtend 64) attributes (0#8) 14
    segments application rip opcodeByte
  change (Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15).run state =
    .ok (packet opcode (0#4), (0#8)) state at scan
  rw [run_bind, scan]
  dsimp only
  simp only [Functions.Mk_prefixes, packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit start (1#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state start (1#48) next (by simpa using advance)]
  dsimp only
  simp only [packet_opcode, shape.modrm, shape.notVex2, shape.notVex3, shape.notEvex,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rw [packet_address_size]
  rfl

theorem rex_then_opcode (opcode : BitVec 8) (shape : PlainOpcode opcode)
    (state : State) (address next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (destination : Fin 16)
    (sum : address.toInt + 1 = next.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (prefixByte : state.mem.get? (address.signExtend 52).toNat = some (X86RegisterEncoding.rex false 0 destination))
    (opcodeByte : state.mem.get? (next.signExtend 52).toNat = some opcode) :
    (Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15).run state =
      .ok (packet opcode (1#4), X86RegisterEncoding.rex false 0 destination) state := by
  rw [rex_advances_scan state address next pointer attributes false 0 destination (0#8) 14 sum
    (by decide) (by decide) segments application rip prefixByte]
  exact opcode_stops_scan opcode shape state next pointer attributes (X86RegisterEncoding.rex false 0 destination) 13
    segments application rip opcodeByte

theorem fetch_rex_to_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : PlainOpcode opcode) (state : State) (start opcodeAddress next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6) (destination : Fin 16)
    (advance : start.toInt + 1 = opcodeAddress.toInt) (finish : start.toInt + 2 = next.toInt)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true) (rip : state.regs.get? .rip = some (start.signExtend 64))
    (prefixByte : state.mem.get? (start.signExtend 52).toNat = some (X86RegisterEncoding.rex false 0 destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some opcode) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit start next (packet opcode (1#4))
        (X86RegisterEncoding.rex false 0 destination) opcode (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state start rip]
  dsimp only
  change (do let decoded ← Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15; _ : SailM Unit).run state = _
  rw [run_bind, rex_then_opcode opcode shape state start opcodeAddress (start.signExtend 64)
    attributes destination advance segments application rip prefixByte opcodeByte]
  dsimp only
  simp only [Functions.Mk_prefixes, packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit start (2#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state start (2#48) next (by simpa using finish)]
  dsimp only
  simp only [packet_opcode, shape.modrm, shape.notVex2, shape.notVex3, shape.notEvex,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rw [packet_address_size]
  rfl

namespace Controls
example : checkOpcode (0xc3#8) = true := by decide
example : checkOpcode (0x5b#8) = true := by decide
example : checkOpcode (0x5f#8) = true := by decide
example : checkOpcode (0x89#8) = false := by decide
example : checkOpcode (0x41#8) = false := by decide
end Controls

end Mettapedia.Machines.TIsa.X86PlainFetch

#print axioms Mettapedia.Machines.TIsa.X86PlainFetch.checkOpcode_iff
#print axioms Mettapedia.Machines.TIsa.X86PlainFetch.fetch_to_dispatch
#print axioms Mettapedia.Machines.TIsa.X86PlainFetch.fetch_rex_to_dispatch
