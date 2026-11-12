import Mettapedia.Machines.TIsa.X86InstructionFetch

/-!
# Reusable fetch/decode for regular register opcodes

The executable opcode check uses the pinned prefix and ModRM tables and
excludes REX/vector-prefix bytes. Its specification supplies the guards for
one shared fetch theorem. Arithmetic, comparison and MOV examples exercise
the profile; REX, VEX and a non-ModRM opcode are refused by this profile.
The theorem dispatches the actual imported fetch body and assumes no handler
correctness.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LegacyFetch

open _root_.X86Registers X86RegisterRefinement X86PrefixRead

def packet (opcode : BitVec 8) : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) opcode) (1#4)

theorem packet_opcode : ∀ opcode : BitVec 8, Functions._get_prefixes_nxt (packet opcode) = opcode := by
  decide

theorem packet_count : ∀ opcode : BitVec 8, Functions._get_prefixes_num (packet opcode) = (1#4) := by
  decide

theorem packet_address : ∀ opcode : BitVec 8, Functions._get_prefixes_adr (packet opcode) = (0#8) := by
  decide

theorem packet_segment : ∀ opcode : BitVec 8, Functions._get_prefixes_seg (packet opcode) = (0#8) := by
  decide

theorem packet_lock : ∀ opcode : BitVec 8, Functions._get_prefixes_lck (packet opcode) = (0#8) := by
  decide

theorem packet_address_size (opcode : BitVec 8) :
    Functions.select_address_size .Mode_64bit (some (packet opcode)) = (pure 8 : SailM Int) := by
  simp [Functions.select_address_size, Functions.in_64bit_mode, packet_address]

def checkOpcode (opcode : BitVec 8) : Bool :=
  decide (Functions.get_one_byte_prefix_array_code opcode = 0) &&
    !(Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt opcode) (-4)) 4 == (0x4#4)) &&
    !(opcode == (0xc5#8)) && !(opcode == (0xc4#8)) && !(opcode == (0x62#8)) &&
    Functions.one_byte_opcode_modr_m_p .Mode_64bit opcode

structure RegularOpcode (opcode : BitVec 8) : Prop where
  group : Functions.get_one_byte_prefix_array_code opcode = 0
  notRex : (Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt opcode) (-4)) 4 ==
    (0x4#4)) = false
  notVex2 : (opcode == (0xc5#8)) = false
  notVex3 : (opcode == (0xc4#8)) = false
  notEvex : (opcode == (0x62#8)) = false
  modrm : Functions.one_byte_opcode_modr_m_p .Mode_64bit opcode = true

theorem checkOpcode_iff (opcode : BitVec 8) : checkOpcode opcode = true ↔ RegularOpcode opcode := by
  simp only [checkOpcode, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨group, notRex⟩, notVex2⟩, notVex3⟩, notEvex⟩, modrm⟩
    exact ⟨group, notRex, notVex2, notVex3, notEvex, modrm⟩
  · intro shape
    exact ⟨⟨⟨⟨⟨shape.group, shape.notRex⟩, shape.notVex2⟩, shape.notVex3⟩, shape.notEvex⟩, shape.modrm⟩

/-- Architectural state and address geometry for a REX/opcode/ModRM instruction. -/
structure Basis (state : State) where
  address : BitVec 48
  opcodeAddress : BitVec 48
  modrmAddress : BitVec 48
  next : BitVec 48
  control : Vector (BitVec 64) 7
  attributes : Vector (BitVec 16) 6
  step1 : address.toInt + 1 = opcodeAddress.toInt
  step2 : address.toInt + 2 = modrmAddress.toInt
  step3 : modrmAddress.toInt + 1 = next.toInt
  status : state.regs.get? .ms_reg = some false
  fault : state.regs.get? .fault_reg = some false
  msrs : state.regs.get? .msrs = some control
  segments : state.regs.get? .seg_hidden_attrs = some attributes
  longMode : Functions._get_ia32_eferbits_lma
    (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1)
  codeMode : Functions._get_code_segment_descriptor_attributesbits_l
    (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1)
  application : state.regs.get? .app_view = some true
  rip : state.regs.get? .rip = some (address.signExtend 64)

/-- Input bytes and geometry; no execution property is included. -/
structure Window (state : State) (opcode : BitVec 8) (wide : Bool)
    (source destination : Fin 16) extends Basis state where
  prefixByte : state.mem.get? (address.signExtend 52).toNat =
    some (X86RegisterEncoding.rex wide source destination)
  opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some opcode
  modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat =
    some (X86RegisterEncoding.modRM source destination)

/-- Raw byte loading at the three architectural addresses in this profile. -/
def loaded (state : State) (address opcodeAddress modrmAddress : BitVec 48) : List Nat → Prop
  | [prefixByte, opcodeByte, modrmByte] =>
      state.mem.get? (address.signExtend 52).toNat = some (BitVec.ofNat 8 prefixByte) ∧
      state.mem.get? (opcodeAddress.signExtend 52).toNat = some (BitVec.ofNat 8 opcodeByte) ∧
      state.mem.get? (modrmAddress.signExtend 52).toNat = some (BitVec.ofNat 8 modrmByte)
  | _ => False

local instance : MemoryPrimitives := X86Memory.ordinary

theorem opcode_scan_stops (opcode : BitVec 8)
    (group : Functions.get_one_byte_prefix_array_code opcode = 0)
    (notRex : (Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt opcode) (-4)) 4 ==
      (0x4#4)) = false)
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
    group, Functions.in_64bit_mode, Bool.true_and, notRex]
  rfl

theorem grade_opcode_scan (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (rex : BitVec 8) (count : Nat)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (0xbf#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) rex (count + 1)).run state =
      .ok (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) (0xbf#8))
        (Functions.bits_of_int (15 - ((count + 1 : Nat) : Int)) 4), rex) state :=
  opcode_scan_stops (0xbf#8) (by decide) (by decide) state address pointer attributes rex count
    segments application rip present


theorem opcode_stops_scan (opcode : BitVec 8) (shape : RegularOpcode opcode)
    (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (rex : BitVec 8) (count : Nat)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some opcode) :
    (Functions.get_prefixes .Mode_64bit address (0#52) rex (count + 1)).run state =
      .ok (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) opcode)
        (Functions.bits_of_int (15 - ((count + 1 : Nat) : Int)) 4), rex) state :=
  opcode_scan_stops opcode shape.group shape.notRex state address pointer attributes rex count
    segments application rip present

theorem rex_then_opcode (opcode : BitVec 8) (shape : RegularOpcode opcode)
    (state : State) (address next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (wide : Bool) (source destination : Fin 16)
    (before : BitVec 8) (sum : address.toInt + 1 = next.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (opcodeByte : state.mem.get? (next.signExtend 52).toNat = some opcode) :
    (Functions.get_prefixes .Mode_64bit address (0#52) before 15).run state =
      .ok (packet opcode, X86RegisterEncoding.rex wide source destination) state := by
  rw [rex_advances_scan state address next pointer attributes wide source destination before 14 sum
    (by decide) (by decide) segments application rip prefixByte]
  exact opcode_stops_scan opcode shape state next pointer attributes
    (X86RegisterEncoding.rex wide source destination) 13 segments application rip opcodeByte

theorem fetch_to_dispatch_no_sib [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : RegularOpcode opcode) (wide : Bool)
    (state : State) (address opcodeAddress modrmAddress next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (source destination : Fin 16)
    (modrm : BitVec 8) (withoutSib : ∀ address16 : Bool, Functions.x86_decode_sib_p modrm address16 = false)
    (step1 : address.toInt + 1 = opcodeAddress.toInt)
    (step2 : address.toInt + 2 = modrmAddress.toInt)
    (step3 : modrmAddress.toInt + 1 = next.toInt)
    (status : state.regs.get? .ms_reg = some false)
    (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (address.signExtend 64))
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some opcode)
    (modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat = some modrm) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit address next (packet opcode)
        (X86RegisterEncoding.rex wide source destination) opcode
        modrm (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state address rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, rex_then_opcode opcode shape state address opcodeAddress
    (address.signExtend 64) attributes wide source destination (0#8) step1
    segments application rip prefixByte opcodeByte]
  dsimp only
  simp only [Functions.Mk_prefixes, packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit address (2#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state address (2#48) modrmAddress (by simpa using step2)]
  dsimp only
  simp only [packet_opcode, shape.modrm, shape.notVex2, shape.notVex3, shape.notEvex,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, ite_true, pure_bind]
  rw [packet_address_size]
  simp only [pure_bind, Functions.Mk_modr_m, bind_pure, Sail.BitVec.signExtend]
  have readModrm : (Functions.rme08 .Mode_64bit (Int.toNat (8 : Int))
      (modrmAddress.signExtend 64) none 1 ":X").run state =
        .ok modrm state := by
    exact X86EffectiveFetch.effective_read_exact state modrmAddress
      (address.signExtend 64) attributes modrm
      segments application rip modrmByte
  rw [run_bind, readModrm]
  dsimp only
  rw [run_bind, add_pointer_checked state modrmAddress (1#48) next (by simpa using step3)]
  dsimp only
  simp only [pure_bind, withoutSib, Bool.and_false, Bool.false_eq_true, ite_false,
    Functions.Mk_sib, bind_pure]

theorem fetch_to_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : RegularOpcode opcode) (wide : Bool)
    (state : State) (address opcodeAddress modrmAddress next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (source destination : Fin 16)
    (step1 : address.toInt + 1 = opcodeAddress.toInt)
    (step2 : address.toInt + 2 = modrmAddress.toInt)
    (step3 : modrmAddress.toInt + 1 = next.toInt)
    (status : state.regs.get? .ms_reg = some false)
    (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (address.signExtend 64))
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some opcode)
    (modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat =
      some (X86RegisterEncoding.modRM source destination)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit address next (packet opcode)
        (X86RegisterEncoding.rex wide source destination) opcode
        (X86RegisterEncoding.modRM source destination) (0#8)).run state :=
  fetch_to_dispatch_no_sib opcode shape wide state address opcodeAddress modrmAddress next control attributes
    source destination (X86RegisterEncoding.modRM source destination) (X86InstructionFetch.no_sib source destination)
    step1 step2 step3 status fault msrs segments longMode codeMode application rip prefixByte opcodeByte modrmByte

theorem Window.dispatches [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (opcode : BitVec 8) (shape : RegularOpcode opcode) (wide : Bool) (state : State)
    (source destination : Fin 16) (window : Window state opcode wide source destination) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit window.address window.next (packet opcode)
        (X86RegisterEncoding.rex wide source destination) opcode
        (X86RegisterEncoding.modRM source destination) (0#8)).run state :=
  fetch_to_dispatch opcode shape wide state window.address window.opcodeAddress window.modrmAddress
    window.next window.control window.attributes source destination window.step1 window.step2 window.step3
    window.status window.fault window.msrs window.segments window.longMode window.codeMode
    window.application window.rip window.prefixByte window.opcodeByte window.modrmByte

namespace Controls

example : checkOpcode (0x01#8) = true := by decide
example : checkOpcode (0x09#8) = true := by decide
example : checkOpcode (0x21#8) = true := by decide
example : checkOpcode (0x29#8) = true := by decide
example : checkOpcode (0x31#8) = true := by decide
example : checkOpcode (0x39#8) = true := by decide
example : checkOpcode (0x89#8) = true := by decide
example : checkOpcode (0x48#8) = false := by decide
example : checkOpcode (0xc4#8) = false := by decide
example : checkOpcode (0x90#8) = false := by decide

end Controls


end Mettapedia.Machines.TIsa.X86LegacyFetch

#print axioms Mettapedia.Machines.TIsa.X86LegacyFetch.opcode_scan_stops
#print axioms Mettapedia.Machines.TIsa.X86LegacyFetch.grade_opcode_scan
