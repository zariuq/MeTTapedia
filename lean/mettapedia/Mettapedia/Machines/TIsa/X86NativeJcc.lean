import Mettapedia.Machines.TIsa.X86EscapeFetch
import Mettapedia.Machines.TIsa.X86PlainFetch

/-!
# Near control transfers for prepared comparisons

The ordinary unsigned and equality cases use the existing condition
proofs. Signed greater-or-equal reads sign and overflow from the same
RFLAGS word. Both cases use the same fetched rel32 handler.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86NativeJcc

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86TwoByteDispatch (escapePacket)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Condition where
  | ordinary (code : X86BranchCondition.Condition)
  | belowEqual
  | signedLT | signedGE | signedLE | signedGT
  deriving DecidableEq

def opcode : Condition → BitVec 8
  | .ordinary code => X86BranchCondition.opcode code
  | .belowEqual => 0x86
  | .signedLT => 0x8c
  | .signedGE => 0x8d
  | .signedLE => 0x8e
  | .signedGT => 0x8f

def selects : Condition → BitVec 32 → Bool
  | .ordinary code, flags => X86BranchCondition.value code flags
  | .belowEqual, flags => ((1#1) == Functions._get_rflagsbits_cf flags) ||
      ((1#1) == Functions._get_rflagsbits_zf flags)
  | .signedLT, flags => !(Functions._get_rflagsbits_sf flags == Functions._get_rflagsbits_of flags)
  | .signedGE, flags => Functions._get_rflagsbits_sf flags == Functions._get_rflagsbits_of flags
  | .signedLE, flags => ((1#1) == Functions._get_rflagsbits_zf flags) ||
      !(Functions._get_rflagsbits_sf flags == Functions._get_rflagsbits_of flags)
  | .signedGT, flags => ((0#1) == Functions._get_rflagsbits_zf flags) &&
      (Functions._get_rflagsbits_sf flags == Functions._get_rflagsbits_of flags)

theorem signed_choice (state : State) (flags : BitVec 32) (present : state.regs.get? .rflags = some flags) :
    (Functions.jcc_cmovcc_setcc_spec (0x8d#8)).run state = .ok (selects .signedGE flags) state := by
  change (do
    let one ← _root_.X86Registers.readReg .rflags
    let other ← _root_.X86Registers.readReg .rflags
    pure (Functions._get_rflagsbits_sf one == Functions._get_rflagsbits_of other)
    : SailM Bool).run state = _
  rw [run_bind, readRegister_exact, present]
  dsimp only
  rw [run_bind, readRegister_exact, present]
  rfl

theorem condition_reads (state : State) (condition : Condition) (flags : BitVec 32)
    (present : state.regs.get? .rflags = some flags) :
    (Functions.jcc_cmovcc_setcc_spec (opcode condition)).run state = .ok (selects condition flags) state := by
  cases condition with
  | ordinary code => exact X86BranchCondition.executes code state flags present
  | belowEqual =>
    change (do
      let carries ← _root_.X86Registers.readReg .rflags
      let zero ← _root_.X86Registers.readReg .rflags
      pure (((1#1) == Functions._get_rflagsbits_cf carries) || ((1#1) == Functions._get_rflagsbits_zf zero))
      : SailM Bool).run state = _
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    rfl
  | signedLT =>
    change (do
      let one ← _root_.X86Registers.readReg .rflags
      let other ← _root_.X86Registers.readReg .rflags
      pure (!(Functions._get_rflagsbits_sf one == Functions._get_rflagsbits_of other))
      : SailM Bool).run state = _
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    rfl
  | signedGE => exact signed_choice state flags present
  | signedLE =>
    change (do
      let zero ← _root_.X86Registers.readReg .rflags
      let one ← _root_.X86Registers.readReg .rflags
      let other ← _root_.X86Registers.readReg .rflags
      pure (((1#1) == Functions._get_rflagsbits_zf zero) ||
        !(Functions._get_rflagsbits_sf one == Functions._get_rflagsbits_of other))
      : SailM Bool).run state = _
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    rfl
  | signedGT =>
    change (do
      let zero ← _root_.X86Registers.readReg .rflags
      let one ← _root_.X86Registers.readReg .rflags
      let other ← _root_.X86Registers.readReg .rflags
      pure (((0#1) == Functions._get_rflagsbits_zf zero) &&
        (Functions._get_rflagsbits_sf one == Functions._get_rflagsbits_of other))
      : SailM Bool).run state = _
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    dsimp only
    rw [run_bind, readRegister_exact, present]
    rfl

private theorem no_mandatory (condition : Condition) :
    Functions.compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit (opcode condition) escapePacket = 0#8 := by
  cases condition with
  | ordinary code => exact X86TwoByteDispatch.mandatory_zero code
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

private theorem no_modrm (condition : Condition) :
    Functions.two_byte_opcode_modr_m_p .Mode_64bit (0#8) (opcode condition) = false := by
  cases condition with
  | ordinary code => exact X86TwoByteDispatch.no_modrm code
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

private theorem selected [OtherOpcodeHandlers] [OtherTwoByteHandlers]
    (condition : Condition) (start tail : BitVec 48) :
    Functions.two_byte_opcode_execute .Mode_64bit start tail escapePacket (0#8) (0#8)
      (opcode condition) (0#8) (0#8) =
    Functions.x86_two_byte_jcc .Mode_64bit start tail escapePacket (0#8) (opcode condition) (0#8) (0#8) := by
  cases condition with
  | ordinary code => exact X86TwoByteDispatch.selection code start tail 0
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

def code (condition : Condition) (displacement : BitVec 32) : List Nat :=
  [0x0f, (opcode condition).toNat] ++
    (List.range 4).map fun byte => (displacement.extractLsb' (8 * byte) 8).toNat

theorem code_length (condition : Condition) (displacement : BitVec 32) :
    (code condition displacement).length = 6 := by simp [code]

structure Inputs (state : State) (condition : Condition) extends X86PlainFetch.Facts state where
  start : BitVec 48
  target : BitVec 48
  flags : BitVec 32
  displacement : BitVec 32
  upper : start.toInt + 6 < (2^47 : Int)
  jump : target.toInt = start.toInt + 6 + displacement.toInt
  rip : state.regs.get? .rip = some (start.signExtend 64)
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  bytes : codeLoaded state start.toInt (code condition displacement)

def next {state : State} {condition : Condition} (input : Inputs state condition) : BitVec 48 :=
  if selects condition input.flags then input.target else address input.start.toInt 6

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (condition : Condition) (input : Inputs state condition) :
    letI : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (X86Move.putPointer state (next input)) := by
  let : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
  let : VectorOpcodeHandlers := vector
  let second := address input.start.toInt 1
  let tail := address input.start.toInt 2
  let finish := address input.start.toInt 6
  have position (offset : Nat) (within : offset ≤ 6) :
      (address input.start.toInt offset).toInt = input.start.toInt + offset :=
    address_toInt _ (BitVec.le_toInt input.start) input.upper offset within
  have step1 : input.start.toInt + 1 = second.toInt := (position 1 (by decide)).symm
  have step2 : second.toInt + 1 = tail.toInt := by
    change (address input.start.toInt 1).toInt + 1 = (address input.start.toInt 2).toInt
    rw [position 1 (by decide), position 2 (by decide)]
    omega
  have advance : tail.toInt + 4 = finish.toInt := by
    change (address input.start.toInt 2).toInt + 4 = (address input.start.toInt 6).toInt
    rw [position 2 (by decide), position 6 (by decide)]
    omega
  have jump : input.target.toInt = finish.toInt + input.displacement.toInt := by
    change input.target.toInt = (address input.start.toInt 6).toInt + input.displacement.toInt
    rw [position 6 (by decide)]
    exact input.jump
  have startPoint : address input.start.toInt 0 = input.start := by simp [address]
  have firstByte : state.mem.get? (input.start.signExtend 52).toNat = some (0x0f#8) := by
    simpa only [startPoint] using input.bytes 0 0x0f (by simp [code])
  have secondByte : state.mem.get? (second.signExtend 52).toNat = some (opcode condition) := by
    simpa only [second, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      input.bytes 1 (opcode condition).toNat (by simp [code])
  have displacementBytes : ∀ index < 4,
      state.mem.get? ((address tail.toInt index).signExtend 52).toNat =
        some (input.displacement.extractLsb' (8 * index) 8) := by
    intro index within
    have located : address tail.toInt index = address input.start.toInt (2 + index) := by
      change address (address input.start.toInt 2).toInt index = _
      rw [position 2 (by decide)]
      simp [address, Int.add_assoc]
    rw [located]
    have byte : (code condition input.displacement)[2 + index]? =
        some (input.displacement.extractLsb' (8 * index) 8).toNat := by interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.bytes _ _ byte
  rw [X86EscapeFetch.fetch_to_escape state input.start second input.control input.attributes step1
    input.status input.fault input.msrs input.segments input.longMode input.codeMode input.application
    input.rip firstByte]
  change (@Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary other extra
    .Mode_64bit input.start second escapePacket (0#8) (0x0f#8)).run state = _
  rw [@X86TwoByteDispatch.decode_to_branch_opcode other extra (opcode condition) state input.start second
    tail (0#8) input.attributes (input.start.signExtend 64) step2 input.segments input.application input.rip
    (no_mandatory condition) (no_modrm condition) (@selected other extra condition input.start tail) secondByte]
  exact X86NearBranch.handler_with_condition (opcode condition) (selects condition input.flags) state
    input.start tail finish input.target escapePacket 0 input.attributes (input.start.signExtend 64)
    input.displacement (by omega) advance jump (by rfl) input.segments input.application input.rip
    (condition_reads state condition input.flags input.flagsKnown) input.quiet displacementBytes

end Mettapedia.Machines.TIsa.X86NativeJcc
