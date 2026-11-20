import Mettapedia.Machines.TIsa.X86PlacedScalar

/-! # The sign-extended entry sentinel and immediate comparisons -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedLiteral

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code handlers)
local instance : MemoryPrimitives := X86Memory.ordinary

private abbrev prefixes := X86LegacyFetch.packet (0xc7#8)

theorem sentinel_handler (state : State) (origin : X86LegacyFetch.Basis state)
    (finish : BitVec 48) (advance : origin.next.toInt + 4 = finish.toInt)
    (upper : origin.next.toInt + 4 ≤ (2^47 : Int))
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ i < 4, state.mem.get? ((address origin.next.toInt i).signExtend 52).toNat = some (255#8)) :
    (Functions.x86_mov_op_en_mi .Mode_64bit origin.address origin.next prefixes
      (0x48#8) (0xc7#8) (0xc6#8) (0#8)).run state =
        .ok () (X86Move.putPointer (put state 6 (0xffffffffffffffff#64)) finish) := by
  have immediateBytes : ∀ i < 4, state.mem.get? ((address origin.next.toInt i).signExtend 52).toNat =
      some ((0xffffffff#32).extractLsb' (8 * i) 8) := by
    intro i within
    interval_cases i <;> exact bytes _ (by decide)
  have length : Functions.check_instruction_length origin.address finish (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  have rme := X86FrameStore.read_dword state origin.next (origin.address.signExtend 64) origin.attributes
    (0xffffffff#32) upper origin.segments origin.application origin.rip immediateBytes
  unfold Functions.x86_mov_op_en_mi
  dsimp only
  simp only [show ((0xc7#8) == (0xc6#8)) = false from rfl]
  rw [show Functions.select_operand_size .Mode_64bit false (0x48#8) true prefixes false false false =
    (pure 4 : SailM Int) from rfl, run_bind, run_pure]
  dsimp only
  rw [show ((Functions._get_modr_m_mod (0xc6#8)) == (3#2)) = true from rfl, if_pos rfl,
    run_bind, run_pure]
  dsimp only
  rw [show Functions.select_segment_register .Mode_64bit prefixes (Functions._get_modr_m_mod (0xc6#8))
    (Functions._get_modr_m_r_m (0xc6#8)) (0#8) =
    (pure 3 : SailM seg_reg_idx) from rfl, run_bind, run_pure]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) from rfl,
    run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [show Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl]
  rw [show Sail.BitVec.signExtend origin.next 64 = origin.next.signExtend 64 from rfl, run_bind, rme]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state origin.next (4#48) finish (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false
      (Sail.BitVec.zeroExtend (0xffffffffffffffff#64) 128)
      3 (0#64) (0#52) (rex true 0 6) (Functions._get_modr_m_r_m (modRM 0 6)) (3#2) (0#8)
    Functions.write_iptr .Mode_64bit finish).run state = _
  rw [run_bind, X86Move.write_operand_register64 state 0 6 (0xffffffffffffffff#64) quiet]
  apply X86Move.write_pointer64
  exact ((put_frame state 6 (0xffffffffffffffff#64)).registers .log_register_writes (by decide)).trans quiet

private theorem code_byte {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start : Nat} (point : At image state base start) (inside : start ≤ image.size)
    {bytes : List Nat} (code : Code image start bytes) (offset value : Nat) (found : bytes[offset]? = some value) :
    state.mem.get? ((address base.toInt (start + offset)).signExtend 52).toNat = some (.ofNat 8 value) := by
  have read := point.bytes _ inside bytes code offset value found
  rwa [point.relative_address start offset inside] at read

def sentinelCode : List Nat := [0x48, 0xc7, 0xc6, 0xff, 0xff, 0xff, 0xff]

theorem sentinel (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start) (inside : start + 7 ≤ image.size)
    (code : Code image start sentinelCode) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.rsi, .rip} state after ∧ lookup after 6 = some (0xffffffffffffffff#64) ∧
      Nonempty (At image after base (start + 7)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin : X86LegacyFetch.Window state 0xc7 true 0 6 :=
    { toBasis := point.basis (by omega)
      prefixByte := by
        change state.mem.get? ((address base.toInt start).signExtend 52).toNat = some (0x48#8)
        simpa only [Nat.add_zero] using code_byte point (by omega) code 0 0x48 rfl
      opcodeByte := code_byte point (by omega) code 1 0xc7 rfl
      modrmByte := code_byte point (by omega) code 2 0xc6 rfl }
  let finish := address base.toInt (start + 7)
  have advance : origin.next.toInt + 4 = finish.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have upper : origin.next.toInt + 4 ≤ (2^47 : Int) := by
    rw [advance]
    have := BitVec.toInt_lt (x := finish)
    omega
  have bytes : ∀ byte < 4, state.mem.get? ((address origin.next.toInt byte).signExtend 52).toNat = some (255#8) := by
    intro byte within
    change state.mem.get? ((address (address base.toInt (start + 3)).toInt byte).signExtend 52).toNat = _
    rw [point.relative_address (start + 3) byte (by omega), Nat.add_assoc]
    exact code_byte point (by omega) code _ 255 (by interval_cases byte <;> rfl)
  let after := X86Move.putPointer (put state 6 (0xffffffffffffffff#64)) finish
  have ran : (Functions.x86_fetch_decode_execute ()).run state = .ok () after := by
    rw [X86LegacyFetch.Window.dispatches _ ((X86LegacyFetch.checkOpcode_iff _).mp (by decide)) true state 0 6 origin]
    change (Functions.x86_mov_op_en_mi .Mode_64bit origin.address origin.next prefixes
      (0x48#8) (0xc7#8) (0xc6#8) (0#8)).run state = _
    exact sentinel_handler state origin.toBasis finish advance upper point.quiet bytes
  have frame : RegisterFrame {.rsi, .rip} state after := ((put_frame _ _ _).trans (pointer_frame _ _)).mono (by decide)
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame,
    by simp only [after, X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance frame (by decide) (X86FuelPrefix.pointer_rip _ _) point.flags
      ((frame.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

def compareDelta (start rejected : Nat) : BitVec 32 := .ofInt 32 ((rejected : Int) - (start + 13))

def CompareBranch (image : NativeImage.View) (start rejected : Nat)
    (condition : Comparison) (reg : Fin 16) (literal : X86CmpImmediate64.Literal) : Prop :=
  start + 13 ≤ image.size ∧ rejected ≤ image.size ∧
  (rejected : Int) = start + 13 + (compareDelta start rejected).toInt ∧
  Code image start (X86CmpImmediate64.code reg literal) ∧
  Code image (start + 7) (X86NativeJcc.code (X86PreparedCompare.negative condition) (compareDelta start rejected))

instance (image : NativeImage.View) (start rejected : Nat)
    (condition : Comparison) (reg : Fin 16) (literal : X86CmpImmediate64.Literal) :
    Decidable (CompareBranch image start rejected condition reg literal) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem compare_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start rejected : Nat} (point : At image state base start)
    (condition : Comparison) (reg : Fin 16) (literal : X86CmpImmediate64.Literal)
    (checked : CompareBranch image start rejected condition reg literal)
    (value : Word) (known : lookup state reg = some value) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame {.rflags, .rip} state after ∧
      Nonempty (At image after base (if condition.evaluate value literal.value then start + 13 else rejected)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨inside, target, relative, compare, jump⟩ := checked
  let origin := point.basis (by omega)
  let finish := address base.toInt (start + 7)
  have advance : origin.next.toInt + 4 = finish.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ (by omega)]
    omega
  let branch : X86PreparedCompare.BranchSite state condition finish :=
    { target := address base.toInt rejected
      displacement := compareDelta start rejected
      upper := by
        rw [show finish.toInt = base.toInt + (start + 7 : Nat) from point.location _ (by omega)]
        have := point.upper
        omega
      jump := by
        rw [point.location _ target, show finish.toInt = base.toInt + (start + 7 : Nat) from point.location _ (by omega)]
        omega
      bytes := point.bytes _ (by omega) _ jump }
  have data : ∀ i < 4, state.mem.get? ((address origin.next.toInt i).signExtend 52).toNat =
      some (literal.bits.extractLsb' (8 * i) 8) := by
    intro i within
    change state.mem.get? ((address (address base.toInt (start + 3)).toInt i).signExtend 52).toNat = _
    rw [point.relative_address (start + 3) i (by omega), Nat.add_assoc]
    have encoded : (X86CmpImmediate64.code reg literal)[3 + i]? =
      some ((literal.bits.extractLsb' (8 * i) 8).toNat) := by interval_cases i <;> rfl
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      code_byte point (by omega) compare (3 + i) _ encoded
  obtain ⟨after, ran, rip, frame, flags, read⟩ :=
    X86PreparedCompare.fused_immediate_branch_flags (X86PlacedScalar.baseHandlers other) extra vector state origin
      reg literal condition value point.flags finish advance known point.knownFlags point.quiet
      (by simpa only [origin, At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        code_byte point (by omega) compare 0 (rex true 7 reg).toNat rfl)
      (code_byte point (by omega) compare 1 0x81 rfl)
      (by simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        code_byte point (by omega) compare 2 (modRM 7 reg).toNat rfl) data branch
  change after.regs.get? .rip = some ((if condition.evaluate value literal.value then
      address (address base.toInt (start + 7)).toInt 6 else address base.toInt rejected).signExtend 64) at rip
  rw [point.relative_address (start + 7) 6 (by omega)] at rip
  have next : (if condition.evaluate value literal.value then address base.toInt (start + 7 + 6)
      else address base.toInt rejected) =
      address base.toInt (if condition.evaluate value literal.value then start + 13 else rejected) := by split <;> rfl
  rw [next] at rip
  exact ⟨after, ran, frame, ⟨point.advance frame (by decide) rip flags read⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedLiteral
