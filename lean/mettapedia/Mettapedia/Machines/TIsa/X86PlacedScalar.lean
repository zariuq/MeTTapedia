import Mettapedia.Machines.TIsa.X86PlacedInstruction
import Mettapedia.Machines.TIsa.X86PreparedCompare
import Mettapedia.Machines.TIsa.X86Immediate32
import Mettapedia.Machines.TIsa.X86BareImmediate32
import Mettapedia.Machines.TIsa.X86UnconditionalJump

/-! # Scalar instructions and edges of a placed image

These refinements use the fetched instruction library at arbitrary
certificate offsets. Placement and register frames supply the next fetch
boundary. No source program or captured image is fixed here.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedScalar

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Code (image : NativeImage.View) (offset : Nat) (bytes : List Nat) : Prop :=
  NativeImage.readRange? image offset bytes.length = some (bytes.map (.ofNat 8))

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) :=
  X86FrameStore.linkedHandlers (X86UnconditionalJump.linked other)

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PreparedCompare.handlers (baseHandlers other) extra

private theorem byte {image : NativeImage.View} {state : State} {base : BitVec 48}
    {entry offset : Nat} (point : At image state base entry)
    (inside : offset ≤ image.size) {bytes : List Nat} (code : Code image offset bytes)
    (index value : Nat) (present : bytes[index]? = some value) :
    state.mem.get? ((address base.toInt (offset + index)).signExtend 52).toNat =
      some (BitVec.ofNat 8 value) := by
  have read := point.bytes offset inside bytes code index value present
  rwa [point.relative_address offset index inside] at read

def registerCode (opcode : BitVec 8) (source destination : Fin 16) : List Nat :=
  [(rex true source destination).toNat, opcode.toNat, (modRM source destination).toNat]

def window {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (inside : offset + 3 ≤ image.size)
    (opcode : BitVec 8) (source destination : Fin 16)
    (code : Code image offset (registerCode opcode source destination)) :
    X86LegacyFetch.Window state opcode true source destination where
  toBasis := point.basis inside
  prefixByte := by
    simpa only [At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) code 0 (rex true source destination).toNat rfl
  opcodeByte := by
    simpa only [At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) code 1 opcode.toNat rfl
  modrmByte := by
    simpa only [At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) code 2 (modRM source destination).toNat rfl

theorem rex_immediate (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {offset : Nat} (point : At image state base offset)
    (inside : offset + 6 ≤ image.size) (destination : Fin 16) (value : BitVec 32)
    (code : Code image offset (X86Immediate32.code destination value)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (X86Immediate32.writes destination) state after ∧
      lookup after destination = some (value.zeroExtend 64) ∧
      Nonempty (At image after base (offset + 6)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : X86Immediate32.Inputs state destination value :=
    { toBasis := point.basis (by omega)
      quiet := point.quiet
      upper := by
        change (address base.toInt offset).toInt + 6 < (2^47 : Int)
        rw [point.location offset (by omega)]
        have := point.upper
        omega
      loaded := point.bytes _ (by omega) _ code }
  obtain ⟨after, ran, frame, word, rip⟩ :=
    X86Immediate32.executes (handlers other extra) vector state destination value input
  have installed : X86FrameStore.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [installed] at ran
  change after.regs.get? .rip = some ((address (address base.toInt offset).toInt 6).signExtend 64) at rip
  rw [point.relative_address offset 6 (by omega)] at rip
  have keepsFlags : ∀ index : Fin 16, Register.rflags ∉ X86Immediate32.writes index := by decide
  exact ⟨after, ran, frame, word, ⟨point.advance frame (X86Immediate32.writes_data destination)
    rip point.flags ((frame.registers .rflags (keepsFlags destination)).trans point.knownFlags)⟩⟩

theorem bare_immediate (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {offset : Nat} (point : At image state base offset)
    (inside : offset + 5 ≤ image.size) (destination : Fin 8) (value : BitVec 32)
    (code : Code image offset (X86BareImmediate32.code destination value)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (X86Immediate32.writes (X86BareImmediate32.register destination)) state after ∧
      lookup after (X86BareImmediate32.register destination) = some (value.zeroExtend 64) ∧
      Nonempty (At image after base (offset + 5)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let finish := address base.toInt (offset + 5)
  have distance : origin.opcodeAddress.toInt + 4 = finish.toInt := by
    change (address base.toInt (offset + 1)).toInt + 4 = (address base.toInt (offset + 5)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have opcode : state.mem.get? (origin.address.signExtend 52).toNat = some (X86BareImmediate32.opcode destination) := by
    simpa only [origin, At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) code 0 (X86BareImmediate32.opcode destination).toNat rfl
  have payload : ∀ index < 4, state.mem.get?
      ((address origin.opcodeAddress.toInt index).signExtend 52).toNat = some (value.extractLsb' (8 * index) 8) := by
    intro index valid
    change state.mem.get? ((address (address base.toInt (offset + 1)).toInt index).signExtend 52).toNat = _
    rw [point.relative_address (offset + 1) index (by omega), Nat.add_assoc]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) code (1 + index) (value.extractLsb' (8 * index) 8).toNat
        (by interval_cases index <;> rfl)
  have ran := X86BareImmediate32.fetched (handlers other extra) vector state destination origin
    finish value distance point.quiet opcode payload
  have installed : X86FrameStore.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [installed] at ran
  let target := X86BareImmediate32.register destination
  let after := X86Move.putPointer (put state target (value.zeroExtend 64)) finish
  have frame := X86Immediate32.result_frame state target value finish
  have keepsFlags : ∀ index : Fin 16, Register.rflags ∉ X86Immediate32.writes index := by decide
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame,
    by
      change lookup after target = _
      rw [X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance frame (X86Immediate32.writes_data _) (X86FuelPrefix.pointer_rip _ _)
      point.flags ((frame.registers .rflags (keepsFlags target)).trans point.knownFlags)⟩⟩

def compareDelta (offset rejected : Nat) : BitVec 32 :=
  .ofInt 32 ((rejected : Int) - (offset + 9))

def CompareBranch (image : NativeImage.View) (offset rejected : Nat)
    (condition : Comparison) (left right : Fin 16) : Prop :=
  offset + 9 ≤ image.size ∧ rejected ≤ image.size ∧
  (rejected : Int) = offset + 9 + (compareDelta offset rejected).toInt ∧
  Code image offset (registerCode 0x39 right left) ∧
  Code image (offset + 3) (X86NativeJcc.code (X86PreparedCompare.negative condition) (compareDelta offset rejected))

instance (image : NativeImage.View) (offset rejected : Nat) (condition : Comparison) (left right : Fin 16) :
    Decidable (CompareBranch image offset rejected condition left right) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem compare_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {offset rejected : Nat} (point : At image state base offset)
    (condition : Comparison) (left right : Fin 16)
    (checked : CompareBranch image offset rejected condition left right)
    (a b : Word) (aKnown : lookup state left = some a) (bKnown : lookup state right = some b) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame {.rflags, .rip} state after ∧
      Nonempty (At image after base (if condition.evaluate a b then offset + 9 else rejected)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, targetExtent, distance, cmp, branch⟩ := checked
  let compareWindow := window point (by omega) 0x39 right left cmp
  let branchSite : X86PreparedCompare.BranchSite state condition compareWindow.next :=
    { target := address base.toInt rejected
      displacement := compareDelta offset rejected
      upper := by
        change (address base.toInt (offset + 3)).toInt + 6 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      jump := by
        change (address base.toInt rejected).toInt =
          (address base.toInt (offset + 3)).toInt + 6 + (compareDelta offset rejected).toInt
        rw [point.location _ targetExtent, point.location _ (by omega)]
        omega
      bytes := point.bytes _ (by omega) _ branch }
  obtain ⟨after, ran, rip, frame, flags, flagsRead⟩ :=
    X86PreparedCompare.fused_register_branch_flags (baseHandlers other) extra vector state
      right left compareWindow condition a b point.flags aKnown bKnown point.knownFlags point.quiet branchSite
  change after.regs.get? .rip = some ((if condition.evaluate a b then
    address (address base.toInt (offset + 3)).toInt 6 else address base.toInt rejected).signExtend 64) at rip
  rw [point.relative_address (offset + 3) 6 (by omega)] at rip
  have next : (if condition.evaluate a b then address base.toInt (offset + 3 + 6) else address base.toInt rejected) =
      address base.toInt (if condition.evaluate a b then offset + 9 else rejected) := by
    split <;> rfl
  rw [next] at rip
  exact ⟨after, ran, frame, ⟨point.advance frame (by decide) rip flags flagsRead⟩⟩

def jumpDelta (offset target : Nat) : BitVec 32 := .ofInt 32 ((target : Int) - (offset + 5))

def Jump (image : NativeImage.View) (offset target : Nat) : Prop :=
  offset + 5 ≤ image.size ∧ target ≤ image.size ∧
  (target : Int) = offset + 5 + (jumpDelta offset target).toInt ∧
  Code image offset (X86UnconditionalJump.Block.code (jumpDelta offset target))

instance (image : NativeImage.View) (offset target : Nat) : Decidable (Jump image offset target) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem jump (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {offset target : Nat} (point : At image state base offset) (checked : Jump image offset target) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.rip} state after ∧ Nonempty (At image after base target) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, targetExtent, distance, code⟩ := checked
  let input : X86UnconditionalJump.Block.Inputs state :=
    { toBasis := point.basis (by omega)
      quiet := point.quiet
      upper := by
        change (address base.toInt offset).toInt + 5 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      displacement := jumpDelta offset target
      target := address base.toInt target
      jump := by
        change (address base.toInt target).toInt = (address base.toInt offset).toInt + 5 +
          (jumpDelta offset target).toInt
        rw [point.location _ targetExtent, point.location _ (by omega)]
        omega
      loaded := point.bytes _ (by omega) _ code }
  obtain ⟨ran, frame⟩ := X86UnconditionalJump.Block.executes (handlers other extra) vector state input
  have linked : X86UnconditionalJump.linked (handlers other extra) = handlers other extra := rfl
  change @Step X86Memory.ordinary (X86UnconditionalJump.linked (handlers other extra)) vector _ _ at ran
  rw [linked] at ran
  exact ⟨_, X86FuelPrefix.fetches_one _ _ ran, frame, ⟨point.advance frame (by decide)
    (X86FuelPrefix.pointer_rip _ _) point.flags ((frame.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

def jumpPath (image : NativeImage.View) : Nat → List Nat → Prop
  | start, [] => start ≤ image.size
  | start, target :: later => Jump image start target ∧ jumpPath image target later

instance jumpPathDecidable (image : NativeImage.View) (start : Nat) (targets : List Nat) :
    Decidable (jumpPath image start targets) :=
  match targets with
  | [] => inferInstanceAs (Decidable (start ≤ image.size))
  | target :: later =>
    letI := jumpPathDecidable image target later
    inferInstanceAs (Decidable (Jump image start target ∧ jumpPath image target later))

def jumpEnd : Nat → List Nat → Nat
  | start, [] => start
  | _, target :: later => jumpEnd target later

theorem jumps (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State}
    {base : BitVec 48} {start : Nat} (point : At image state base start)
    (targets : List Nat) (checked : jumpPath image start targets) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches targets.length).run state = .ok () after ∧
      RegisterFrame {.rip} state after ∧ Nonempty (At image after base (jumpEnd start targets)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction targets generalizing start state with
  | nil => exact ⟨state, rfl, RegisterFrame.refl _ _, ⟨point⟩⟩
  | cons target later follow =>
    obtain ⟨first, ran, frame, ⟨there⟩⟩ := jump other extra vector point checked.1
    obtain ⟨after, rest, untouched, atEnd⟩ := follow there checked.2
    have total := X86FuelPrefix.fetches_then 1 later.length _ _ _ ran rest
    exact ⟨after, by simpa only [List.length_cons, Nat.add_comm] using total,
      (frame.trans untouched).mono (by simp), atEnd⟩

end Mettapedia.Machines.TIsa.X86PlacedScalar
