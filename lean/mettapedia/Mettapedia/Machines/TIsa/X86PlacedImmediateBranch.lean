import Mettapedia.Machines.TIsa.X86PlacedScalar

/-! # Placed comparisons against a sign-extended immediate -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedImmediateBranch

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code handlers baseHandlers)
local instance : MemoryPrimitives := X86Memory.ordinary

def delta (start rejected : Nat) : BitVec 32 := .ofInt 32 ((rejected : Int) - (start + 13))

def Checked (image : NativeImage.View) (start rejected : Nat)
    (condition : Comparison) (register : Fin 16) (literal : X86CmpImmediate64.Literal) : Prop :=
  start + 13 ≤ image.size ∧ rejected ≤ image.size ∧
  (rejected : Int) = start + 13 + (delta start rejected).toInt ∧
  Code image start (X86CmpImmediate64.code register literal) ∧
  Code image (start + 7) (X86NativeJcc.code (X86PreparedCompare.negative condition) (delta start rejected))

instance (image : NativeImage.View) (start rejected : Nat) (condition : Comparison)
    (register : Fin 16) (literal : X86CmpImmediate64.Literal) :
    Decidable (Checked image start rejected condition register literal) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem immediate_byte (register : Fin 16) (literal : X86CmpImmediate64.Literal) (index : Fin 4) :
    (X86CmpImmediate64.code register literal)[3 + index.val]? =
      some (literal.bits.extractLsb' (8 * index.val) 8).toNat := by
  fin_cases index <;> rfl

theorem branches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {start rejected : Nat}
    (point : At image state base start) (condition : Comparison) (register : Fin 16)
    (literal : X86CmpImmediate64.Literal) (checked : Checked image start rejected condition register literal)
    (word : Word) (known : lookup state register = some word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame {.rflags, .rip} state after ∧
      Nonempty (At image after base (if condition.evaluate word literal.value then start + 13 else rejected)) := by
  obtain ⟨extent, rejectedInside, distance, compare, branch⟩ := checked
  let origin := point.basis (by omega)
  let target := address base.toInt (start + 7)
  have advance : origin.next.toInt + 4 = target.toInt := by
    change (address base.toInt (start + 3)).toInt + 4 = (address base.toInt (start + 7)).toInt
    rw [point.location _ (by omega), point.location _ (by omega)]
    omega
  let site : X86PreparedCompare.BranchSite state condition target :=
    { target := address base.toInt rejected
      displacement := delta start rejected
      upper := by
        change (address base.toInt (start + 7)).toInt + 6 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      jump := by
        change (address base.toInt rejected).toInt = (address base.toInt (start + 7)).toInt + 6 + _
        rw [point.location _ rejectedInside, point.location _ (by omega)]
        omega
      bytes := point.bytes _ (by omega) _ branch }
  have byte (index value : Nat) (present : (X86CmpImmediate64.code register literal)[index]? = some value) :
      state.mem.get? ((address base.toInt (start + index)).signExtend 52).toNat = some (BitVec.ofNat 8 value) := by
    have got := point.bytes start (by omega) _ compare index value present
    rwa [point.relative_address start index (by omega)] at got
  have rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true 7 register) := by
    simpa only [origin, At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte 0 (rex true 7 register).toNat rfl
  have rm : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (modRM 7 register) := by
    simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte 2 (modRM 7 register).toNat rfl
  have immediate : ∀ index < 4, state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
      some (literal.bits.extractLsb' (8 * index) 8) := by
    intro index inside
    change state.mem.get? ((address (address base.toInt (start + 3)).toInt index).signExtend 52).toNat = _
    rw [point.relative_address (start + 3) index (by omega), Nat.add_assoc]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte (3 + index) _ (immediate_byte register literal ⟨index, inside⟩)
  obtain ⟨after, ran, rip, frame, flags, flagRead⟩ := X86PreparedCompare.fused_immediate_branch_flags
    (baseHandlers other) extra vector state origin register literal condition word point.flags target advance known
    point.knownFlags point.quiet rexByte (byte 1 0x81 rfl) rm immediate site
  change after.regs.get? .rip = some ((if condition.evaluate word literal.value then
    address (address base.toInt (start + 7)).toInt 6 else address base.toInt rejected).signExtend 64) at rip
  rw [point.relative_address (start + 7) 6 (by omega)] at rip
  have selected : (if condition.evaluate word literal.value then address base.toInt (start + 7 + 6)
    else address base.toInt rejected) =
      address base.toInt (if condition.evaluate word literal.value then start + 13 else rejected) := by
    split <;> rfl
  rw [selected] at rip
  exact ⟨after, ran, frame, ⟨point.advance frame (by decide) rip flags flagRead⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedImmediateBranch
