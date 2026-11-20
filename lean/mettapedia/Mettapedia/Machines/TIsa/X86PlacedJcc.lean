import Mettapedia.Machines.TIsa.X86PlacedScalar

/-! # Conditional jumps between placed instruction boundaries -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PlacedJcc

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code handlers)
local instance : MemoryPrimitives := X86Memory.ordinary

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {offset target : Nat} (point : At image state base offset)
    (inside : offset + 6 ≤ image.size) (targetInside : target ≤ image.size)
    (condition : X86NativeJcc.Condition) (displacement : BitVec 32)
    (relative : (target : Int) = offset + 6 + displacement.toInt)
    (code : Code image offset (X86NativeJcc.code condition displacement)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {.rip} state after ∧
      Nonempty (At image after base (if X86NativeJcc.selects condition point.flags then target else offset + 6)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : X86NativeJcc.Inputs state condition :=
    { point.mode with
      start := address base.toInt offset
      target := address base.toInt target
      flags := point.flags
      displacement := displacement
      upper := by
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      jump := by
        rw [point.location target targetInside, point.location offset (by omega)]
        omega
      rip := point.rip
      flagsKnown := point.knownFlags
      quiet := point.quiet
      bytes := point.bytes _ (by omega) _ code }
  have ran := X86NativeJcc.fetched (handlers other extra) extra vector state condition input
  have installed : X86EscapeFetch.linked (handlers other extra) extra = handlers other extra := rfl
  rw [installed] at ran
  let next := if X86NativeJcc.selects condition point.flags then target else offset + 6
  have arrives : X86NativeJcc.next input = address base.toInt next := by
    change (if X86NativeJcc.selects condition point.flags then address base.toInt target
      else address (address base.toInt offset).toInt 6) = _
    rw [point.relative_address offset 6 (by omega)]
    unfold next
    split <;> rfl
  rw [arrives] at ran
  have frame := pointer_frame state (address base.toInt next)
  exact ⟨_, X86FuelPrefix.fetches_one _ _ ran, frame, ⟨point.advance frame (by decide)
    (X86FuelPrefix.pointer_rip _ _) point.flags ((frame.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedJcc
