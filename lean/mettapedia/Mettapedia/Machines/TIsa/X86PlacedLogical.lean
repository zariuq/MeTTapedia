import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86LogicalWord

/-! # A logical word operation at a placed instruction boundary -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedLogical

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
local instance : MemoryPrimitives := X86Memory.ordinary

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start + 3 ≤ image.size)
    (operation : X86LogicalWord.Kind) (source destination : Fin 16) (left right : Word)
    (sourceRead : lookup state source = some right) (destRead : lookup state destination = some left)
    (code : Code image start (X86LogicalWord.code operation source destination)) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (X86LogicalWord.writes destination) state after ∧
      lookup after destination = some (X86LogicalWord.result operation left right) ∧
      Nonempty (At image after base (start + 3)) := by
  let input : X86LogicalWord.Inputs state operation source destination :=
    { toBasis := point.basis inside
      left := left
      right := right
      flags := point.flags
      sourceKnown := sourceRead
      destinationKnown := destRead
      flagsKnown := point.knownFlags
      quiet := point.quiet
      upper := by
        change (address base.toInt start).toInt + 3 < (2^47 : Int)
        rw [point.location _ (by omega)]
        have := point.upper
        omega
      loaded := point.bytes _ (by omega) _ code }
  obtain ⟨after, flags, ran, frame, value, flagRead, rip⟩ :=
    X86LogicalWord.executes other vector operation state source destination input
  change after.regs.get? .rip = some ((address (address base.toInt start).toInt 3).signExtend 64) at rip
  rw [point.relative_address start 3 (by omega)] at rip
  exact ⟨after, ran, frame, value, ⟨point.advance frame (X86LogicalWord.writes_data _) rip flags flagRead⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedLogical
