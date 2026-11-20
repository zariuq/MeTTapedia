import Mettapedia.Machines.TIsa.X86PlacedMemory
import Mettapedia.Machines.TIsa.X86DataLoad

/-! # Placed loads from an already admitted word cell -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedWordLoad

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Encoding Cell Controls Reads)
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (encoding : Encoding) (destination : Fin 16) (displacement : BitVec 32) : List Nat :=
  match encoding with
  | .direct base _ _ => X86DataLoad.code true destination base displacement
  | .r12 => X86SibQword.code .load destination displacement

theorem loads (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (controls : Controls state)
    (encoding : Encoding) (destination : Fin 16) (displacement : BitVec 32)
    (baseValue value : Word) (cell : Cell baseValue displacement)
    (baseKnown : lookup state encoding.base = some baseValue) (read : Reads state cell.address value)
    (extent : offset + encoding.length ≤ image.size)
    (code : Code image offset (bytes encoding destination displacement)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination, .rip} state after ∧ lookup after destination = some value ∧
      Nonempty (At image after base (offset + encoding.length)) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have enough : 3 ≤ encoding.length := by cases encoding <;> simp [Encoding.length]
  let origin := point.basis (by omega)
  have upper : origin.address.toInt + encoding.length < (2^47 : Int) := by
    change (address base.toInt offset).toInt + encoding.length < (2^47 : Int)
    rw [point.location offset (by omega)]
    have := point.upper
    omega
  have loaded := point.bytes _ (by omega) _ code
  have fetch : ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination, .rip} state after ∧ lookup after destination = some value ∧
      after.regs.get? .rip = some ((address base.toInt (offset + encoding.length)).signExtend 64) := by
    cases encoding with
    | direct baseReg noSib noStack =>
      let input : X86DataLoad.Inputs state true destination baseReg displacement :=
        { toBasis := origin
          noSib := noSib
          noStack := noStack
          visible := controls.visible
          controls := controls.controls
          baseValue := baseValue
          word := value
          flags := point.flags
          dataAddress := cell.address
          baseKnown := baseKnown
          controlKnown := controls.controlsKnown
          flagsKnown := point.knownFlags
          visibleKnown := controls.visibleKnown
          quiet := point.quiet
          upper := upper
          dataUpper := cell.upper
          effective := cell.effective
          safe := Or.inr cell.aligned
          loaded := loaded
          dataPresent := read }
      obtain ⟨after, ran, frame, found, rip⟩ := X86DataLoad.executes other vector state true destination
        baseReg displacement input
      change after.regs.get? .rip = some
        ((address (address base.toInt offset).toInt 7).signExtend 64) at rip
      rw [point.relative_address offset 7 (by omega)] at rip
      exact ⟨after, ran, frame, found, rip⟩
    | r12 =>
      let input : X86SibQword.Inputs state displacement :=
        { toBasis := origin
          controls := controls.controls
          visible := controls.visible
          flags := point.flags
          baseValue := baseValue
          target := cell.address
          controlsRead := controls.controlsKnown
          visibleRead := controls.visibleKnown
          flagsRead := point.knownFlags
          quiet := point.quiet
          baseKnown := baseKnown
          effective := cell.effective
          upper := upper
          dataUpper := cell.upper
          aligned := cell.aligned }
      have ran := X86SibQword.fetched_load other vector state destination displacement input loaded value read
      change (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer (put state destination value) (address (address base.toInt offset).toInt 8))
        at ran
      rw [point.relative_address offset 8 (by omega)] at ran
      let finish := address base.toInt (offset + 8)
      exact ⟨_, X86FuelPrefix.fetches_one _ _ ran,
        ((put_frame state destination value).trans (pointer_frame _ finish)).mono (by simp),
        by rw [X86Move.lookup_putPointer, lookup_put_same], X86FuelPrefix.pointer_rip _ finish⟩
  obtain ⟨after, ran, frame, found, rip⟩ := fetch
  have outside : Register.rflags ∉ ({key destination, .rip} : Finset Register) :=
    (by decide : ∀ reg : Fin 16, Register.rflags ∉ ({key reg, .rip} : Finset Register)) destination
  have data : ({key destination, .rip} : Finset Register) ⊆ dataRegisters := by
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact data_key destination
    · decide
  exact ⟨after, ran, frame, found, ⟨point.advance frame data rip point.flags
    ((frame.registers .rflags outside).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedWordLoad
