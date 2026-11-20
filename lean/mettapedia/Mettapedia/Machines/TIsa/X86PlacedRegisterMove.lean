import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86ResourceCopy

/-! # A word copy at a placed instruction boundary -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PlacedRegisterMove

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode window)
local instance : MemoryPrimitives := X86Memory.ordinary

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (inside : offset + 3 ≤ image.size)
    (source destination : Fin 16) (value : Word) (known : lookup state source = some value)
    (code : Code image offset (registerCode 0x89 source destination)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination, .rip} state after ∧ lookup after destination = some value ∧
      Nonempty (At image after base (offset + 3)) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  let fetch : X86ResourceCopy.Window state source destination := window point inside _ _ _ code
  let next := address base.toInt (offset + 3)
  let after := X86Move.putPointer (put state destination value) next
  have ran := fetch.executes state source destination value known point.quiet
  have frame : RegisterFrame {key destination, .rip} state after :=
    ((put_frame state destination value).trans (pointer_frame _ next)).mono (by simp)
  have flagsFixed : Register.rflags ∉ ({key destination, .rip} : Finset Register) :=
    (by decide : ∀ reg : Fin 16, Register.rflags ∉ ({key reg, .rip} : Finset Register)) destination
  have data : ({key destination, .rip} : Finset Register) ⊆ dataRegisters := by
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact data_key destination
    · decide
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame,
    by rw [show after = X86Move.putPointer (put state destination value) next from rfl,
      X86Move.lookup_putPointer, lookup_put_same],
    ⟨point.advance frame data (X86FuelPrefix.pointer_rip _ _) point.flags
      ((frame.registers .rflags flagsFixed).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedRegisterMove
