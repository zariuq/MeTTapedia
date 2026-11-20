import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86Arithmetic

/-! # Register arithmetic at a placed instruction -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedArithmetic

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode window)
open X86Arithmetic (DefinedOperation opcode result linkedHandlers)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev writes (destination : Fin 16) : Finset Register := {key destination, .rflags, .rip}

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (inside : offset + 3 ≤ image.size)
    (op : DefinedOperation) (source destination : Fin 16) (left right : Word)
    (sourceRead : lookup state source = some right) (destinationRead : lookup state destination = some left)
    (bytes : Code image offset (registerCode (opcode op) source destination)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧
      lookup after destination = some (result op left right) ∧
      Nonempty (At image after base (offset + 3)) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let fetch := window point inside (opcode op) source destination bytes
  obtain ⟨outFlags, ran⟩ := X86Arithmetic.fetched_register64 other vector op state source destination fetch
    left right point.flags sourceRead destinationRead point.knownFlags point.quiet
  let flags := X86Flags.mergeFlags point.flags outFlags
  let value := result op left right
  let next := address base.toInt (offset + 3)
  change (Functions.x86_fetch_decode_execute ()).run state =
    .ok () (X86Move.putPointer (X86Flags.putFlags (put state destination value) flags) next) at ran
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination value) flags) next
  let tail := (flags_frame (put state destination value) flags).trans (pointer_frame _ next)
  have frame : RegisterFrame (writes destination) state after := by
    apply ((put_frame state destination value).trans tail).mono
    intro register member
    simp only [writes, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
    tauto
  have outside : key destination ∉ ({Register.rflags} ∪ {Register.rip} : Finset Register) :=
    (by decide : ∀ reg : Fin 16, key reg ∉ ({Register.rflags} ∪ {Register.rip} : Finset Register)) destination
  have data : writes destination ⊆ dataRegisters := by
    intro register member
    simp only [writes, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact data_key destination
    · decide
    · decide
  have newFlags : after.regs.get? .rflags = some flags := by
    unfold after
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame,
    (tail.lookup _ outside).trans (lookup_put_same _ _ _),
    ⟨point.advance frame data (X86FuelPrefix.pointer_rip _ _) flags newFlags⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedArithmetic
