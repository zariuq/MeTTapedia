import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86FetchEntry
import Mettapedia.Machines.TIsa.X86ControlFlags
import Mettapedia.Machines.TIsa.X86WordPrimitive

/-!
# One-instruction ADD/SUB at an observed native entry

The original fetched register instruction reads both operands, writes its
result and arithmetic flags, and advances RIP. The three actual bytes and
all other architectural locations are accounted for explicitly.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86ArithmeticWord
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86FetchEntry
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (operation : X86Arithmetic.DefinedOperation) (source destination : Fin 16) : List Nat :=
  [(rex true source destination).toNat,(X86Arithmetic.opcode operation).toNat,(modRM source destination).toNat]

def writes (destination : Fin 16) : Finset Register := {key destination,.rflags,.rip}

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : X86Arithmetic.DefinedOperation) (state : State) (source destination : Fin 16)
    (left right : Word) (flags : BitVec 32) (origin : Entry state)
    (leftKnown : lookup state destination = some left) (rightKnown : lookup state source = some right)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt (bytes operation source destination)) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (writes destination) state after ∧
      lookup after destination = some (X86Arithmetic.result operation left right) ∧
      after.regs.get? .rip = some ((address origin.address.toInt 3).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved state after ∧
      ∀ count ≤ 1, ∀ observed, (X86FuelPrefix.fetches count).run state = .ok () observed →
        RegisterFrame (writes destination) state observed := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let window := origin.rexWindow (X86Arithmetic.opcode operation) true source destination upper loaded
  obtain ⟨output,step⟩ := X86Arithmetic.fetched_register64 other vector operation state source destination window
    left right flags rightKnown leftKnown flagsKnown quiet
  let after := X86Move.putPointer
    (X86Flags.putFlags (put state destination (X86Arithmetic.result operation left right))
      (X86Flags.mergeFlags flags output)) (address origin.address.toInt 3)
  have run : (X86FuelPrefix.fetches 1).run state = .ok () after :=
    X86FuelPrefix.fetches_one state after step
  have frame : RegisterFrame (writes destination) state after :=
    (((put_frame state destination (X86Arithmetic.result operation left right)).trans
      (flags_frame _ (X86Flags.mergeFlags flags output))).trans (pointer_frame _ _)).mono (by simp [writes])
  have nextKnown : after.regs.get? .rflags = some (X86Flags.mergeFlags flags output) := by
    change (X86Move.putPointer (X86Flags.putFlags _ (X86Flags.mergeFlags flags output)) _).regs.get? .rflags = _
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  have noLog : ∀ destination : Fin 16, Register.log_register_writes ∉ writes destination := by decide
  refine ⟨after,X86Flags.mergeFlags flags output,run,frame,?_,?_,nextKnown,
    (frame.registers .log_register_writes (noLog destination)).trans quiet,?_,?_⟩
  · dsimp only [after]
    rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · simp [after,X86Move.putPointer]
  · unfold X86ControlFlags.Preserved
    rw [nextKnown,flagsKnown]
    simp only [Option.map_some,X86ControlFlags.arithmetic_mask]
  · exact X86WordPrimitive.one_prefixes state after _ run frame

#print axioms executes
end Mettapedia.Machines.TIsa.X86ArithmeticWord
