import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86ResourceCopy

/-!
# Resource arithmetic and fetched x86 instructions

The existing resource system realizes and reflects in-place ADD/SUB updates.
The live-register relation joins those updates to the original Sail
fetch/dispatch/handler execution, including flags and RIP. Aliased inputs
consume one destination occurrence and require no duplicate read cell.

This is an instruction-level relation. X86BinBlock composes the captured
copy/arithmetic/copy sequence. Fuel, ABI and whole-program refinement remain
separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86ResourceBinary

open _root_.X86Registers X86RegisterRefinement X86Arithmetic

def binary : DefinedOperation → Binary
  | .add => .add | .sub => .sub

def action {Key : Type} (operation : DefinedOperation) (source destination : Key) : Cells.Action Key :=
  ⟨.binary (binary operation), [destination, source], destination⟩

theorem support {Key : Type} [DecidableEq Key] (operation : DefinedOperation) (source destination : Key) :
    (action operation source destination).support = {destination, source} := by
  ext register
  simp [action, Cells.Action.support]

theorem computes {Key : Type} (operation : DefinedOperation) (values : Key → Word)
    (source destination : Key) :
    (action operation source destination).scalar.evaluate
      ((action operation source destination).inputs.map values) =
      some (result operation (values destination) (values source)) := by
  cases operation <;> rfl

theorem realized {Key : Type} [DecidableEq Key]
    (operation : DefinedOperation) (keys : Finset Key) (values : Key → Word)
    (source destination : Key) (sourcePresent : source ∈ keys) (destinationPresent : destination ∈ keys) :
    ∃ invocation : Cells.Invocation (action operation source destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination
          (result operation (values destination) (values source))) := by
  apply Cells.scalar_update_realized _ keys values _
  · rw [support]
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact destinationPresent
    · exact sourcePresent
  · exact computes operation values source destination

theorem reflected {Key : Type} [DecidableEq Key]
    (operation : DefinedOperation) (keys : Finset Key) (values : Key → Word)
    (source destination : Key) (invocation : Cells.Invocation (action operation source destination))
    (enabled : Cells.system.Enables (Cells.encode keys values) invocation) :
    invocation.result = result operation (values destination) (values source) ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination
          (result operation (values destination) (values source))) := by
  obtain ⟨computed, after⟩ := Cells.scalar_update_reflected
    (action operation source destination) invocation keys values enabled
  rw [computes] at computed
  have same := (Option.some.inj computed).symm
  exact ⟨same, same ▸ after⟩

local instance : MemoryPrimitives := X86Memory.ordinary

theorem fetched_inplace_refines (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation)
    (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word) (state : State)
    (source destination : Fin 12)
    (window : X86LegacyFetch.Window state (opcode operation) true
      (placed placement valid (Registers.logicalSlot source))
      (placed placement valid (Registers.logicalSlot destination)))
    (sourcePresent : source ∈ keys) (destinationPresent : destination ∈ keys)
    (represented : RepresentsOn placement valid keys values state)
    (flags : BitVec 32) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ invocation : Cells.Invocation (action operation source destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination
          (result operation (values destination) (values source))) ∧
      ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
        RepresentsOn placement valid keys
          (Function.update values destination (result operation (values destination) (values source))) after := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨invocation, enabled, resourceStep⟩ :=
    realized operation keys values source destination sourcePresent destinationPresent
  obtain ⟨output, executed⟩ := fetched_register64 other vector operation state _ _ window
    (values destination) (values source) flags
    (represented source sourcePresent) (represented destination destinationPresent) flagsKnown quiet
  refine ⟨invocation, enabled, resourceStep, _, executed, ?_⟩
  apply X86ResourceCopy.pointer_preserves_representation
  apply X86Flags.putFlags_represents
  apply put_logical_represents
  intro register member
  exact represented register (Finset.mem_of_mem_erase member)

namespace Controls

private abbrev double : Cells.Action (Fin 1) := action .add 0 0

theorem alias_has_no_separate_read : double.readKeys = ∅ := by decide

theorem alias_realized :
    ∃ invocation : Cells.Invocation double,
      Cells.system.Enables (Cells.encode {0} (fun _ => (7#64))) invocation ∧
      Cells.system.fire (Cells.encode {0} (fun _ => (7#64))) invocation =
        Cells.encode {0} (fun _ => (14#64)) := by
  obtain ⟨invocation, enabled, fired⟩ :=
    realized .add ({0} : Finset (Fin 1)) (fun _ => (7#64)) 0 0 (by simp) (by simp)
  refine ⟨invocation, enabled, ?_⟩
  rw [fired]
  apply Cells.encode_congr
  intro register _
  have same : register = (0 : Fin 1) := Subsingleton.elim _ _
  subst register
  rw [Function.update_self]
  rfl

theorem wrong_result_refused (invocation : Cells.Invocation double)
    (enabled : Cells.system.Enables (Cells.encode {0} (fun _ => (7#64))) invocation) :
    invocation.result ≠ (13#64) := by
  have same := (reflected .add {0} (fun _ => (7#64)) 0 0 invocation enabled).1
  rw [same]
  decide

end Controls
end Mettapedia.Machines.TIsa.X86ResourceBinary

#print axioms Mettapedia.Machines.TIsa.X86ResourceBinary.fetched_inplace_refines
