import Mettapedia.Machines.TIsa.X86LegacyFetch
import Mettapedia.Machines.TIsa.Cells

/-!
# Resource copy and a fetched x86 MOV

A Window carries architectural state, address geometry and code-byte facts;
it contains no execution hypothesis. The CPU result is derived from the
pinned fetch/decode definition. The same logical update is realized by the
existing resource system and reflected from any enabled copy invocation.

Register placement and the live-register relation connect the two results.
This covers the U64 copy operation; canonicalization, emitted-byte placement,
fuel, ABI and whole-program simulation are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86ResourceCopy

open _root_.X86Registers X86RegisterRefinement

/-- MOV specializes the common architectural input window. -/
abbrev Window (state : State) (source destination : Fin 16) :=
  X86LegacyFetch.Window state (0x89#8) true source destination

local instance : MemoryPrimitives := X86Memory.ordinary

theorem Window.executes [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (source destination : Fin 16) (window : Window state source destination)
    (value : Word) (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) window.next) :=
  X86InstructionFetch.fetch_register64 state window.address window.opcodeAddress window.modrmAddress
    window.next window.control window.attributes source destination window.step1 window.step2 window.step3
    window.status window.fault window.msrs window.segments window.longMode window.codeMode
    window.application window.rip window.prefixByte window.opcodeByte window.modrmByte value known quiet

def copyAction (source destination : Fin 12) : Cells.Action (Fin 12) :=
  ⟨.copy, [source], destination⟩

theorem copy_support (source destination : Fin 12) :
    (copyAction source destination).support = {destination, source} := by
  ext register
  simp [copyAction, Cells.Action.support]

theorem copy_realized (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (source destination : Fin 12) (sourcePresent : source ∈ keys) (destinationPresent : destination ∈ keys) :
    ∃ invocation : Cells.Invocation (copyAction source destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (values source)) := by
  apply Cells.scalar_update_realized (copyAction source destination) keys values (values source)
  · rw [copy_support]
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact destinationPresent
    · exact sourcePresent
  · rfl

theorem copy_reflected (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (source destination : Fin 12) (invocation : Cells.Invocation (copyAction source destination))
    (enabled : Cells.system.Enables (Cells.encode keys values) invocation) :
    invocation.result = values source ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (values source)) := by
  obtain ⟨computed, after⟩ := Cells.scalar_update_reflected
    (copyAction source destination) invocation keys values enabled
  have result : invocation.result = values source := by
    simpa [copyAction, Scalar.evaluate] using computed.symm
  exact ⟨result, result ▸ after⟩

theorem pointer_preserves_representation (placement : Registers.Placement)
    (valid : placement.admitted .x86_64) (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (state : State) (pointer : BitVec 48)
    (represented : RepresentsOn placement valid keys values state) :
    RepresentsOn placement valid keys values (X86Move.putPointer state pointer) := by
  intro register member
  rw [X86Move.lookup_putPointer]
  exact represented register member

theorem fetched_copy_refines [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word) (state : State)
    (source destination : Fin 12)
    (window : Window state (placed placement valid (Registers.logicalSlot source))
      (placed placement valid (Registers.logicalSlot destination)))
    (sourcePresent : source ∈ keys) (destinationPresent : destination ∈ keys)
    (represented : RepresentsOn placement valid keys values state)
    (quiet : state.regs.get? .log_register_writes = some false) :
    ∃ invocation : Cells.Invocation (copyAction source destination),
      Cells.system.Enables (Cells.encode keys values) invocation ∧
      Cells.system.fire (Cells.encode keys values) invocation =
        Cells.encode keys (Function.update values destination (values source)) ∧
      ∃ after,
        (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
        RepresentsOn placement valid keys (Function.update values destination (values source)) after := by
  obtain ⟨invocation, enabled, resourceStep⟩ :=
    copy_realized keys values source destination sourcePresent destinationPresent
  let after := X86Move.putPointer
    (put state (placed placement valid (Registers.logicalSlot destination)) (values source)) window.next
  refine ⟨invocation, enabled, resourceStep, after, ?_, ?_⟩
  · exact window.executes state _ _ (values source) (represented source sourcePresent) quiet
  · apply pointer_preserves_representation
    apply put_logical_represents
    intro register member
    exact represented register (Finset.mem_of_mem_erase member)

theorem fetched_scratch_copy_preserves [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (keys : Finset (Fin 12)) (values : Fin 12 → Word) (state : State)
    (source : Fin 12) (scratch : Fin 2)
    (window : Window state (placed placement valid (Registers.logicalSlot source))
      (placed placement valid (Registers.scratchSlot scratch)))
    (sourcePresent : source ∈ keys)
    (represented : RepresentsOn placement valid keys values state)
    (quiet : state.regs.get? .log_register_writes = some false) :
    ∃ after,
      (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      RepresentsOn placement valid keys values after := by
  let after := X86Move.putPointer
    (put state (placed placement valid (Registers.scratchSlot scratch)) (values source)) window.next
  refine ⟨after, ?_, ?_⟩
  · exact window.executes state _ _ (values source) (represented source sourcePresent) quiet
  · apply pointer_preserves_representation
    exact put_scratch_represents placement valid keys values state represented scratch (values source)

theorem copy_self_fire (keys : Finset (Fin 12)) (values : Fin 12 → Word)
    (register : Fin 12) (invocation : Cells.Invocation (copyAction register register))
    (enabled : Cells.system.Enables (Cells.encode keys values) invocation) :
    Cells.system.fire (Cells.encode keys values) invocation = Cells.encode keys values := by
  have updated := (copy_reflected keys values register register invocation enabled).2
  have unchanged : Function.update values register (values register) = values := by
    funext other
    by_cases same : other = register
    · subst other
      simp
    · simp [Function.update_of_ne same]
  simpa only [unchanged] using updated

namespace Controls

example : (copyAction 0 0).readKeys = ∅ := by
  simp [copyAction, Cells.Action.readKeys]

example : ∃ invocation : Cells.Invocation (copyAction 0 1),
    Cells.system.Enables (Cells.encode {0, 1} (fun _ => (7#64))) invocation ∧
    Cells.system.fire (Cells.encode {0, 1} (fun _ => (7#64))) invocation =
      Cells.encode {0, 1} (Function.update (fun _ => (7#64)) 1 (7#64)) :=
  copy_realized {0, 1} (fun _ => 7#64) 0 1 (by simp) (by simp)

theorem wrong_copy_result_refused : ¬∃ invocation : Cells.Invocation (copyAction 0 1),
    Cells.system.Enables (Cells.encode {0, 1} (fun _ => (7#64))) invocation ∧
      invocation.result = (8#64) := by
  rintro ⟨invocation, enabled, wrong⟩
  have correct := (copy_reflected {0, 1} (fun _ => (7#64)) 0 1 invocation enabled).1
  rw [wrong] at correct
  exact (by decide : (8#64) ≠ (7#64)) correct

end Controls


end Mettapedia.Machines.TIsa.X86ResourceCopy
