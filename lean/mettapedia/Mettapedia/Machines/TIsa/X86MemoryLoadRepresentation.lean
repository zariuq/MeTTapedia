import Mettapedia.Machines.TIsa.X86MemoryBounds

/-!
# Representation after a native memory read

A load updates its destination register and keeps the byte and capability
observations in the memory view. The statement applies at any legal code
placement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryFieldLoad

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86MemoryView X86MemoryReadback X86MemoryBounds

def physical (register : Fin 12) : Fin 16 := placed (Registers.canonical .x86_64)
  (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register)

theorem other_register_outside : ∀ destination register : Fin 12, register ≠ destination →
    key (physical register) ∉ insert (key (physical destination)) X86Bounds.writes := by decide

theorem frame_outside : ∀ destination : Fin 12, destination ≠ 0 →
    key (7 : Fin 16) ∉ insert (key (physical destination)) X86Bounds.writes := by decide

theorem load_represents (view : View) (values : Key → Word) (before after : State)
    (destination : Fin 12) (unlocked : destination ≠ 0) (value : Word)
    (known : ∀ location ∈ view.keys, readback view.modes before location = some (values location))
    (frame : RegisterFrame (insert (key (physical destination)) X86Bounds.writes) before after)
    (result : lookup after (physical destination) = some value) :
    represents view (Cells.encode view.keys (Function.update values (.register destination) value)) after := by
  refine ⟨Function.update values (.register destination) value,rfl,?_⟩
  intro location member
  by_cases register : ∃ name, location = Memory.Key.register name
  · obtain ⟨name,rfl⟩ := register
    by_cases same : name = destination
    · subst name
      change lookup after (physical destination) = _
      rw [Function.update_self]
      exact result
    · have old := known (.register name) member
      change lookup before (physical name) = some (values (.register name)) at old
      change lookup after (physical name) = _
      rw [frame.lookup _ (other_register_outside destination name same)]
      simpa only [Function.update_of_ne (by intro equal; exact same (Memory.Key.register.inj equal))] using old
  · have readonly : ∀ name, location ≠ Memory.Key.register name := by
      intro name same
      exact register ⟨name,same⟩
    have bytes : memory after = memory before := by funext address; change after.mem.get? address = before.mem.get? address; rw [frame.memory]
    rw [readback_nonregister view.modes before after bytes (frame.lookup 7 (frame_outside destination unlocked)) location readonly]
    simpa only [Function.update_of_ne (readonly destination)] using known location member

end Mettapedia.Machines.TIsa.X86MemoryFieldLoad
