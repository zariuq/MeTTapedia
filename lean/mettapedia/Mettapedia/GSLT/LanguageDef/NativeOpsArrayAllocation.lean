import Mettapedia.GSLT.LanguageDef.NativeOpsArrayBaseDiscipline
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryExtension
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryEffects
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval
import Mettapedia.GSLT.LanguageDef.NativeSystemAllocation

/-!
# Array bases through allocation and initialization

These laws use the existing allocator and initialization relations. They
cover contents and addresses, without identifying logical storage with an ABI.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ArrayAllocation

open NativeWord64 (Word)
open NativeSystemAllocation

theorem install_extends (memory : SourceMemory) (storage : Nat) (extent : Word)
    (initial : Nat → Option SourceValue) (fresh : sourceFresh memory storage) :
    MemoryExtension.Extends memory (sourceInstall memory storage extent initial) := by
  intro candidate index value stored
  by_cases same : candidate = storage
  · subst candidate
    rw [fresh.2 index] at stored
    contradiction
  · simpa only [sourceInstall, same, if_false] using stored

theorem malloc_extends {memory after : SourceMemory} {extent : Word}
    {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial memory pointer after) : MemoryExtension.Extends memory after := by
  cases allocated with
  | failure => exact MemoryExtension.refl memory
  | success fresh => exact install_extends memory _ extent initial fresh

theorem install_discipline {memory : SourceMemory} (valid : ArrayBaseDiscipline.Memory memory)
    (storage : Nat) (extent : Word) (initial : Nat → Option SourceValue)
    (initialValid : ∀ index value, initial index = some value → ArrayBaseDiscipline.value value = true) :
    ArrayBaseDiscipline.Memory (sourceInstall memory storage extent initial) := by
  intro candidate index value stored
  by_cases same : candidate = storage
  · by_cases inside : index < extent.val
    · exact initialValid index value (by simpa only [sourceInstall, same, inside, if_true] using stored)
    · simp only [sourceInstall, same, inside, if_true, if_false] at stored
      contradiction
  · exact valid candidate index value (by simpa only [sourceInstall, same, if_false] using stored)

theorem malloc_discipline {memory after : SourceMemory} (valid : ArrayBaseDiscipline.Memory memory)
    {extent : Word} {initial : Nat → Option SourceValue} {pointer : Option Address}
    (initialValid : ∀ index value, initial index = some value → ArrayBaseDiscipline.value value = true)
    (allocated : SourceMalloc extent initial memory pointer after) : ArrayBaseDiscipline.Memory after := by
  cases allocated with
  | failure => exact valid
  | success _ => exact install_discipline valid _ extent initial initialValid

theorem malloc_array_value {memory after : SourceMemory} {extent : Word}
    {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial memory pointer after) (element : NativeType) :
    ArrayBaseDiscipline.value (.array element pointer extent) = true := by
  cases allocated <;> rfl

theorem initialize_discipline {before after : SourceMemory} (valid : ArrayBaseDiscipline.Memory before)
    {address : Option Address} {count : Nat} {value : SourceValue}
    (validValue : ArrayBaseDiscipline.value value = true)
    (initialized : SourceInitialize address count value before after) : ArrayBaseDiscipline.Memory after := by
  induction initialized with
  | empty => exact valid
  | next wrote rest ih => exact ih (ArrayBaseDiscipline.write valid _ _ validValue wrote) validValue

theorem zero_initialize_discipline {before after : SourceMemory} (valid : ArrayBaseDiscipline.Memory before)
    {address : Option Address} {count : Nat} {interface : Interface} {element : NativeType} {zero : SourceValue}
    (zeroed : SourceZero interface element zero)
    (initialized : SourceInitialize address count zero before after) : ArrayBaseDiscipline.Memory after :=
  initialize_discipline valid (ArrayBaseDiscipline.zero zeroed) initialized

theorem advance_keeps_array_base (element : NativeType) (address : Address) (length : Word) (offset : Nat)
    (valid : ArrayBaseDiscipline.value (.array element (some address) length) = true) :
    ArrayBaseDiscipline.value (.array element (some (advanceAddress address offset)) length) = true := valid

theorem success_cannot_return_interior_pointer (extent : Word) (initial : Nat → Option SourceValue)
    (before after : SourceMemory) (pointer : Address) (interior : pointer.fields ≠ []) :
    ¬ SourceMalloc extent initial before (some pointer) after := by
  intro allocated
  exact interior (source_success_base_live extent initial before after pointer allocated).2.1

theorem initialize_other_storage {before after : SourceMemory} {pointer : Option Address}
    {count : Nat} {value : SourceValue} (initialized : SourceInitialize pointer count value before after)
    (storage element : Nat) (different : ∀ address, pointer = some address → storage ≠ address.storage) :
    after.cells storage element = before.cells storage element := by
  induction initialized with
  | empty => rfl
  | @next address count value before middle after wrote rest ih =>
    have away := different address rfl
    have tailAway : ∀ next, some (advanceAddress address 1) = some next → storage ≠ next.storage := by
      intro next same
      cases same
      exact away
    exact (ih tailAway).trans (source_write_preserves_other_cells before address value middle wrote
      storage element (.inl away))

theorem malloc_initialize_extends {before allocatedMemory after : SourceMemory} {extent : Word}
    {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial before pointer allocatedMemory)
    {count : Nat} {value : SourceValue}
    (initialized : SourceInitialize pointer count value allocatedMemory after) :
    MemoryExtension.Extends before after := by
  intro storage element observed stored
  have away : ∀ address, pointer = some address → storage ≠ address.storage := by
    intro address same
    have allocation : SourceMalloc extent initial before (some address) allocatedMemory := same ▸ allocated
    exact source_success_avoids_live_read extent initial before allocatedMemory address
      ⟨storage, element, []⟩ observed allocation
      (by simp only [sourceRead, sourceReadPath, stored, Option.bind_some])
  exact (initialize_other_storage initialized storage element away).trans
    (malloc_extends allocated storage element observed stored)

end Mettapedia.GSLT.LanguageDef.NativeOps.ArrayAllocation
