import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage
import Mettapedia.GSLT.LanguageDef.NativeExecutionBufferCopy

/-!
# Storage support through allocation and execution-buffer copying

The defined logical allocation and byte-store operations preserve finite
storage support. Their composition closes the invariant for every branch of
the execution buffer helper, including resource refusal and ordered caller
publication. The proof inspects the existing operations; it imposes no
preservation premise on an arbitrary allocator or external-call relation.

Logical allocation and physical C allocation remain distinct realization
boundaries. These laws neither guarantee physical allocation success nor
establish a concrete pointer/ABI representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFiniteStorage

open NativeOps
open NativeSystemAllocation

theorem source_install_bound {memory : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) (storage : Nat)
    (extent : NativeWord64.Word) (initial : Nat → Option SourceValue) :
    SourceStorageBound (sourceInstall memory storage extent initial)
      (max bound (storage + 1)) := by
  intro candidate above
  have old := bounded candidate (Nat.le_trans (Nat.le_max_left _ _) above)
  have different : candidate ≠ storage := by
    intro same
    subst candidate
    exact Nat.not_succ_le_self storage (Nat.le_trans (Nat.le_max_right _ _) above)
  constructor
  · simpa only [sourceInstall, if_neg different] using old.1
  · intro position
    simpa only [sourceInstall, if_neg different] using old.2 position

theorem target_install_bound {memory : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) (storage : Nat)
    (extent : BitVec 64) (initial : Nat → Option TargetValue) :
    TargetStorageBound (targetInstall memory storage extent initial)
      (max bound (storage + 1)) := by
  intro candidate above
  have old := bounded candidate (Nat.le_trans (Nat.le_max_left _ _) above)
  have different : candidate ≠ storage := by
    intro same
    subst candidate
    exact Nat.not_succ_le_self storage (Nat.le_trans (Nat.le_max_right _ _) above)
  constructor
  · simpa only [targetInstall, if_neg (Ne.symm different)] using old.1
  · intro position
    simpa only [targetInstall, if_pos different] using old.2 position

theorem source_install_finite {memory : SourceMemory}
    (finite : SourceFiniteStorage memory) (storage : Nat)
    (extent : NativeWord64.Word) (initial : Nat → Option SourceValue) :
    SourceFiniteStorage (sourceInstall memory storage extent initial) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨max bound (storage + 1), source_install_bound bounded storage extent initial⟩

theorem target_install_finite {memory : TargetMemory}
    (finite : TargetFiniteStorage memory) (storage : Nat)
    (extent : BitVec 64) (initial : Nat → Option TargetValue) :
    TargetFiniteStorage (targetInstall memory storage extent initial) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨max bound (storage + 1), target_install_bound bounded storage extent initial⟩

theorem source_malloc_finite {memory post : SourceMemory}
    {extent : NativeWord64.Word} {initial : Nat → Option SourceValue} {pointer : Option Address}
    (finite : SourceFiniteStorage memory)
    (allocated : SourceMalloc extent initial memory pointer post) : SourceFiniteStorage post := by
  cases allocated with
  | failure => exact finite
  | success => exact source_install_finite finite _ _ _

theorem target_malloc_finite {memory post : TargetMemory}
    {extent : BitVec 64} {initial : Nat → Option TargetValue} {pointer : Option Address}
    (finite : TargetFiniteStorage memory)
    (allocated : TargetMalloc extent initial memory pointer post) : TargetFiniteStorage post := by
  cases allocated with
  | failure => exact finite
  | success => exact target_install_finite finite _ _ _

theorem source_byte_store_bound {memory post : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) (address : Address) (bytes : List UInt8)
    (stored : NativeExecutionByteCopy.sourceStore memory address bytes = some post) :
    SourceStorageBound post bound := by
  induction bytes generalizing memory address with
  | nil =>
      have same : memory = post := Option.some.inj stored
      exact same ▸ bounded
  | cons byte rest ih =>
      cases written : sourceWrite memory address (NativeExecutionByteCopy.sourceByte byte) with
      | none =>
          simp only [NativeExecutionByteCopy.sourceStore, written, bind, Option.bind_none] at stored
          cases stored
      | some changed =>
          have tail := stored
          simp only [NativeExecutionByteCopy.sourceStore, written, bind, Option.bind_some] at tail
          exact ih (source_write_bound bounded written) (ByteViews.advance address) tail

theorem target_byte_store_bound {memory post : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) (address : Address) (bytes : List UInt8)
    (stored : NativeExecutionByteCopy.targetStore memory address bytes = some post) :
    TargetStorageBound post bound := by
  induction bytes generalizing memory address with
  | nil =>
      have same : memory = post := Option.some.inj stored
      exact same ▸ bounded
  | cons byte rest ih =>
      cases written : targetWrite memory address (NativeExecutionByteCopy.targetByte byte) with
      | none =>
          simp only [NativeExecutionByteCopy.targetStore, written] at stored
          cases stored
      | some changed =>
          have tail := stored
          simp only [NativeExecutionByteCopy.targetStore, written] at tail
          exact ih (target_write_bound bounded written) (ByteViews.advance address) tail

theorem source_byte_store_finite {memory post : SourceMemory}
    (finite : SourceFiniteStorage memory) (address : Address) (bytes : List UInt8)
    (stored : NativeExecutionByteCopy.sourceStore memory address bytes = some post) :
    SourceFiniteStorage post := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, source_byte_store_bound bounded address bytes stored⟩

theorem target_byte_store_finite {memory post : TargetMemory}
    (finite : TargetFiniteStorage memory) (address : Address) (bytes : List UInt8)
    (stored : NativeExecutionByteCopy.targetStore memory address bytes = some post) :
    TargetFiniteStorage post := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, target_byte_store_bound bounded address bytes stored⟩

theorem source_buffer_call_finite {memory post : SourceMemory}
    {garbage : Nat → UInt8} {bytes : NativeExecutionEntryGuards.SourceBytes}
    {out : Address} {succeeded : Bool} {captured : List UInt8}
    (finite : SourceFiniteStorage memory)
    (called : NativeExecutionBufferCopy.SourceCall garbage memory bytes out succeeded captured post) :
    SourceFiniteStorage post := by
  cases called with
  | empty clear _ => exact source_write_finite finite clear
  | resource clear _ allocation published =>
      exact source_write_finite (source_malloc_finite (source_write_finite finite clear) allocation)
        published
  | copied clear _ allocation publish _ _ _ store =>
      exact source_byte_store_finite
        (source_write_finite (source_malloc_finite (source_write_finite finite clear) allocation)
          publish) _ _ store

theorem target_buffer_call_finite {memory post : TargetMemory}
    {garbage : Nat → UInt8} {bytes : NativeExecutionEntryGuards.TargetBytes}
    {out : Address} {succeeded : Bool} {captured : List UInt8}
    (finite : TargetFiniteStorage memory)
    (called : NativeExecutionBufferCopy.TargetCall garbage memory bytes out succeeded captured post) :
    TargetFiniteStorage post := by
  cases called with
  | empty clear _ => exact target_write_finite finite clear
  | resource clear _ allocation published =>
      exact target_write_finite (target_malloc_finite (target_write_finite finite clear) allocation)
        published
  | copied clear _ allocation publish _ _ _ store =>
      exact target_byte_store_finite
        (target_write_finite (target_malloc_finite (target_write_finite finite clear) allocation)
          publish) _ _ store

/-- The actual buffer helper leaves space for a subsequent source invocation. -/
theorem source_buffer_call_has_next_frame {memory post : SourceMemory}
    {garbage : Nat → UInt8} {bytes : NativeExecutionEntryGuards.SourceBytes}
    {out : Address} {succeeded : Bool} {captured : List UInt8}
    (finite : SourceFiniteStorage memory)
    (called : NativeExecutionBufferCopy.SourceCall garbage memory bytes out succeeded captured post) :
    ∃ storage, sourceFreshFrame post storage :=
  source_finite_fresh (source_buffer_call_finite finite called)

theorem target_buffer_call_has_next_frame {memory post : TargetMemory}
    {garbage : Nat → UInt8} {bytes : NativeExecutionEntryGuards.TargetBytes}
    {out : Address} {succeeded : Bool} {captured : List UInt8}
    (finite : TargetFiniteStorage memory)
    (called : NativeExecutionBufferCopy.TargetCall garbage memory bytes out succeeded captured post) :
    ∃ storage, targetFreshFrame post storage :=
  target_finite_fresh (target_buffer_call_finite finite called)

/-- Even arbitrarily chosen initial bytes occupy only the selected storage. -/
theorem allocation_from_empty_is_finite (storage : Nat) (extent : BitVec 64)
    (initial : Nat → Option TargetValue) :
    TargetFiniteStorage (targetInstall ⟨fun _ _ => none, fun _ => none⟩ storage extent initial) :=
  target_install_finite empty_target_storage_finite storage extent initial

/-- A defined allocation cannot produce the unrestricted infinite-cell state. -/
theorem allocation_cannot_invent_infinite_storage {memory : TargetMemory}
    {extent : BitVec 64} {initial : Nat → Option TargetValue} {pointer : Option Address}
    (finite : TargetFiniteStorage memory) :
    ¬ TargetMalloc extent initial memory pointer ⟨fun _ _ => some .unit, fun _ => none⟩ := by
  intro allocated
  exact infinite_target_cells_not_finite (target_malloc_finite finite allocated)

end Mettapedia.GSLT.LanguageDef.NativeExecutionFiniteStorage
