import Mettapedia.GSLT.LanguageDef.NativeExecutionEntryGuards
import Mettapedia.GSLT.LanguageDef.NativeExecutionByteCopy
import Mettapedia.GSLT.LanguageDef.NativeSystemAllocation

/-!
The native copy_bytes helper, including its caller-pointer writes and resource
refusal. The output field is cleared before the zero-length test. A nonempty
copy allocates, publishes the allocation pointer, then copies the borrowed
bytes. The copied contents are an observation of those reads, not caller
supplied execution evidence. Initial allocation bytes are arbitrary and are
overwritten by a successful copy. Source and target relations retain the
ordered stores and the complete memory post-state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionBufferCopy

open NativeOps (Address SourceMemory TargetMemory MemoryRelated)
open NativeExecutionEntryGuards (SourceBytes TargetBytes encodeBytes)

def sourceInitial (garbage : Nat → UInt8) (element : Nat) : Option NativeOps.SourceValue :=
  some (NativeExecutionByteCopy.sourceByte (garbage element))

def targetInitial (garbage : Nat → UInt8) (element : Nat) : Option NativeOps.TargetValue :=
  some (NativeExecutionByteCopy.targetByte (garbage element))

theorem initial_correspondence (garbage : Nat → UInt8) :
    (fun element => (sourceInitial garbage element).map NativeOps.encodeValue) =
      targetInitial garbage := by
  funext element
  simp only [sourceInitial, targetInitial, Option.map_some,
    NativeExecutionByteCopy.byte_correspondence]

inductive SourceCall (garbage : Nat → UInt8) :
    SourceMemory → SourceBytes → Address → Bool → List UInt8 → SourceMemory → Prop where
  | empty {memory cleared : SourceMemory} {bytes : SourceBytes} {out : Address}
      (clear : NativeOps.sourceWrite memory out (.reference none) = some cleared)
      (zero : bytes.length.val = 0) : SourceCall garbage memory bytes out true [] cleared
  | resource {memory cleared allocated post : SourceMemory} {bytes : SourceBytes} {out : Address}
      (clear : NativeOps.sourceWrite memory out (.reference none) = some cleared)
      (nonempty : bytes.length.val ≠ 0)
      (allocation : NativeSystemAllocation.SourceMalloc bytes.length (sourceInitial garbage)
        cleared none allocated)
      (published : NativeOps.sourceWrite allocated out (.reference none) = some post) :
      SourceCall garbage memory bytes out false [] post
  | copied {memory cleared allocated published post : SourceMemory} {bytes : SourceBytes}
      {out input output : Address} {captured : List UInt8}
      (clear : NativeOps.sourceWrite memory out (.reference none) = some cleared)
      (nonempty : bytes.length.val ≠ 0)
      (allocation : NativeSystemAllocation.SourceMalloc bytes.length (sourceInitial garbage)
        cleared (some output) allocated)
      (publish : NativeOps.sourceWrite allocated out (.reference (some output)) = some published)
      (inputPointer : bytes.pointer = some input)
      (separate : NativeExecutionByteCopy.disjoint input output bytes.length.val)
      (read : NativeOps.ByteViews.sourceBlock published input bytes.length.val = some captured)
      (store : NativeExecutionByteCopy.sourceStore published output captured = some post) :
      SourceCall garbage memory bytes out true captured post

inductive TargetCall (garbage : Nat → UInt8) :
    TargetMemory → TargetBytes → Address → Bool → List UInt8 → TargetMemory → Prop where
  | empty {memory cleared : TargetMemory} {bytes : TargetBytes} {out : Address}
      (clear : NativeOps.targetWrite memory out (.reference none) = some cleared)
      (zero : bytes.length = 0) : TargetCall garbage memory bytes out true [] cleared
  | resource {memory cleared allocated post : TargetMemory} {bytes : TargetBytes} {out : Address}
      (clear : NativeOps.targetWrite memory out (.reference none) = some cleared)
      (nonempty : bytes.length ≠ 0)
      (allocation : NativeSystemAllocation.TargetMalloc bytes.length (targetInitial garbage)
        cleared none allocated)
      (published : NativeOps.targetWrite allocated out (.reference none) = some post) :
      TargetCall garbage memory bytes out false [] post
  | copied {memory cleared allocated published post : TargetMemory} {bytes : TargetBytes}
      {out input output : Address} {captured : List UInt8}
      (clear : NativeOps.targetWrite memory out (.reference none) = some cleared)
      (nonempty : bytes.length ≠ 0)
      (allocation : NativeSystemAllocation.TargetMalloc bytes.length (targetInitial garbage)
        cleared (some output) allocated)
      (publish : NativeOps.targetWrite allocated out (.reference (some output)) = some published)
      (inputPointer : bytes.pointer = some input)
      (separate : NativeExecutionByteCopy.disjoint input output bytes.length.toNat)
      (read : NativeOps.ByteViews.targetBlock published input bytes.length.toNat = some captured)
      (store : NativeExecutionByteCopy.targetStore published output captured = some post) :
      TargetCall garbage memory bytes out true captured post

theorem call_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (garbage : Nat → UInt8) (bytes : SourceBytes)
    (out : Address) (succeeded : Bool) (captured : List UInt8) (post : SourceMemory)
    (called : SourceCall garbage source bytes out succeeded captured post) :
    ∃ native, TargetCall garbage target (encodeBytes bytes) out succeeded captured native ∧
      MemoryRelated post native := by
  cases called with
  | empty clear zero =>
    obtain ⟨native, wrote, memories⟩ := NativeOps.memory_write_forward source target related
      out (.reference none) _ clear
    exact ⟨native, .empty wrote ((NativeWord64.encode_eq_zero bytes.length).mpr zero), memories⟩
  | resource clear nonempty allocation published =>
    obtain ⟨nativeCleared, nativeClear, clearedRelated⟩ := NativeOps.memory_write_forward
      source target related out (.reference none) _ clear
    obtain ⟨nativeAllocated, nativeMalloc, allocatedRelated⟩ := NativeSystemAllocation.malloc_forward
      _ nativeCleared clearedRelated bytes.length (sourceInitial garbage) none _ allocation
    rw [initial_correspondence] at nativeMalloc
    obtain ⟨nativePost, nativePublish, memories⟩ := NativeOps.memory_write_forward
      _ nativeAllocated allocatedRelated out (.reference none) _ published
    refine ⟨nativePost, .resource nativeClear ?_ nativeMalloc nativePublish, memories⟩
    exact fun zero => nonempty ((NativeWord64.encode_eq_zero bytes.length).mp zero)
  | copied clear nonempty allocation publish inputPointer separate read store =>
    obtain ⟨nativeCleared, nativeClear, clearedRelated⟩ := NativeOps.memory_write_forward
      source target related out (.reference none) _ clear
    obtain ⟨nativeAllocated, nativeMalloc, allocatedRelated⟩ := NativeSystemAllocation.malloc_forward
      _ nativeCleared clearedRelated bytes.length (sourceInitial garbage) _ _ allocation
    rw [initial_correspondence] at nativeMalloc
    obtain ⟨nativePublished, nativePublish, publishedRelated⟩ := NativeOps.memory_write_forward
      _ nativeAllocated allocatedRelated out (.reference _) _ publish
    obtain ⟨nativePost, nativeStore, memories⟩ := NativeExecutionByteCopy.store_forward
      _ nativePublished publishedRelated _ _ _ store
    refine ⟨nativePost, .copied nativeClear ?_ nativeMalloc nativePublish inputPointer ?_ ?_
      nativeStore, memories⟩
    · exact fun zero => nonempty ((NativeWord64.encode_eq_zero bytes.length).mp zero)
    · simpa only [encodeBytes, NativeWord64.encode_toNat] using separate
    · simpa only [encodeBytes, NativeWord64.encode_toNat,
        NativeOps.ByteViews.block_correspondence _ nativePublished publishedRelated] using read

theorem call_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (garbage : Nat → UInt8) (bytes : SourceBytes)
    (out : Address) (succeeded : Bool) (captured : List UInt8) (native : TargetMemory)
    (called : TargetCall garbage target (encodeBytes bytes) out succeeded captured native) :
    ∃ post, SourceCall garbage source bytes out succeeded captured post ∧
      MemoryRelated post native := by
  cases called with
  | empty clear zero =>
    obtain ⟨post, wrote, memories⟩ := NativeOps.memory_write_backward source target related
      out (.reference none) _ clear
    exact ⟨post, .empty wrote ((NativeWord64.encode_eq_zero bytes.length).mp zero), memories⟩
  | resource clear nonempty allocation published =>
    obtain ⟨sourceCleared, sourceClear, clearedRelated⟩ := NativeOps.memory_write_backward
      source target related out (.reference none) _ clear
    have encodedMalloc := allocation
    rw [← initial_correspondence] at encodedMalloc
    obtain ⟨sourceAllocated, sourceMalloc, allocatedRelated⟩ := NativeSystemAllocation.malloc_backward
      sourceCleared _ clearedRelated bytes.length (sourceInitial garbage) none _ encodedMalloc
    obtain ⟨post, sourcePublish, memories⟩ := NativeOps.memory_write_backward
      sourceAllocated _ allocatedRelated out (.reference none) _ published
    refine ⟨post, .resource sourceClear ?_ sourceMalloc sourcePublish, memories⟩
    exact fun zero => nonempty ((NativeWord64.encode_eq_zero bytes.length).mpr zero)
  | copied clear nonempty allocation publish inputPointer separate read store =>
    obtain ⟨sourceCleared, sourceClear, clearedRelated⟩ := NativeOps.memory_write_backward
      source target related out (.reference none) _ clear
    have encodedMalloc := allocation
    rw [← initial_correspondence] at encodedMalloc
    obtain ⟨sourceAllocated, sourceMalloc, allocatedRelated⟩ := NativeSystemAllocation.malloc_backward
      sourceCleared _ clearedRelated bytes.length (sourceInitial garbage) _ _ encodedMalloc
    obtain ⟨sourcePublished, sourcePublish, publishedRelated⟩ := NativeOps.memory_write_backward
      sourceAllocated _ allocatedRelated out (.reference _) _ publish
    obtain ⟨post, sourceStore, memories⟩ := NativeExecutionByteCopy.store_backward
      sourcePublished _ publishedRelated _ _ _ store
    refine ⟨post, .copied sourceClear ?_ sourceMalloc sourcePublish inputPointer ?_ ?_
      sourceStore, memories⟩
    · exact fun zero => nonempty ((NativeWord64.encode_eq_zero bytes.length).mpr zero)
    · simpa only [encodeBytes, NativeWord64.encode_toNat] using separate
    · simpa only [encodeBytes, NativeWord64.encode_toNat,
        NativeOps.ByteViews.block_correspondence sourcePublished _ publishedRelated] using read

theorem captured_length (garbage : Nat → UInt8) (memory post : SourceMemory)
    (bytes : SourceBytes) (out : Address) (captured : List UInt8)
    (called : SourceCall garbage memory bytes out true captured post) :
    captured.length = bytes.length.val := by
  cases called with
  | empty _ zero => exact zero.symm
  | copied _ _ _ _ _ _ read _ => exact NativeOps.ByteViews.source_block_length _ _ _ _ read

theorem resource_failure_clears_output (garbage : Nat → UInt8) (memory post : SourceMemory)
    (bytes : SourceBytes) (out : Address)
    (called : SourceCall garbage memory bytes out false [] post) :
    NativeOps.sourceRead post out = some (.reference none) := by
  cases called with
  | resource _ _ _ published => exact NativeOps.source_read_after_write _ _ _ _ published

theorem successful_copy_publishes_contents (garbage : Nat → UInt8) (memory post : SourceMemory)
    (bytes : SourceBytes) (out : Address) (captured : List UInt8)
    (called : SourceCall garbage memory bytes out true captured post) :
    ∃ pointer : Option Address, NativeOps.sourceRead post out = some (.reference pointer) ∧
      match pointer with
      | none => captured = []
      | some base => NativeOps.ByteViews.sourceBlock post base captured.length = some captured := by
  cases called with
  | empty clear _ => exact ⟨none, NativeOps.source_read_after_write _ _ _ _ clear, rfl⟩
  | copied clear _ allocation publish _ _ _ store =>
    have separate := NativeSystemAllocation.source_success_avoids_live_read _ _ _ _ _ out
      (.reference none) allocation (NativeOps.source_read_after_write _ _ _ _ clear)
    refine ⟨some _, ?_, NativeExecutionByteCopy.stored_contents _ _ _ _ store⟩
    rw [NativeExecutionByteCopy.store_preserves_earlier_read _ _ _ out _ store (Or.inl separate)]
    exact NativeOps.source_read_after_write _ _ _ _ publish

theorem successful_copy_contents_on_target (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (garbage : Nat → UInt8) (bytes : SourceBytes)
    (out : Address) (captured : List UInt8) (native : TargetMemory)
    (called : TargetCall garbage target (encodeBytes bytes) out true captured native) :
    ∃ pointer : Option Address, NativeOps.targetRead native out = some (.reference pointer) ∧
      match pointer with
      | none => captured = []
      | some base => NativeOps.ByteViews.targetBlock native base captured.length = some captured := by
  obtain ⟨post, sourceCall, memories⟩ := call_backward source target related garbage bytes out true
    captured native called
  obtain ⟨pointer, published, contents⟩ := successful_copy_publishes_contents garbage source post
    bytes out captured sourceCall
  refine ⟨pointer, ?_, ?_⟩
  · rw [NativeOps.memory_read_correspondence post native memories, published]
    rfl
  · cases pointer with
    | none => exact contents
    | some base =>
      change NativeOps.ByteViews.targetBlock native base captured.length = some captured
      change NativeOps.ByteViews.sourceBlock post base captured.length = some captured at contents
      rw [NativeOps.ByteViews.block_correspondence post native memories]
      exact contents

end Mettapedia.GSLT.LanguageDef.NativeExecutionBufferCopy
