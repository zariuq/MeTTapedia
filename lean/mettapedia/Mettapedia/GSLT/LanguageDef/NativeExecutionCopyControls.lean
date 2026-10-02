import Mettapedia.GSLT.LanguageDef.NativeExecutionBufferCopy

/-!
Observable allocation/copy controls for the native execution interface:
captured bytes, caller publication, empty input, allocation failure and invalid
storage. They inspect the actual call and memory relations, not a second test
implementation. No control supplies a physical execution observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionCopyControls

open NativeOps (Address SourceMemory sourceRead)
open NativeExecutionBufferCopy (SourceCall)

private def out : Address := ⟨100, 0, []⟩
private def input : Address := ⟨100, 1, []⟩
private def output : Address := ⟨200, 0, []⟩
private def previous : Address := ⟨99, 0, []⟩
private def garbage (_ : Nat) : UInt8 := 173
private def bytes : NativeExecutionEntryGuards.SourceBytes := ⟨some input, 2⟩

private def memory : SourceMemory :=
  ⟨fun storage element => if storage = 100 then match element with
    | 0 => some (.reference (some previous))
    | 1 => some (NativeExecutionByteCopy.sourceByte 7)
    | 2 => some (NativeExecutionByteCopy.sourceByte 9)
    | _ => none
  else none, fun _ => none⟩

private def cleared : SourceMemory := NativeOps.sourceStoreCell memory 100 0 (.reference none)
private def allocated : SourceMemory :=
  NativeSystemAllocation.sourceInstall cleared 200 2 (NativeExecutionBufferCopy.sourceInitial garbage)
private def published : SourceMemory :=
  NativeOps.sourceStoreCell allocated 100 0 (.reference (some output))
private def copied : SourceMemory :=
  NativeOps.sourceStoreCell (NativeOps.sourceStoreCell published 200 0
    (NativeExecutionByteCopy.sourceByte 7)) 200 1 (NativeExecutionByteCopy.sourceByte 9)
private def refused : SourceMemory := NativeOps.sourceStoreCell cleared 100 0 (.reference none)

theorem nonempty_copy_executes : SourceCall garbage memory bytes out true [7, 9] copied := by
  apply SourceCall.copied (cleared := cleared) (allocated := allocated) (published := published)
    (input := input) (output := output)
  · rfl
  · decide
  · exact .success ⟨rfl, fun _ => rfl⟩
  · rfl
  · rfl
  · exact Or.inl (by decide)
  · rfl
  · rfl

theorem actual_copied_bytes_are_read_back :
    NativeOps.ByteViews.sourceBlock copied output 2 = some [7, 9] := rfl

theorem successful_copy_replaces_previous_pointer :
    sourceRead copied out = some (.reference (some output)) := rfl

theorem copy_retains_original_borrowed_inputs :
    NativeOps.ByteViews.sourceBlock copied input 2 = some [7, 9] := rfl

theorem allocation_garbage_is_overwritten :
    NativeOps.ByteViews.sourceBlock allocated output 2 = some [173, 173] ∧
      NativeOps.ByteViews.sourceBlock copied output 2 = some [7, 9] := ⟨rfl, rfl⟩

theorem copied_buffer_keeps_its_owned_extent : copied.owned 200 = some 2 := rfl

theorem resource_refusal_executes_before_borrowed_read :
    SourceCall garbage memory ⟨none, 2⟩ out false [] refused := by
  exact .resource (cleared := cleared) (allocated := cleared) rfl (by decide)
    (.failure cleared) rfl

theorem resource_refusal_clears_previous_pointer :
    sourceRead refused out = some (.reference none) :=
  NativeExecutionBufferCopy.resource_failure_clears_output garbage memory refused ⟨none, 2⟩
    out resource_refusal_executes_before_borrowed_read

theorem resource_refusal_retains_input_bytes :
    NativeOps.ByteViews.sourceBlock refused input 2 = some [7, 9] := rfl

theorem empty_null_copy_executes_without_allocation :
    SourceCall garbage memory ⟨none, 0⟩ out true [] cleared := .empty rfl rfl

theorem empty_copy_clears_previous_pointer : sourceRead cleared out = some (.reference none) := rfl

theorem empty_copy_retains_all_ownership : cleared.owned = memory.owned := rfl

theorem missing_output_has_no_call (succeeded : Bool) (captured : List UInt8) (post : SourceMemory) :
    ¬SourceCall garbage memory bytes ⟨300, 0, []⟩ succeeded captured post := by
  intro called
  cases called with
  | empty clear _ => cases clear
  | resource clear _ _ _ => cases clear
  | copied clear _ _ _ _ _ _ _ => cases clear

theorem live_borrowed_storage_is_not_fresh : ¬NativeSystemAllocation.sourceFresh memory 100 := by
  intro fresh
  have absent := fresh.2 0
  cases absent

theorem overlapping_byte_copy_has_no_transition :
    NativeExecutionByteCopy.sourceCopy memory input input 1 = none := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeExecutionCopyControls
