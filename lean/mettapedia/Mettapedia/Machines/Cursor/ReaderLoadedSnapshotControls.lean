import Mettapedia.Machines.Cursor.ReaderLoadedSnapshot

/-!
# Residency controls: pending, absence, stale metadata and duplicate loading
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderLoadedSnapshot.Controls

open StampedSnapshots

def original : State Nat := ⟨StampedSnapshots.add StampedSnapshots.empty 7, unloaded⟩
def reader : Reader := start original.source
def resident : State Nat := loadSlot original 0
def retired : State Nat := ReaderLoadedSnapshot.remove resident 0

theorem unloaded_is_pending : ReaderLoadedSnapshot.step original.cache reader = .pending reader := by decide

theorem load_preserves_original_birth :
    resident.source.clock = 1 ∧ resident.source.next = 1 ∧
      resident.cache 0 = some (some ⟨7, 1, none⟩) ∧ resident.cache 1 = none := by decide

theorem load_then_read : ReaderLoadedSnapshot.step resident.cache reader =
    .ready (.value 0 7) ⟨1, 1, 1⟩ := by decide

theorem invalidated_removal_is_pending :
    ReaderLoadedSnapshot.step retired.cache (start retired.source) =
      .pending (start retired.source) := by decide

theorem fresh_reader_after_reload_skips :
    ReaderLoadedSnapshot.step (loadSlot retired 0).cache (start retired.source) =
      .ready .skip ⟨2, 1, 1⟩ := by decide

/-- A reader's original timestamp still sees the retired occurrence after
its payload and updated death metadata load later. -/
theorem old_reader_after_reload_sees_entry :
    ReaderLoadedSnapshot.step (loadSlot retired 0).cache reader =
      .ready (.value 0 7) ⟨1, 1, 1⟩ := by decide

def staleRemoval : State Nat := ⟨StampedSnapshots.remove resident.source 0, resident.cache⟩

theorem stale_cache_resurrects_retired_row :
    ReaderLoadedSnapshot.step staleRemoval.cache (start staleRemoval.source) =
      .ready (.value 0 7) ⟨2, 1, 1⟩ ∧
      StampedSnapshots.step staleRemoval.source (start staleRemoval.source) =
        (.skip, ⟨2, 1, 1⟩) := by decide

def observedAbsent : State Nat :=
  ⟨StampedSnapshots.empty, load StampedSnapshots.empty unloaded 0⟩

def newlyAdded : State Nat := ReaderLoadedSnapshot.add observedAbsent 7
def staleAbsence : State Nat := ⟨StampedSnapshots.add observedAbsent.source 7, observedAbsent.cache⟩

theorem add_invalidates_cached_absence :
    observedAbsent.cache 0 = some none ∧ newlyAdded.cache 0 = none ∧
      ReaderLoadedSnapshot.step newlyAdded.cache (start newlyAdded.source) =
        .pending (start newlyAdded.source) := by decide

theorem stale_absence_hides_new_row :
    ReaderLoadedSnapshot.step staleAbsence.cache (start staleAbsence.source) =
      .ready .skip ⟨1, 1, 1⟩ ∧
      StampedSnapshots.step staleAbsence.source (start staleAbsence.source) =
        (.value 0 7, ⟨1, 1, 1⟩) := by decide

def hole : State Nat := ⟨⟨0, 1, fun _ => none⟩, unloaded⟩

theorem loaded_absence_is_not_pending_or_exhaustion :
    ReaderLoadedSnapshot.step hole.cache (start hole.source) = .pending (start hole.source) ∧
      ReaderLoadedSnapshot.step (loadSlot hole 0).cache (start hole.source) =
        .ready .skip ⟨0, 1, 1⟩ ∧
      ReaderLoadedSnapshot.step (loadSlot hole 0).cache ⟨0, 1, 1⟩ =
        .ready .exhausted ⟨0, 1, 1⟩ := by decide

def payloads (store : Store Nat) : List Nat :=
  (snapshot store (start store)).filterMap (fun row => row.map Prod.snd)

/-- Treating residency as a logical insertion duplicates an existing
occurrence and invents a new birth. A load must not do this. -/
theorem loading_as_add_duplicates_logical_content :
    payloads (loadSlot original 0).source = [7] ∧
      payloads (StampedSnapshots.add original.source 7) = [7, 7] := by decide

theorem writes_and_loads_preserve_cache_invariant :
    CacheValid (loadSlot retired 0).source (loadSlot retired 0).cache :=
  valid_loadSlot retired (valid_remove resident (valid_loadSlot original (valid_unloaded _) 0) 0) 0

#print axioms valid_load
#print axioms valid_add
#print axioms valid_remove
#print axioms step_refines
#print axioms step_after_load

end Mettapedia.Machines.Cursor.ReaderLoadedSnapshot.Controls
